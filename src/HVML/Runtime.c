//./Type.hs//

#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <time.h>

typedef uint8_t  Tag;
typedef uint32_t Lab;
typedef uint32_t Loc;
typedef uint64_t Term;
typedef uint32_t u32;
typedef uint64_t u64;

typedef _Atomic(Term) ATerm;

// Runtime Types
// -------------

// Global State Type
typedef struct {
  Term*  sbuf; // reduction stack buffer
  u64*   spos; // reduction stack position
  ATerm* heap; // global node buffer
  u64*   size; // global node length
  u64*   itrs; // interaction count
  u64*   frsh; // fresh dup label count
  Term (*book[4096])(Term); // functions
} State;

// Global State Value
static State HVM = {
  .sbuf = NULL,
  .spos = NULL,
  .heap = NULL,
  .size = NULL,
  .itrs = NULL,
  .frsh = NULL,
  .book = {NULL}
};

// Constants
// ---------

#define DP0 0x00
#define DP1 0x01
#define VAR 0x02
#define SUB 0x03
#define REF 0x04
#define LET 0x05
#define APP 0x06
#define ANN 0x07
#define MAT 0x08
#define OPX 0x09
#define OPY 0x0A
#define ERA 0x0B
#define LAM 0x0C
#define SUP 0x0D
#define TYP 0x0E
#define CTR 0x0F
#define W32 0x10
#define CHR 0x11

#define OP_ADD 0x00
#define OP_SUB 0x01
#define OP_MUL 0x02
#define OP_DIV 0x03
#define OP_MOD 0x04
#define OP_EQ  0x05
#define OP_NE  0x06
#define OP_LT  0x07
#define OP_GT  0x08
#define OP_LTE 0x09
#define OP_GTE 0x0A
#define OP_AND 0x0B
#define OP_OR  0x0C
#define OP_XOR 0x0D
#define OP_LSH 0x0E
#define OP_RSH 0x0F

#define DUP_F 0xFFF
#define SUP_F 0xFFE
#define LOG_F 0xFFD
#define FRESH_F 0xFFC

#define LAZY 0x0
#define STRI 0x1
#define PARA 0x2

#define VOID 0x00000000000000

// Heap
// ----

Loc get_len() {
  return *HVM.size;
}

u64 get_itr() {
  return *HVM.itrs;
}

u64 fresh() {
  return (*HVM.frsh)++;
}

void set_len(Loc value) {
  *HVM.size = value;
}

void set_itr(Loc value) {
  *HVM.itrs = value;
}

// Terms
// ------

Term term_new(Tag tag, Lab lab, Loc loc) {
  Term tag_enc = tag;
  Term lab_enc = ((Term)lab) << 8;
  Term loc_enc = ((Term)loc) << 32;
  return tag_enc | lab_enc | loc_enc;
}

Tag term_tag(Term x) {
  return x & 0x7F;
}

Tag term_bit(Term x) {
  return (x >> 7) & 1;
}

Lab term_lab(Term x) {
  return (x >> 8) & 0xFFFFFF;
}

Loc term_loc(Term x) {
  return (x >> 32) & 0xFFFFFFFF;
}

Term term_set_bit(Term term) {
  return term | (1ULL << 7);
}

// u12v2
// -----

u64 u12v2_new(u64 x, u64 y) {
  return (y << 12) | x;
}

u64 u12v2_x(u64 u12v2) {
  return u12v2 & 0xFFF;
}

u64 u12v2_y(u64 u12v2) {
  return u12v2 >> 12;
}

// Atomics
// -------

Term swap(Loc loc, Term term) {
  Term val = atomic_exchange_explicit(&HVM.heap[loc], term, memory_order_relaxed);
  if (val == 0) {
    printf("SWAP 0 at %x\n", loc);
    exit(0);
  }
  return val;
}

Term got(Loc loc) {
  Term val = atomic_load_explicit(&HVM.heap[loc], memory_order_relaxed);
  if (val == 0) {
    printf("GOT 0 at %x\n", loc);
    exit(0);
  }
  return val;
}

void set(Loc loc, Term term) {
  atomic_store_explicit(&HVM.heap[loc], term, memory_order_relaxed);
}

Term take(Loc loc) {
  return swap(loc, VOID);
}

// Allocation
// ----------

Loc alloc_node(Loc arity) {
  u64 old = *HVM.size;
  *HVM.size += arity;
  return old;
}

Loc inc_itr() {
  u64 old = *HVM.itrs;
  *HVM.itrs += 1;
  return old;
}

// Stringification
// ---------------

void print_tag(Tag tag) {
  switch (tag) {
    case SUB: printf("SUB"); break;
    case VAR: printf("VAR"); break;
    case DP0: printf("DP0"); break;
    case DP1: printf("DP1"); break;
    case APP: printf("APP"); break;
    case LAM: printf("LAM"); break;
    case TYP: printf("TYP"); break;
    case ANN: printf("ANN"); break;
    case ERA: printf("ERA"); break;
    case SUP: printf("SUP"); break;
    case REF: printf("REF"); break;
    case LET: printf("LET"); break;
    case CTR: printf("CTR"); break;
    case MAT: printf("MAT"); break;
    case W32: printf("W32"); break;
    case CHR: printf("CHR"); break;
    case OPX: printf("OPX"); break;
    case OPY: printf("OPY"); break;
    default : printf("???"); break;
  }
}

void print_term(Term term) {
  printf("term_new(");
  print_tag(term_tag(term));
  printf(",0x%06x,0x%09x)", term_lab(term), term_loc(term));
}

void print_term_ln(Term term) {
  print_term(term);
  printf("\n");
}

void print_heap() {
  Loc len = get_len();
  for (Loc i = 0; i < len; i++) {
    Term term = got(i);
    if (term != 0) {
      printf("set(0x%09x, ", i);
      print_term(term);
      printf(");\n");
    }
  }
}

// Evaluation
// ----------

// @foo(&L{ax ay} b c ...)
// ----------------------- REF-SUP-COPY (when @L not in @foo)
// ! &L{bx by} = b
// ! &L{cx cy} = b
// ...
// &L{@foo(ax bx cx ...) @foo(ay by cy ...)}
// TODO: implement this in an index-generic way.
// that is, receive the index where the SUP is.
// clone all other indexes with a DUP
Term reduce_ref_sup(Term ref, u32 idx) {
  inc_itr();
  Loc ref_loc = term_loc(ref);
  Lab ref_lab = term_lab(ref);
  u64 fun_id = u12v2_x(ref_lab);
  u64 arity  = u12v2_y(ref_lab);
  if (idx >= arity) {
    printf("ERROR: Invalid index in reduce_ref_sup\n");
    exit(1);
  }
  Term sup = got(ref_loc + idx);
  if (term_tag(sup) != SUP) {
    printf("ERROR: Expected SUP at index %u\n", idx);
    exit(1);
  }
  Lab sup_lab = term_lab(sup);
  Loc sup_loc = term_loc(sup);
  Term sup0 = got(sup_loc + 0);
  Term sup1 = got(sup_loc + 1);
  // Allocate space for new REF node arguments for the second branch
  Loc ref1_loc = alloc_node(arity);
  for (u64 i = 0; i < arity; ++i) {
    if (i != idx) {
      // Duplicate argument
      Term arg = got(ref_loc + i);
      Loc dup_loc = alloc_node(2);
      set(dup_loc + 0, arg);
      set(dup_loc + 1, term_new(SUB, 0, 0));
      set(ref_loc + i, term_new(DP0, sup_lab, dup_loc));
      set(ref1_loc + i, term_new(DP1, sup_lab, dup_loc));
    } else {
      // Set the SUP components directly
      set(ref_loc + i, sup0);
      set(ref1_loc + i, sup1);
    }
  }
  // Create new REF nodes
  Term ref0 = term_new(REF, ref_lab, ref_loc);
  Term ref1 = term_new(REF, ref_lab, ref1_loc);
  // Reuse sup_loc to create the new SUP node
  set(sup_loc + 0, ref0);
  set(sup_loc + 1, ref1);
  return term_new(SUP, sup_lab, sup_loc);
}

// @foo(a b c ...)
// -------------------- REF
// book[foo](a b c ...)
Term reduce_ref(Term ref) {
  //printf("reduce_ref "); print_term(ref); printf("\n");
  //printf("call %d %p\n", term_loc(ref), HVM.book[term_loc(ref)]);
  inc_itr();
  return HVM.book[u12v2_x(term_lab(ref))](ref);
}

// ! x = val
// bod
// --------- LET
// x <- val
// bod
Term reduce_let(Term let, Term val) {
  //printf("reduce_let "); print_term(let); printf("\n");
  inc_itr();
  Loc let_loc = term_loc(let);
  Term bod    = got(let_loc + 2);
  set(let_loc + 0, val);
  return bod;
}

// (* a)
// ----- APP-ERA
// *
Term reduce_app_era(Term app, Term era) {
  //printf("reduce_app_era "); print_term(app); printf("\n");
  inc_itr();
  return era;
}

// (λx(body) a)
// ------------ APP-LAM
// x <- a
// body
Term reduce_app_lam(Term app, Term lam) {
  //printf("reduce_app_lam "); print_term(app); printf("\n");
  inc_itr();
  Loc app_loc = term_loc(app);
  Loc lam_loc = term_loc(lam);
  Term arg    = got(app_loc + 1);
  Term bod    = got(lam_loc + 1);
  set(lam_loc + 0, arg);
  return bod;
}

// (&L{a b} c)
// ----------------- APP-SUP
// ! &L{x0 x1} = c
// &L{(a x0) (b x1)}
Term reduce_app_sup(Term app, Term sup) {
  //printf("reduce_app_sup "); print_term(app); printf("\n");
  inc_itr();
  Loc app_loc = term_loc(app);
  Loc sup_loc = term_loc(sup);
  Lab sup_lab = term_lab(sup);
  Term arg    = got(app_loc + 1);
  Term tm0    = got(sup_loc + 0);
  Term tm1    = got(sup_loc + 1);
  Loc du0     = alloc_node(2);
  //Loc su0     = alloc_node(2);
  //Loc ap0     = alloc_node(2);
  Loc ap0     = app_loc;
  Loc su0     = sup_loc;
  Loc ap1     = alloc_node(2);
  set(du0 + 0, arg);
  set(du0 + 1, term_new(SUB, 0, 0));
  set(ap0 + 0, tm0);
  set(ap0 + 1, term_new(DP0, sup_lab, du0));
  set(ap1 + 0, tm1);
  set(ap1 + 1, term_new(DP1, sup_lab, du0));
  set(su0 + 0, term_new(APP, 0, ap0));
  set(su0 + 1, term_new(APP, 0, ap1));
  return term_new(SUP, sup_lab, su0);
}

// (%x(F) a)
// ----------- APP-TYP
// x <- λk(y)
// %y(F <k:a>)
Term reduce_app_typ(Term app, Term typ) {
  //printf("reduce_app_typ "); print_term(app); printf("\n");
  inc_itr();
  Loc app_loc = term_loc(app);
  Loc typ_loc = term_loc(typ);
  Term arg    = got(app_loc + 1);
  Term bod    = got(typ_loc + 1);
  Loc ap0     = app_loc;
  Loc lm0     = alloc_node(2);
  Loc an0     = alloc_node(2);
  Loc ty0     = alloc_node(2);
  set(lm0 + 0, term_new(SUB, 0, 0));
  set(lm0 + 1, term_new(VAR, 0, ty0));
  set(an0 + 0, term_new(VAR, 0, lm0));
  set(an0 + 1, arg);
  set(ty0 + 0, term_new(SUB, 0, 0));
  set(ty0 + 1, term_new(APP, 0, ap0));
  set(ap0 + 0, bod);
  set(ap0 + 1, term_new(ANN, 0, an0));
  set(typ_loc + 0, term_new(LAM, 0, lm0));
  return term_new(TYP, 0, ty0);
}

// (#{x y z ...} a)
// ---------------- APP-CTR
// ⊥
Term reduce_app_ctr(Term app, Term ctr) {
  //printf("reduce_app_ctr "); print_term(app); printf("\n");
  printf("invalid:app-ctr");
  exit(0);
}

// (123 a)
// ------- APP-W32
// ⊥
Term reduce_app_w32(Term app, Term w32) {
  //printf("reduce_app_w32 "); print_term(app); printf("\n");
  printf("invalid:app-w32");
  exit(0);
}

// ! &L{x y} = *
// ------------- DUP-ERA
// x <- *
// y <- *
Term reduce_dup_era(Term dup, Term era) {
  //printf("reduce_dup_era "); print_term(dup); printf("\n");
  inc_itr();
  Loc dup_loc = term_loc(dup);
  Tag dup_num = term_tag(dup) == DP0 ? 0 : 1;
  set(dup_loc + 0, era);
  set(dup_loc + 1, era);
  return got(dup_loc + dup_num);
}

// ! &L{r s} = λx(f)
// ----------------- DUP-LAM
// ! &L{f0 f1} = f
// r <- λx0(f0)
// s <- λx1(f1)
// x <- &L{x0 x1}
Term reduce_dup_lam(Term dup, Term lam) {
  //printf("reduce_dup_lam "); print_term(dup); printf("\n");
  inc_itr();
  Loc dup_loc = term_loc(dup);
  Lab dup_lab = term_lab(dup);
  Tag dup_num = term_tag(dup) == DP0 ? 0 : 1;
  Loc lam_loc = term_loc(lam);
  Term bod    = got(lam_loc + 1);
  Loc du0     = alloc_node(2);
  Loc lm0     = alloc_node(2);
  Loc lm1     = alloc_node(2);
  Loc su0     = alloc_node(2);
  set(du0 + 0, bod);
  set(du0 + 1, term_new(SUB, 0, 0));
  set(lm0 + 0, term_new(SUB, 0, 0));
  set(lm0 + 1, term_new(DP0, dup_lab, du0));
  set(lm1 + 0, term_new(SUB, 0, 0));
  set(lm1 + 1, term_new(DP1, dup_lab, du0));
  set(su0 + 0, term_new(VAR, 0, lm0));
  set(su0 + 1, term_new(VAR, 0, lm1));
  set(dup_loc + 0, term_new(LAM, 0, lm0));
  set(dup_loc + 1, term_new(LAM, 0, lm1));
  set(lam_loc + 0, term_new(SUP, dup_lab, su0));
  return got(dup_loc + dup_num);
}

// ! &L{x y} = &R{a b}
// ------------------- DUP-SUP
// if L == R:
//   x <- a
//   y <- b
// else:
//   x <- &R{a0 b0} 
//   y <- &R{a1 b1}
//   ! &L{a0 a1} = a
//   ! &L{b0 b1} = b
Term reduce_dup_sup(Term dup, Term sup) {
  //printf("reduce_dup_sup %u %u | %llu ", term_lab(dup), term_lab(sup), *HVM.spos); print_term(dup); printf(" "); print_term(sup); printf("\n");
  inc_itr();
  Loc dup_loc = term_loc(dup);
  Lab dup_lab = term_lab(dup);
  Tag dup_num = term_tag(dup) == DP0 ? 0 : 1;
  Lab sup_lab = term_lab(sup);
  Loc sup_loc = term_loc(sup);
  if (dup_lab == sup_lab) {
    Term tm0 = got(sup_loc + 0);
    Term tm1 = got(sup_loc + 1);
    set(dup_loc + 0, tm0);
    set(dup_loc + 1, tm1);
    return got(dup_loc + dup_num);
  } else {
    Loc du0 = alloc_node(2);
    Loc du1 = alloc_node(2);
    //Loc su0 = alloc_node(2);
    Loc su0 = sup_loc;
    Loc su1 = alloc_node(2);
    Term tm0 = take(sup_loc + 0);
    Term tm1 = take(sup_loc + 1);
    set(du0 + 0, tm0);
    set(du0 + 1, term_new(SUB, 0, 0));
    set(du1 + 0, tm1);
    set(du1 + 1, term_new(SUB, 0, 0));
    set(su0 + 0, term_new(DP0, dup_lab, du0));
    set(su0 + 1, term_new(DP0, dup_lab, du1));
    set(su1 + 0, term_new(DP1, dup_lab, du0));
    set(su1 + 1, term_new(DP1, dup_lab, du1));
    set(dup_loc + 0, term_new(SUP, sup_lab, su0));
    set(dup_loc + 1, term_new(SUP, sup_lab, su1));
    return got(dup_loc + dup_num);
  }
}

// ! &L{a b} = %x(T)
// ----------------- DUP-TYP
// a <- %x0(t0)
// b <- %x1(t1)
// x <- &L{x0 x1}
// ! &L{t0 t1} = T
Term reduce_dup_typ(Term dup, Term typ) {
  //printf("reduce_dup_typ "); print_term(dup); printf("\n");
  inc_itr();
  Loc dup_loc = term_loc(dup);
  Lab dup_lab = term_lab(dup);
  Tag dup_num = term_tag(dup) == DP0 ? 0 : 1;
  Loc typ_loc = term_loc(typ);
  Term bod    = got(typ_loc + 1);
  Loc du0     = alloc_node(2);
  Loc ty0     = alloc_node(2);
  Loc ty1     = alloc_node(2);
  Loc su0     = alloc_node(2);
  set(du0 + 0, bod);
  set(du0 + 1, term_new(SUB, 0, 0));
  set(ty0 + 0, term_new(SUB, 0, 0));
  set(ty0 + 1, term_new(DP0, dup_lab, du0));
  set(ty1 + 0, term_new(SUB, 0, 0));
  set(ty1 + 1, term_new(DP1, dup_lab, du0));
  set(su0 + 0, term_new(VAR, 0, ty0));
  set(su0 + 1, term_new(VAR, 0, ty1));
  set(dup_loc + 0, term_new(TYP, 0, ty0));
  set(dup_loc + 1, term_new(TYP, 0, ty1));
  set(typ_loc + 0, term_new(SUP, dup_lab, su0));
  return got(dup_loc + dup_num);
}

// ! &L{x y} = #{a b c ...}
// ------------------------ DUP-CTR
// ! &L{a0 a1} = a
// ! &L{b0 b1} = b
// ! &L{c0 c1} = c
// ...
// x <- #{a0 b0 c0 ...} 
// y <- #{a1 b1 c1 ...}
Term reduce_dup_ctr(Term dup, Term ctr) {
  //printf("reduce_dup_ctr "); print_term(dup); printf("\n");
  inc_itr();
  Loc dup_loc = term_loc(dup);
  Lab dup_lab = term_lab(dup);
  Tag dup_num = term_tag(dup) == DP0 ? 0 : 1;
  Loc ctr_loc = term_loc(ctr);
  Lab ctr_lab = term_lab(ctr);
  u64 ctr_ari = u12v2_y(ctr_lab);
  //Loc ctr0    = alloc_node(ctr_ari);
  Loc ctr0    = ctr_loc;
  Loc ctr1    = alloc_node(ctr_ari);
  for (u64 i = 0; i < ctr_ari; i++) {
    Loc du0 = alloc_node(2);
    set(du0 + 0, got(ctr_loc + i));
    set(du0 + 1, term_new(SUB, 0, 0));
    set(ctr0 + i, term_new(DP0, dup_lab, du0));
    set(ctr1 + i, term_new(DP1, dup_lab, du0));
  }
  set(dup_loc + 0, term_new(CTR, ctr_lab, ctr0));
  set(dup_loc + 1, term_new(CTR, ctr_lab, ctr1));
  return got(dup_loc + dup_num);
}

// ! &L{x y} = 123
// --------------- DUP-W32
// x <- 123
// y <- 123
Term reduce_dup_w32(Term dup, Term w32) {
  //printf("reduce_dup_w32 "); print_term(dup); printf("\n");
  inc_itr();
  Loc dup_loc = term_loc(dup);
  Tag dup_num = term_tag(dup) == DP0 ? 0 : 1;
  set(dup_loc + 0, w32);
  set(dup_loc + 1, w32);
  return got(dup_loc + dup_num);
}

// ! &L{x y} = @foo(a b c ...)
// --------------------------- DUP-REF-COPY (when &L not in @foo)
// ! &L{a0 a1} = a
// ! &L{b0 b1} = b
// ! &L{c0 c1} = c
// ...
// x <- @foo(a0 b0 c0 ...)
// y <- @foo(a1 b1 c1 ...)
Term reduce_dup_ref(Term dup, Term ref) {
  //printf("reduce_dup_ref "); print_term(dup); printf("\n");
  inc_itr();
  Loc dup_loc = term_loc(dup);
  Lab dup_lab = term_lab(dup);
  Tag dup_num = term_tag(dup) == DP0 ? 0 : 1;
  Loc ref_loc = term_loc(ref);
  Lab ref_lab = term_lab(ref);
  u64 ref_ari = u12v2_y(ref_lab);
  Loc ref0    = ref_loc;
  Loc ref1    = alloc_node(1 + ref_ari);
  for (u64 i = 0; i < ref_ari; i++) {
    Loc du0 = alloc_node(2);
    set(du0 + 0, got(ref_loc + i));
    set(du0 + 1, term_new(SUB, 0, 0));
    set(ref0 + i, term_new(DP0, dup_lab, du0));
    set(ref1 + i, term_new(DP1, dup_lab, du0));
  }
  set(dup_loc + 0, term_new(REF, ref_lab, ref0));
  set(dup_loc + 1, term_new(REF, ref_lab, ref1));
  return got(dup_loc + dup_num);
}

// ~ * {K0 K1 K2 ...} 
// ------------------ MAT-ERA
// *
Term reduce_mat_era(Term mat, Term era) {
  //printf("reduce_mat_era "); print_term(mat); printf("\n");
  inc_itr();
  return era;
}

// ~ λx(x) {K0 K1 K2 ...}
// ---------------------- MAT-LAM
// ⊥
Term reduce_mat_lam(Term mat, Term lam) {
  //printf("reduce_mat_lam "); print_term(mat); printf("\n");
  printf("invalid:mat-lam");
  exit(0);
}

// ~ &L{x y} {K0 K1 K2 ...}
// ------------------------ MAT-SUP
// ! &L{k0a k0b} = K0
// ! &L{k1a k1b} = K1
// ! &L{k2a k2b} = K2
// ...
// &L{ ~ x {K0a K1a K2a ...}
//     ~ y {K0b K1b K2b ...} }
Term reduce_mat_sup(Term mat, Term sup) {
  //printf("reduce_mat_sup "); print_term(mat); printf("\n");
  inc_itr();
  Loc mat_loc = term_loc(mat);
  Loc sup_loc = term_loc(sup);
  Lab sup_lab = term_lab(sup);
  Term tm0    = got(sup_loc + 0);
  Term tm1    = got(sup_loc + 1);
  Lab mat_lab = term_lab(mat);
  u64 mat_len = u12v2_x(mat_lab);
  Loc mat1    = alloc_node(1 + mat_len);
  //Loc mat0    = alloc_node(1 + mat_len);
  //Loc sup0    = alloc_node(2);
  Loc mat0    = mat_loc;
  Loc sup0    = sup_loc;
  set(mat0 + 0, tm0);
  set(mat1 + 0, tm1);
  for (u64 i = 0; i < mat_len; i++) {
    Loc du0 = alloc_node(2);
    set(du0 + 0, got(mat_loc + 1 + i));
    set(du0 + 1, term_new(SUB, 0, 0));
    set(mat0 + 1 + i, term_new(DP0, sup_lab, du0));
    set(mat1 + 1 + i, term_new(DP1, sup_lab, du0));
  }
  set(sup0 + 0, term_new(MAT, mat_lab, mat0));
  set(sup0 + 1, term_new(MAT, mat_lab, mat1));
  return term_new(SUP, sup_lab, sup0);
}

// ~ %x(T) {K0 K1 K2 ...}
// ---------------------- MAT-TYP
// ⊥
Term reduce_mat_typ(Term mat, Term sup) {
  printf("invalid:mat-typ\n");
  exit(0);
}

// ~ #N{x y z ...} {K0 K1 K2 ...} 
// ------------------------------ MAT-CTR
// (((KN x) y) z ...)
Term reduce_mat_ctr(Term mat, Term ctr) {
  //printf("reduce_mat_ctr "); print_term(mat); printf("\n");
  inc_itr();
  Loc mat_loc = term_loc(mat);
  Lab mat_lab = term_lab(mat);
  // If-Let
  if (u12v2_y(mat_lab) > 0) {
    Loc ctr_loc = term_loc(ctr);
    Lab ctr_lab = term_lab(ctr);
    u64 mat_ctr = u12v2_y(mat_lab) - 1;
    u64 ctr_num = u12v2_x(ctr_lab);
    u64 ctr_ari = u12v2_y(ctr_lab);
    if (mat_ctr == ctr_num) {
      Term app = got(mat_loc + 1);
      for (u64 i = 0; i < ctr_ari; i++) {
        Loc new_app = alloc_node(2);
        set(new_app + 0, app);
        set(new_app + 1, got(ctr_loc + i));
        app = term_new(APP, 0, new_app);
      }
      return app;
    } else {
      Term app = got(mat_loc + 2);
      Loc new_app = alloc_node(2);
      set(new_app + 0, app);
      set(new_app + 1, ctr);
      app = term_new(APP, 0, new_app);
      return app;
    }
  // Match
  } else {
    Loc ctr_loc = term_loc(ctr);
    Lab ctr_lab = term_lab(ctr);
    u64 ctr_num = u12v2_x(ctr_lab);
    u64 ctr_ari = u12v2_y(ctr_lab);
    Term app = got(mat_loc + 1 + ctr_num);
    for (u64 i = 0; i < ctr_ari; i++) {
      Loc new_app = alloc_node(2);
      set(new_app + 0, app);
      set(new_app + 1, got(ctr_loc + i));
      app = term_new(APP, 0, new_app);
    }
    return app;
  }
}

// ~ num {K0 K1 K2 ... KN}
// ----------------------- MAT-W32
// if n < N: Kn
// else    : KN(num-N)
Term reduce_mat_w32(Term mat, Term w32) {
  //printf("reduce_mat_w32 "); print_term(mat); printf("\n");
  inc_itr();
  Lab mat_tag = term_tag(mat);
  Loc mat_loc = term_loc(mat);
  Lab mat_lab = term_lab(mat);
  u64 mat_len = u12v2_x(mat_lab);
  u64 w32_val = term_loc(w32);
  if (w32_val < mat_len - 1) {
    return got(mat_loc + 1 + w32_val);
  } else {
    Loc app = alloc_node(2);
    set(app + 0, got(mat_loc + mat_len));
    set(app + 1, term_new(W32, 0, w32_val - (mat_len - 1)));
    return term_new(APP, 0, app);
  }
}

// <op(* b)
// -------- OPX-ERA
// *
Term reduce_opx_era(Term opx, Term era) {
  //printf("reduce_opx_era "); print_term(opx); printf("\n");
  inc_itr();
  return era;
}

// <op(λx(B) y)
// ------------ OPX-LAM
// ⊥
Term reduce_opx_lam(Term opx, Term lam) {
  //printf("reduce_opx_lam "); print_term(opx); printf("\n");
  printf("invalid:opx-lam");
  exit(0);
}

// <op(&L{x0 x1} y)
// ------------------------- OPX-SUP
// ! &L{y0 y1} = y
// &L{<op(x0 y0) <op(x1 y1)}
Term reduce_opx_sup(Term opx, Term sup) {
  //printf("reduce_opx_sup "); print_term(opx); printf("\n");
  inc_itr();
  Loc opx_loc = term_loc(opx);
  Loc sup_loc = term_loc(sup);
  Lab sup_lab = term_lab(sup);
  Term nmy    = got(opx_loc + 1);
  Term tm0    = got(sup_loc + 0);
  Term tm1    = got(sup_loc + 1);
  Loc du0     = alloc_node(2);
  //Loc op0     = alloc_node(2);
  //Loc op1     = alloc_node(2);
  Loc op0     = opx_loc;
  Loc op1     = sup_loc;
  Loc su0     = alloc_node(2);
  set(du0 + 0, nmy);
  set(du0 + 1, term_new(SUB, 0, 0));
  set(op0 + 0, tm0);
  set(op0 + 1, term_new(DP0, sup_lab, du0));
  set(op1 + 0, tm1);
  set(op1 + 1, term_new(DP1, sup_lab, du0));
  set(su0 + 0, term_new(OPX, term_lab(opx), op0));
  set(su0 + 1, term_new(OPX, term_lab(opx), op1));
  return term_new(SUP, sup_lab, su0);
}

// <op(%x(T) y)
// ------------ OPX-TYP
// ⊥
Term reduce_opx_typ(Term opx, Term typ) {
  printf("invalid:opx-typ");
  exit(0);
}

// <op(#{x0 x1 x2...} y)
// --------------------- OPX-CTR
// ⊥
Term reduce_opx_ctr(Term opx, Term ctr) {
  //printf("reduce_opx_ctr "); print_term(opx); printf("\n");
  printf("invalid:opx-ctr");
  exit(0);
}

// <op(x0 x1)
// ---------- OPX-W32
// <op(x0 x1)
Term reduce_opx_w32(Term opx, Term w32) {
  //printf("reduce_opx_w32 "); print_term(opx); printf("\n");
  inc_itr();
  Lab opx_lab = term_lab(opx);
  Lab opx_loc = term_loc(opx);
  set(opx_loc + 0, w32);
  return term_new(OPY, opx_lab, opx_loc);
}

// >op(a *)
// -------- OPY-ERA
// *
Term reduce_opy_era(Term opy, Term era) {
  //printf("reduce_opy_era "); print_term(opy); printf("\n");
  inc_itr();
  return era;
}

// >op(a λx(B))
// ------------ OPY-LAM
// *
Term reduce_opy_lam(Term opy, Term era) {
  //printf("reduce_opy_lam "); print_term(opy); printf("\n");
  printf("invalid:opy-lam");
  exit(0);
}

// >op(a &L{x y})
// --------------------- OPY-SUP
// &L{>op(a x) >op(a y)}
Term reduce_opy_sup(Term opy, Term sup) {
  //printf("reduce_opy_sup "); print_term(opy); printf("\n");
  inc_itr();
  Loc opy_loc = term_loc(opy);
  Loc sup_loc = term_loc(sup);
  Lab sup_lab = term_lab(sup);
  Term nmx    = got(opy_loc + 0);
  Term tm0    = got(sup_loc + 0);
  Term tm1    = got(sup_loc + 1);
  //Loc op0     = alloc_node(2);
  //Loc op1     = alloc_node(2);
  Loc op0     = opy_loc;
  Loc op1     = sup_loc;
  Loc su0     = alloc_node(2);
  set(op0 + 0, nmx);
  set(op0 + 1, tm0);
  set(op1 + 0, nmx);
  set(op1 + 1, tm1);
  set(su0 + 0, term_new(OPY, term_lab(opy), op0));
  set(su0 + 1, term_new(OPY, term_lab(opy), op1));
  return term_new(SUP, sup_lab, su0);
}

// >op(%x(T) y)
// ------------ OPY-TYP
// ⊥
Term reduce_opy_typ(Term opy, Term typ) {
  printf("invalid:opy-typ");
  exit(0);
}

// >op(#{x y z ...} b)
// ---------------------- OPY-CTR
// ⊥
Term reduce_opy_ctr(Term opy, Term ctr) {
  //printf("reduce_opy_ctr "); print_term(opy); printf("\n");
  printf("invalid:opy-ctr");
  exit(0);
}

// >op(x y)
// --------- OPY-W32
// x op y
Term reduce_opy_w32(Term opy, Term w32) {
  //printf("reduce_opy_w32 "); print_term(opy); printf("\n");
  inc_itr();
  Loc opy_loc = term_loc(opy);
  u32 t = term_tag(w32);
  u32 x = term_loc(got(opy_loc + 0));
  u32 y = term_loc(w32);
  u32 result;
  switch (term_lab(opy)) {
    case OP_ADD: result = x + y; break;
    case OP_SUB: result = x - y; break;
    case OP_MUL: result = x * y; break;
    case OP_DIV: result = x / y; break;
    case OP_MOD: result = x % y; break;
    case OP_EQ:  result = x == y; break;
    case OP_NE:  result = x != y; break;
    case OP_LT:  result = x < y; break;
    case OP_GT:  result = x > y; break;
    case OP_LTE: result = x <= y; break;
    case OP_GTE: result = x >= y; break;
    case OP_AND: result = x & y; break;
    case OP_OR:  result = x | y; break;
    case OP_XOR: result = x ^ y; break;
    case OP_LSH: result = x << y; break;
    case OP_RSH: result = x >> y; break;
    default: result = 0;
  }
  return term_new(t, 0, result);
}

// <v : *>
// -------------- ANN-ERA
// *
Term reduce_ann_era(Term ann, Term era) {
  inc_itr();
  return era;
}

// <v : λx(T)>
// -------------- ANN-LAM
// x <- %k(y)
// λy <(v k) : T>
Term reduce_ann_lam(Term ann, Term lam) {
  //printf("reduce_ann_lam "); print_term(ann); printf("\n");
  inc_itr();
  Loc ann_loc = term_loc(ann);
  Loc lam_loc = term_loc(lam);
  Term val    = got(ann_loc + 0);
  Term typ    = got(lam_loc + 1);
  Loc lm0     = alloc_node(2);
  Loc ty0     = alloc_node(2);
  Loc ap0     = alloc_node(2);
  Loc an0     = ann_loc;
  set(lm0 + 0, term_new(SUB, 0, 0));
  set(lm0 + 1, term_new(ANN, 0, an0));
  set(ty0 + 0, term_new(SUB, 0, 0));
  set(ty0 + 1, term_new(VAR, 0, lm0));
  set(ap0 + 0, val);
  set(ap0 + 1, term_new(VAR, 0, ty0));
  set(an0 + 0, term_new(APP, 0, ap0));
  set(an0 + 1, typ);
  set(lam_loc + 0, term_new(TYP, 0, ty0));
  return term_new(LAM, 0, lm0);
}

// <v : &L{a b}>
// -------------- ANN-SUP
// ! &L{v0 v1} = v
// &L{<v0:a> <v1:b>}
Term reduce_ann_sup(Term ann, Term sup) {
  //printf("reduce_ann_sup "); print_term(ann); printf("\n");
  inc_itr();
  Loc ann_loc = term_loc(ann);
  Loc sup_loc = term_loc(sup);
  Lab sup_lab = term_lab(sup);
  Term val    = got(ann_loc + 0);
  Term tm0    = got(sup_loc + 0);
  Term tm1    = got(sup_loc + 1);
  Loc du0     = alloc_node(2);
  Loc an0     = alloc_node(2);
  Loc su0     = alloc_node(2);
  Loc an1     = ann_loc;
  set(du0 + 0, val);
  set(du0 + 1, term_new(SUB, 0, 0));
  set(an0 + 0, term_new(DP0, sup_lab, du0));
  set(an0 + 1, tm0);
  set(an1 + 0, term_new(DP1, sup_lab, du0));
  set(an1 + 1, tm1);
  set(su0 + 0, term_new(ANN, 0, an0));
  set(su0 + 1, term_new(ANN, 0, an1));
  return term_new(SUP, sup_lab, su0);
}

// <v : %x(T)>
// ----------- ANN-TYP
// x <- v
// T
Term reduce_ann_typ(Term ann, Term typ) {
  //printf("reduce_ann_typ "); print_term(ann); printf("\n");
  inc_itr();
  Loc ann_loc = term_loc(ann);
  Loc typ_loc = term_loc(typ);
  Term val    = got(ann_loc + 0);
  Term bod    = got(typ_loc + 1);
  set(typ_loc + 0, val);
  return bod;
}

// <v : #{x y z ...}>
// ------------------ ANN-CTR
// ⊥
Term reduce_ann_ctr(Term ann, Term ctr) {
  printf("invalid:ann-ctr");
  exit(0);
}

// <v : 123>
// --------- ANN-U32
// ⊥
Term reduce_ann_w32(Term ann, Term w32) {
  printf("invalid:ann-w32");
  exit(0);
}

Term reduce(Term term) {
  if (term_tag(term) >= ERA) return term;
  Term next = term;
  u64  stop = *HVM.spos;
  u64* spos = HVM.spos;
  while (1) {
    //printf("NEXT "); print_term(term); printf("\n");
    //printf("PATH ");
    //for (u64 i = 0; i < *spos; ++i) {
      //print_tag(term_tag(HVM.sbuf[i]));
      //printf(" ");
    //}
    //printf(" ~ %p", HVM.sbuf);
    //printf("\n");
    Tag tag = term_tag(next);
    Lab lab = term_lab(next);
    Loc loc = term_loc(next);
    switch (tag) {
      case LET: {
        switch (lab) {
          case LAZY: {
            next = reduce_let(next, got(loc + 1));
            continue;
          }
          case STRI: {
            HVM.sbuf[(*spos)++] = next;
            next = got(loc + 1);
            continue;
          }
          case PARA: {
            printf("TODO\n");
            continue;
          }
        }
      }
      case APP: {
        HVM.sbuf[(*spos)++] = next;
        next = got(loc + 0);
        continue;
      }
      case ANN: {
        HVM.sbuf[(*spos)++] = next;
        next = got(loc + 1);
        continue;
      }
      case DP0: {
        Term sb0 = got(loc + 0);
        Term sb1 = got(loc + 1);
        if (term_tag(sb1) == SUB) {
          HVM.sbuf[(*spos)++] = next;
          next = got(loc + 0);
          continue;
        } else {
          next = sb0;
          continue;
        }
      }
      case DP1: {
        Term sb0 = got(loc + 0);
        Term sb1 = got(loc + 1);
        if (term_tag(sb1) == SUB) {
          HVM.sbuf[(*spos)++] = next;
          next = got(loc + 0);
          continue;
        } else {
          next = sb1;
          continue;
        }
      }
      case MAT: {
        HVM.sbuf[(*spos)++] = next;
        next = got(loc + 0);
        continue;
      }
      case OPX: {
        HVM.sbuf[(*spos)++] = next;
        next = got(loc + 0);
        continue;
      }
      case OPY: {
        HVM.sbuf[(*spos)++] = next;
        next = got(loc + 1);
        continue;
      }
      case VAR: {
        Term sub = got(loc);
        if (term_tag(sub) == SUB) {
          break;
        } else {
          next = sub;
          continue;
        }
      }
      case REF: {
        next = reduce_ref(next); // TODO
        continue;
      }
      default: {
        if ((*spos) == stop) {
          break;
        } else {
          Term prev = HVM.sbuf[--(*spos)];
          Tag  ptag = term_tag(prev);
          Lab  plab = term_lab(prev);
          Loc  ploc = term_loc(prev);
          switch (ptag) {
            case LET: {
              next = reduce_let(prev, next);
              continue;
            }
            case APP: {
              switch (tag) {
                case ERA: next = reduce_app_era(prev, next); continue;
                case LAM: next = reduce_app_lam(prev, next); continue;
                case SUP: next = reduce_app_sup(prev, next); continue;
                case TYP: next = reduce_app_typ(prev, next); continue;
                case CTR: next = reduce_app_ctr(prev, next); continue;
                case W32: next = reduce_app_w32(prev, next); continue;
                case CHR: next = reduce_app_w32(prev, next); continue;
                default: break;
              }
              break;
            }
            case ANN: {
              switch (tag) {
                case ERA: next = reduce_ann_era(prev, next); continue;
                case LAM: next = reduce_ann_lam(prev, next); continue;
                case SUP: next = reduce_ann_sup(prev, next); continue;
                case TYP: next = reduce_ann_typ(prev, next); continue;
                case CTR: next = reduce_ann_ctr(prev, next); continue;
                case W32: next = reduce_ann_w32(prev, next); continue;
                case CHR: next = reduce_ann_w32(prev, next); continue;
                default: break;
              }
              break;
            }
            case DP0:
            case DP1: {
              switch (tag) {
                case ERA: next = reduce_dup_era(prev, next); continue;
                case LAM: next = reduce_dup_lam(prev, next); continue;
                case SUP: next = reduce_dup_sup(prev, next); continue;
                case TYP: next = reduce_dup_typ(prev, next); continue;
                case CTR: next = reduce_dup_ctr(prev, next); continue;
                case W32: next = reduce_dup_w32(prev, next); continue;
                case CHR: next = reduce_dup_w32(prev, next); continue;
                default: break;
              }
              break;
            }
            case MAT: {
              switch (tag) {
                case ERA: next = reduce_mat_era(prev, next); continue;
                case LAM: next = reduce_mat_lam(prev, next); continue;
                case SUP: next = reduce_mat_sup(prev, next); continue;
                case TYP: next = reduce_mat_typ(prev, next); continue;
                case CTR: next = reduce_mat_ctr(prev, next); continue;
                case W32: next = reduce_mat_w32(prev, next); continue;
                case CHR: next = reduce_mat_w32(prev, next); continue;
                default: break;
              }
            }
            case OPX: {
              switch (tag) {
                case ERA: next = reduce_opx_era(prev, next); continue;
                case LAM: next = reduce_opx_lam(prev, next); continue;
                case SUP: next = reduce_opx_sup(prev, next); continue;
                case TYP: next = reduce_opx_typ(prev, next); continue;
                case CTR: next = reduce_opx_ctr(prev, next); continue;
                case W32: next = reduce_opx_w32(prev, next); continue;
                case CHR: next = reduce_opx_w32(prev, next); continue;
                default: break;
              }
            }
            case OPY: {
              switch (tag) {
                case ERA: next = reduce_opy_era(prev, next); continue;
                case LAM: next = reduce_opy_lam(prev, next); continue;
                case SUP: next = reduce_opy_sup(prev, next); continue;
                case TYP: next = reduce_opy_typ(prev, next); continue;
                case CTR: next = reduce_opy_ctr(prev, next); continue;
                case W32: next = reduce_opy_w32(prev, next); continue;
                case CHR: next = reduce_opy_w32(prev, next); continue;
                default: break;
              }
            } 
            default: break;
          }
          break;
        }
      }
    }
    if ((*HVM.spos) == stop) {
      return next;
    } else {
      Term host = HVM.sbuf[--(*HVM.spos)];
      Tag  htag = term_tag(host);
      Lab  hlab = term_lab(host);
      Loc  hloc = term_loc(host);
      switch (htag) {
        case APP: set(hloc + 0, next); break;
        case DP0: set(hloc + 0, next); break;
        case DP1: set(hloc + 0, next); break;
        case MAT: set(hloc + 0, next); break;
        case ANN: set(hloc + 1, next); break;
        case OPX: set(hloc + 0, next); break;
        case OPY: set(hloc + 1, next); break;
      }
      *HVM.spos = stop;
      return HVM.sbuf[stop];
    }
  }
  printf("retr: ERR\n");
  return 0;
}

Term reduce_at(Loc host) {
  Term term = reduce(got(host));
  set(host, term);
  return term;
}

Term normal(Term term) {
  Term wnf = reduce(term);
  Tag tag = term_tag(wnf);
  Lab lab = term_lab(wnf);
  Loc loc = term_loc(wnf);
  switch (tag) {
    case LAM: {
      Term bod = got(loc + 1);
      bod = normal(bod);
      set(loc + 1, bod);
      return wnf;
    }
    case APP: {
      Term fun = got(loc + 0);
      Term arg = got(loc + 1);
      fun = normal(fun);
      arg = normal(arg);
      set(loc + 0, fun);
      set(loc + 1, arg);
      return wnf;
    }
    case SUP: {
      Term tm0 = got(loc + 0);
      Term tm1 = got(loc + 1);
      tm0 = normal(tm0);
      tm1 = normal(tm1);
      set(loc + 0, tm0);
      set(loc + 1, tm1);
      return wnf;
    }
    case DP0:
    case DP1: {
      Term val = got(loc + 0);
      val = normal(val);
      set(loc + 0, val);
      return wnf;
    }
    case TYP: {
      Term bod = got(loc + 1);
      bod = normal(bod);
      set(loc + 1, bod);
      return wnf;
    }
    case ANN: {
      Term val = got(loc + 0);
      Term typ = got(loc + 1);
      val = normal(val);
      typ = normal(typ);
      set(loc + 0, val);
      set(loc + 1, typ);
      return wnf;
    }
    case CTR: {
      u64 cid = u12v2_x(lab);
      u64 ari = u12v2_y(lab);
      for (u64 i = 0; i < ari; i++) {
        Term arg = got(loc + i);
        arg = normal(arg);
        set(loc + i, arg);
      }
      return wnf;
    }
    case MAT: {
      u64 mat_len = u12v2_x(lab);
      for (u64 i = 0; i <= mat_len; i++) {
        Term arg = got(loc + i);
        arg = normal(arg);
        set(loc + i, arg);
      }
      return wnf;
    }
    default:
      return wnf;
  }
}

// Primitives
// ----------

// Primitive: Dynamic Sup `@SUP(lab tm0 tm1)`
// Allocates a new SUP node with given label.
Term SUP_f(Term ref) {
  Loc ref_loc = term_loc(ref);
  Term lab = reduce(got(ref_loc + 0));
  if (term_tag(lab) != W32) {
    printf("ERROR:non-numeric-sup-label\n");
  }
  Term tm0 = got(ref_loc + 1);
  Term tm1 = got(ref_loc + 2);
  Loc  sup = alloc_node(2);
  Term ret = term_new(SUP, term_loc(lab), sup);
  set(sup + 0, tm0);
  set(sup + 1, tm1);
  return ret;
}

// Primitive: Dynamic Dup `@DUP(lab val λdp0λdp1(bod))`
// Creates a DUP node with given label.
Term DUP_f(Term ref) {
  Loc ref_loc = term_loc(ref);
  Term lab = reduce(got(ref_loc + 0));
  if (term_tag(lab) != W32) {
    printf("ERROR:non-numeric-dup-label\n");
  }
  Term val = got(ref_loc + 1);
  Term bod = got(ref_loc + 2);
  Loc dup = alloc_node(2);
  set(dup + 0, val);
  set(dup + 1, term_new(SUB, 0, 0));
  Term bod_term = got(ref_loc + 2);
  if (term_tag(bod_term) == LAM) {
    Loc lam1_loc = term_loc(bod_term);
    Term lam1_bod = got(lam1_loc + 1);
    if (term_tag(lam1_bod) == LAM) {
      Loc lam2_loc = term_loc(lam1_bod);
      Term lam2_bod = got(lam2_loc + 1);
      set(lam1_loc + 0, term_new(DP0, term_loc(lab), dup));
      set(lam2_loc + 0, term_new(DP1, term_loc(lab), dup));
      *HVM.itrs += 2;
      return lam2_bod;
    }
  }
  Loc app1 = alloc_node(2);
  set(app1 + 0, bod);
  set(app1 + 1, term_new(DP0, term_loc(lab), dup));
  Loc app2 = alloc_node(2);
  set(app2 + 0, term_new(APP, 0, app1));
  set(app2 + 1, term_new(DP1, term_loc(lab), dup));
  return term_new(APP, 0, app2);

}

Term LOG_f(Term ref) {
  printf("TODO: LOG_f");
  exit(0);
}

Term FRESH_f(Term ref) {
  printf("TODO: FRESH_f");
  exit(0);
}

// Runtime Memory
// --------------

void hvm_init() {
  // FIXME: use mmap instead
  HVM.sbuf  = malloc((1ULL << 32) * sizeof(Term));
  HVM.spos  = malloc(sizeof(u64));
  *HVM.spos = 0;
  HVM.heap  = malloc((1ULL << 32) * sizeof(ATerm));
  HVM.size  = malloc(sizeof(u64));
  HVM.itrs  = malloc(sizeof(u64));
  *HVM.size = 1;
  *HVM.itrs = 0;
  HVM.frsh  = malloc(sizeof(u64));
  *HVM.frsh = 0x20;
  HVM.book[SUP_F] = SUP_f;
  HVM.book[DUP_F] = DUP_f;
  HVM.book[LOG_F] = LOG_f;
  HVM.book[FRESH_F] = FRESH_f;
}

void hvm_free() {
  free(HVM.sbuf);
  free(HVM.spos);
  free(HVM.heap);
  free(HVM.size);
  free(HVM.itrs);
  free(HVM.frsh);
}

State* hvm_get_state() {
  return &HVM;
}

void hvm_set_state(State* hvm) {
  HVM.sbuf = hvm->sbuf;
  HVM.spos = hvm->spos;
  HVM.heap = hvm->heap;
  HVM.size = hvm->size;
  HVM.itrs = hvm->itrs;
  HVM.frsh = hvm->frsh;
  for (int i = 0; i < 4096; i++) {
    HVM.book[i] = hvm->book[i];
  }
}

void hvm_define(u64 fid, Term (*func)()) {
  //printf("defined %llu %p\n", fid, func);
  HVM.book[fid] = func;
}
