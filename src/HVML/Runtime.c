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
  Term*  path; // reduction path / stack
  ATerm* heap; // global node buffer
  u64*   size; // global node length
  u64*   itrs; // interaction count
  Term (*book[1024])(); // functions
} State;

// Global State Value
static State HVM = {
  .path = NULL,
  .heap = NULL,
  .size = NULL,
  .itrs = NULL,
  .book = {NULL}
};

// Constants
// ---------

#define DP0 0x00
#define DP1 0x01
#define VAR 0x02
#define APP 0x03
#define ERA 0x04
#define LAM 0x05
#define SUP 0x06
#define SUB 0x07
#define REF 0x08
#define CTR 0x09
#define MAT 0x0A
#define W32 0x0B
#define OPX 0x0C
#define OPY 0x0D

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

#define VOID 0x00000000000000

// Heap
// ----

Loc get_len() {
  return *HVM.size;
}

Loc get_itr() {
  return *HVM.itrs;
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
  return x & 0xFF;
}

Lab term_lab(Term x) {
  return (x >> 8) & 0xFFFFFF;
}

Loc term_loc(Term x) {
  return (x >> 32) & 0xFFFFFFFF;
}

Loc term_key(Term term) {
  switch (term_tag(term)) {
    case VAR: return term_loc(term) + 0;
    case DP0: return term_loc(term) + 0;
    case DP1: return term_loc(term) + 1;
    default:  return 0;
  }
}

// u12v2
// -----

u64 u12v2_new(u64 x, u64 y) {
  return (y << 12) | x;
}

u64 u12v2_x(u64 u12v2) {
  return u12v2 & 0x3FF;
}

u64 u12v2_y(u64 u12v2) {
  return u12v2 >> 12;
}

// Atomics
// -------

Term swap(Loc loc, Term term) {
  return atomic_exchange_explicit(&HVM.heap[loc], term, memory_order_relaxed);
}

Term got(Loc loc) {
  return atomic_load_explicit(&HVM.heap[loc], memory_order_relaxed);
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
    case ERA: printf("ERA"); break;
    case LAM: printf("LAM"); break;
    case SUP: printf("SUP"); break;
    case REF: printf("REF"); break;
    case CTR: printf("CTR"); break;
    case MAT: printf("MAT"); break;
    default : printf("???"); break;
  }
}

void print_term(Term term) {
  printf("term_new(");
  print_tag(term_tag(term));
  printf(",0x%06x,0x%09x)", term_lab(term), term_loc(term));
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

// @foo
// --------- REF
// book[foo]
Term reduce_ref(Term ref) {
  inc_itr();
  return HVM.book[term_loc(ref)]();
}

// (* a)
// ----- APP-ERA
// *
Term reduce_app_era(Term app, Term era) {
  inc_itr();
  return era;
}

// (λx(body) a)
// ------------ APP-LAM
// x <- a
// body
Term reduce_app_lam(Term app, Term lam) {
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
  inc_itr();
  Loc app_loc = term_loc(app);
  Loc sup_loc = term_loc(sup);
  Lab sup_lab = term_lab(sup);
  Term arg    = got(app_loc + 1);
  Term tm0    = got(sup_loc + 0);
  Term tm1    = got(sup_loc + 1);
  Loc du0     = alloc_node(3);
  Loc su0     = alloc_node(2);
  Loc ap0     = alloc_node(2);
  Loc ap1     = alloc_node(2);
  set(du0 + 0, term_new(SUB, 0, 0));
  set(du0 + 1, term_new(SUB, 0, 0));
  set(du0 + 2, arg);
  set(ap0 + 0, tm0);
  set(ap0 + 1, term_new(DP0, sup_lab, du0));
  set(ap1 + 0, tm1);
  set(ap1 + 1, term_new(DP1, sup_lab, du0));
  set(su0 + 0, term_new(APP, 0, ap0));
  set(su0 + 1, term_new(APP, 0, ap1));
  return term_new(SUP, sup_lab, su0);
}

// (#{x y z ...} a)
// ---------------- APP-CTR
// ⊥
Term reduce_app_ctr(Term app, Term ctr) {
  printf("invalid:app-ctr");
  exit(0);
}

// (123 a)
// ------- APP-W32
// ⊥
Term reduce_app_w32(Term app, Term w32) {
  printf("invalid:app-w32");
  exit(0);
}

// ! &L{x y} = *
// ------------- DUP-ERA
// x <- *
// y <- *
Term reduce_dup_era(Term dup, Term era) {
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
  inc_itr();
  Loc dup_loc = term_loc(dup);
  Lab dup_lab = term_lab(dup);
  Tag dup_num = term_tag(dup) == DP0 ? 0 : 1;
  Loc lam_loc = term_loc(lam);
  Term bod    = got(lam_loc + 1);
  Loc du0     = alloc_node(3);
  Loc lm0     = alloc_node(2);
  Loc lm1     = alloc_node(2);
  Loc su0     = alloc_node(2);
  set(du0 + 0, term_new(SUB, 0, 0));
  set(du0 + 1, term_new(SUB, 0, 0));
  set(du0 + 2, bod);
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
    Loc du0 = alloc_node(3);
    Loc du1 = alloc_node(3);
    Loc su0 = alloc_node(2);
    Loc su1 = alloc_node(2);
    Term tm0 = got(sup_loc + 0);
    Term tm1 = got(sup_loc + 1);
    set(du0 + 0, term_new(SUB, 0, 0));
    set(du0 + 1, term_new(SUB, 0, 0));
    set(du0 + 2, tm0);
    set(du1 + 0, term_new(SUB, 0, 0));
    set(du1 + 1, term_new(SUB, 0, 0));
    set(du1 + 2, tm1);
    set(su0 + 0, term_new(DP0, dup_lab, du0));
    set(su0 + 1, term_new(DP0, dup_lab, du1));
    set(su1 + 0, term_new(DP1, dup_lab, du0));
    set(su1 + 1, term_new(DP1, dup_lab, du1));
    set(dup_loc + 0, term_new(SUP, sup_lab, su0));
    set(dup_loc + 1, term_new(SUP, sup_lab, su1));
    return got(dup_loc + dup_num);
  }
}

// ! &{x y} = #{a b c ...}
// ----------------------- DUP-CTR
// ! &{a0 a1} = a
// ! &{b0 b1} = b
// ! &{c0 c1} = c
// ...
// {#{a0 b0 c0 ...} #{a1 b1 c1 ...}}
Term reduce_dup_ctr(Term dup, Term ctr) {
  inc_itr();
  Loc dup_loc = term_loc(dup);
  Tag dup_num = term_tag(dup) == DP0 ? 0 : 1;
  Loc ctr_loc = term_loc(ctr);
  Lab ctr_lab = term_lab(ctr);
  u64 ctr_ari = u12v2_y(ctr_lab);
  Loc ctr0    = alloc_node(ctr_ari);
  Loc ctr1    = alloc_node(ctr_ari);
  for (u64 i = 0; i < ctr_ari; i++) {
    Loc du0 = alloc_node(3);
    set(du0 + 0, term_new(SUB, 0, 0));
    set(du0 + 1, term_new(SUB, 0, 0));
    set(du0 + 2, got(ctr_loc + i));
    set(ctr0 + i, term_new(DP0, 0, du0));
    set(ctr1 + i, term_new(DP1, 0, du0));
  }
  Loc sup = alloc_node(2);
  set(sup + 0, term_new(CTR, ctr_lab, ctr0));
  set(sup + 1, term_new(CTR, ctr_lab, ctr1));
  set(dup_loc + 0, term_new(CTR, ctr_lab, ctr0));
  set(dup_loc + 1, term_new(CTR, ctr_lab, ctr1));
  return got(dup_loc + dup_num);
}

// ! &L{x y} = 123
// --------------- DUP-W32
// x <- 123
// y <- 123
Term reduce_dup_w32(Term dup, Term w32) {
  inc_itr();
  Loc dup_loc = term_loc(dup);
  Tag dup_num = term_tag(dup) == DP0 ? 0 : 1;
  set(dup_loc + 0, w32);
  set(dup_loc + 1, w32);
  return got(dup_loc + dup_num);
}

// ~ * {K0 K1 K2 ...} 
// ------------------ MAT-ERA
// *
Term reduce_mat_era(Term mat, Term era) {
  inc_itr();
  return era;
}

// ~ λx(x) {K0 K1 K2 ...}
// ---------------------- MAT-LAM
// ⊥
Term reduce_mat_lam(Term mat, Term lam) {
  printf("invalid:mat-lam");
  exit(0);
}

// ~ {x y} {K0 K1 K2 ...}
// ---------------------- MAT-SUP
// ! &{k0a k0b} = K0
// ! &{k1a k1b} = K1
// ! &{k2a k2b} = K2
// ...
// { ~ x {K0a K1a K2a ...}
//   ~ y {K0b K1b K2b ...} }
Term reduce_mat_sup(Term mat, Term sup) {
  inc_itr();
  Loc mat_loc = term_loc(mat);
  Loc sup_loc = term_loc(sup);
  Term tm0    = got(sup_loc + 0);
  Term tm1    = got(sup_loc + 1);
  Lab mat_len = term_lab(mat);
  Loc sup0    = alloc_node(2);
  Loc mat0    = alloc_node(1 + mat_len);
  Loc mat1    = alloc_node(1 + mat_len);
  set(mat0 + 0, tm0);
  set(mat1 + 0, tm1);
  for (u64 i = 0; i < mat_len; i++) {
    Loc du0 = alloc_node(3);
    set(du0 + 0, term_new(SUB, 0, 0));
    set(du0 + 1, term_new(SUB, 0, 0));
    set(du0 + 2, got(mat_loc + 1 + i));
    set(mat0 + 1 + i, term_new(DP0, 0, du0));
    set(mat1 + 1 + i, term_new(DP1, 0, du0));
  }
  set(sup0 + 0, term_new(MAT, mat_len, mat0));
  set(sup0 + 1, term_new(MAT, mat_len, mat1));
  return term_new(SUP, 0, sup0);
}

// ~ #N{x y z ...} {K0 K1 K2 ...} 
// ------------------------------ MAT-CTR
// (((KN x) y) z ...)
Term reduce_mat_ctr(Term mat, Term ctr) {
  inc_itr();
  Loc mat_loc = term_loc(mat);
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

// ~ num {K0 K1 K2 ... KN}
// ----------------------- MAT-W32
// if n < N: Kn
// else    : KN(num-N)
Term reduce_mat_w32(Term mat, Term w32) {
  inc_itr();
  Loc mat_loc = term_loc(mat);
  Lab mat_len = term_lab(mat);
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

// TODO: now, let's implement the missing OPX interactions.

// <op(* b)
// --------- OPX-ERA
// *
Term reduce_opx_era(Term opx, Term era) {
  inc_itr();
  return era;
}

// <op(λx(B) y)
// ------------- OPX-LAM
// ⊥
Term reduce_opx_lam(Term opx, Term lam) {
  printf("invalid:opx-lam");
  exit(0);
}

// <op(&L{x0 x1} y)
// ------------------------- OPX-SUP
// ! &L{y0 y1} = y
// &L{<op(x0 y0) <op(x1 y1)}
Term reduce_opx_sup(Term opx, Term sup) {
  inc_itr();
  Loc opx_loc = term_loc(opx);
  Loc sup_loc = term_loc(sup);
  Lab sup_lab = term_lab(sup);
  Term nmy    = got(opx_loc + 1);
  Term tm0    = got(sup_loc + 0);
  Term tm1    = got(sup_loc + 1);
  Loc du0     = alloc_node(3);
  Loc op0     = alloc_node(2);
  Loc op1     = alloc_node(2);
  Loc su0     = alloc_node(2);
  set(du0 + 0, term_new(SUB, 0, 0));
  set(du0 + 1, term_new(SUB, 0, 0));
  set(du0 + 2, nmy);
  set(op0 + 0, tm0);
  set(op0 + 1, term_new(DP0, 0, du0));
  set(op1 + 0, tm1);
  set(op1 + 1, term_new(DP1, 0, du0));
  set(su0 + 0, term_new(OPX, term_lab(opx), op0));
  set(su0 + 1, term_new(OPX, term_lab(opx), op1));
  return term_new(SUP, sup_lab, su0);
}

// <op(#{x0 x1 x2...} y)
// ---------------------- OPX-CTR
// ⊥
Term reduce_opx_ctr(Term opx, Term ctr) {
  printf("invalid:opx-ctr");
  exit(0);
}

// <op(x0 x1)
// ----------- OPX-W32
// <op(x0 x1)
Term reduce_opx_w32(Term opx, Term w32) {
  inc_itr();
  Lab opx_lab = term_lab(opx);
  Lab opx_loc = term_loc(opx);
  return term_new(OPY, opx_lab, opx_loc);
}

// >op(a *)
// --------- OPY-ERA
// *
Term reduce_opy_era(Term opy, Term era) {
  inc_itr();
  return era;
}

// >op(a λx(B))
// ------------- OPY-LAM
// *
Term reduce_opy_lam(Term opy, Term era) {
  printf("invalid:opy-lam");
  exit(0);
}

// >op(a &L{x y})
// ------------------------- OPY-SUP
// &L{>op(a x) >op(a y)}
Term reduce_opy_sup(Term opy, Term sup) {
  inc_itr();
  Loc opy_loc = term_loc(opy);
  Loc sup_loc = term_loc(sup);
  Lab sup_lab = term_lab(sup);
  Term nmx    = got(opy_loc + 0);
  Term tm0    = got(sup_loc + 0);
  Term tm1    = got(sup_loc + 1);
  Loc op0     = alloc_node(2);
  Loc op1     = alloc_node(2);
  Loc su0     = alloc_node(2);
  set(op0 + 0, nmx);
  set(op0 + 1, tm0);
  set(op1 + 0, nmx);
  set(op1 + 1, tm1);
  set(su0 + 0, term_new(OPY, term_lab(opy), op0));
  set(su0 + 1, term_new(OPY, term_lab(opy), op1));
  return term_new(SUP, sup_lab, su0);
}

// >op(#{x y z ...} b)
// ---------------------- OPY-CTR
// ⊥
Term reduce_opy_ctr(Term opy, Term ctr) {
  printf("invalid:opy-ctr");
  exit(0);
}

// >op(x y)
// --------- OPY-W32
// x op y
Term reduce_opy_w32(Term opy, Term w32) {
  inc_itr();
  Loc opy_loc = term_loc(opy);
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
  return term_new(W32, 0, result);
}

Term reduce(Term term) {
  //printf("reduce\n");
  Loc   spos = 0;
  Term  next = term;
  while (1) {
    //printf("NEXT! "); print_term(next); printf("\n");
    Tag tag = term_tag(next);
    Lab lab = term_lab(next);
    Loc loc = term_loc(next);
    switch (tag) {
      case APP: {
        HVM.path[spos++] = next;
        next = got(loc + 0);
        continue;
      }
      case DP0:
      case DP1: {
        Loc key = term_key(next);
        Term sub = got(key);
        if (term_tag(sub) == SUB) {
          HVM.path[spos++] = next;
          next = got(loc + 2);
          continue;
        } else {
          next = sub;
          continue;
        }
      }
      case MAT: {
        HVM.path[spos++] = next;
        next = got(loc + 0);
        continue;
      }
      case OPX: {
        HVM.path[spos++] = next;
        next = got(loc + 0);
        continue;
      }
      case OPY: {
        HVM.path[spos++] = next;
        next = got(loc + 1);
        continue;
      }
      case VAR: {
        Loc key = term_key(next);
        Term sub = got(key);
        if (term_tag(sub) == SUB) {
          break;
        } else {
          next = sub;
          continue;
        }
      }
      case REF: {
        next = reduce_ref(next);
        continue;
      }
      default: {
        if (spos == 0) {
          break;
        } else {
          Term prev = HVM.path[--spos];
          Tag  ptag = term_tag(prev);
          Lab  plab = term_lab(prev);
          Loc  ploc = term_loc(prev);
          switch (ptag) {
            case APP: {
              switch (tag) {
                case ERA: next = reduce_app_era(prev, next); continue;
                case LAM: next = reduce_app_lam(prev, next); continue;
                case SUP: next = reduce_app_sup(prev, next); continue;
                case CTR: next = reduce_app_ctr(prev, next); continue;
                case W32: next = reduce_app_w32(prev, next); continue;
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
                case CTR: next = reduce_dup_ctr(prev, next); continue;
                case W32: next = reduce_dup_w32(prev, next); continue;
                default: break;
              }
              break;
            }
            case MAT: {
              switch (tag) {
                case ERA: next = reduce_mat_era(prev, next); continue;
                case LAM: next = reduce_mat_lam(prev, next); continue;
                case SUP: next = reduce_mat_sup(prev, next); continue;
                case CTR: next = reduce_mat_ctr(prev, next); continue;
                case W32: next = reduce_mat_w32(prev, next); continue;
                default: break;
              }
            }
            case OPX: {
              switch (tag) {
                case ERA: next = reduce_opx_era(prev, next); continue;
                case LAM: next = reduce_opx_lam(prev, next); continue;
                case SUP: next = reduce_opx_sup(prev, next); continue;
                case CTR: next = reduce_opx_ctr(prev, next); continue;
                case W32: next = reduce_opx_w32(prev, next); continue;
                default: break;
              }
            }
            case OPY: {
              switch (tag) {
                case ERA: next = reduce_opy_era(prev, next); continue;
                case LAM: next = reduce_opy_lam(prev, next); continue;
                case SUP: next = reduce_opy_sup(prev, next); continue;
                case CTR: next = reduce_opy_ctr(prev, next); continue;
                case W32: next = reduce_opy_w32(prev, next); continue;
                default: break;
              }
            }
            default: break;
          }
          break;
        }
      }
    }
    if (spos == 0) {
      //printf("retr: "); print_term(next); printf("\n");
      return next;
    } else {
      Term host = HVM.path[--spos];
      Tag  htag = term_tag(host);
      Lab  hlab = term_lab(host);
      Loc  hloc = term_loc(host);
      switch (htag) {
        case APP: set(hloc + 0, next); break;
        case DP0: set(hloc + 2, next); break;
        case DP1: set(hloc + 2, next); break;
        case MAT: set(hloc + 0, next); break;
      }
      return HVM.path[0];
    }
  }
  printf("retr: ERR\n");
  return 0;
}

// Runtime Memory
// --------------

void hvm_init() {
  // FIXME: use mmap instead
  HVM.path = malloc((1ULL << 32) * sizeof(Term));
  HVM.heap = malloc((1ULL << 32) * sizeof(ATerm));
  HVM.size = malloc(sizeof(u64));
  HVM.itrs = malloc(sizeof(u64));
  *HVM.size = 1;
  *HVM.itrs = 0;
}

void hvm_free() {
  free(HVM.path);
  free(HVM.heap);
  free(HVM.size);
  free(HVM.itrs);
}

State* hvm_get_state() {
  return &HVM;
}

void hvm_set_state(State* hvm) {
  HVM.path = hvm->path;
  HVM.heap = hvm->heap;
  HVM.size = hvm->size;
  HVM.itrs = hvm->itrs;
  for (int i = 0; i < 1024; i++) {
    HVM.book[i] = hvm->book[i];
  }
}

void hvm_define(u64 fid, Term (*func)()) {
  HVM.book[fid] = func;
}

// Main
// ----

//#include "book.c"

//int main() {
  //hvm_init();
  //inject_P24();

  //clock_t start = clock();

  //// Normalize and get interaction count
  //Term root = got(0);
  //normal(root);
  //clock_t end = clock();

  //printf("Itrs: %u\n", get_itr());
  //double time_spent = (double)(end - start) / CLOCKS_PER_SEC * 1000;
  //printf("Size: %u nodes\n", get_len());
  //printf("Time: %.2f seconds\n", time_spent / 1000.0);
  //printf("MIPS: %.2f\n", (get_itr() / 1000000.0) / (time_spent / 1000.0));

  //hvm_free();
  //return 0;
//}

