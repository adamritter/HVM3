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

// (* a)
// ----- APP_ERA
// *
Term reduce_app_era(Term app, Term era) {
  inc_itr();
  return era;
}

// (λx(body) a)
// ------------ APP_LAM
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

// ({a b} c)
// --------------- APP_SUP
// & {x0 x1} = c
// {(a x0) (b x1)}
Term reduce_app_sup(Term app, Term sup) {
  inc_itr();
  Loc app_loc = term_loc(app);
  Loc sup_loc = term_loc(sup);
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
  set(ap0 + 1, term_new(DP0, 0, du0));
  set(ap1 + 0, tm1);
  set(ap1 + 1, term_new(DP1, 0, du0));
  set(su0 + 0, term_new(APP, 0, ap0));
  set(su0 + 1, term_new(APP, 0, ap1));
  return term_new(SUP, 0, su0);
}

// & {x y} = *
// ----------- DUP_ERA
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

// & {r s} = λx(f)
// --------------- DUP_LAM
// & {f0 f1} = f
// r <- λx0(f0)
// s <- λx1(f1)
// x <- {x0 x1}
Term reduce_dup_lam(Term dup, Term lam) {
  inc_itr();
  Loc dup_loc = term_loc(dup);
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
  set(lm0 + 1, term_new(DP0, 0, du0));
  set(lm1 + 0, term_new(SUB, 0, 0));
  set(lm1 + 1, term_new(DP1, 0, du0));
  set(su0 + 0, term_new(VAR, 0, lm0));
  set(su0 + 1, term_new(VAR, 0, lm1));
  set(dup_loc + 0, term_new(LAM, 0, lm0));
  set(dup_loc + 1, term_new(LAM, 0, lm1));
  set(lam_loc + 0, term_new(SUP, 0, su0));
  return got(dup_loc + dup_num);
}

// & {x y} = {a b}
// --------------- DUP_SUP
// x <- a
// y <- b
Term reduce_dup_sup(Term dup, Term sup) {
  inc_itr();
  Loc dup_loc = term_loc(dup);
  Tag dup_num = term_tag(dup) == DP0 ? 0 : 1;
  Loc sup_loc = term_loc(sup);
  Term tm0    = got(sup_loc + 0);
  Term tm1    = got(sup_loc + 1);
  set(dup_loc + 0, tm0);
  set(dup_loc + 1, tm1);
  return got(dup_loc + dup_num);
}

Term reduce_ref(Term ref) {
  inc_itr();
  return HVM.book[term_loc(ref)]();
}

Term reduce(Term term) {
  //printf("reduce\n");
  Loc   spos = 0;
  Term  next = term;
  while (1) {
    //printf("next: "); print_term(next); printf("\n");
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
          Tag ptag = term_tag(prev);
          Lab plab = term_lab(prev);
          Loc ploc = term_loc(prev);
          switch (ptag) {
            case APP: {
              switch (tag) {
                case ERA: next = reduce_app_era(prev, next); continue;
                case LAM: next = reduce_app_lam(prev, next); continue;
                case SUP: next = reduce_app_sup(prev, next); continue;
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
                default: break;
              }
              break;
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
      }
      return HVM.path[0];
    }
  }
  printf("retr: ERR\n");
  return 0;
}

//Term normal(Term term) {
  //Term wnf = reduce(term);
  //Tag tag = term_tag(wnf);
  //Lab lab = term_lab(wnf);
  //Loc loc = term_loc(wnf);
  //switch (tag) {
    //case APP: {
      //Term fun;
      //Term arg;
      //fun = got(loc + 0);
      //fun = normal(fun);
      //arg = got(loc + 1);
      //arg = normal(arg);
      //set(loc + 0, fun);
      //set(loc + 1, arg);
      //return wnf;
    //}
    //case LAM: {
      //Term bod;
      //bod = got(loc + 1);
      //bod = normal(bod);
      //set(loc + 1, bod);
      //return wnf;
    //}
    //case SUP: {
      //Term tm0;
      //Term tm1;
      //tm0 = got(loc + 0);
      //tm0 = normal(tm0);
      //tm1 = got(loc + 1);
      //tm1 = normal(tm1);
      //set(loc + 0, tm0);
      //set(loc + 1, tm1);
      //return wnf;
    //}
    //case DP0: {
      //Term val;
      //val = got(loc + 2);
      //val = normal(val);
      //set(loc + 2, val);
      //return wnf;
    //}
    //case DP1: {
      //Term val;
      //val = got(loc + 2);
      //val = normal(val);
      //set(loc + 2, val);
      //return wnf;
    //}
    //default:
      //return wnf;
  //}
//}

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

// TODO: create an hvm_get and an hvm_set function that get/set the whole HVM struct
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

