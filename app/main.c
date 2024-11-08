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

// Global state
static Term*  PATH;
static ATerm* HEAP;
static u64    SIZE;
static u64    ITRS;

#define MEM_SIZE (1024ULL * 1024ULL * 1024ULL * 1024ULL) // 1TB

// Runtime Memory
// --------------

void hvm_init() {
  PATH = malloc((1ULL << 32) * sizeof(Term));
  HEAP = malloc((1ULL << 32) * sizeof(ATerm));
  SIZE = 1;
  ITRS = 0;
}

void hvm_free() {
  free(PATH);
  free(HEAP);
}

// Constants
// ---------

const  u64    TEST = 1234;

#define DP0 0x00
#define DP1 0x01
#define VAR 0x02
#define APP 0x03
#define ERA 0x04
#define LAM 0x05
#define SUP 0x06
#define SUB 0x07

#define VOID 0x00000000000000

// Heap
// ----

Loc get_len() {
  return SIZE;
}

Loc get_itr() {
  return ITRS;
}

void set_len(Loc value) {
  SIZE = value;
}

void set_itr(Loc value) {
  ITRS = value;
}

// Terms
// ------

Term new_term(Tag tag, Lab lab, Loc loc) {
  Term tag_enc = tag;
  Term lab_enc = ((Term)lab) << 8;
  Term loc_enc = ((Term)loc) << 32;
  return tag_enc | lab_enc | loc_enc;
}

Tag get_tag(Term x) {
  return x & 0xFF;
}

Lab get_lab(Term x) {
  return (x >> 8) & 0xFFFFFF;
}

Loc get_loc(Term x) {
  return (x >> 32) & 0xFFFFFFFF;
}

Loc get_key(Term term) {
  switch (get_tag(term)) {
    case VAR: return get_loc(term) + 0;
    case DP0: return get_loc(term) + 0;
    case DP1: return get_loc(term) + 1;
    default:  return 0;
  }
}

// Atomics
// -------

Term swap(Loc loc, Term term) {
  return atomic_exchange_explicit(&HEAP[loc], term, memory_order_relaxed);
}

Term got(Loc loc) {
  return atomic_load_explicit(&HEAP[loc], memory_order_relaxed);
}

void set(Loc loc, Term term) {
  atomic_store_explicit(&HEAP[loc], term, memory_order_relaxed);
}

Term take(Loc loc) {
  return swap(loc, VOID);
}

// Allocation
// ----------

Loc alloc_node(Loc arity) {
  u64 old = SIZE;
  SIZE += arity;
  return old;
}

Loc inc_itr() {
  u64 old = ITRS;
  ITRS += 1;
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
    default : printf("???"); break;
  }
}

void print_term(Term term) {
  printf("new_term(");
  print_tag(get_tag(term));
  printf(",0x%06x,0x%09x)", get_lab(term), get_loc(term));
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
  Loc app_loc = get_loc(app);
  Loc lam_loc = get_loc(lam);
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
  Loc app_loc = get_loc(app);
  Loc sup_loc = get_loc(sup);
  Term arg    = got(app_loc + 1);
  Term tm0    = got(sup_loc + 0);
  Term tm1    = got(sup_loc + 1);
  Loc du0     = alloc_node(3);
  Loc su0     = alloc_node(2);
  Loc ap0     = alloc_node(2);
  Loc ap1     = alloc_node(2);
  set(du0 + 0, new_term(SUB, 0, 0));
  set(du0 + 1, new_term(SUB, 0, 0));
  set(du0 + 2, arg);
  set(ap0 + 0, tm0);
  set(ap0 + 1, new_term(DP0, 0, du0));
  set(ap1 + 0, tm1);
  set(ap1 + 1, new_term(DP1, 0, du0));
  set(su0 + 0, new_term(APP, 0, ap0));
  set(su0 + 1, new_term(APP, 0, ap1));
  return new_term(SUP, 0, su0);
}

// & {x y} = *
// ----------- DUP_ERA
// x <- *
// y <- *
Term reduce_dup_era(Term dup, Term era) {
  inc_itr();
  Loc dup_loc = get_loc(dup);
  Tag dup_num = get_tag(dup) == DP0 ? 0 : 1;
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
  Loc dup_loc = get_loc(dup);
  Tag dup_num = get_tag(dup) == DP0 ? 0 : 1;
  Loc lam_loc = get_loc(lam);
  Term bod    = got(lam_loc + 1);
  Loc du0     = alloc_node(3);
  Loc lm0     = alloc_node(2);
  Loc lm1     = alloc_node(2);
  Loc su0     = alloc_node(2);
  set(du0 + 0, new_term(SUB, 0, 0));
  set(du0 + 1, new_term(SUB, 0, 0));
  set(du0 + 2, bod);
  set(lm0 + 0, new_term(SUB, 0, 0));
  set(lm0 + 1, new_term(DP0, 0, du0));
  set(lm1 + 0, new_term(SUB, 0, 0));
  set(lm1 + 1, new_term(DP1, 0, du0));
  set(su0 + 0, new_term(VAR, 0, lm0));
  set(su0 + 1, new_term(VAR, 0, lm1));
  set(dup_loc + 0, new_term(LAM, 0, lm0));
  set(dup_loc + 1, new_term(LAM, 0, lm1));
  set(lam_loc + 0, new_term(SUP, 0, su0));
  return got(dup_loc + dup_num);
}

// & {x y} = {a b}
// --------------- DUP_SUP
// x <- a
// y <- b
Term reduce_dup_sup(Term dup, Term sup) {
  inc_itr();
  Loc dup_loc = get_loc(dup);
  Tag dup_num = get_tag(dup) == DP0 ? 0 : 1;
  Loc sup_loc = get_loc(sup);
  Term tm0    = got(sup_loc + 0);
  Term tm1    = got(sup_loc + 1);
  set(dup_loc + 0, tm0);
  set(dup_loc + 1, tm1);
  return got(dup_loc + dup_num);
}

Term reduce(Term term) {
  Loc   spos = 0;
  Term  next = term;
  while (1) {
    Tag tag = get_tag(next);
    Lab lab = get_lab(next);
    Loc loc = get_loc(next);
    switch (tag) {
      case APP: {
        PATH[spos++] = next;
        next = got(loc + 0);
        continue;
      }
      case DP0:
      case DP1: {
        Loc key = get_key(next);
        Term sub = got(key);
        if (get_tag(sub) == SUB) {
          PATH[spos++] = next;
          next = got(loc + 2);
          continue;
        } else {
          next = sub;
          continue;
        }
      }
      case VAR: {
        Loc key = get_key(next);
        Term sub = got(key);
        if (get_tag(sub) == SUB) {
          break;
        } else {
          next = sub;
          continue;
        }
      }
      default: {
        if (spos == 0) {
          break;
        } else {
          Term prev = PATH[--spos];
          Tag ptag = get_tag(prev);
          Lab plab = get_lab(prev);
          Loc ploc = get_loc(prev);
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
      return next;
    } else {
      Term host = PATH[--spos];
      Tag htag = get_tag(host);
      Lab hlab = get_lab(host);
      Loc hloc = get_loc(host);
      switch (htag) {
        case APP: {
          set(hloc + 0, next);
          continue;
        }
        case DP0:
        case DP1: {
          set(hloc + 2, next);
          continue;
        }
        default: {
          return 0;
        }
      }
    }
  }
  return 0;
}

//Term normal(Term term) {
  //Term wnf = reduce(term);
  //Tag tag = get_tag(wnf);
  //Lab lab = get_lab(wnf);
  //Loc loc = get_loc(wnf);
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
