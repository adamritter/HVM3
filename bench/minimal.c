// Post: https://x.com/VictorTaelin/status/1854326873590792276
// Note: The atomics must be kept.
// Note: This will segfault on non-Apple devices due to upfront mallocs.#include <stdint.h>

#include <stdint.h>
#include <stdatomic.h>
#include <stdlib.h>
#include <stdio.h>
#include <time.h>

typedef uint8_t  Tag;
typedef uint32_t Lab;
typedef uint32_t Loc;
typedef uint64_t Term;
typedef uint64_t u64;

typedef _Atomic(u64) a64;
typedef _Atomic(Term) ATerm;

// Runtime Types
// -------------

typedef struct {
  Term*  stk; // evaluation stack
  ATerm* mem; // global memory
  a64*   ini; // memory first index (not used)
  a64*   end; // memory alloc index
  a64*   itr; // interaction count
} Heap;

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

#define VOID 0x00000000000000

// Initialization
// --------------

Heap* new_heap() {
  Heap* heap = malloc(sizeof(Heap));
  heap->stk  = malloc((1ULL << 32) * sizeof(Term));
  heap->mem  = malloc((1ULL << 32) * sizeof(ATerm));
  heap->ini  = malloc(sizeof(a64));
  heap->end  = malloc(sizeof(a64));
  heap->itr  = malloc(sizeof(a64));
  atomic_store_explicit(heap->ini, 0, memory_order_relaxed);
  atomic_store_explicit(heap->end, 1, memory_order_relaxed);
  atomic_store_explicit(heap->itr, 0, memory_order_relaxed);
  return heap;
}

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

Loc get_ini(Heap* heap) {
  return atomic_load_explicit(heap->ini, memory_order_relaxed);
}

Loc get_end(Heap* heap) {
  return atomic_load_explicit(heap->end, memory_order_relaxed);
}

Loc get_itr(Heap* heap) {
  return atomic_load_explicit(heap->itr, memory_order_relaxed);
}

void set_ini(Heap* heap, Loc value) {
  atomic_store_explicit(heap->ini, value, memory_order_relaxed);
}

void set_end(Heap* heap, Loc value) {
  atomic_store_explicit(heap->end, value, memory_order_relaxed);
}

void set_itr(Heap* heap, Loc value) {
  atomic_store_explicit(heap->itr, value, memory_order_relaxed);
}

// Memory
// ------

Term swap(Heap* heap, Loc loc, Term term) {
  return atomic_exchange_explicit(&heap->mem[loc], term, memory_order_relaxed);
}

Term got(Heap* heap, Loc loc) {
  return atomic_load_explicit(&heap->mem[loc], memory_order_relaxed);
}

void set(Heap* heap, Loc loc, Term term) {
  atomic_store_explicit(&heap->mem[loc], term, memory_order_relaxed);
}

Term take(Heap* heap, Loc loc) {
  return swap(heap, loc, VOID);
}

// Allocation
// ----------

Loc alloc_node(Heap* heap, Loc arity) {
  return atomic_fetch_add_explicit(heap->end, arity, memory_order_relaxed);
}

Loc inc_itr(Heap* heap) {
  return atomic_fetch_add_explicit(heap->itr, 1, memory_order_relaxed);
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

void print_heap(Heap* heap) {
  Loc end = get_end(heap);
  for (Loc i = 0; i < end; i++) {
    Term term = got(heap, i);
    if (term != 0) {
      printf("set(heap, 0x%09x, ", i);
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
Term reduce_app_era(Heap* heap, Term app, Term era) {
  inc_itr(heap);
  return era;
}

// (λx(body) a)
// ------------ APP_LAM
// x <- a
// body
Term reduce_app_lam(Heap* heap, Term app, Term lam) {
  inc_itr(heap);
  Loc app_loc = get_loc(app);
  Loc lam_loc = get_loc(lam);
  Term arg    = got(heap, app_loc + 1);
  Term bod    = got(heap, lam_loc + 1);
  set(heap, lam_loc + 0, arg);
  return bod;
}

// ({a b} c)
// --------------- APP_SUP
// & {x0 x1} = c
// {(a x0) (b x1)}
Term reduce_app_sup(Heap* heap, Term app, Term sup) {
  inc_itr(heap);
  Loc app_loc = get_loc(app);
  Loc sup_loc = get_loc(sup);
  Term arg    = got(heap, app_loc + 1);
  Term tm0    = got(heap, sup_loc + 0);
  Term tm1    = got(heap, sup_loc + 1);
  Loc du0     = alloc_node(heap, 3);
  Loc su0     = alloc_node(heap, 2);
  Loc ap0     = alloc_node(heap, 2);
  Loc ap1     = alloc_node(heap, 2);
  set(heap, du0 + 0, new_term(SUB, 0, 0));
  set(heap, du0 + 1, new_term(SUB, 0, 0));
  set(heap, du0 + 2, arg);
  set(heap, ap0 + 0, tm0);
  set(heap, ap0 + 1, new_term(DP0, 0, du0));
  set(heap, ap1 + 0, tm1);
  set(heap, ap1 + 1, new_term(DP1, 0, du0));
  set(heap, su0 + 0, new_term(APP, 0, ap0));
  set(heap, su0 + 1, new_term(APP, 0, ap1));
  return new_term(SUP, 0, su0);
}

// & {x y} = *
// ----------- DUP_ERA
// x <- *
// y <- *
Term reduce_dup_era(Heap* heap, Term dup, Term era) {
  inc_itr(heap);
  Loc dup_loc = get_loc(dup);
  Tag dup_num = get_tag(dup) == DP0 ? 0 : 1;
  set(heap, dup_loc + 0, era);
  set(heap, dup_loc + 1, era);
  return got(heap, dup_loc + dup_num);
}

// & {r s} = λx(f)
// --------------- DUP_LAM
// & {f0 f1} = f
// r <- λx0(f0)
// s <- λx1(f1)
// x <- {x0 x1}
Term reduce_dup_lam(Heap* heap, Term dup, Term lam) {
  inc_itr(heap);
  Loc dup_loc = get_loc(dup);
  Tag dup_num = get_tag(dup) == DP0 ? 0 : 1;
  Loc lam_loc = get_loc(lam);
  Term bod    = got(heap, lam_loc + 1);
  Loc du0     = alloc_node(heap, 3);
  Loc lm0     = alloc_node(heap, 2);
  Loc lm1     = alloc_node(heap, 2);
  Loc su0     = alloc_node(heap, 2);
  set(heap, du0 + 0, new_term(SUB, 0, 0));
  set(heap, du0 + 1, new_term(SUB, 0, 0));
  set(heap, du0 + 2, bod);
  set(heap, lm0 + 0, new_term(SUB, 0, 0));
  set(heap, lm0 + 1, new_term(DP0, 0, du0));
  set(heap, lm1 + 0, new_term(SUB, 0, 0));
  set(heap, lm1 + 1, new_term(DP1, 0, du0));
  set(heap, su0 + 0, new_term(VAR, 0, lm0));
  set(heap, su0 + 1, new_term(VAR, 0, lm1));
  set(heap, dup_loc + 0, new_term(LAM, 0, lm0));
  set(heap, dup_loc + 1, new_term(LAM, 0, lm1));
  set(heap, lam_loc + 0, new_term(SUP, 0, su0));
  return got(heap, dup_loc + dup_num);
}

// & {x y} = {a b}
// --------------- DUP_SUP
// x <- a
// y <- b
Term reduce_dup_sup(Heap* heap, Term dup, Term sup) {
  inc_itr(heap);
  Loc dup_loc = get_loc(dup);
  Tag dup_num = get_tag(dup) == DP0 ? 0 : 1;
  Loc sup_loc = get_loc(sup);
  Term tm0    = got(heap, sup_loc + 0);
  Term tm1    = got(heap, sup_loc + 1);
  set(heap, dup_loc + 0, tm0);
  set(heap, dup_loc + 1, tm1);
  return got(heap, dup_loc + dup_num);
}

Term reduce(Heap* heap, Term term) {
  Term* path = heap->stk;
  Loc   spos = 0;
  Term  next = term;
  while (1) {
    Tag tag = get_tag(next);
    Lab lab = get_lab(next);
    Loc loc = get_loc(next);
    switch (tag) {
      case APP: {
        path[spos++] = next;
        next = got(heap, loc + 0);
        continue;
      }
      case DP0:
      case DP1: {
        Loc key = get_key(next);
        Term sub = got(heap, key);
        if (get_tag(sub) == SUB) {
          path[spos++] = next;
          next = got(heap, loc + 2);
          continue;
        } else {
          next = sub;
          continue;
        }
      }
      case VAR: {
        Loc key = get_key(next);
        Term sub = got(heap, key);
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
          Term prev = path[--spos];
          Tag ptag = get_tag(prev);
          Lab plab = get_lab(prev);
          Loc ploc = get_loc(prev);
          switch (ptag) {
            case APP: {
              switch (tag) {
                case ERA: next = reduce_app_era(heap, prev, next); continue;
                case LAM: next = reduce_app_lam(heap, prev, next); continue;
                case SUP: next = reduce_app_sup(heap, prev, next); continue;
                default: break;
              }
              break;
            }
            case DP0:
            case DP1: {
              switch (tag) {
                case ERA: next = reduce_dup_era(heap, prev, next); continue;
                case LAM: next = reduce_dup_lam(heap, prev, next); continue;
                case SUP: next = reduce_dup_sup(heap, prev, next); continue;
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
      Term host = path[--spos];
      Tag htag = get_tag(host);
      Lab hlab = get_lab(host);
      Loc hloc = get_loc(host);
      switch (htag) {
        case APP: {
          set(heap, hloc + 0, next);
          continue;
        }
        case DP0:
        case DP1: {
          set(heap, hloc + 2, next);
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

Term normal(Heap* heap, Term term) {
  Term wnf = reduce(heap, term);
  Tag tag = get_tag(wnf);
  Lab lab = get_lab(wnf);
  Loc loc = get_loc(wnf);
  switch (tag) {
    case APP: {
      Term fun;
      Term arg;
      fun = got(heap, loc + 0);
      fun = normal(heap, fun);
      arg = got(heap, loc + 1);
      arg = normal(heap, arg);
      set(heap, loc + 0, fun);
      set(heap, loc + 1, arg);
      return wnf;
    }
    case LAM: {
      Term bod;
      bod = got(heap, loc + 1);
      bod = normal(heap, bod);
      set(heap, loc + 1, bod);
      return wnf;
    }
    case SUP: {
      Term tm0;
      Term tm1;
      tm0 = got(heap, loc + 0);
      tm0 = normal(heap, tm0);
      tm1 = got(heap, loc + 1);
      tm1 = normal(heap, tm1);
      set(heap, loc + 0, tm0);
      set(heap, loc + 1, tm1);
      return wnf;
    }
    case DP0: {
      Term val;
      val = got(heap, loc + 2);
      val = normal(heap, val);
      set(heap, loc + 2, val);
      return wnf;
    }
    case DP1: {
      Term val;
      val = got(heap, loc + 2);
      val = normal(heap, val);
      set(heap, loc + 2, val);
      return wnf;
    }
    default:
      return wnf;
  }
}

// Main
// ----

static void inject_P24(Heap* heap) {
  set_ini(heap, 0x000000000);
  set_end(heap, 0x0000000f1);
  set_itr(heap, 0x000000000);
  set(heap, 0x000000000, new_term(APP,0x000000,0x000000001));
  set(heap, 0x000000001, new_term(APP,0x000000,0x000000003));
  set(heap, 0x000000002, new_term(LAM,0x000000,0x0000000ed));
  set(heap, 0x000000003, new_term(LAM,0x000000,0x000000005));
  set(heap, 0x000000004, new_term(LAM,0x000000,0x0000000df));
  set(heap, 0x000000005, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000006, new_term(LAM,0x000000,0x0000000d9));
  set(heap, 0x000000007, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000008, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000009, new_term(VAR,0x000000,0x000000005));
  set(heap, 0x00000000a, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x00000000b, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x00000000c, new_term(LAM,0x000000,0x00000000d));
  set(heap, 0x00000000d, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x00000000e, new_term(APP,0x000000,0x00000000f));
  set(heap, 0x00000000f, new_term(DP0,0x000000,0x000000007));
  set(heap, 0x000000010, new_term(APP,0x000000,0x000000011));
  set(heap, 0x000000011, new_term(DP1,0x000000,0x000000007));
  set(heap, 0x000000012, new_term(VAR,0x000000,0x00000000d));
  set(heap, 0x000000013, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000014, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000015, new_term(LAM,0x000000,0x000000016));
  set(heap, 0x000000016, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000017, new_term(APP,0x000000,0x000000018));
  set(heap, 0x000000018, new_term(DP0,0x000000,0x00000000a));
  set(heap, 0x000000019, new_term(APP,0x000000,0x00000001a));
  set(heap, 0x00000001a, new_term(DP1,0x000000,0x00000000a));
  set(heap, 0x00000001b, new_term(VAR,0x000000,0x000000016));
  set(heap, 0x00000001c, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x00000001d, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x00000001e, new_term(LAM,0x000000,0x00000001f));
  set(heap, 0x00000001f, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000020, new_term(APP,0x000000,0x000000021));
  set(heap, 0x000000021, new_term(DP0,0x000000,0x000000013));
  set(heap, 0x000000022, new_term(APP,0x000000,0x000000023));
  set(heap, 0x000000023, new_term(DP1,0x000000,0x000000013));
  set(heap, 0x000000024, new_term(VAR,0x000000,0x00000001f));
  set(heap, 0x000000025, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000026, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000027, new_term(LAM,0x000000,0x000000028));
  set(heap, 0x000000028, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000029, new_term(APP,0x000000,0x00000002a));
  set(heap, 0x00000002a, new_term(DP0,0x000000,0x00000001c));
  set(heap, 0x00000002b, new_term(APP,0x000000,0x00000002c));
  set(heap, 0x00000002c, new_term(DP1,0x000000,0x00000001c));
  set(heap, 0x00000002d, new_term(VAR,0x000000,0x000000028));
  set(heap, 0x00000002e, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x00000002f, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000030, new_term(LAM,0x000000,0x000000031));
  set(heap, 0x000000031, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000032, new_term(APP,0x000000,0x000000033));
  set(heap, 0x000000033, new_term(DP0,0x000000,0x000000025));
  set(heap, 0x000000034, new_term(APP,0x000000,0x000000035));
  set(heap, 0x000000035, new_term(DP1,0x000000,0x000000025));
  set(heap, 0x000000036, new_term(VAR,0x000000,0x000000031));
  set(heap, 0x000000037, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000038, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000039, new_term(LAM,0x000000,0x00000003a));
  set(heap, 0x00000003a, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x00000003b, new_term(APP,0x000000,0x00000003c));
  set(heap, 0x00000003c, new_term(DP0,0x000000,0x00000002e));
  set(heap, 0x00000003d, new_term(APP,0x000000,0x00000003e));
  set(heap, 0x00000003e, new_term(DP1,0x000000,0x00000002e));
  set(heap, 0x00000003f, new_term(VAR,0x000000,0x00000003a));
  set(heap, 0x000000040, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000041, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000042, new_term(LAM,0x000000,0x000000043));
  set(heap, 0x000000043, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000044, new_term(APP,0x000000,0x000000045));
  set(heap, 0x000000045, new_term(DP0,0x000000,0x000000037));
  set(heap, 0x000000046, new_term(APP,0x000000,0x000000047));
  set(heap, 0x000000047, new_term(DP1,0x000000,0x000000037));
  set(heap, 0x000000048, new_term(VAR,0x000000,0x000000043));
  set(heap, 0x000000049, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x00000004a, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x00000004b, new_term(LAM,0x000000,0x00000004c));
  set(heap, 0x00000004c, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x00000004d, new_term(APP,0x000000,0x00000004e));
  set(heap, 0x00000004e, new_term(DP0,0x000000,0x000000040));
  set(heap, 0x00000004f, new_term(APP,0x000000,0x000000050));
  set(heap, 0x000000050, new_term(DP1,0x000000,0x000000040));
  set(heap, 0x000000051, new_term(VAR,0x000000,0x00000004c));
  set(heap, 0x000000052, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000053, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000054, new_term(LAM,0x000000,0x000000055));
  set(heap, 0x000000055, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000056, new_term(APP,0x000000,0x000000057));
  set(heap, 0x000000057, new_term(DP0,0x000000,0x000000049));
  set(heap, 0x000000058, new_term(APP,0x000000,0x000000059));
  set(heap, 0x000000059, new_term(DP1,0x000000,0x000000049));
  set(heap, 0x00000005a, new_term(VAR,0x000000,0x000000055));
  set(heap, 0x00000005b, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x00000005c, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x00000005d, new_term(LAM,0x000000,0x00000005e));
  set(heap, 0x00000005e, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x00000005f, new_term(APP,0x000000,0x000000060));
  set(heap, 0x000000060, new_term(DP0,0x000000,0x000000052));
  set(heap, 0x000000061, new_term(APP,0x000000,0x000000062));
  set(heap, 0x000000062, new_term(DP1,0x000000,0x000000052));
  set(heap, 0x000000063, new_term(VAR,0x000000,0x00000005e));
  set(heap, 0x000000064, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000065, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000066, new_term(LAM,0x000000,0x000000067));
  set(heap, 0x000000067, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000068, new_term(APP,0x000000,0x000000069));
  set(heap, 0x000000069, new_term(DP0,0x000000,0x00000005b));
  set(heap, 0x00000006a, new_term(APP,0x000000,0x00000006b));
  set(heap, 0x00000006b, new_term(DP1,0x000000,0x00000005b));
  set(heap, 0x00000006c, new_term(VAR,0x000000,0x000000067));
  set(heap, 0x00000006d, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x00000006e, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x00000006f, new_term(LAM,0x000000,0x000000070));
  set(heap, 0x000000070, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000071, new_term(APP,0x000000,0x000000072));
  set(heap, 0x000000072, new_term(DP0,0x000000,0x000000064));
  set(heap, 0x000000073, new_term(APP,0x000000,0x000000074));
  set(heap, 0x000000074, new_term(DP1,0x000000,0x000000064));
  set(heap, 0x000000075, new_term(VAR,0x000000,0x000000070));
  set(heap, 0x000000076, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000077, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000078, new_term(LAM,0x000000,0x000000079));
  set(heap, 0x000000079, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x00000007a, new_term(APP,0x000000,0x00000007b));
  set(heap, 0x00000007b, new_term(DP0,0x000000,0x00000006d));
  set(heap, 0x00000007c, new_term(APP,0x000000,0x00000007d));
  set(heap, 0x00000007d, new_term(DP1,0x000000,0x00000006d));
  set(heap, 0x00000007e, new_term(VAR,0x000000,0x000000079));
  set(heap, 0x00000007f, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000080, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000081, new_term(LAM,0x000000,0x000000082));
  set(heap, 0x000000082, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000083, new_term(APP,0x000000,0x000000084));
  set(heap, 0x000000084, new_term(DP0,0x000000,0x000000076));
  set(heap, 0x000000085, new_term(APP,0x000000,0x000000086));
  set(heap, 0x000000086, new_term(DP1,0x000000,0x000000076));
  set(heap, 0x000000087, new_term(VAR,0x000000,0x000000082));
  set(heap, 0x000000088, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000089, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x00000008a, new_term(LAM,0x000000,0x00000008b));
  set(heap, 0x00000008b, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x00000008c, new_term(APP,0x000000,0x00000008d));
  set(heap, 0x00000008d, new_term(DP0,0x000000,0x00000007f));
  set(heap, 0x00000008e, new_term(APP,0x000000,0x00000008f));
  set(heap, 0x00000008f, new_term(DP1,0x000000,0x00000007f));
  set(heap, 0x000000090, new_term(VAR,0x000000,0x00000008b));
  set(heap, 0x000000091, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000092, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000093, new_term(LAM,0x000000,0x000000094));
  set(heap, 0x000000094, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x000000095, new_term(APP,0x000000,0x000000096));
  set(heap, 0x000000096, new_term(DP0,0x000000,0x000000088));
  set(heap, 0x000000097, new_term(APP,0x000000,0x000000098));
  set(heap, 0x000000098, new_term(DP1,0x000000,0x000000088));
  set(heap, 0x000000099, new_term(VAR,0x000000,0x000000094));
  set(heap, 0x00000009a, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x00000009b, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x00000009c, new_term(LAM,0x000000,0x00000009d));
  set(heap, 0x00000009d, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x00000009e, new_term(APP,0x000000,0x00000009f));
  set(heap, 0x00000009f, new_term(DP0,0x000000,0x000000091));
  set(heap, 0x0000000a0, new_term(APP,0x000000,0x0000000a1));
  set(heap, 0x0000000a1, new_term(DP1,0x000000,0x000000091));
  set(heap, 0x0000000a2, new_term(VAR,0x000000,0x00000009d));
  set(heap, 0x0000000a3, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x0000000a4, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x0000000a5, new_term(LAM,0x000000,0x0000000a6));
  set(heap, 0x0000000a6, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x0000000a7, new_term(APP,0x000000,0x0000000a8));
  set(heap, 0x0000000a8, new_term(DP0,0x000000,0x00000009a));
  set(heap, 0x0000000a9, new_term(APP,0x000000,0x0000000aa));
  set(heap, 0x0000000aa, new_term(DP1,0x000000,0x00000009a));
  set(heap, 0x0000000ab, new_term(VAR,0x000000,0x0000000a6));
  set(heap, 0x0000000ac, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x0000000ad, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x0000000ae, new_term(LAM,0x000000,0x0000000af));
  set(heap, 0x0000000af, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x0000000b0, new_term(APP,0x000000,0x0000000b1));
  set(heap, 0x0000000b1, new_term(DP0,0x000000,0x0000000a3));
  set(heap, 0x0000000b2, new_term(APP,0x000000,0x0000000b3));
  set(heap, 0x0000000b3, new_term(DP1,0x000000,0x0000000a3));
  set(heap, 0x0000000b4, new_term(VAR,0x000000,0x0000000af));
  set(heap, 0x0000000b5, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x0000000b6, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x0000000b7, new_term(LAM,0x000000,0x0000000b8));
  set(heap, 0x0000000b8, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x0000000b9, new_term(APP,0x000000,0x0000000ba));
  set(heap, 0x0000000ba, new_term(DP0,0x000000,0x0000000ac));
  set(heap, 0x0000000bb, new_term(APP,0x000000,0x0000000bc));
  set(heap, 0x0000000bc, new_term(DP1,0x000000,0x0000000ac));
  set(heap, 0x0000000bd, new_term(VAR,0x000000,0x0000000b8));
  set(heap, 0x0000000be, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x0000000bf, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x0000000c0, new_term(LAM,0x000000,0x0000000c1));
  set(heap, 0x0000000c1, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x0000000c2, new_term(APP,0x000000,0x0000000c3));
  set(heap, 0x0000000c3, new_term(DP0,0x000000,0x0000000b5));
  set(heap, 0x0000000c4, new_term(APP,0x000000,0x0000000c5));
  set(heap, 0x0000000c5, new_term(DP1,0x000000,0x0000000b5));
  set(heap, 0x0000000c6, new_term(VAR,0x000000,0x0000000c1));
  set(heap, 0x0000000c7, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x0000000c8, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x0000000c9, new_term(LAM,0x000000,0x0000000ca));
  set(heap, 0x0000000ca, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x0000000cb, new_term(APP,0x000000,0x0000000cc));
  set(heap, 0x0000000cc, new_term(DP0,0x000000,0x0000000be));
  set(heap, 0x0000000cd, new_term(APP,0x000000,0x0000000ce));
  set(heap, 0x0000000ce, new_term(DP1,0x000000,0x0000000be));
  set(heap, 0x0000000cf, new_term(VAR,0x000000,0x0000000ca));
  set(heap, 0x0000000d0, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x0000000d1, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x0000000d2, new_term(LAM,0x000000,0x0000000d3));
  set(heap, 0x0000000d3, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x0000000d4, new_term(APP,0x000000,0x0000000d5));
  set(heap, 0x0000000d5, new_term(DP0,0x000000,0x0000000c7));
  set(heap, 0x0000000d6, new_term(APP,0x000000,0x0000000d7));
  set(heap, 0x0000000d7, new_term(DP1,0x000000,0x0000000c7));
  set(heap, 0x0000000d8, new_term(VAR,0x000000,0x0000000d3));
  set(heap, 0x0000000d9, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x0000000da, new_term(APP,0x000000,0x0000000db));
  set(heap, 0x0000000db, new_term(DP0,0x000000,0x0000000d0));
  set(heap, 0x0000000dc, new_term(APP,0x000000,0x0000000dd));
  set(heap, 0x0000000dd, new_term(DP1,0x000000,0x0000000d0));
  set(heap, 0x0000000de, new_term(VAR,0x000000,0x0000000d9));
  set(heap, 0x0000000df, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x0000000e0, new_term(APP,0x000000,0x0000000e1));
  set(heap, 0x0000000e1, new_term(APP,0x000000,0x0000000e3));
  set(heap, 0x0000000e2, new_term(LAM,0x000000,0x0000000e9));
  set(heap, 0x0000000e3, new_term(VAR,0x000000,0x0000000df));
  set(heap, 0x0000000e4, new_term(LAM,0x000000,0x0000000e5));
  set(heap, 0x0000000e5, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x0000000e6, new_term(LAM,0x000000,0x0000000e7));
  set(heap, 0x0000000e7, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x0000000e8, new_term(VAR,0x000000,0x0000000e7));
  set(heap, 0x0000000e9, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x0000000ea, new_term(LAM,0x000000,0x0000000eb));
  set(heap, 0x0000000eb, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x0000000ec, new_term(VAR,0x000000,0x0000000e9));
  set(heap, 0x0000000ed, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x0000000ee, new_term(LAM,0x000000,0x0000000ef));
  set(heap, 0x0000000ef, new_term(SUB,0x000000,0x000000000));
  set(heap, 0x0000000f0, new_term(VAR,0x000000,0x0000000ed));
}

int main() {
  Heap* heap = new_heap();
  inject_P24(heap);

  clock_t start = clock();

  // Normalize and get interaction count
  Term root = got(heap, 0);
  normal(heap, root);
  clock_t end = clock();

  printf("Itrs: %u\n", get_itr(heap));
  double time_spent = (double)(end - start) / CLOCKS_PER_SEC * 1000;
  printf("Size: %u nodes\n", get_end(heap));
  printf("Time: %.2f seconds\n", time_spent / 1000.0);
  printf("MIPS: %.2f\n", (get_itr(heap) / 1000000.0) / (time_spent / 1000.0));

  free(heap->stk);
  free(heap->mem);
  free(heap->ini);
  free(heap->end);
  free(heap->itr);
  free(heap);
  return 0;
}

