#include <stdint.h>
#include <stdatomic.h>
#include <stdlib.h>
#include <stdio.h>
#include <time.h>

typedef uint64_t u64;
typedef _Atomic(u64) a64;

// Runtime Types
// -------------

typedef struct {
  a64* mem;
  a64* ini;
  a64* end;
  a64* itr;
} Heap;

// Constants
// ---------

#define AIR 0x00
#define SUB 0x01
#define VAR 0x02
#define DP0 0x03
#define DP1 0x04
#define APP 0x05
#define ERA 0x06
#define LAM 0x07
#define SUP 0x08

#define APP_ERA ((APP << 8) | ERA)
#define APP_LAM ((APP << 8) | LAM)
#define APP_SUP ((APP << 8) | SUP)
#define DP0_ERA ((DP0 << 8) | ERA)
#define DP0_LAM ((DP0 << 8) | LAM)
#define DP0_SUP ((DP0 << 8) | SUP)
#define DP1_ERA ((DP1 << 8) | ERA)
#define DP1_LAM ((DP1 << 8) | LAM)
#define DP1_SUP ((DP1 << 8) | SUP)

#define VOID 0x00000000000000

// Initialization
// --------------

Heap* new_heap() {
  Heap* heap = malloc(sizeof(Heap));
  heap->mem = calloc(1ULL << 42, sizeof(a64));
  heap->ini = calloc(1, sizeof(a64));
  heap->end = calloc(1, sizeof(a64));
  heap->itr = calloc(1, sizeof(a64));
  atomic_store_explicit(heap->ini, 0, memory_order_relaxed);
  atomic_store_explicit(heap->end, 1, memory_order_relaxed);
  atomic_store_explicit(heap->itr, 0, memory_order_relaxed);
  return heap;
}

u64 new_term(u64 tag, u64 lab, u64 loc) {
  u64 tag_enc = tag;
  u64 lab_enc = lab << 8;
  u64 loc_enc = loc << 32;
  return tag_enc | lab_enc | loc_enc;
}

u64 get_tag(u64 x) {
  return x & 0xFF;
}

u64 get_lab(u64 x) {
  return (x >> 8) & 0xFFFFFF;
}

u64 get_loc(u64 x) {
  return (x >> 32) & 0xFFFFFFFF;
}

u64 get_key(u64 term) {
  switch (get_tag(term)) {
    case VAR: return get_loc(term) + 0;
    case DP0: return get_loc(term) + 0;
    case DP1: return get_loc(term) + 1;
    default:  return 0;
  }
}

u64 get_ini(Heap* heap) {
  return atomic_load_explicit(heap->ini, memory_order_relaxed);
}

u64 get_end(Heap* heap) {
  return atomic_load_explicit(heap->end, memory_order_relaxed);
}

u64 get_itr(Heap* heap) {
  return atomic_load_explicit(heap->itr, memory_order_relaxed);
}

void set_ini(Heap* heap, u64 value) {
  atomic_store_explicit(heap->ini, value, memory_order_relaxed);
}

void set_end(Heap* heap, u64 value) {
  atomic_store_explicit(heap->end, value, memory_order_relaxed);
}

void set_itr(Heap* heap, u64 value) {
  atomic_store_explicit(heap->itr, value, memory_order_relaxed);
}

// Memory
// ------

u64 swap(Heap* heap, u64 loc, u64 term) {
  return atomic_exchange_explicit(&heap->mem[loc], term, memory_order_relaxed);
}

u64 got(Heap* heap, u64 loc) {
  return atomic_load_explicit(&heap->mem[loc], memory_order_relaxed);
}

void set(Heap* heap, u64 loc, u64 term) {
  atomic_store_explicit(&heap->mem[loc], term, memory_order_relaxed);
}

u64 take(Heap* heap, u64 loc) {
  return swap(heap, loc, VOID);
}

// Allocation
// ----------

u64 alloc_node(Heap* heap, u64 arity) {
  return atomic_fetch_add_explicit(heap->end, arity, memory_order_relaxed);
}

u64 inc_itr(Heap* heap) {
  return atomic_fetch_add_explicit(heap->itr, 1, memory_order_relaxed);
}

// Stringification
// ---------------

void print_tag(u64 tag) {
  switch (tag) {
    case AIR: printf("AIR"); break;
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

void print_term(u64 term) {
  printf("new_term(");
  print_tag(get_tag(term));
  printf(",0x%06llx,0x%09llx)", get_lab(term), get_loc(term));
}

void print_heap(Heap* heap) {
  u64 end = get_end(heap);
  for (u64 i = 0; i < end; i++) {
    u64 term = got(heap, i);
    if (term != 0) {
      printf("set(heap, 0x%09llx, ", i);
      print_term(term);
      printf(");\n");
    }
  }
}

// Evaluation
// ----------

u64 reduce_app_era(Heap* heap, u64 app, u64 era) {
  //printf("APP_ERA\n");
  inc_itr(heap);
  return era;
}

// TODO: implement the app_lam rule below. only the app_lam rule.
u64 reduce_app_lam(Heap* heap, u64 app, u64 lam) {
  //printf("APP_LAM\n");
  inc_itr(heap);
  u64 app_loc = get_loc(app);
  u64 lam_loc = get_loc(lam);
  u64 arg     = got(heap, app_loc + 1);
  u64 bod     = got(heap, lam_loc + 1);
  set(heap, lam_loc + 0, arg);
  set(heap, app_loc + 0, 0);
  set(heap, app_loc + 1, 0);
  set(heap, lam_loc + 1, 0);
  return bod;
}

u64 reduce_app_sup(Heap* heap, u64 app, u64 sup) {
  //printf("APP_SUP\n");
  inc_itr(heap);
  u64 app_loc = get_loc(app);
  u64 sup_loc = get_loc(sup);
  u64 arg     = got(heap, app_loc + 1);
  u64 tm0     = got(heap, sup_loc + 0);
  u64 tm1     = got(heap, sup_loc + 1);
  u64 du0     = alloc_node(heap, 3);
  u64 su0     = alloc_node(heap, 2);
  u64 ap0     = alloc_node(heap, 2);
  u64 ap1     = alloc_node(heap, 2);
  set(heap, du0 + 0, new_term(SUB, 0, 0));
  set(heap, du0 + 1, new_term(SUB, 0, 0));
  set(heap, du0 + 2, new_term(ERA, 0, 0));
  set(heap, du0 + 2, arg);
  set(heap, ap0 + 0, tm0);
  set(heap, ap0 + 1, new_term(DP0, 0, du0));
  set(heap, ap1 + 0, tm1);
  set(heap, ap1 + 1, new_term(DP1, 0, du0));
  set(heap, su0 + 0, new_term(APP, 0, ap0));
  set(heap, su0 + 1, new_term(APP, 0, ap1));
  set(heap, app_loc + 0, 0);
  set(heap, app_loc + 1, 0);
  set(heap, sup_loc + 0, 0);
  set(heap, sup_loc + 1, 0);
  return new_term(SUP, 0, su0);
}

u64 reduce_dup_era(Heap* heap, u64 dup, u64 era) {
  //printf("DUP_ERA\n");
  inc_itr(heap);
  u64 dup_loc = get_loc(dup);
  u64 dup_num = get_tag(dup) == DP0 ? 0 : 1;
  set(heap, dup_loc + 0, era);
  set(heap, dup_loc + 1, era);
  set(heap, dup_loc + 2, 0);
  return got(heap, dup_loc + dup_num);
}

u64 reduce_dup_lam(Heap* heap, u64 dup, u64 lam) {
  //printf("DUP_LAM\n");
  inc_itr(heap);
  u64 dup_loc = get_loc(dup);
  u64 dup_num = get_tag(dup) == DP0 ? 0 : 1;
  u64 lam_loc = get_loc(lam);
  u64 bod     = got(heap, lam_loc + 1);
  u64 du0     = alloc_node(heap, 3);
  u64 lm0     = alloc_node(heap, 2);
  u64 lm1     = alloc_node(heap, 2);
  u64 su0     = alloc_node(heap, 2);
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
  set(heap, dup_loc + 2, 0);
  set(heap, lam_loc + 1, 0);
  return got(heap, dup_loc + dup_num);
}

u64 reduce_dup_sup(Heap* heap, u64 dup, u64 sup) {
  //printf("DUP_SUP\n");
  inc_itr(heap);
  u64 dup_loc = get_loc(dup);
  u64 dup_num = get_tag(dup) == DP0 ? 0 : 1;
  u64 sup_loc = get_loc(sup);
  u64 tm0     = got(heap, sup_loc + 0);
  u64 tm1     = got(heap, sup_loc + 1);
  set(heap, dup_loc + 0, tm0);
  set(heap, dup_loc + 1, tm1);
  set(heap, dup_loc + 2, 0);
  set(heap, sup_loc + 0, 0);
  set(heap, sup_loc + 1, 0);
  return got(heap, dup_loc + dup_num);
}

u64 reduce(Heap* heap, u64 term) {
  static u64 path[8 * 256 * 256 * 256];
  //u64 loop = 0;
  u64 spos = 0;
  u64 next = term;
  while (1) {
    //if (++loop % 65536 == 0) {
      //printf("%llx %llx\n", ++loop, spos);
    //}

    //printf("NEXT: ");
    //print_term(next);
    //printf(" ## ");
    //for (int i = spos - 1; i >= 0; --i) {
      //print_tag(get_tag(path[i]));
      //printf(" ");
    //}
    //printf("\n");

    u64 tag = get_tag(next);
    u64 lab = get_lab(next);
    u64 loc = get_loc(next);
    switch (tag) {
      case APP: {
        path[spos++] = next;
        next = got(heap, loc + 0);
        continue;
      }
      case DP0:
      case DP1: {
        u64 key = get_key(next);
        u64 sub = got(heap, key);
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
        u64 key = get_key(next);
        u64 sub = got(heap, key);
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
          u64 prev = path[--spos];
          u64 ptag = get_tag(prev);
          u64 plab = get_lab(prev);
          u64 ploc = get_loc(prev);
          //printf("RULE: %llx\n", ((ptag << 8) | tag));
          switch ((ptag << 8) | tag) {
            case APP_ERA: next = reduce_app_era(heap, prev, next); continue;
            case APP_LAM: next = reduce_app_lam(heap, prev, next); continue;
            case APP_SUP: next = reduce_app_sup(heap, prev, next); continue;
            case DP0_ERA: next = reduce_dup_era(heap, prev, next); continue;
            case DP0_LAM: next = reduce_dup_lam(heap, prev, next); continue;
            case DP0_SUP: next = reduce_dup_sup(heap, prev, next); continue;
            case DP1_ERA: next = reduce_dup_era(heap, prev, next); continue;
            case DP1_LAM: next = reduce_dup_lam(heap, prev, next); continue;
            case DP1_SUP: next = reduce_dup_sup(heap, prev, next); continue;
          }
          break;
        }
      }
    }
    // Return
    if (spos == 0) {
      //printf("DONE\n");
      return next;
    } else {
      u64 host = path[spos];
      u64 htag = get_tag(host);
      u64 hlab = get_lab(host);
      u64 hloc = get_loc(host);
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
          //printf("ERROR-X\n");
          return 0;
        }
      }
    }
  }
  //printf("ERROR-Y\n");
  return 0;
}

// Normalization
// -------------

u64 normal(Heap* heap, u64 term) {
  u64 wnf = reduce(heap, term);
  u64 tag = get_tag(wnf);
  u64 lab = get_lab(wnf);
  u64 loc = get_loc(wnf);
  switch (tag) {
    case APP: {
      u64 fun;
      u64 arg;
      fun = got(heap, loc + 0);
      fun = normal(heap, fun);
      arg = got(heap, loc + 1);
      arg = normal(heap, arg);
      set(heap, loc + 0, fun);
      set(heap, loc + 1, arg);
      return wnf;
    }
    case LAM: {
      u64 bod;
      bod = got(heap, loc + 1);
      bod = normal(heap, bod);
      set(heap, loc + 1, bod);
      return wnf;
    }
    case SUP: {
      u64 tm0;
      u64 tm1;
      tm0 = got(heap, loc + 0);
      tm0 = normal(heap, tm0);
      tm1 = got(heap, loc + 1);
      tm1 = normal(heap, tm1);
      set(heap, loc + 0, tm0);
      set(heap, loc + 1, tm1);
      return wnf;
    }
    case DP0: {
      u64 val;
      val = got(heap, loc + 2);
      val = normal(heap, val);
      set(heap, loc + 2, val);
      return wnf;
    }
    case DP1: {
      u64 val;
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

#include "book.c"

int main() {
  Heap* heap = new_heap();
  inject_P22(heap);

  clock_t start = clock();

  // Normalize and get interaction count
  u64 root = got(heap, 0);
  normal(heap, root);
  printf("Interactions: %llu\n", get_itr(heap));

  clock_t end = clock();
  double time_spent = (double)(end - start) / CLOCKS_PER_SEC * 1000;
  printf("Time: %.2fms\n", time_spent);

  free(heap->mem);
  free(heap->ini);
  free(heap->end);
  free(heap->itr);
  free(heap);
  return 0;
}
