// HVM3 Core: single-thread, polarized, LAM/APP & DUP/SUP only

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdatomic.h>
#include <string.h>
#include <time.h>

// Constants
#define VAR 0x01
#define SUB 0x02
#define NUL 0x03
#define ERA 0x04
#define LAM 0x05
#define APP 0x06
#define SUP 0x07
#define DUP 0x08

#define VOID 0x0000000000000000
#define RBAG 0x100000000

// Types
typedef uint64_t u64;
typedef _Atomic(u64) a64;

// Global heap
static a64* BUFF = NULL;
static u64  RNOD_INI = 0;
static u64  RNOD_END = 0;
static u64  RBAG_INI = 0;
static u64  RBAG_END = 0;

// Term operations
static inline u64 term_new(u64 tag, u64 lab, u64 loc) {
  return tag | (lab << 8) | (loc << 32);
}

static inline u64 term_tag(u64 term) {
  return term & 0xFF;
}

static inline u64 term_lab(u64 term) {
  return (term >> 8) & 0xFFFFFF;
}

static inline u64 term_loc(u64 term) {
  return (term >> 32) & 0xFFFFFFFF;
}

static inline u64 port(u64 n, u64 x) {
  return n + x - 1;
}

// Memory operations
static inline u64 swap(u64 loc, u64 term) {
  return atomic_exchange_explicit(&BUFF[loc], term, memory_order_relaxed);
}

static inline u64 got(u64 loc) {
  return atomic_load_explicit(&BUFF[loc], memory_order_relaxed);
}

static inline void set(u64 loc, u64 term) {
  atomic_store_explicit(&BUFF[loc], term, memory_order_relaxed);
}

// Allocation
static inline u64 alloc_node(u64 arity) {
  u64 loc = RNOD_END;
  RNOD_END += arity;
  return loc;
}

static inline u64 inc_itr() {
  return RBAG_END / 2;
}

// Atomic Linker
static void move(u64 neg_loc, u64 pos);

static void link(u64 neg, u64 pos) {
  if (term_tag(pos) == VAR) {
    u64 far = swap(term_loc(pos), neg);
    if (term_tag(far) != SUB) {
      move(term_loc(pos), far);
    }
  } else {
    u64 loc = RBAG + RBAG_END;
    RBAG_END += 2;
    set(loc + 0, neg);
    set(loc + 1, pos);
  }
}

static void move(u64 neg_loc, u64 pos) {
  u64 neg = swap(neg_loc, pos);
  if (term_tag(neg) != SUB) {
    link(neg, pos);
  }
}

// Interactions
static void interact_applam(u64 a_loc, u64 b_loc) {
  u64 arg = swap(port(1, a_loc), VOID);
  u64 ret = port(2, a_loc);
  u64 var = port(1, b_loc);
  u64 bod = swap(port(2, b_loc), VOID);
  move(var, arg);
  move(ret, bod);
}

static void interact_appsup(u64 a_loc, u64 b_loc) {
  u64 arg = swap(port(1, a_loc), VOID);
  u64 ret = port(2, a_loc);
  u64 tm1 = swap(port(1, b_loc), VOID);
  u64 tm2 = swap(port(2, b_loc), VOID);
  u64 dp1 = alloc_node(2);
  u64 dp2 = alloc_node(2);
  u64 cn1 = alloc_node(2);
  u64 cn2 = alloc_node(2);
  set(port(1, dp1), term_new(SUB, 0, port(1, dp1)));
  set(port(2, dp1), term_new(SUB, 0, port(2, dp1)));
  set(port(1, dp2), term_new(VAR, 0, port(2, cn1)));
  set(port(2, dp2), term_new(VAR, 0, port(2, cn2)));
  set(port(1, cn1), term_new(VAR, 0, port(1, dp1)));
  set(port(2, cn1), term_new(SUB, 0, port(2, cn1)));
  set(port(1, cn2), term_new(VAR, 0, port(2, dp1)));
  set(port(2, cn2), term_new(SUB, 0, port(2, cn2)));
  link(term_new(DUP, 0, dp1), arg);
  move(ret, term_new(SUP, 0, dp2));
  link(term_new(APP, 0, cn1), tm1);
  link(term_new(APP, 0, cn2), tm2);
}

static void interact_appnul(u64 a_loc) {
  u64 arg = swap(port(1, a_loc), VOID);
  u64 ret = port(2, a_loc);
  link(term_new(ERA, 0, 0), arg);
  move(ret, term_new(NUL, 0, 0));
}

static void interact_dupsup(u64 a_loc, u64 b_loc) {
  u64 dp1 = port(1, a_loc);
  u64 dp2 = port(2, a_loc);
  u64 tm1 = swap(port(1, b_loc), VOID);
  u64 tm2 = swap(port(2, b_loc), VOID);
  move(dp1, tm1);
  move(dp2, tm2);
}

static void interact_duplam(u64 a_loc, u64 b_loc) {
  u64 dp1 = port(1, a_loc);
  u64 dp2 = port(2, a_loc);
  u64 var = port(1, b_loc);
  u64 bod = swap(port(2, b_loc), VOID);
  u64 co1 = alloc_node(2);
  u64 co2 = alloc_node(2);
  u64 du1 = alloc_node(2);
  u64 du2 = alloc_node(2);
  set(port(1, co1), term_new(SUB, 0, port(1, co1)));
  set(port(2, co1), term_new(VAR, 0, port(1, du2)));
  set(port(1, co2), term_new(SUB, 0, port(1, co2)));
  set(port(2, co2), term_new(VAR, 0, port(2, du2)));
  set(port(1, du1), term_new(VAR, 0, port(1, co1)));
  set(port(2, du1), term_new(VAR, 0, port(1, co2)));
  set(port(1, du2), term_new(SUB, 0, port(1, du2)));
  set(port(2, du2), term_new(SUB, 0, port(2, du2)));
  move(dp1, term_new(LAM, 0, co1));
  move(dp2, term_new(LAM, 0, co2));
  move(var, term_new(SUP, 0, du1));
  link(term_new(DUP, 0, du2), bod);
}

static void interact_dupnul(u64 a_loc) {
  u64 dp1 = port(1, a_loc);
  u64 dp2 = port(2, a_loc);
  move(dp1, term_new(NUL, 0, 0));
  move(dp2, term_new(NUL, 0, 0));
}

static void interact_eralam(u64 b_loc) {
  u64 var = port(1, b_loc);
  u64 bod = swap(port(2, b_loc), VOID);
  move(var, term_new(NUL, 0, 0));
  link(term_new(ERA, 0, 0), bod);
}

static void interact_erasup(u64 b_loc) {
  u64 tm1 = swap(port(1, b_loc), VOID);
  u64 tm2 = swap(port(2, b_loc), VOID);
  link(term_new(ERA, 0, 0), tm1);
  link(term_new(ERA, 0, 0), tm2);
}

static void interact(u64 a, u64 b) {
  u64 a_tag = term_tag(a);
  u64 b_tag = term_tag(b);
  u64 a_loc = term_loc(a);
  u64 b_loc = term_loc(b);
  switch (a_tag) {
    case APP:
      switch (b_tag) {
        case LAM: interact_applam(a_loc, b_loc); break;
        case SUP: interact_appsup(a_loc, b_loc); break;
        case NUL: interact_appnul(a_loc); break;
      }
      break;
    case DUP:
      switch (b_tag) {
        case SUP: interact_dupsup(a_loc, b_loc); break;
        case LAM: interact_duplam(a_loc, b_loc); break;
        case NUL: interact_dupnul(a_loc); break;
      }
      break;
    case ERA:
      switch (b_tag) {
        case LAM: interact_eralam(b_loc); break;
        case SUP: interact_erasup(b_loc); break;
        case NUL: break;
      }
      break;
  }
}

// Evaluation
static int normal_step() {
  if (RBAG_INI < RBAG_END) {
    u64 loc = RBAG + RBAG_INI;
    u64 neg = got(loc + 0);
    u64 pos = got(loc + 1);
    set(loc + 0, VOID);
    set(loc + 1, VOID);
    interact(neg, pos);
    RBAG_INI += 2;
    return 1;
  }
  return 0;
}

// FFI exports
void hvm_init() {
  if (BUFF == NULL) {
    BUFF = calloc((1ULL << 33), sizeof(a64));
  }
  RNOD_INI = 0;
  RNOD_END = 0;
  RBAG_INI = 0;
  RBAG_END = 0;
}

void hvm_free() {
  if (BUFF != NULL) {
    free(BUFF);
    BUFF = NULL;
  }
}

u64 normal(u64 term) {
  while (normal_step());
  return term;
}

//u64 term_new(u64 tag, u64 lab, u64 loc);
//u64 term_tag(u64 term);
//u64 term_lab(u64 term);
//u64 term_loc(u64 term);
//u64 swap(u64 loc, u64 term);
//u64 got(u64 loc);
//void set(u64 loc, u64 term);
//u64 alloc_node(u64 arity);
//u64 inc_itr();
