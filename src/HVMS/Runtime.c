// HVM3 Core: single-thread, polarized, LAM/APP & DUP/SUP only

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdatomic.h>
#include <string.h>
#include <time.h>

typedef uint8_t  Tag;  //  8 bits
typedef uint32_t Lab;  // 24 bits
typedef uint32_t Loc;  // 32 bits
typedef uint64_t Term; // Loc | Lab | Tag
typedef uint32_t u32;
typedef uint64_t u64;

// Constants
const Tag VAR = 0x01;
const Tag SUB = 0x02;
const Tag NUL = 0x03;
const Tag ERA = 0x04;
const Tag LAM = 0x05;
const Tag APP = 0x06;
const Tag SUP = 0x07;
const Tag DUP = 0x08;

const Term VOID = 0;

// Types
typedef uint64_t u64;
typedef _Atomic(u64) a64;

// Global heap
static a64* BUFF     = NULL;
static u64  RNOD_INI = 0;
static u64  RNOD_END = 0;
static u64  RBAG     = 0x100000000;
static u64  RBAG_INI = 0;
static u64  RBAG_END = 0;

// Term operations
Term term_new(Tag tag, Lab lab, Loc loc) {
  Term tag_enc = tag;
  Term lab_enc = ((Term)lab) << 8;
  Term loc_enc = ((Term)loc) << 32;

  return loc_enc | lab_enc | tag_enc;
}

Tag term_tag(Term term) {
  return term & 0xFF;
}

Lab term_lab(Term term) {
  return (term >> 8) & 0xFFFFFF;
}

Loc term_loc(Term term) {
  return (term >> 32) & 0xFFFFFFFF;
}

// Memory operations
Term swap(Loc loc, Term term) {
  return atomic_exchange_explicit(&BUFF[loc], term, memory_order_relaxed);
}

Term got(Loc loc) {
  return atomic_load_explicit(&BUFF[loc], memory_order_relaxed);
}

void set(Loc loc, Term term) {
  atomic_store_explicit(&BUFF[loc], term, memory_order_relaxed);
}

Loc port(u64 n, Loc x) {
  return n + x - 1;
}

// Allocation
Loc alloc_node(u64 arity) {
  u64 loc = RNOD_END;
  RNOD_END += arity;
  return loc;
}

u64 inc_itr() {
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
static void interact_applam(Loc a_loc, Loc b_loc) {
  Term arg = swap(port(1, a_loc), VOID);
  Loc  ret = port(2, a_loc);
  Loc  var = port(1, b_loc);
  Term bod = swap(port(2, b_loc), VOID);
  move(var, arg);
  move(ret, bod);
}

static void interact_appsup(Loc a_loc, Loc b_loc) {
  Term arg = swap(port(1, a_loc), VOID);
  Loc  ret = port(2, a_loc);
  Term tm1 = swap(port(1, b_loc), VOID);
  Term tm2 = swap(port(2, b_loc), VOID);
  Loc  dp1 = alloc_node(2);
  Loc  dp2 = alloc_node(2);
  Loc  cn1 = alloc_node(2);
  Loc  cn2 = alloc_node(2);
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

static void interact_appnul(Loc a_loc) {
  Term arg = swap(port(1, a_loc), VOID);
  Loc  ret = port(2, a_loc);
  link(term_new(ERA, 0, 0), arg);
  move(ret, term_new(NUL, 0, 0));
}

static void interact_dupsup(Loc a_loc, Loc b_loc) {
  Loc  dp1 = port(1, a_loc);
  Loc  dp2 = port(2, a_loc);
  Term tm1 = swap(port(1, b_loc), VOID);
  Term tm2 = swap(port(2, b_loc), VOID);
  move(dp1, tm1);
  move(dp2, tm2);
}

static void interact_duplam(Loc a_loc, Loc b_loc) {
  Loc  dp1 = port(1, a_loc);
  Loc  dp2 = port(2, a_loc);
  Loc  var = port(1, b_loc);
  Term bod = swap(port(2, b_loc), VOID);
  Loc  co1 = alloc_node(2);
  Loc  co2 = alloc_node(2);
  Loc  du1 = alloc_node(2);
  Loc  du2 = alloc_node(2);
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

static void interact_eralam(Loc b_loc) {
  Loc  var = port(1, b_loc);
  Term bod = swap(port(2, b_loc), VOID);
  move(var, term_new(NUL, 0, 0));
  link(term_new(ERA, 0, 0), bod);
}

static void interact_erasup(Loc b_loc) {
  Term tm1 = swap(port(1, b_loc), VOID);
  Term tm2 = swap(port(2, b_loc), VOID);
  link(term_new(ERA, 0, 0), tm1);
  link(term_new(ERA, 0, 0), tm2);
}

static void interact(Term a, Term b) {
  Tag a_tag = term_tag(a);
  Tag b_tag = term_tag(b);
  Loc a_loc = term_loc(a);
  Loc b_loc = term_loc(b);
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
    Loc  loc = RBAG + RBAG_INI;
    Term neg = got(loc + 0);
    Term pos = got(loc + 1);
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

Term normal(Term term) {
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
