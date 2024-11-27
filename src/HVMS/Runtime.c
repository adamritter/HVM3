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
#define VAR 0x01
#define SUB 0x02
#define NUL 0x03
#define ERA 0x04
#define LAM 0x05
#define APP 0x06
#define SUP 0x07
#define DUP 0x08

const Term VOID = 0;

// Types
typedef uint64_t u64;
typedef _Atomic(u64) a64;

// Global heap
static a64* BUFF     = NULL;
static u64  RNOD_INI = 0;
static u64  RNOD_END = 0;
static u64  RBAG     = 0x1000;
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

Term get(Loc loc) {
  return atomic_load_explicit(&BUFF[loc], memory_order_relaxed);
}

Term take(Loc loc) {
  return atomic_exchange_explicit(&BUFF[loc], VOID, memory_order_relaxed);
}

void set(Loc loc, Term term) {
  atomic_store_explicit(&BUFF[loc], term, memory_order_relaxed);
}

Loc port(u64 n, Loc x) {
  return n + x - 1;
}

// Allocation
Loc alloc_node(u64 arity) {
  Loc loc = RNOD_END;
  RNOD_END += arity;
  return loc;
}

u64 inc_itr() {
  return RBAG_END / 2;
}

Loc rbag_push(Term neg, Term pos) {
  Loc loc = RBAG + RBAG_END;
  RBAG_END += 2;
  set(loc + 0, neg);
  set(loc + 1, pos);
  return loc;
}

Loc rbag_pop() {
  if (RBAG_INI < RBAG_END) {
    Loc loc = RBAG + RBAG_INI;
    RBAG_INI += 2;
    return loc;
  }

  return 0;
}

Loc rbag_ini() {
  return RBAG + RBAG_INI;
}

Loc rbag_end() {
  return RBAG + RBAG_END;
}

// Atomic Linker
static void move(Loc neg_loc, u64 pos);

static void link(Term neg, Term pos) {
  if (term_tag(pos) == VAR) {
    Term far = swap(term_loc(pos), neg);
    if (term_tag(far) != SUB) {
      move(term_loc(pos), far);
    }
  } else {
    rbag_push(neg, pos);
  }
}

static void move(Loc neg_loc, Term pos) {
  Term neg = swap(neg_loc, pos);
  if (term_tag(neg) != SUB) {
    link(neg, pos);
  }
}

// Interactions
static void interact_applam(Loc a_loc, Loc b_loc) {
  Term arg = take(port(1, a_loc));
  Loc  ret = port(2, a_loc);
  Loc  var = port(1, b_loc);
  Term bod = take(port(2, b_loc));
  move(var, arg);
  move(ret, bod);
}

static void interact_appsup(Loc a_loc, Loc b_loc) {
  Term arg = take(port(1, a_loc));
  Loc  ret = port(2, a_loc);
  Term tm1 = take(port(1, b_loc));
  Term tm2 = take(port(2, b_loc));
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
  Term arg = take(port(1, a_loc));
  Loc  ret = port(2, a_loc);
  link(term_new(ERA, 0, 0), arg);
  move(ret, term_new(NUL, 0, 0));
}

static void interact_dupsup(Loc a_loc, Loc b_loc) {
  Loc  dp1 = port(1, a_loc);
  Loc  dp2 = port(2, a_loc);
  Term tm1 = take(port(1, b_loc));
  Term tm2 = take(port(2, b_loc));
  move(dp1, tm1);
  move(dp2, tm2);
}

static void interact_duplam(Loc a_loc, Loc b_loc) {
  Loc  dp1 = port(1, a_loc);
  Loc  dp2 = port(2, a_loc);
  Loc  var = port(1, b_loc);
  // TODO(enricozb): why is this the only take?
  Term bod = take(port(2, b_loc));
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
  Term bod = take(port(2, b_loc));
  move(var, term_new(NUL, 0, 0));
  link(term_new(ERA, 0, 0), bod);
}

static void interact_erasup(Loc b_loc) {
  Term tm1 = take(port(1, b_loc));
  Term tm2 = take(port(2, b_loc));
  link(term_new(ERA, 0, 0), tm1);
  link(term_new(ERA, 0, 0), tm2);
}

static char* tag_to_str(Tag tag);

static void interact(Term a, Term b) {
  Tag a_tag = term_tag(a);
  Tag b_tag = term_tag(b);
  Loc a_loc = term_loc(a);
  Loc b_loc = term_loc(b);

  // printf("INTERACT %s ~ %s\n", tag_to_str(a_tag), tag_to_str(b_tag));

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
  Loc loc = rbag_pop();
  if (loc == 0) {
    return 0;
  }

  Term neg = take(loc + 0);
  Term pos = take(loc + 1);

  interact(neg, pos);

  return 1;
}

// FFI exports
void hvm_init() {
  if (BUFF == NULL) {
    BUFF = calloc((1ULL << 16), sizeof(a64));
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

// Debugging Functions

static char* tag_to_str(Tag tag) {
  switch (tag) {
    case VOID: return "___";
    case VAR:  return "VAR";
    case SUB:  return "SUB";
    case NUL:  return "NUL";
    case ERA:  return "ERA";
    case LAM:  return "LAM";
    case APP:  return "APP";
    case SUP:  return "SUP";
    case DUP:  return "DUP";
    default:   return "???";
  }
}

void dump_buff() {
  printf("------------------\n");
  printf("      NODES\n");
  printf("ADDR   LOC LAB TAG\n");
  printf("------------------\n");
  for (Loc loc = RNOD_INI; loc < RNOD_END; loc++) {
    Term term = get(loc);
    Loc t_loc = term_loc(term);
    Lab t_lab = term_lab(term);
    Tag t_tag = term_tag(term);
    printf("%06X %03X %03X %s\n", loc, term_loc(term), term_lab(term), tag_to_str(term_tag(term)));
  }
  printf("------------------\n");
  printf("    REDEX BAG\n");
  printf("ADDR   LOC LAB TAG\n");
  printf("------------------\n");
  for (Loc loc = RBAG + RBAG_INI; loc < RBAG + RBAG_END; loc++) {
    Term term = get(loc);
    Loc t_loc = term_loc(term);
    Lab t_lab = term_lab(term);
    Tag t_tag = term_tag(term);
    printf("%06X %03X %03X %s\n", loc, term_loc(term), term_lab(term), tag_to_str(term_tag(term)));
  }
  printf("------------------\n");
}
