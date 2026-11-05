/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "OptionLeftEquals.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>




/* -------------------------------------- enums ----- */

typedef enum {
  tag_None_int32,
  tag_Some_int32
} enum_Option_int32;


/* ---------------------- data type definitions ----- */

typedef struct {
  int8_t extra;
} None_int32;

typedef struct {
  int32_t v;
} Some_int32;

typedef union {
  None_int32 None_int32_v;
  Some_int32 Some_int32_v;
} union_Option_int32;

typedef struct {
  enum_Option_int32 tag;
  union_Option_int32 value;
} Option_int32;



/* ---------------------- function declarations ----- */

static STAINLESS_FUNC_PURE bool differsFromOne(Option_int32 o);
static STAINLESS_FUNC_PURE bool equals_Option_int32(Option_int32 lhs, Option_int32 rhs);
static STAINLESS_FUNC_PURE bool isNone(Option_int32 o);
static 
void print(char* s);
static void printAnswer(bool b);
static 
void print_1(char c);
static void println(char* s);
static void println_1(void);


/* ----------------------- function definitions ----- */

static STAINLESS_FUNC_PURE bool differsFromOne(Option_int32 o) {
    return !equals_Option_int32((Option_int32) { .tag = tag_Some_int32, .value = (union_Option_int32) { .Some_int32_v = (Some_int32) { .v = 1 } } }, o);
}

static STAINLESS_FUNC_PURE bool equals_Option_int32(Option_int32 lhs, Option_int32 rhs) {
    return (lhs.tag == tag_None_int32 && rhs.tag == tag_None_int32) && true || (lhs.tag == tag_Some_int32 && rhs.tag == tag_Some_int32) && lhs.value.Some_int32_v.v == rhs.value.Some_int32_v.v;
}

static STAINLESS_FUNC_PURE bool isNone(Option_int32 o) {
    return equals_Option_int32((Option_int32) { .tag = tag_None_int32, .value = (union_Option_int32) { .None_int32_v = (None_int32) { .extra = 0 } } }, o);
}

void main(void) {
    printAnswer(isNone((Option_int32) { .tag = tag_Some_int32, .value = (union_Option_int32) { .Some_int32_v = (Some_int32) { .v = 1 } } }));
    printAnswer(isNone((Option_int32) { .tag = tag_None_int32, .value = (union_Option_int32) { .None_int32_v = (None_int32) { .extra = 0 } } }));
    printAnswer(differsFromOne((Option_int32) { .tag = tag_Some_int32, .value = (union_Option_int32) { .Some_int32_v = (Some_int32) { .v = 1 } } }));
    printAnswer(differsFromOne((Option_int32) { .tag = tag_Some_int32, .value = (union_Option_int32) { .Some_int32_v = (Some_int32) { .v = 2 } } }));
    printAnswer(differsFromOne((Option_int32) { .tag = tag_None_int32, .value = (union_Option_int32) { .None_int32_v = (None_int32) { .extra = 0 } } }));
    printAnswer(equals_Option_int32((Option_int32) { .tag = tag_Some_int32, .value = (union_Option_int32) { .Some_int32_v = (Some_int32) { .v = 1 } } }, (Option_int32) { .tag = tag_None_int32, .value = (union_Option_int32) { .None_int32_v = (None_int32) { .extra = 0 } } }));
}


void print(char* s) {
  printf("%s", s);
}
      

static void printAnswer(bool b) {
    if (b) {
        println("yes");
    } else {
        println("no");
    }
}


void print_1(char c) {
  printf("%c", c);
}
      

static void println(char* s) {
    print(s);
    println_1();
}

static void println_1(void) {
    print_1('\n');
}
