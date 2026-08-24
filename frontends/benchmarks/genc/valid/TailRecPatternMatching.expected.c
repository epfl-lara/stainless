/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "TailRecPatternMatching.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>



/* ------------------------------- type aliases ----- */

typedef void* State;


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

static void* newState(void);
static STAINLESS_FUNC_PURE int32_t patternMatch(Option_int32 x, int32_t acc);
static 
void print(int32_t x);
static 
void print_1(char c);
static void println(int32_t x);
static void println_1(void);


/* ----------------------- function definitions ----- */

void main(void) {
    State state = newState();
    println(patternMatch((Option_int32) { .tag = tag_Some_int32, .value = (union_Option_int32) { .Some_int32_v = (Some_int32) { .v = 5 } } }, 0));
}

void* newState(void) {
  return NULL;
}

static STAINLESS_FUNC_PURE int32_t patternMatch(Option_int32 x, int32_t acc) {
    Option_int32 x_0 = x;
    int32_t acc_0 = acc;
    label_0: ;
        int32_t measure;
        if (x_0.tag == tag_None_int32) {
            measure = 0;
        } else if (x_0.tag == tag_Some_int32) {
            measure = x_0.value.Some_int32_v.v;
        }
        if (x_0.tag == tag_None_int32) {
            return acc_0;
        } else if (x_0.tag == tag_Some_int32 && x_0.value.Some_int32_v.v == 1) {
            Option_int32 x_0_0 = (Option_int32) { .tag = tag_None_int32, .value = (union_Option_int32) { .None_int32_v = (None_int32) { .extra = 0 } } };
            int32_t acc_0_0 = acc_0 + 1;
            x_0 = x_0_0;
            acc_0 = acc_0_0;
            goto label_0;
        } else if (x_0.tag == tag_Some_int32) {
            Option_int32 x_0_1 = (Option_int32) { .tag = tag_Some_int32, .value = (union_Option_int32) { .Some_int32_v = (Some_int32) { .v = (x_0.value.Some_int32_v.v - 1) } } };
            int32_t acc_0_1 = acc_0 + 1;
            x_0 = x_0_1;
            acc_0 = acc_0_1;
            goto label_0;
        };
}


void print(int32_t x) {
  printf("%"PRIi32, x);
}
     


void print_1(char c) {
  printf("%c", c);
}
      

static void println(int32_t x) {
    print(x);
    println_1();
}

static void println_1(void) {
    print_1('\n');
}
