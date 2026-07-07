/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "TwoOptions.h"

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

typedef enum {
  tag_None_int64,
  tag_Some_int64
} enum_Option_int64;


/* ---------------------- data type definitions ----- */

typedef struct {
  int8_t extra;
} None_int64;

typedef struct {
  int64_t v;
} Some_int64;

typedef union {
  None_int64 None_int64_v;
  Some_int64 Some_int64_v;
} union_Option_int64;

typedef struct {
  enum_Option_int64 tag;
  union_Option_int64 value;
} Option_int64;

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

static STAINLESS_FUNC_PURE bool isEmpty_int32(Option_int32 thiss);
static STAINLESS_FUNC_PURE bool isEmpty_int64(Option_int64 thiss);


/* ----------------------- function definitions ----- */

static STAINLESS_FUNC_PURE bool isEmpty_int32(Option_int32 thiss) {
    if (thiss.tag == tag_Some_int32) {
        return false;
    } else if (thiss.tag == tag_None_int32) {
        return true;
    }
}

static STAINLESS_FUNC_PURE bool isEmpty_int64(Option_int64 thiss) {
    if (thiss.tag == tag_Some_int64) {
        return false;
    } else if (thiss.tag == tag_None_int64) {
        return true;
    }
}

STAINLESS_FUNC_PURE void main(void) {
    
}

STAINLESS_FUNC_PURE void twoOptions(void) {
    Option_int64 opt1 = (Option_int64) { .tag = tag_None_int64, .value = (union_Option_int64) { .None_int64_v = (None_int64) { .extra = 0 } } };
    Option_int32 opt2 = (Option_int32) { .tag = tag_None_int32, .value = (union_Option_int32) { .None_int32_v = (None_int32) { .extra = 0 } } };
    isEmpty_int64(opt1);
    isEmpty_int32(opt2);
}
