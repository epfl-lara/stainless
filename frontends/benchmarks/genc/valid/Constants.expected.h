#ifndef __CONSTANTS_H__
#define __CONSTANTS_H__

/* --------------------------- preprocessor macros ----- */

#define STAINLESS_FUNC_PURE
#if defined(__cplusplus)
#undef STAINLESS_FUNC_PURE
#define STAINLESS_FUNC_PURE _Pragma("FUNC_IS_PURE;")
#elif __GNUC__>=3
#undef STAINLESS_FUNC_PURE
#define STAINLESS_FUNC_PURE __attribute__((__pure__))
#elif defined(__has_attribute)
#if __has_attribute(pure)
#undef STAINLESS_FUNC_PURE
#define STAINLESS_FUNC_PURE __attribute__((__pure__))
#endif
#endif


/* ----------------------------------- includes ----- */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>




/* ---------------------- data type definitions ----- */

typedef struct {
  int32_t x;
  int32_t y;
} Point;



/* ---------------------- function declarations ----- */

STAINLESS_FUNC_PURE int32_t check(int32_t f);
void main(void);

/* --------------------------- global variables ----- */

static const Point Center = { .x = 50, .y = 50 };
static const int32_t Limit = 16 + 1;
static int32_t (* const Op)(int32_t) = check;
static const int32_t Version = 3;

#endif
