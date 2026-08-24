#ifndef __FIXEDARRAY_H__
#define __FIXEDARRAY_H__

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
  int32_t a[5];
  int32_t y;
} W;

typedef struct {
  int32_t* data;
  int32_t length;
} array_int32;



/* ---------------------- function declarations ----- */

int32_t f(W* w);
void g(array_int32 a);
void main(void);

#endif
