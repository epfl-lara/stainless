#ifndef __TRIMUNREACHABLE_H__
#define __TRIMUNREACHABLE_H__

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
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>




/* ---------------------- data type definitions ----- */

typedef struct {
  int32_t x;
  int32_t y;
} Point;



/* ---------------------- function declarations ----- */

STAINLESS_FUNC_PURE int32_t get(int32_t* s);
STAINLESS_FUNC_PURE void main(void);

#endif
