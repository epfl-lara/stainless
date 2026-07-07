/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "InPlaceRefFnCall2.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>





/* ---------------------- data type definitions ----- */

typedef struct {
  int32_t _1;
  int32_t _2;
} Tuple_int32_Ref_int32;



/* ---------------------- function declarations ----- */

static STAINLESS_FUNC_PURE void placeholder(Tuple_int32_Ref_int32* r);


/* ----------------------- function definitions ----- */

STAINLESS_FUNC_PURE void f(int32_t v) {
    int32_t tmp_1 = v + 10;
    int32_t* norm_0 = &tmp_1;
    Tuple_int32_Ref_int32 tmp = (Tuple_int32_Ref_int32) { ._1 = 456, ._2 = (*norm_0) };
    Tuple_int32_Ref_int32* norm_1 = &tmp;
    placeholder(norm_1);
}

STAINLESS_FUNC_PURE void main(void) {
    
}

static STAINLESS_FUNC_PURE void placeholder(Tuple_int32_Ref_int32* r) {
    
}
