/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "RefInCtor.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>








/* ----------------------- function definitions ----- */

STAINLESS_FUNC_PURE void main(void) {
    
}

STAINLESS_FUNC_PURE void test1(int32_t v) {
    int32_t tmp = v;
    int32_t* norm_0 = &tmp;
    int32_t cont = *norm_0;
}

STAINLESS_FUNC_PURE void test2(int32_t v) {
    int32_t tmp_1 = v;
    int32_t* tmp = &tmp_1;
    int32_t* norm_1 = tmp;
    int32_t cont = *norm_1;
}
