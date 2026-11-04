/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "TrimUnreachable.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>








/* --------------------------- global variables ----- */

int32_t count = 0;


/* ----------------------- function definitions ----- */

STAINLESS_FUNC_PURE int32_t get(int32_t* s) {
    return *s;
}

STAINLESS_FUNC_PURE void main(void) {
    
}
