/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "TailRecUnitNoExplicitEnd.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>



/* ------------------------------- type aliases ----- */

typedef void* State;





/* ---------------------- function declarations ----- */

static STAINLESS_FUNC_PURE void countDown(int32_t n);
static void* newState(void);


/* ----------------------- function definitions ----- */

static STAINLESS_FUNC_PURE void countDown(int32_t n) {
    int32_t n_0 = n;
    label_0: ;
        if (n_0 > 0) {
            int32_t n_0_0 = n_0 - 1;
            n_0 = n_0_0;
            goto label_0;
        };
}

void main(void) {
    State state = newState();
    countDown(1000000);
}

void* newState(void) {
  return NULL;
}
