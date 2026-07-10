/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "StateTest.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>



/* ------------------------------- type aliases ----- */

typedef void* State;





/* ---------------------- function declarations ----- */

static STAINLESS_FUNC_PURE int32_t f(State state);
static void* newState(void);


/* ----------------------- function definitions ----- */

static STAINLESS_FUNC_PURE int32_t f(State state) {
    return 0;
}

int32_t main(void) {
    State state = newState();
    return f(state);
}

void* newState(void) {
  return NULL;
}
