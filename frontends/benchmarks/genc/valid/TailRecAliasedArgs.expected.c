/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "TailRecAliasedArgs.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>



/* ------------------------------- type aliases ----- */

typedef void* State;





/* ---------------------- function declarations ----- */

static STAINLESS_FUNC_PURE int32_t aliased(int32_t n, int32_t a, int32_t b);
static void* newState(void);
static 
void print(int32_t x);
static 
void print_1(char c);
static void println(int32_t x);
static void println_1(void);


/* ----------------------- function definitions ----- */

static STAINLESS_FUNC_PURE int32_t aliased(int32_t n, int32_t a, int32_t b) {
    int32_t n_0 = n;
    int32_t a_0 = a;
    int32_t b_0 = b;
    label_0: ;
        if (n_0 == 0) {
            return a_0;
        } else {
            int32_t n_0_0 = n_0 - 1;
            int32_t a_0_0 = b_0;
            int32_t b_0_0 = a_0 + b_0;
            n_0 = n_0_0;
            a_0 = a_0_0;
            b_0 = b_0_0;
            goto label_0;
        };
}

void main(void) {
    State state = newState();
    println(aliased(5, 0, 1));
}

void* newState(void) {
  return NULL;
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
