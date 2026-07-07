/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "TailRecFib.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>



/* ------------------------------- type aliases ----- */

typedef void* State;





/* ---------------------- function declarations ----- */

static STAINLESS_FUNC_PURE int32_t fib(int32_t n, int32_t i, int32_t j);
static STAINLESS_FUNC_PURE int32_t fib_default_2(void);
static STAINLESS_FUNC_PURE int32_t fib_default_3(void);
static void* newState(void);
static 
void print(int32_t x);
static 
void print_1(char c);
static void println(int32_t x);
static void println_1(void);


/* ----------------------- function definitions ----- */

static STAINLESS_FUNC_PURE int32_t fib(int32_t n, int32_t i, int32_t j) {
    int32_t n_0 = n;
    int32_t i_0 = i;
    int32_t j_0 = j;
    while (true) {
        label_0: ;
            if (n_0 == 0) {
                return i_0;
            } else {
                int32_t n_0_0 = n_0 - 1;
                int32_t i_0_0 = j_0;
                int32_t j_0_0 = i_0 + j_0;
                n_0 = n_0_0;
                i_0 = i_0_0;
                j_0 = j_0_0;
                goto label_0;
            };
    }
}

static STAINLESS_FUNC_PURE int32_t fib_default_2(void) {
    return 0;
}

static STAINLESS_FUNC_PURE int32_t fib_default_3(void) {
    return 1;
}

void main(void) {
    State state = newState();
    println(fib(10, fib_default_2(), fib_default_3()));
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
