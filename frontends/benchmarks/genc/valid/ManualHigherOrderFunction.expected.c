/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "ManualHigherOrderFunction.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>







/* ---------------------- function declarations ----- */

static int32_t applyTo(int32_t (*f)(int32_t (*)(int32_t)), int32_t (*g)(int32_t));
static STAINLESS_FUNC_PURE int32_t callWithOne(int32_t (*g)(int32_t));
static STAINLESS_FUNC_PURE int32_t inc(int32_t x);
static 
void print(int32_t x);
static 
void print_1(char c);
static void println(int32_t x);
static void println_1(void);


/* ----------------------- function definitions ----- */

int32_t applyTo(int32_t (*f)(int32_t (*)(int32_t)), int32_t (*g)(int32_t)) { return f(g); }

static STAINLESS_FUNC_PURE int32_t callWithOne(int32_t (*g)(int32_t)) {
    return g(1);
}

static STAINLESS_FUNC_PURE int32_t inc(int32_t x) {
    if (x == 2147483647) {
        return x;
    } else {
        return x + 1;
    }
}

void main(void) {
    println(applyTo(callWithOne, inc));
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
