/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "Pointer2.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>







/* ---------------------- function declarations ----- */

static STAINLESS_FUNC_PURE int32_t f(int32_t v);
static int32_t inc(int32_t* p);
static 
void print(int32_t x);
static 
void print_1(char c);
static void println(int32_t x);
static void println_1(void);


/* ----------------------- function definitions ----- */

static STAINLESS_FUNC_PURE int32_t f(int32_t v) {
    int32_t tmp = v + 42;
    int32_t* norm_0 = &tmp;
    return inc(norm_0);
}

static int32_t inc(int32_t* p) {
    *p = (*p) + 1;
    return *p;
}

void main(void) {
    int32_t tmp = 123;
    int32_t* norm_1 = &tmp;
    int32_t res1 = inc(norm_1);
    int32_t res2 = f(400);
    println(res1);
    println(res2);
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
