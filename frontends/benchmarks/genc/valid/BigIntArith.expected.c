/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "BigIntArith.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>







/* ---------------------- function declarations ----- */

static STAINLESS_FUNC_PURE uint32_t compute(uint32_t a, uint32_t b);
static STAINLESS_FUNC_PURE uint32_t diff(uint32_t a, uint32_t b);
static 
void print(int32_t x);
static 
void print_1(char c);
static void println(int32_t x);
static void println_1(void);
static STAINLESS_FUNC_PURE uint32_t sumTo(uint32_t n);


/* ----------------------- function definitions ----- */

static STAINLESS_FUNC_PURE uint32_t compute(uint32_t a, uint32_t b) {
    return (((a + b) * 3 + a / 2) + b % 1000) + b % 7;
}

static STAINLESS_FUNC_PURE uint32_t diff(uint32_t a, uint32_t b) {
    return a - b;
}

void main(void) {
    print((int32_t)compute(1000, 500));
    print((int32_t)diff(1000, 400));
    println((int32_t)sumTo(100));
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

STAINLESS_FUNC_PURE uint32_t scaleClamped(uint32_t x) {
    assert((0 <= x && x <= 1000000));
    return x * 3;
}

static STAINLESS_FUNC_PURE uint32_t sumTo(uint32_t n) {
    if (n <= 0) {
        return 0;
    } else {
        return n + sumTo(n - 1);
    }
}
