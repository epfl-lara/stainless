/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "ConversionOfIf.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>







/* ---------------------- function declarations ----- */

static STAINLESS_FUNC_PURE int64_t inArgument(bool c, int32_t a, int32_t b);
static STAINLESS_FUNC_PURE int32_t inCondition(bool c, int32_t n);
static STAINLESS_FUNC_PURE int8_t narrow(bool c, int32_t a, int32_t b);
static STAINLESS_FUNC_PURE int64_t ofMatch(int32_t n);
static 
void print(char c);
static 
void printU8(uint8_t x);
static 
void print_1(int32_t x);
static void println(void);
static 
void printlnLong(int64_t x);
static void printlnU8(uint8_t x);
static void println_1(int32_t x);
static STAINLESS_FUNC_PURE uint8_t toUnsigned(bool c, int32_t a, int32_t b);
static STAINLESS_FUNC_PURE int64_t twice(int64_t x);
static STAINLESS_FUNC_PURE int64_t widen(bool c, int32_t a, int32_t b);
static STAINLESS_FUNC_PURE int64_t widenOr(bool c, int32_t a);


/* ----------------------- function definitions ----- */

static STAINLESS_FUNC_PURE int64_t inArgument(bool c, int32_t a, int32_t b) {
    int32_t norm_0;
    if (c) {
        norm_0 = a;
    } else {
        norm_0 = b;
    }
    int64_t norm_1 = (int64_t)norm_0;
    return twice(norm_1);
}

static STAINLESS_FUNC_PURE int32_t inCondition(bool c, int32_t n) {
    int32_t i = 0;
    while (true) {
        int32_t norm_2;
        if (c) {
            norm_2 = i;
        } else {
            norm_2 = i + 1;
        }
        int64_t norm_3 = (int64_t)norm_2;
        int64_t norm_4 = (int64_t)n;
        if (norm_3 < norm_4) {
            i = i + 1;
        } else {
            break;
        }
    }
    return i;
}

void main(void) {
    printlnLong(widen(true, 1, 2));
    printlnLong(widen(false, 1, 2));
    printlnLong(widenOr(true, 4));
    printlnLong(widenOr(false, 4));
    printlnLong((int64_t)narrow(true, -3, 100));
    printlnLong((int64_t)narrow(false, -3, 100));
    printlnU8(toUnsigned(true, 200, 7));
    printlnU8(toUnsigned(false, 200, 7));
    printlnLong(ofMatch(0));
    printlnLong(ofMatch(3));
    printlnLong(inArgument(false, 1, 21));
    println_1(inCondition(true, 3));
    println_1(inCondition(false, 3));
}

static STAINLESS_FUNC_PURE int8_t narrow(bool c, int32_t a, int32_t b) {
    int32_t norm_9;
    if (c) {
        norm_9 = a;
    } else {
        norm_9 = b;
    }
    return (int8_t)norm_9;
}

static STAINLESS_FUNC_PURE int64_t ofMatch(int32_t n) {
    int32_t norm_11;
    if (n == 0) {
        norm_11 = 10;
    } else {
        norm_11 = 20;
    }
    return (int64_t)norm_11;
}


void print(char c) {
  printf("%c", c);
}
      


void printU8(uint8_t x) {
  printf("%"PRIu8, x);
}
     


void print_1(int32_t x) {
  printf("%"PRIi32, x);
}
     

static void println(void) {
    print('\n');
}


void printlnLong(int64_t x) {
  printf("%"PRIi64"\n", x);
}
      

static void printlnU8(uint8_t x) {
    printU8(x);
    println();
}

static void println_1(int32_t x) {
    print_1(x);
    println();
}

static STAINLESS_FUNC_PURE uint8_t toUnsigned(bool c, int32_t a, int32_t b) {
    int32_t norm_10;
    if (c) {
        norm_10 = a;
    } else {
        norm_10 = b;
    }
    return (uint8_t)((uint32_t)norm_10);
}

static STAINLESS_FUNC_PURE int64_t twice(int64_t x) {
    return 2LL * x;
}

static STAINLESS_FUNC_PURE int64_t widen(bool c, int32_t a, int32_t b) {
    int32_t norm_5;
    if (c) {
        norm_5 = a;
    } else {
        norm_5 = b;
    }
    return (int64_t)norm_5;
}

static STAINLESS_FUNC_PURE int64_t widenOr(bool c, int32_t a) {
    int32_t norm_7 = a;
    int32_t norm_6;
    if (c) {
        norm_6 = 1;
    } else {
        norm_6 = 0;
    }
    int32_t norm_8 = norm_6;
    return (int64_t)(norm_7 | norm_8);
}
