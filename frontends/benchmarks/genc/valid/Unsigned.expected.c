/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "Unsigned.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>







/* ---------------------- function declarations ----- */

static STAINLESS_FUNC_PURE uint64_t fa(uint64_t x, uint64_t y);
static STAINLESS_FUNC_PURE uint32_t fb(uint32_t x, uint32_t y);
static STAINLESS_FUNC_PURE uint16_t fc(uint16_t x, uint16_t y);
static STAINLESS_FUNC_PURE uint8_t fd(uint8_t x, uint8_t y);
static 
void print(char c);
static 
void printU16(uint16_t x);
static 
void printU32(uint32_t x);
static 
void printU64(uint64_t x);
static 
void printU8(uint8_t x);
static void println(void);
static void printlnU16(uint16_t x);
static void printlnU32(uint32_t x);
static void printlnU64(uint64_t x);
static void printlnU8(uint8_t x);


/* ----------------------- function definitions ----- */

static STAINLESS_FUNC_PURE uint64_t fa(uint64_t x, uint64_t y) {
    return x + y;
}

static STAINLESS_FUNC_PURE uint32_t fb(uint32_t x, uint32_t y) {
    return x - y;
}

static STAINLESS_FUNC_PURE uint16_t fc(uint16_t x, uint16_t y) {
    return x * y;
}

static STAINLESS_FUNC_PURE uint8_t fd(uint8_t x, uint8_t y) {
    return x / y;
}

void main(void) {
    uint64_t a = fa(16, 84);
    uint32_t b = fb(84, 14);
    uint16_t c = fc(5, 7);
    uint8_t d = fd(126, 3);
    printlnU64(a);
    printlnU32(b);
    printlnU16(c);
    printlnU8(d);
}


void print(char c) {
  printf("%c", c);
}
      


void printU16(uint16_t x) {
  printf("%"PRIu16, x);
}
     


void printU32(uint32_t x) {
  printf("%"PRIu32, x);
}
     


void printU64(uint64_t x) {
  printf("%"PRIu64, x);
}
     


void printU8(uint8_t x) {
  printf("%"PRIu8, x);
}
     

static void println(void) {
    print('\n');
}

static void printlnU16(uint16_t x) {
    printU16(x);
    println();
}

static void printlnU32(uint32_t x) {
    printU32(x);
    println();
}

static void printlnU64(uint64_t x) {
    printU64(x);
    println();
}

static void printlnU8(uint8_t x) {
    printU8(x);
    println();
}
