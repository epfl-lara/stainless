/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "BigIntLiterals.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>







/* ---------------------- function declarations ----- */

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
static 
void print_1(int32_t x);
static void println(void);
static void printlnU16(uint16_t x);
static void printlnU32(uint32_t x);
static void printlnU64(uint64_t x);
static void printlnU8(uint8_t x);
static void println_1(int32_t x);


/* ----------------------- function definitions ----- */

void main(void) {
    uint8_t a = 200;
    uint16_t b = 60000;
    uint32_t c = 4000000000;
    uint64_t d = 5000000000;
    printlnU8(a);
    printlnU16(b);
    printlnU32(c);
    printlnU64(d);
    int8_t e = -100;
    int16_t f = -30000;
    int32_t g = -2000000000;
    int64_t h = -5000000000;
    println_1((int32_t)e);
    println_1((int32_t)f);
    println_1(g);
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
     


void print_1(int32_t x) {
  printf("%"PRIi32, x);
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

static void println_1(int32_t x) {
    print_1(x);
    println();
}
