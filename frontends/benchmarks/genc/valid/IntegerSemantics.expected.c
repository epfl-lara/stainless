/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "IntegerSemantics.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>







/* ---------------------- function declarations ----- */

static STAINLESS_FUNC_PURE uint8_t addU8(uint8_t a, uint8_t b);
static STAINLESS_FUNC_PURE int32_t bitOps(int32_t x, int32_t y);
static STAINLESS_FUNC_PURE int32_t bnot(int32_t x);
static STAINLESS_FUNC_PURE int32_t boolToInt(bool b);
static STAINLESS_FUNC_PURE int32_t byteLshr(int8_t b, int32_t n);
static STAINLESS_FUNC_PURE int32_t byteShl(int8_t b, int32_t n);
static STAINLESS_FUNC_PURE int32_t byteToInt(int8_t b);
static STAINLESS_FUNC_PURE int64_t byteToLong(int8_t b);
static STAINLESS_FUNC_PURE int32_t byteToUnsigned(int8_t b);
static STAINLESS_FUNC_PURE int32_t div(int32_t a, int32_t b);
static STAINLESS_FUNC_PURE int64_t divLong(int64_t a, int64_t b);
static STAINLESS_FUNC_PURE int32_t lshr(int32_t x, int32_t n);
static STAINLESS_FUNC_PURE int64_t lshrLong(int64_t x, int64_t n);
static STAINLESS_FUNC_PURE bool mixedCmp(int8_t b, int32_t i);
static STAINLESS_FUNC_PURE uint16_t mulU16(uint16_t a, uint16_t b);
static STAINLESS_FUNC_PURE uint8_t narrowU32(uint32_t x);
static STAINLESS_FUNC_PURE int32_t negate(int32_t x);
static 
void print(int32_t x);
static 
void printU16(uint16_t x);
static 
void printU32(uint32_t x);
static 
void printU8(uint8_t x);
static 
void print_1(char c);
static void println(int32_t x);
static 
void printlnLong(int64_t x);
static void printlnU16(uint16_t x);
static void printlnU32(uint32_t x);
static void printlnU8(uint8_t x);
static void println_1(void);
static STAINLESS_FUNC_PURE int32_t rem(int32_t a, int32_t b);
static STAINLESS_FUNC_PURE int64_t remLong(int64_t a, int64_t b);
static STAINLESS_FUNC_PURE int32_t shl(int32_t x, int32_t n);
static STAINLESS_FUNC_PURE int64_t shlLong(int64_t x, int64_t n);
static STAINLESS_FUNC_PURE uint32_t shlU32(uint32_t a, uint32_t n);
static STAINLESS_FUNC_PURE int32_t shortLshr(int16_t s, int32_t n);
static STAINLESS_FUNC_PURE uint8_t shrU8(uint8_t a, uint8_t n);
static STAINLESS_FUNC_PURE uint32_t subU32(uint32_t a, uint32_t b);
static STAINLESS_FUNC_PURE int8_t toByte(int32_t x);
static STAINLESS_FUNC_PURE int32_t toInt(int64_t x);
static STAINLESS_FUNC_PURE int64_t toLong(int32_t x);
static STAINLESS_FUNC_PURE int16_t toShort(int32_t x);
static STAINLESS_FUNC_PURE int32_t toSigned(uint32_t x);
static STAINLESS_FUNC_PURE uint32_t toUnsigned(int32_t x);
static STAINLESS_FUNC_PURE int32_t u8ToInt(uint8_t x);
static STAINLESS_FUNC_PURE uint32_t widenU8(uint8_t x);


/* ----------------------- function definitions ----- */

static STAINLESS_FUNC_PURE uint8_t addU8(uint8_t a, uint8_t b) {
    return a + b;
}

static STAINLESS_FUNC_PURE int32_t bitOps(int32_t x, int32_t y) {
    return (x & y) | (x ^ y);
}

static STAINLESS_FUNC_PURE int32_t bnot(int32_t x) {
    return ~x;
}

static STAINLESS_FUNC_PURE int32_t boolToInt(bool b) {
    if (b) {
        return 1;
    } else {
        return 0;
    }
}

static STAINLESS_FUNC_PURE int32_t byteLshr(int8_t b, int32_t n) {
    return (int32_t)(((uint32_t)((int32_t)b)) >> n);
}

static STAINLESS_FUNC_PURE int32_t byteShl(int8_t b, int32_t n) {
    return (int32_t)(((uint32_t)((int32_t)b)) << n);
}

static STAINLESS_FUNC_PURE int32_t byteToInt(int8_t b) {
    return (int32_t)b;
}

static STAINLESS_FUNC_PURE int64_t byteToLong(int8_t b) {
    return (int64_t)b;
}

static STAINLESS_FUNC_PURE int32_t byteToUnsigned(int8_t b) {
    return ((int32_t)b) & 255;
}

static STAINLESS_FUNC_PURE int32_t div(int32_t a, int32_t b) {
    return a / b;
}

static STAINLESS_FUNC_PURE int64_t divLong(int64_t a, int64_t b) {
    return a / b;
}

static STAINLESS_FUNC_PURE int32_t lshr(int32_t x, int32_t n) {
    return (int32_t)(((uint32_t)x) >> n);
}

static STAINLESS_FUNC_PURE int64_t lshrLong(int64_t x, int64_t n) {
    return (int64_t)(((uint64_t)x) >> n);
}

void main(void) {
    println(lshr(-16, 2));
    println(lshr(-1, 31));
    println(lshr(-1, 0));
    println(shl(1, 31));
    println(shl(2147483647, 1));
    println(shl(-1, 20));
    printlnLong(shlLong(1, 40));
    printlnLong(lshrLong(-1, 60));
    printlnLong(shlLong(-1, 63));
    printlnLong(lshrLong(shlLong(-1, 63), 63));
    println(byteShl(-1, 4));
    println(byteShl(100, 2));
    println(byteLshr(-1, 4));
    println(shortLshr(-2, 1));
    println(byteToInt(toByte(300)));
    println(byteToInt(toByte(-129)));
    println(byteToInt(toByte(200)));
    println(byteToUnsigned(toByte(200)));
    println((int32_t)toShort(70000));
    println((int32_t)toShort(-40000));
    println(toInt(shlLong(1, 35) + ((int64_t)7)));
    println(toInt(-1));
    printlnLong(toLong(-1));
    printlnLong(toLong(2147483647) + ((int64_t)1));
    printlnLong(byteToLong(-128));
    println(div(-7, 2));
    println(rem(-7, 2));
    println(div(7, -2));
    println(rem(7, -2));
    println(rem(-7, -2));
    printlnLong(divLong(-9000000000, 7));
    printlnLong(remLong(-9000000000, 7));
    println(bnot(0));
    println(bnot(5));
    println(bitOps(3855, 255));
    println(boolToInt(mixedCmp(-1, 0)));
    println(boolToInt(mixedCmp(127, 127)));
    println(negate(-5));
    printlnU8(addU8(250, 10));
    printlnU32(subU32(0, 1));
    printlnU16(mulU16(300, 300));
    printlnU8(shrU8(200, 3));
    printlnU32(shlU32(1, 31));
    printlnU32(toUnsigned(-1));
    println(toSigned(subU32(0, 1)));
    println(toSigned(toUnsigned(-2147483648)));
    println(u8ToInt(narrowU32(subU32(0, 1))));
    printlnU32(widenU8(200));
}

static STAINLESS_FUNC_PURE bool mixedCmp(int8_t b, int32_t i) {
    return ((int32_t)b) < i;
}

static STAINLESS_FUNC_PURE uint16_t mulU16(uint16_t a, uint16_t b) {
    return a * b;
}

static STAINLESS_FUNC_PURE uint8_t narrowU32(uint32_t x) {
    return (uint8_t)x;
}

static STAINLESS_FUNC_PURE int32_t negate(int32_t x) {
    return -x;
}


void print(int32_t x) {
  printf("%"PRIi32, x);
}
     


void printU16(uint16_t x) {
  printf("%"PRIu16, x);
}
     


void printU32(uint32_t x) {
  printf("%"PRIu32, x);
}
     


void printU8(uint8_t x) {
  printf("%"PRIu8, x);
}
     


void print_1(char c) {
  printf("%c", c);
}
      

static void println(int32_t x) {
    print(x);
    println_1();
}


void printlnLong(int64_t x) {
  printf("%"PRIi64"\n", x);
}
      

static void printlnU16(uint16_t x) {
    printU16(x);
    println_1();
}

static void printlnU32(uint32_t x) {
    printU32(x);
    println_1();
}

static void printlnU8(uint8_t x) {
    printU8(x);
    println_1();
}

static void println_1(void) {
    print_1('\n');
}

static STAINLESS_FUNC_PURE int32_t rem(int32_t a, int32_t b) {
    return a % b;
}

static STAINLESS_FUNC_PURE int64_t remLong(int64_t a, int64_t b) {
    return a % b;
}

static STAINLESS_FUNC_PURE int32_t shl(int32_t x, int32_t n) {
    return (int32_t)(((uint32_t)x) << n);
}

static STAINLESS_FUNC_PURE int64_t shlLong(int64_t x, int64_t n) {
    return (int64_t)(((uint64_t)x) << n);
}

static STAINLESS_FUNC_PURE uint32_t shlU32(uint32_t a, uint32_t n) {
    return a << n;
}

static STAINLESS_FUNC_PURE int32_t shortLshr(int16_t s, int32_t n) {
    return (int32_t)(((uint32_t)((int32_t)s)) >> n);
}

static STAINLESS_FUNC_PURE uint8_t shrU8(uint8_t a, uint8_t n) {
    return a >> n;
}

static STAINLESS_FUNC_PURE uint32_t subU32(uint32_t a, uint32_t b) {
    return a - b;
}

static STAINLESS_FUNC_PURE int8_t toByte(int32_t x) {
    return (int8_t)x;
}

static STAINLESS_FUNC_PURE int32_t toInt(int64_t x) {
    return (int32_t)x;
}

static STAINLESS_FUNC_PURE int64_t toLong(int32_t x) {
    return (int64_t)x;
}

static STAINLESS_FUNC_PURE int16_t toShort(int32_t x) {
    return (int16_t)x;
}

static STAINLESS_FUNC_PURE int32_t toSigned(uint32_t x) {
    return (int32_t)x;
}

static STAINLESS_FUNC_PURE uint32_t toUnsigned(int32_t x) {
    return (uint32_t)x;
}

static STAINLESS_FUNC_PURE int32_t u8ToInt(uint8_t x) {
    return (int32_t)((uint32_t)x);
}

static STAINLESS_FUNC_PURE uint32_t widenU8(uint8_t x) {
    return (uint32_t)x;
}
