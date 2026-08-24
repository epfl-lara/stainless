/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "Normalisation.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>





/* ---------------------- data type definitions ----- */

typedef struct {
  int32_t x;
  uint16_t y;
  int64_t z;
} A;

typedef struct {
  A a1;
  uint8_t i;
  uint32_t j;
  A a2;
} B;



/* ---------------------- function declarations ----- */

static 
void print(int32_t x);
static 
void print_1(char c);
static void println(int32_t x);
static void println_1(void);
static STAINLESS_FUNC_PURE int32_t sum(A thiss);


/* ----------------------- function definitions ----- */

void main(void) {
    A a = (A) { .x = 100, .y = 9, .z = 200 };
    int32_t x = sum(a) + sum(a);
    int32_t y = x + sum(a);
    println(y);
    B b = (B) { .a1 = a, .i = 76, .j = 14, .a2 = a };
    println(((sum(b.a1) + ((int32_t)((uint32_t)b.i))) + ((int32_t)b.j)) + sum(b.a2));
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

static STAINLESS_FUNC_PURE int32_t sum(A thiss) {
    return (thiss.x + ((int32_t)((uint32_t)thiss.y))) + ((int32_t)thiss.z);
}
