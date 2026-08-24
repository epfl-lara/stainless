/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "ArgumentsEffects.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>







/* ---------------------- function declarations ----- */

static void f(int32_t x1, int32_t x2, int32_t x3);
static 
void print(int32_t x);
static 
void print_1(char c);
static void println(int32_t x);
static void println_1(void);


/* ----------------------- function definitions ----- */

static void f(int32_t x1, int32_t x2, int32_t x3) {
    print(x1);
    print(x2);
    println(x3);
}

void main(void) {
    int32_t x = 0;
    x = x + 1;
    int32_t norm_0 = x;
    int32_t norm_1 = x;
    x = x + 2;
    int32_t norm_2 = x;
    f(norm_0, norm_1, norm_2);
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
