/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "FixedArray.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>







/* ---------------------- function declarations ----- */

static 
void print(int32_t x);
static 
void print_1(char c);
static void println(int32_t x);
static void println_1(void);


/* ----------------------- function definitions ----- */

int32_t f(W* w) {
    assert((0 <= w->a[0] && w->a[0] <= 1000));
    assert((0 <= w->a[1] && w->a[1] <= 1000));
    assert((0 <= w->a[2] && w->a[2] <= 1000));
    assert((0 <= w->a[3] && w->a[3] <= 1000));
    assert((0 <= w->a[4] && w->a[4] <= 1000));
    w->a[0] = 155;
    return (((((w->a[0] + w->a[1]) + w->a[2]) + w->a[3]) + w->a[4]) + w->x) + w->y;
}

void g(array_int32 a) {
    assert((a.length > 0));
    assert((0 <= a.data[0] && a.data[0] <= 1000));
    a.data[0] = a.data[0] + 1;
}

void main(void) {
    W w = (W) { .x = 30, .a = { 10, 20, 30, 20, 42 }, .y = 100 };
    w.a[0] = w.a[0] + 1;
    W w2 = (W) { .x = 30, .a = { 10, 20, 30, 20, 42 }, .y = 100 };
    g((array_int32) { .data = w.a, .length = 5 });
    array_int32 a2 = (array_int32) { .data = w.a, .length = 5 };
    g(a2);
    int32_t z = f(&w);
    println(z);
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
