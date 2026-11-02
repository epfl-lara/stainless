/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "GhostAssignments.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>





/* ---------------------- data type definitions ----- */

typedef struct {
  int32_t n;
  int32_t last;
} Counter;



/* ---------------------- function declarations ----- */

static void bump(Counter* c);
static STAINLESS_FUNC_PURE int32_t countdown(int32_t x);
static 
void print(int32_t x);
static 
void print_1(char c);
static void println(int32_t x);
static void println_1(void);
static STAINLESS_FUNC_PURE void reset(Counter* c);


/* ----------------------- function definitions ----- */

static void bump(Counter* c) {
    c->last = c->n;
    c->n = c->n + 1;
}

static STAINLESS_FUNC_PURE int32_t countdown(int32_t x) {
    int32_t i = x;
    while (i > 0) {
        i = i - 1;
    }
    return i;
}

void main(void) {
    Counter c = (Counter) { .n = 0, .last = 0 };
    bump(&c);
    bump(&c);
    reset(&c);
    println(c.n);
    println(c.last);
    println(countdown(5));
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

static STAINLESS_FUNC_PURE void reset(Counter* c) {
    
}
