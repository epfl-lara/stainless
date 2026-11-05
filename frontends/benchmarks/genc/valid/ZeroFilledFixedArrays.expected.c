/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "ZeroFilledFixedArrays.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>





/* ---------------------- data type definitions ----- */

typedef struct {
  int32_t values[2];
  int32_t count;
} Cell;

typedef struct {
  Cell cells[3];
  int32_t size;
} Grid;



/* ---------------------- function declarations ----- */

static 
void print(int32_t x);
static void printZeroFilled(int32_t n);
static 
void print_1(char c);
static void println(int32_t x);
static void println_1(void);


/* ----------------------- function definitions ----- */

void main(void) {
    printZeroFilled(3);
}


void print(int32_t x) {
  printf("%"PRIi32, x);
}
     

static void printZeroFilled(int32_t n) {
    Grid g;
    memset(&g, 0, sizeof(Grid));
    g.cells[1].values[0] = 5;
    println(g.cells[0].values[0]);
    println(g.cells[1].values[0]);
    println(g.cells[2].values[1]);
    println(g.cells[2].count);
    println(g.size);
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
