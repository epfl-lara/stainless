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

typedef struct {
  Grid grid;
  int32_t turn;
} Board;



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
    Grid h;
    memset(&h, 0, sizeof(Grid));
    h.cells[0].values[1] = 6;
    println(h.cells[0].values[1]);
    println(h.cells[2].values[0]);
    Cell c;
    memset(&c, 0, sizeof(Cell));
    c.values[1] = 8;
    println(c.values[0]);
    println(c.values[1]);
    Board b;
    memset(&b, 0, sizeof(Board));
    b.grid.cells[2].values[0] = 7;
    println(b.grid.cells[2].values[0]);
    println(b.grid.cells[0].values[1]);
    println(b.turn);
    Grid tmp;
    memset(&tmp, 0, sizeof(Grid));
    Grid* norm_0 = &tmp;
    Board d = (Board) { .grid = (*norm_0), .turn = 4 };
    d.grid.cells[1].values[1] = 9;
    println(d.grid.cells[1].values[1]);
    println(d.grid.cells[1].values[0]);
    println(d.turn);
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
