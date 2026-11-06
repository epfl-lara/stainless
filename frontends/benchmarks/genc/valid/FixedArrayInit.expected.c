/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "FixedArrayInit.h"

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
static void printInit(int32_t n, int32_t k);
static 
void print_1(char c);
static void println(int32_t x);
static void println_1(void);


/* ----------------------- function definitions ----- */

void main(void) {
    printInit(3, 2);
}


void print(int32_t x) {
  printf("%"PRIi32, x);
}
     

static void printInit(int32_t n, int32_t k) {
    Grid g = (Grid) { .cells = { (Cell) { .values = { 4, 4 }, .count = 1 }, (Cell) { .values = { 4, 4 }, .count = 1 }, (Cell) { .values = { 4, 4 }, .count = 1 } }, .size = 9 };
    g.cells[1].values[0] = 5;
    println(g.cells[1].values[0]);
    println(g.cells[2].values[1]);
    println(g.cells[2].count);
    println(g.size);
    Grid h = (Grid) { .cells = { (Cell) { .values = { k, k }, .count = (k + 1) }, (Cell) { .values = { k, k }, .count = (k + 1) }, (Cell) { .values = { k, k }, .count = (k + 1) } }, .size = 0 };
    h.cells[0].values[1] = 6;
    println(h.cells[0].values[1]);
    println(h.cells[2].values[0]);
    println(h.cells[1].count);
    Cell c = (Cell) { .values = { 8, 8 }, .count = 0 };
    c.values[0] = 7;
    println(c.values[0]);
    println(c.values[1]);
    Cell d = (Cell) { .values = { 0 }, .count = 5 };
    println(d.values[1]);
    println(d.count);
    Grid e = (Grid) { .cells = { (Cell) { .values = { 1, 2 }, .count = 3 }, (Cell) { .values = { 4, 5 }, .count = 6 }, (Cell) { .values = { 7, 8 }, .count = 9 } }, .size = 0 };
    println(e.cells[1].values[1]);
    println(e.cells[2].count);
    Grid tmp = (Grid) { .cells = { (Cell) { .values = { 1, 1 }, .count = 1 }, (Cell) { .values = { 1, 1 }, .count = 1 }, (Cell) { .values = { 1, 1 }, .count = 1 } }, .size = 1 };
    Grid* norm_0 = &tmp;
    Board b = (Board) { .grid = (*norm_0), .turn = 4 };
    b.grid.cells[1].values[1] = 9;
    println(b.grid.cells[1].values[1]);
    println(b.grid.cells[1].values[0]);
    println(b.turn);
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
