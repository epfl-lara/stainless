/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "TypeAliases.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>




/* -------------------------------------- enums ----- */

typedef enum {
  tag_Dot,
  tag_Empty
} enum_Shape;


/* ---------------------- data type definitions ----- */

typedef struct {
  int32_t* data;
  int32_t length;
} array_int32;

typedef struct {
  int32_t x;
  int32_t y;
} Point;

typedef struct {
  int32_t _1;
  int32_t _2;
} Tuple_int32_int32;

typedef struct {
  Point p;
} Dot;

typedef struct {
  int8_t extra;
} Empty;

typedef union {
  Dot Dot_v;
  Empty Empty_v;
} union_Shape;

typedef struct {
  enum_Shape tag;
  union_Shape value;
} Shape;



/* ---------------------- function declarations ----- */

static STAINLESS_FUNC_PURE int32_t first(array_int32 ps);
static STAINLESS_FUNC_PURE int32_t getX(Point p);
static 
void print(int32_t x);
static 
void print_1(char c);
static void println(int32_t x);
static void println_1(void);
static STAINLESS_FUNC_PURE Tuple_int32_int32 swapped(int32_t a, int32_t b);
static STAINLESS_FUNC_PURE int32_t xOrZero(Shape s);


/* ----------------------- function definitions ----- */

static STAINLESS_FUNC_PURE int32_t first(array_int32 ps) {
    return ps.data[0];
}

static STAINLESS_FUNC_PURE int32_t getX(Point p) {
    return p.x;
}

void main(void) {
    println(samePixel(10));
    Point p = (Point) { .x = 1, .y = 2 };
    println(getX(p));
    Tuple_int32_int32 q = swapped(3, 4);
    println(q._1);
    int32_t stainless_buffer_0[3] = { 5, 6, 7 };
    array_int32 ps = (array_int32) { .data = stainless_buffer_0, .length = 3 };
    println(first(ps));
    Shape s = (Shape) { .tag = tag_Dot, .value = (union_Shape) { .Dot_v = (Dot) { .p = (Point) { .x = 8, .y = 9 } } } };
    println(xOrZero(s));
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

STAINLESS_FUNC_PURE int32_t samePixel(int32_t x) {
    return x;
}

static STAINLESS_FUNC_PURE Tuple_int32_int32 swapped(int32_t a, int32_t b) {
    return (Tuple_int32_int32) { ._1 = b, ._2 = a };
}

static STAINLESS_FUNC_PURE int32_t xOrZero(Shape s) {
    if (s.tag == tag_Dot) {
        return s.value.Dot_v.p.x;
    } else {
        return 0;
    }
}
