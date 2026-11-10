/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "ExhaustiveMatch.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>




/* -------------------------------------- enums ----- */

typedef enum {
  tag_Blue,
  tag_Green,
  tag_Red
} enum_Color;

typedef enum {
  tag_Rect,
  tag_Square
} enum_Shape;


/* ---------------------- data type definitions ----- */

typedef struct {
  int32_t width;
  int32_t height;
} Rect;

typedef struct {
  int32_t side;
} Square;

typedef union {
  Rect Rect_v;
  Square Square_v;
} union_Shape;

typedef struct {
  enum_Shape tag;
  union_Shape value;
} Shape;



/* ---------------------- function declarations ----- */

static STAINLESS_FUNC_PURE int32_t code(enum_Color c);
static STAINLESS_FUNC_PURE int32_t longestSide(Shape s);
static 
void print(int32_t x);
static 
void print_1(char c);
static void println(int32_t x);
static void println_1(void);
static STAINLESS_FUNC_PURE int32_t sign(int32_t n);
static STAINLESS_FUNC_PURE int32_t width(Shape s);


/* ----------------------- function definitions ----- */

static STAINLESS_FUNC_PURE int32_t code(enum_Color c) {
    if (c == tag_Red) {
        return 0;
    } else if (c == tag_Green) {
        return 1;
    } else {
        return 2;
    }
}

static STAINLESS_FUNC_PURE int32_t longestSide(Shape s) {
    int32_t side;
    if (s.tag == tag_Square) {
        side = s.value.Square_v.side;
    } else if (s.value.Rect_v.width >= s.value.Rect_v.height) {
        side = s.value.Rect_v.width;
    } else {
        side = s.value.Rect_v.height;
    }
    if (side < 0) {
        return 0;
    } else {
        return side;
    }
}

void main(void) {
    println(code(tag_Green));
    println(code(tag_Blue));
    println(width((Shape) { .tag = tag_Square, .value = (union_Shape) { .Square_v = (Square) { .side = 3 } } }));
    println(width((Shape) { .tag = tag_Rect, .value = (union_Shape) { .Rect_v = (Rect) { .width = 4, .height = 5 } } }));
    println(sign(-7));
    println(sign(0));
    println(sign(7));
    println(longestSide((Shape) { .tag = tag_Rect, .value = (union_Shape) { .Rect_v = (Rect) { .width = 4, .height = 5 } } }));
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

static STAINLESS_FUNC_PURE int32_t sign(int32_t n) {
    if (n < 0) {
        return -1;
    } else if (n == 0) {
        return 0;
    } else {
        return 1;
    }
}

static STAINLESS_FUNC_PURE int32_t width(Shape s) {
    if (s.tag == tag_Square) {
        return s.value.Square_v.side;
    } else {
        return s.value.Rect_v.width;
    }
}
