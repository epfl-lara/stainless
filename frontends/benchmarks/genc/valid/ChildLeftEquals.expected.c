/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "ChildLeftEquals.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>




/* -------------------------------------- enums ----- */

typedef enum {
  tag_Circle,
  tag_Square
} enum_Shape;


/* ---------------------- data type definitions ----- */

typedef struct {
  int32_t r;
} Circle;

typedef struct {
  int32_t s;
} Square;

typedef union {
  Circle Circle_v;
  Square Square_v;
} union_Shape;

typedef struct {
  enum_Shape tag;
  union_Shape value;
} Shape;



/* ---------------------- function declarations ----- */

static STAINLESS_FUNC_PURE bool equals_Shape(Shape lhs, Shape rhs);
static STAINLESS_FUNC_PURE bool isNotUnitSquare(Shape s);
static STAINLESS_FUNC_PURE bool isUnitCircle(Shape s);
static 
void print(char* s);
static void printAnswer(bool b);
static 
void print_1(char c);
static void println(char* s);
static void println_1(void);


/* ----------------------- function definitions ----- */

static STAINLESS_FUNC_PURE bool equals_Shape(Shape lhs, Shape rhs) {
    return (lhs.tag == tag_Circle && rhs.tag == tag_Circle) && lhs.value.Circle_v.r == rhs.value.Circle_v.r || (lhs.tag == tag_Square && rhs.tag == tag_Square) && lhs.value.Square_v.s == rhs.value.Square_v.s;
}

static STAINLESS_FUNC_PURE bool isNotUnitSquare(Shape s) {
    return !equals_Shape((Shape) { .tag = tag_Square, .value = (union_Shape) { .Square_v = (Square) { .s = 1 } } }, s);
}

static STAINLESS_FUNC_PURE bool isUnitCircle(Shape s) {
    return equals_Shape((Shape) { .tag = tag_Circle, .value = (union_Shape) { .Circle_v = (Circle) { .r = 1 } } }, s);
}

void main(void) {
    printAnswer(isUnitCircle((Shape) { .tag = tag_Square, .value = (union_Shape) { .Square_v = (Square) { .s = 1 } } }));
    printAnswer(isUnitCircle((Shape) { .tag = tag_Circle, .value = (union_Shape) { .Circle_v = (Circle) { .r = 1 } } }));
    printAnswer(isUnitCircle((Shape) { .tag = tag_Circle, .value = (union_Shape) { .Circle_v = (Circle) { .r = 2 } } }));
    printAnswer(isNotUnitSquare((Shape) { .tag = tag_Square, .value = (union_Shape) { .Square_v = (Square) { .s = 1 } } }));
    printAnswer(isNotUnitSquare((Shape) { .tag = tag_Circle, .value = (union_Shape) { .Circle_v = (Circle) { .r = 1 } } }));
    printAnswer(equals_Shape((Shape) { .tag = tag_Circle, .value = (union_Shape) { .Circle_v = (Circle) { .r = 1 } } }, (Shape) { .tag = tag_Square, .value = (union_Shape) { .Square_v = (Square) { .s = 1 } } }));
    printAnswer(equals_Shape((Shape) { .tag = tag_Circle, .value = (union_Shape) { .Circle_v = (Circle) { .r = 1 } } }, (Shape) { .tag = tag_Circle, .value = (union_Shape) { .Circle_v = (Circle) { .r = 1 } } }));
    printAnswer(!equals_Shape((Shape) { .tag = tag_Square, .value = (union_Shape) { .Square_v = (Square) { .s = 2 } } }, (Shape) { .tag = tag_Circle, .value = (union_Shape) { .Circle_v = (Circle) { .r = 2 } } }));
}


void print(char* s) {
  printf("%s", s);
}
      

static void printAnswer(bool b) {
    if (b) {
        println("yes");
    } else {
        println("no");
    }
}


void print_1(char c) {
  printf("%c", c);
}
      

static void println(char* s) {
    print(s);
    println_1();
}

static void println_1(void) {
    print_1('\n');
}
