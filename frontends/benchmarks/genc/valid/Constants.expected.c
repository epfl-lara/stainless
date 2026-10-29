/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "Constants.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>


/* ------------------------------------- macros ----- */

#define BufferSize 16



/* -------------------------------------- enums ----- */

typedef enum {
  tag_Green,
  tag_Red
} enum_Color;

typedef enum {
  tag_Circle,
  tag_Square
} enum_Shape;


/* ---------------------- data type definitions ----- */

typedef struct {
  Point topLeft;
  Point bottomRight;
} Rect;

typedef struct {
  int32_t radius;
} Circle;

typedef struct {
  int32_t side;
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

static STAINLESS_FUNC_PURE int32_t area(Shape s);
static STAINLESS_FUNC_PURE int32_t incImpl(int32_t x);
static STAINLESS_FUNC_PURE bool isGreen(enum_Color c);
static 
void print(int32_t x);
static 
void printU32(uint32_t x);
static 
void print_1(char c);
static void println(int32_t x);
static void printlnU32(uint32_t x);
static void println_1(void);
static void println_2(char c);
static STAINLESS_FUNC_PURE int32_t width(Rect r);


/* --------------------------- global variables ----- */

static const int32_t MaxF = 65535;
static const int32_t ErrMalformed = -2;
static const int32_t MaxPlusOne = 65535 + 1;
static const int32_t Twice = (65535 + 1) * 2;
static const bool Flag = true;
static const int8_t Small = -8;
static const int16_t Medium = 1234;
static const int64_t Big = 123456789012;
static const char Letter = 'z';
static const uint32_t Unsigned = 4000000000;
static const Point Origin = { .x = 0, .y = 0 };
static const Rect UnitSquare = { .topLeft = { .x = 0, .y = 0 }, .bottomRight = { .x = 1, .y = 1 } };
static const Shape DefaultShape = { .tag = tag_Circle, .value = { .Circle_v = { .radius = 5 } } };
static const enum_Color DefaultColor = tag_Green;
static int32_t (* const Inc)(int32_t) = incImpl;
static const int32_t Lazy = 7;


/* ----------------------- function definitions ----- */

static STAINLESS_FUNC_PURE int32_t area(Shape s) {
    if (s.tag == tag_Circle) {
        return (3 * s.value.Circle_v.radius) * s.value.Circle_v.radius;
    } else if (s.tag == tag_Square) {
        return s.value.Square_v.side * s.value.Square_v.side;
    }
}

STAINLESS_FUNC_PURE int32_t check(int32_t f) {
    if (0 < f && f <= MaxF) {
        return f;
    } else {
        return ErrMalformed;
    }
}

static STAINLESS_FUNC_PURE int32_t incImpl(int32_t x) {
    return x + 1;
}

static STAINLESS_FUNC_PURE bool isGreen(enum_Color c) {
    if (c == tag_Green) {
        return true;
    } else if (c == tag_Red) {
        return false;
    }
}

void main(void) {
    println(check(100));
    println(check(70000));
    println(MaxPlusOne);
    println(Twice);
    int32_t norm_0;
    if (Flag) {
        norm_0 = 1;
    } else {
        norm_0 = 0;
    }
    int32_t norm_1 = norm_0;
    println(norm_1);
    println((int32_t)Small);
    println((int32_t)Medium);
    println((int32_t)(Big % ((int64_t)1000)));
    println_2(Letter);
    printlnU32(Unsigned);
    println(Origin.x + UnitSquare.bottomRight.y);
    println(area(DefaultShape));
    int32_t norm_2;
    if (isGreen(DefaultColor)) {
        norm_2 = 1;
    } else {
        norm_2 = 0;
    }
    int32_t norm_3 = norm_2;
    println(norm_3);
    println(width(UnitSquare));
    println(BufferSize);
    println(Inc(41));
    println(Op(5));
    println(Lazy);
}


void print(int32_t x) {
  printf("%"PRIi32, x);
}
     


void printU32(uint32_t x) {
  printf("%"PRIu32, x);
}
     


void print_1(char c) {
  printf("%c", c);
}
      

static void println(int32_t x) {
    print(x);
    println_1();
}

static void printlnU32(uint32_t x) {
    printU32(x);
    println_1();
}

static void println_1(void) {
    print_1('\n');
}

static void println_2(char c) {
    print_1(c);
    println_1();
}

static STAINLESS_FUNC_PURE int32_t width(Rect r) {
    return r.bottomRight.x - r.topLeft.x;
}
