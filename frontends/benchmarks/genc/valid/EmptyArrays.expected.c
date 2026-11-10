/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "EmptyArrays.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>





/* ---------------------- data type definitions ----- */

typedef struct {
  int32_t* data;
  int32_t length;
} array_int32;

typedef struct {
  int8_t* data;
  int32_t length;
} array_int8;

typedef struct {
  int32_t x;
  int32_t y;
} P;

typedef struct {
  P* data;
  int32_t length;
} array_P;

typedef struct {
  array_int32 data;
  int32_t size;
} Buffer;

typedef struct {
  array_int32* data;
  int32_t length;
} array_array_int32;



/* ---------------------- function declarations ----- */

static STAINLESS_FUNC_PURE int32_t count(array_int32 a, int32_t x);
static STAINLESS_FUNC_PURE int32_t countOfFill(int32_t n);
static STAINLESS_FUNC_PURE int32_t len(array_int32 a);
static 
void print(int32_t x);
static 
void print_1(char c);
static void println(int32_t x);
static void println_1(void);


/* ----------------------- function definitions ----- */

static STAINLESS_FUNC_PURE int32_t count(array_int32 a, int32_t x) {
    int32_t c = 0;
    int32_t i = 0;
    while (i < a.length) {
        if (a.data[i] == x) {
            c = c + 1;
        }
        i = i + 1;
    }
    return c;
}

static STAINLESS_FUNC_PURE int32_t countOfFill(int32_t n) {
    int32_t stainless_length_0 = n;
    int32_t stainless_buffer_0[stainless_length_0 > 0 ? stainless_length_0 : 1];
    int32_t stainless_i_0;
    for (stainless_i_0 = 0; stainless_i_0 < stainless_length_0; ++stainless_i_0) {
        stainless_buffer_0[stainless_i_0] = 7;
    };
    array_int32 norm_0 = (array_int32) { .data = stainless_buffer_0, .length = stainless_length_0 };
    array_int32 norm_1 = norm_0;
    return count(norm_1, 7);
}

static STAINLESS_FUNC_PURE int32_t len(array_int32 a) {
    return a.length;
}

void main(void) {
    array_int32 norm_2 = (array_int32) { .data = NULL, .length = 0 };
    array_int32 norm_3 = norm_2;
    int32_t norm_4 = len(norm_3);
    println(norm_4);
    array_int32 filled = (array_int32) { .data = NULL, .length = 0 };
    println(count(filled, 42));
    array_int8 bytes = (array_int8) { .data = NULL, .length = 0 };
    println(bytes.length);
    array_P ps = (array_P) { .data = NULL, .length = 0 };
    println(ps.length);
    array_int32 norm_5 = (array_int32) { .data = NULL, .length = 0 };
    array_int32 norm_6 = norm_5;
    Buffer b = (Buffer) { .data = norm_6, .size = 0 };
    println(b.data.length + b.size);
    array_array_int32 nested = (array_array_int32) { .data = NULL, .length = 0 };
    println(nested.length);
    println(countOfFill(0));
    println(countOfFill(3));
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
