/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "Return.h"

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



/* ---------------------- function declarations ----- */

static STAINLESS_FUNC_PURE int32_t findIndex_int32(array_int32 a, int32_t t);
static 
void print(char* s);
static 
void print_1(char c);
static void println(char* s);
static void println_1(void);
static STAINLESS_FUNC_PURE int32_t return10(void);
static void verify(bool b);


/* ----------------------- function definitions ----- */

static STAINLESS_FUNC_PURE int32_t findIndex_int32(array_int32 a, int32_t t) {
    int32_t i = 0;
    while (i < a.length) {
        if (a.data[i] == t) {
            return i;
        }
        i = i + 1;
    }
    return 0;
}

void main(void) {
    verify(return10() == 10);
    int32_t stainless_buffer_0[4] = { 0, 100, 200, 250 };
    array_int32 norm_0 = (array_int32) { .data = stainless_buffer_0, .length = 4 };
    array_int32 norm_1 = norm_0;
    int32_t norm_2 = findIndex_int32(norm_1, 0);
    bool norm_3 = norm_2 == 0;
    verify(norm_3);
    int32_t stainless_buffer_1[4] = { 0, 100, 200, 250 };
    array_int32 norm_4 = (array_int32) { .data = stainless_buffer_1, .length = 4 };
    array_int32 norm_5 = norm_4;
    int32_t norm_6 = findIndex_int32(norm_5, 100);
    bool norm_7 = norm_6 == 1;
    verify(norm_7);
    int32_t stainless_buffer_2[4] = { 0, 100, 200, 250 };
    array_int32 norm_8 = (array_int32) { .data = stainless_buffer_2, .length = 4 };
    array_int32 norm_9 = norm_8;
    int32_t norm_10 = findIndex_int32(norm_9, 200);
    bool norm_11 = norm_10 == 2;
    verify(norm_11);
    int32_t stainless_buffer_3[4] = { 0, 100, 200, 250 };
    array_int32 norm_12 = (array_int32) { .data = stainless_buffer_3, .length = 4 };
    array_int32 norm_13 = norm_12;
    int32_t norm_14 = findIndex_int32(norm_13, 250);
    bool norm_15 = norm_14 == 3;
    verify(norm_15);
}


void print(char* s) {
  printf("%s", s);
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

static STAINLESS_FUNC_PURE int32_t return10(void) {
    return 10;
}

static void verify(bool b) {
    if (b) {
        println("OK");
    } else {
        println("ERROR");
    }
}
