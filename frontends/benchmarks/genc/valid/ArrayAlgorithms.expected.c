/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "ArrayAlgorithms.h"

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

static STAINLESS_FUNC_PURE int32_t binarySearch(array_int32 a, int32_t key);
static void insertionSort(array_int32 a);
static 
void print(char c);
static void printArray(array_int32 a);
static 
void print_1(int32_t x);
static void println(void);
static void println_1(int32_t x);
static void reverse(array_int32 a);
static STAINLESS_FUNC_PURE int32_t sum(array_int32 a);


/* ----------------------- function definitions ----- */

static STAINLESS_FUNC_PURE int32_t binarySearch(array_int32 a, int32_t key) {
    int32_t lo = 0;
    int32_t hi = a.length;
    while (lo < hi) {
        int32_t mid = lo + (hi - lo) / 2;
        if (a.data[mid] < key) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    if (lo < a.length && a.data[lo] == key) {
        return lo;
    } else {
        return -1;
    }
}

static void insertionSort(array_int32 a) {
    int32_t n = a.length;
    int32_t i = 0;
    while (i < n) {
        int32_t key = a.data[i];
        int32_t i0 = i;
        int32_t j = i - 1;
        while (j >= 0 && a.data[j] > key) {
            a.data[j + 1] = a.data[j];
            j = j - 1;
        }
        a.data[j + 1] = key;
        i = i + 1;
    }
}

void main(void) {
    int32_t stainless_buffer_0[8] = { 42, -7, 19, 0, 3, 19, -100, 8 };
    array_int32 a = (array_int32) { .data = stainless_buffer_0, .length = 8 };
    printArray(a);
    insertionSort(a);
    printArray(a);
    println_1(binarySearch(a, 19));
    println_1(binarySearch(a, 5));
    println_1(binarySearch(a, -100));
    println_1(binarySearch(a, 42));
    println_1(sum(a));
    reverse(a);
    printArray(a);
}


void print(char c) {
  printf("%c", c);
}
      

static void printArray(array_int32 a) {
    int32_t i = 0;
    while (i < a.length) {
        if (i > 0) {
            print(' ');
        }
        print_1(a.data[i]);
        i = i + 1;
    }
    println();
}


void print_1(int32_t x) {
  printf("%"PRIi32, x);
}
     

static void println(void) {
    print('\n');
}

static void println_1(int32_t x) {
    print_1(x);
    println();
}

static void reverse(array_int32 a) {
    int32_t i = 0;
    int32_t j = a.length - 1;
    while (i < j) {
        int32_t tmp = a.data[i];
        a.data[i] = a.data[j];
        a.data[j] = tmp;
        i = i + 1;
        j = j - 1;
    }
}

static STAINLESS_FUNC_PURE int32_t sum(array_int32 a) {
    int32_t s = 0;
    int32_t i = 0;
    while (i < a.length) {
        s = s + a.data[i];
        i = i + 1;
    }
    return s;
}
