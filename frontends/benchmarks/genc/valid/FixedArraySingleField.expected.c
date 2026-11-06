/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "FixedArraySingleField.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>





/* ---------------------- data type definitions ----- */

typedef struct {
  Buffer payload;
  int32_t id;
} Packet;



/* ---------------------- function declarations ----- */

static 
void print(int32_t x);
static void printBuffers(void);
static 
void print_1(char c);
static void println(int32_t x);
static void println_1(void);
static void set(Buffer* b, int32_t i, int32_t v);


/* ----------------------- function definitions ----- */

STAINLESS_FUNC_PURE int32_t get(Buffer* b, int32_t i) {
    assert((0 <= i && i < 4));
    return b->data[i];
}

void main(void) {
    printBuffers();
}


void print(int32_t x) {
  printf("%"PRIi32, x);
}
     

static void printBuffers(void) {
    Buffer b = (Buffer) { .data = { 1, 2, 3, 4 } };
    set(&b, 2, 9);
    println(get(&b, 2));
    println(get(&b, 3));
    Buffer z;
    memset(&z, 0, sizeof(Buffer));
    z.data[1] = 5;
    println(get(&z, 0));
    println(get(&z, 1));
    Buffer tmp = (Buffer) { .data = { 7, 7, 7, 7 } };
    Buffer* norm_0 = &tmp;
    Packet p = (Packet) { .payload = (*norm_0), .id = 6 };
    p.payload.data[1] = 3;
    println(p.payload.data[1]);
    println(get(&p.payload, 0));
    println(p.id);
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

static void set(Buffer* b, int32_t i, int32_t v) {
    b->data[i] = v;
}
