/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "Global.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>






/* --------------------------- global variables ----- */

int32_t data[100] = { 0 };
bool stable = true;
int32_t x = 5;
int32_t y = 7;


/* ---------------------- function declarations ----- */

static void move(void);
static 
void print(int32_t x);
static 
void print_1(char c);
static void println(int32_t x_1);
static void println_1(void);


/* ----------------------- function definitions ----- */

void main(void) {
    print(x);
    print(y);
    move();
    print(data[6]);
    print(data[7]);
    print(x);
    println(y);
}

static void move(void) {
    while (true) {
        label_0: ;
            stable = false;
            x = x + 1;
            y = y - 1;
            data[y] = 1;
            stable = true;
            if (y > 0) {
                goto label_0;
            }
            return;;
    }
}


void print(int32_t x) {
  printf("%"PRIi32, x);
}
     


void print_1(char c) {
  printf("%c", c);
}
      

static void println(int32_t x_1) {
    print(x_1);
    println_1();
}

static void println_1(void) {
    print_1('\n');
}
