/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "FixedArraySingleFieldInArray.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>





/* ---------------------- data type definitions ----- */

typedef struct {
  int8_t array[4];
} Buffer;

typedef struct {
  Buffer* data;
  int32_t length;
} array_Buffer;

typedef struct {
  array_Buffer buffers;
  int32_t nextIndex;
} Dictionary;




/* ----------------------- function definitions ----- */

STAINLESS_FUNC_PURE int32_t main(void) {
    Buffer stainless_buffer_0[6] = { (Buffer) { .array = { 0 } }, (Buffer) { .array = { 0 } }, (Buffer) { .array = { 0 } }, (Buffer) { .array = { 0 } }, (Buffer) { .array = { 0 } }, (Buffer) { .array = { 0 } } };
    array_Buffer norm_0 = (array_Buffer) { .data = stainless_buffer_0, .length = 6 };
    array_Buffer norm_1 = norm_0;
    Dictionary dictionary = (Dictionary) { .buffers = norm_1, .nextIndex = 0 };
    return 0;
}
