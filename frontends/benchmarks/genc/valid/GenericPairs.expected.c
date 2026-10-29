/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "GenericPairs.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>




/* -------------------------------------- enums ----- */

typedef enum {
  tag_None_int32,
  tag_Some_int32
} enum_Option_int32;


/* ---------------------- data type definitions ----- */

typedef struct {
  int32_t _1;
  int32_t _2;
} Tuple_int32_int32;

typedef struct {
  int8_t extra;
} None_int32;

typedef struct {
  int32_t v;
} Some_int32;

typedef union {
  None_int32 None_int32_v;
  Some_int32 Some_int32_v;
} union_Option_int32;

typedef struct {
  enum_Option_int32 tag;
  union_Option_int32 value;
} Option_int32;

typedef struct {
  int32_t* data;
  int32_t length;
} array_int32;

typedef struct {
  bool first;
  int32_t second;
} Pair_bool_int32;

typedef struct {
  int32_t first;
  bool second;
} Pair_int32_bool;

typedef struct {
  int32_t first;
  int64_t second;
} Pair_int32_int64;

typedef struct {
  Pair_int32_int64 first;
  char second;
} Pair_Pair_int32_int64_char;

typedef struct {
  int32_t first;
  int32_t second;
} Pair_int32_int32;



/* ---------------------- function declarations ----- */

static STAINLESS_FUNC_PURE int32_t applyTwice(int32_t (*f)(int32_t), int32_t x);
static STAINLESS_FUNC_PURE int32_t boolToInt(bool b);
static STAINLESS_FUNC_PURE Tuple_int32_int32 divMod(int32_t a, int32_t b);
static STAINLESS_FUNC_PURE int32_t double_1(int32_t x);
static STAINLESS_FUNC_PURE bool equals_Pair_bool_int32(Pair_bool_int32 lhs, Pair_bool_int32 rhs);
static STAINLESS_FUNC_PURE bool equals_Pair_int32_bool(Pair_int32_bool lhs, Pair_int32_bool rhs);
static STAINLESS_FUNC_PURE Option_int32 findFirst(array_int32 a, bool (*p)(int32_t));
static STAINLESS_FUNC_PURE bool first_bool_int32(Pair_bool_int32 p);
static STAINLESS_FUNC_PURE int32_t inc(int32_t x);
static STAINLESS_FUNC_PURE bool isEmpty_int32(Option_int32 thiss);
static STAINLESS_FUNC_PURE bool isEven(int32_t x);
static STAINLESS_FUNC_PURE bool isNegative(int32_t x);
static STAINLESS_FUNC_PURE Tuple_int32_int32 minMax(array_int32 a);
static STAINLESS_FUNC_PURE int32_t optionToInt(Option_int32 o);
static 
void print(int32_t x);
static 
void print_1(char c);
static void println(int32_t x);
static void println_1(void);
static void println_2(char c);
static STAINLESS_FUNC_PURE Pair_int32_bool swap_bool_int32(Pair_bool_int32 p);
static STAINLESS_FUNC_PURE Pair_bool_int32 swap_int32_bool(Pair_int32_bool p);
static STAINLESS_FUNC_PURE Tuple_int32_int32 toTuple_int32_int32(Pair_int32_int32 p);


/* ----------------------- function definitions ----- */

static STAINLESS_FUNC_PURE int32_t applyTwice(int32_t (*f)(int32_t), int32_t x) {
    return f(f(x));
}

static STAINLESS_FUNC_PURE int32_t boolToInt(bool b) {
    if (b) {
        return 1;
    } else {
        return 0;
    }
}

static STAINLESS_FUNC_PURE Tuple_int32_int32 divMod(int32_t a, int32_t b) {
    return (Tuple_int32_int32) { ._1 = (a / b), ._2 = (a % b) };
}

static STAINLESS_FUNC_PURE int32_t double_1(int32_t x) {
    return x * 2;
}

static STAINLESS_FUNC_PURE bool equals_Pair_bool_int32(Pair_bool_int32 lhs, Pair_bool_int32 rhs) {
    return lhs.first == rhs.first && lhs.second == rhs.second;
}

static STAINLESS_FUNC_PURE bool equals_Pair_int32_bool(Pair_int32_bool lhs, Pair_int32_bool rhs) {
    return lhs.first == rhs.first && lhs.second == rhs.second;
}

static STAINLESS_FUNC_PURE Option_int32 findFirst(array_int32 a, bool (*p)(int32_t)) {
    int32_t i = 0;
    Option_int32 res = (Option_int32) { .tag = tag_None_int32, .value = (union_Option_int32) { .None_int32_v = (None_int32) { .extra = 0 } } };
    while (isEmpty_int32(res) && i < a.length) {
        if (p(a.data[i])) {
            res = (Option_int32) { .tag = tag_Some_int32, .value = (union_Option_int32) { .Some_int32_v = (Some_int32) { .v = i } } };
        }
        i = i + 1;
    }
    return res;
}

static STAINLESS_FUNC_PURE bool first_bool_int32(Pair_bool_int32 p) {
    return p.first;
}

static STAINLESS_FUNC_PURE int32_t inc(int32_t x) {
    return x + 1;
}

static STAINLESS_FUNC_PURE bool isEmpty_int32(Option_int32 thiss) {
    if (thiss.tag == tag_Some_int32) {
        return false;
    } else if (thiss.tag == tag_None_int32) {
        return true;
    }
}

static STAINLESS_FUNC_PURE bool isEven(int32_t x) {
    return x % 2 == 0;
}

static STAINLESS_FUNC_PURE bool isNegative(int32_t x) {
    return x < 0;
}

void main(void) {
    Pair_int32_bool p = (Pair_int32_bool) { .first = 7, .second = true };
    Pair_bool_int32 q = swap_int32_bool(p);
    println(q.second);
    println(boolToInt(first_bool_int32(q)));
    println(boolToInt(equals_Pair_int32_bool(swap_bool_int32(q), p)));
    println(boolToInt(equals_Pair_bool_int32(q, (Pair_bool_int32) { .first = false, .second = 7 })));
    Pair_Pair_int32_int64_char nested = (Pair_Pair_int32_int64_char) { .first = (Pair_int32_int64) { .first = 3, .second = 4 }, .second = 'x' };
    println(nested.first.first + ((int32_t)nested.first.second));
    println_2(nested.second);
    Tuple_int32_int32 tmp = divMod(17, 5);
    Tuple_int32_int32 _2_ = tmp;
    int32_t q1 = _2_._1;
    int32_t r1 = _2_._2;
    println(q1);
    println(r1);
    Tuple_int32_int32 tmp_1 = divMod(-17, 5);
    Tuple_int32_int32 _4_ = tmp_1;
    int32_t q2 = _4_._1;
    int32_t r2 = _4_._2;
    Tuple_int32_int32 t = toTuple_int32_int32((Pair_int32_int32) { .first = q2, .second = r2 });
    println(t._1 * 10 + t._2);
    int32_t stainless_buffer_0[6] = { 5, -3, 9, 0, 12, 7 };
    array_int32 a = (array_int32) { .data = stainless_buffer_0, .length = 6 };
    Tuple_int32_int32 tmp_2 = minMax(a);
    Tuple_int32_int32 _6_ = tmp_2;
    int32_t lo = _6_._1;
    int32_t hi = _6_._2;
    println(lo);
    println(hi);
    println(applyTwice(double_1, 7));
    println(applyTwice(inc, 7));
    println(optionToInt(findFirst(a, isEven)));
    println(optionToInt(findFirst(a, isNegative)));
    int32_t stainless_buffer_1[3] = { 1, 3, 5 };
    array_int32 norm_0 = (array_int32) { .data = stainless_buffer_1, .length = 3 };
    array_int32 norm_1 = norm_0;
    bool (*norm_2)(int32_t) = isEven;
    Option_int32 norm_3 = findFirst(norm_1, norm_2);
    int32_t norm_4 = optionToInt(norm_3);
    println(norm_4);
}

static STAINLESS_FUNC_PURE Tuple_int32_int32 minMax(array_int32 a) {
    int32_t lo = a.data[0];
    int32_t hi = a.data[0];
    int32_t i = 1;
    while (i < a.length) {
        if (a.data[i] < lo) {
            lo = a.data[i];
        }
        if (a.data[i] > hi) {
            hi = a.data[i];
        }
        i = i + 1;
    }
    return (Tuple_int32_int32) { ._1 = lo, ._2 = hi };
}

static STAINLESS_FUNC_PURE int32_t optionToInt(Option_int32 o) {
    if (o.tag == tag_Some_int32) {
        return o.value.Some_int32_v.v;
    } else if (o.tag == tag_None_int32) {
        return -1;
    }
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

static void println_2(char c) {
    print_1(c);
    println_1();
}

static STAINLESS_FUNC_PURE Pair_int32_bool swap_bool_int32(Pair_bool_int32 p) {
    return (Pair_int32_bool) { .first = p.second, .second = p.first };
}

static STAINLESS_FUNC_PURE Pair_bool_int32 swap_int32_bool(Pair_int32_bool p) {
    return (Pair_bool_int32) { .first = p.second, .second = p.first };
}

static STAINLESS_FUNC_PURE Tuple_int32_int32 toTuple_int32_int32(Pair_int32_int32 p) {
    return (Tuple_int32_int32) { ._1 = p.first, ._2 = p.second };
}
