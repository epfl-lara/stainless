/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "FieldScrutinee.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>




/* -------------------------------------- enums ----- */

typedef enum {
  tag_Move,
  tag_Stop
} enum_Command;

typedef enum {
  tag_North,
  tag_South
} enum_Direction;

typedef enum {
  tag_Circle,
  tag_Square
} enum_Shape;


/* ---------------------- data type definitions ----- */

typedef struct {
  int32_t counter;
  int32_t id;
} Box;

typedef struct {
  int32_t steps;
} Move;

typedef struct {
  int8_t extra;
} Stop;

typedef union {
  Move Move_v;
  Stop Stop_v;
} union_Command;

typedef struct {
  enum_Command tag;
  union_Command value;
} Command;

typedef struct {
  int32_t y;
  enum_Direction dir;
  Command cmd;
} Robot;

typedef struct {
  Robot* data;
  int32_t length;
} array_Robot;

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

typedef struct {
  Shape shape;
  int32_t id;
} Holder;

typedef struct {
  Robot robot;
  int32_t time;
} World;

typedef struct {
  int32_t _1;
  enum_Direction _2;
} Tuple_int32_Direction;



/* ---------------------- function declarations ----- */

static void bump(Box* b);
static STAINLESS_FUNC_PURE int32_t dirCode(enum_Direction d);
static STAINLESS_FUNC_PURE int32_t elementDir(array_Robot rs, int32_t i);
static int32_t flip(Robot* r);
static void grow(Holder* h);
static STAINLESS_FUNC_PURE int32_t madeDir(void);
static STAINLESS_FUNC_PURE Robot makeRobot(void);
static 
void print(int32_t x);
static 
void print_1(char c);
static void println(int32_t x);
static void println_1(void);
static STAINLESS_FUNC_PURE int32_t size(Holder* h);
static void step(Robot* r, int32_t n);
static STAINLESS_FUNC_PURE int32_t steps(Robot* r);
static STAINLESS_FUNC_PURE int32_t tupleDir(Tuple_int32_Direction t);
static STAINLESS_FUNC_PURE int32_t worldDir(World* w);


/* ----------------------- function definitions ----- */

static void bump(Box* b) {
    int32_t* tmp = &b->counter;
    *tmp = (*tmp) + 1;
}

static STAINLESS_FUNC_PURE int32_t dirCode(enum_Direction d) {
    if (d == tag_North) {
        return 0;
    } else if (d == tag_South) {
        return 1;
    }
}

static STAINLESS_FUNC_PURE int32_t elementDir(array_Robot rs, int32_t i) {
    enum_Direction tmp = rs.data[i].dir;
    if (tmp == tag_North) {
        return 7;
    } else if (tmp == tag_South) {
        return 8;
    }
}

static int32_t flip(Robot* r) {
    enum_Direction tmp = r->dir;
    if (tmp == tag_North) {
        r->dir = tag_South;
        return dirCode(tmp);
    } else if (tmp == tag_South) {
        r->dir = tag_North;
        return dirCode(tmp);
    }
}

static void grow(Holder* h) {
    Shape* tmp = &h->shape;
    if (tmp->tag == tag_Circle) {
        tmp->value.Circle_v.radius = tmp->value.Circle_v.radius + 1;
    } else if (tmp->tag == tag_Square) {
        tmp->value.Square_v.side = tmp->value.Square_v.side + 2;
    }
}

static STAINLESS_FUNC_PURE int32_t madeDir(void) {
    Robot norm_0 = makeRobot();
    enum_Direction tmp = norm_0.dir;
    if (tmp == tag_North) {
        return 100;
    } else if (tmp == tag_South) {
        return 200;
    }
}

void main(void) {
    Robot r = (Robot) { .y = 0, .dir = tag_North, .cmd = (Command) { .tag = tag_Move, .value = (union_Command) { .Move_v = (Move) { .steps = 5 } } } };
    step(&r, 3);
    println(r.y);
    println(steps(&r));
    r.cmd = (Command) { .tag = tag_Move, .value = (union_Command) { .Move_v = (Move) { .steps = 0 } } };
    println(steps(&r));
    r.cmd = (Command) { .tag = tag_Stop, .value = (union_Command) { .Stop_v = (Stop) { .extra = 0 } } };
    println(steps(&r));
    println(flip(&r));
    println(dirCode(r.dir));
    step(&r, 1);
    println(r.y);
    println(flip(&r));
    println(dirCode(r.dir));
    int32_t tmp = 41;
    int32_t* norm_1 = &tmp;
    Box b = (Box) { .counter = (*norm_1), .id = 0 };
    bump(&b);
    println(b.counter);
    Shape tmp_1 = (Shape) { .tag = tag_Circle, .value = (union_Shape) { .Circle_v = (Circle) { .radius = 3 } } };
    Shape* norm_2 = &tmp_1;
    Holder h = (Holder) { .shape = (*norm_2), .id = 0 };
    grow(&h);
    println(size(&h));
    h.shape = (Shape) { .tag = tag_Square, .value = (union_Shape) { .Square_v = (Square) { .side = 5 } } };
    grow(&h);
    println(size(&h));
    Robot tmp_3 = (Robot) { .y = 0, .dir = tag_South, .cmd = (Command) { .tag = tag_Stop, .value = (union_Command) { .Stop_v = (Stop) { .extra = 0 } } } };
    Robot* norm_3 = &tmp_3;
    World tmp_2 = (World) { .robot = (*norm_3), .time = 0 };
    World* norm_4 = &tmp_2;
    int32_t norm_5 = worldDir(norm_4);
    println(norm_5);
    println(madeDir());
    enum_Direction d = tag_South;
    Tuple_int32_Direction t = (Tuple_int32_Direction) { ._1 = 9, ._2 = d };
    println(tupleDir(t));
    Robot stainless_buffer_0[2] = { (Robot) { .y = 0, .dir = tag_North, .cmd = (Command) { .tag = tag_Stop, .value = (union_Command) { .Stop_v = (Stop) { .extra = 0 } } } }, (Robot) { .y = 0, .dir = tag_South, .cmd = (Command) { .tag = tag_Stop, .value = (union_Command) { .Stop_v = (Stop) { .extra = 0 } } } } };
    array_Robot rs = (array_Robot) { .data = stainless_buffer_0, .length = 2 };
    println(elementDir(rs, 1));
}

static STAINLESS_FUNC_PURE Robot makeRobot(void) {
    return (Robot) { .y = 0, .dir = tag_South, .cmd = (Command) { .tag = tag_Stop, .value = (union_Command) { .Stop_v = (Stop) { .extra = 0 } } } };
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

static STAINLESS_FUNC_PURE int32_t size(Holder* h) {
    Shape* tmp = &h->shape;
    if (tmp->tag == tag_Circle) {
        return tmp->value.Circle_v.radius;
    } else if (tmp->tag == tag_Square) {
        return tmp->value.Square_v.side;
    }
}

static void step(Robot* r, int32_t n) {
    enum_Direction tmp = r->dir;
    if (tmp == tag_North) {
        r->y = r->y + n;
    } else if (tmp == tag_South) {
        r->y = r->y - n;
    }
}

static STAINLESS_FUNC_PURE int32_t steps(Robot* r) {
    Command tmp = r->cmd;
    if (tmp.tag == tag_Move && tmp.value.Move_v.steps > 0) {
        return tmp.value.Move_v.steps;
    } else if (tmp.tag == tag_Move) {
        return 0;
    } else if (tmp.tag == tag_Stop) {
        return -1;
    }
}

static STAINLESS_FUNC_PURE int32_t tupleDir(Tuple_int32_Direction t) {
    enum_Direction tmp = t._2;
    if (tmp == tag_North) {
        return t._1;
    } else if (tmp == tag_South) {
        return 1000 + t._1;
    }
}

static STAINLESS_FUNC_PURE int32_t worldDir(World* w) {
    enum_Direction tmp = w->robot.dir;
    if (tmp == tag_North) {
        return 10;
    } else if (tmp == tag_South) {
        return 20;
    }
}
