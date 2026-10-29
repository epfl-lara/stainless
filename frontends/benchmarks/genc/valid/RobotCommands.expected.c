/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "RobotCommands.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>




/* -------------------------------------- enums ----- */

typedef enum {
  tag_Move,
  tag_Teleport,
  tag_TurnLeft,
  tag_TurnRight
} enum_Command;

typedef enum {
  tag_East,
  tag_North,
  tag_South,
  tag_West
} enum_Direction;


/* ---------------------- data type definitions ----- */

typedef struct {
  int32_t x;
  int32_t y;
  enum_Direction dir;
  int32_t moves;
} Robot;

typedef struct {
  int32_t steps;
} Move;

typedef struct {
  int32_t x;
  int32_t y;
} Teleport;

typedef struct {
  int8_t extra;
} TurnLeft;

typedef struct {
  int8_t extra;
} TurnRight;

typedef union {
  Move Move_v;
  Teleport Teleport_v;
  TurnLeft TurnLeft_v;
  TurnRight TurnRight_v;
} union_Command;

typedef struct {
  enum_Command tag;
  union_Command value;
} Command;

typedef struct {
  Command* data;
  int32_t length;
} array_Command;



/* ---------------------- function declarations ----- */

static STAINLESS_FUNC_PURE int32_t boolToInt(bool b);
static STAINLESS_FUNC_PURE int32_t dirCode(enum_Direction d);
static STAINLESS_FUNC_PURE bool equals_Command(Command lhs, Command rhs);
static STAINLESS_FUNC_PURE bool equals_Direction(enum_Direction lhs, enum_Direction rhs);
static 
void print(int32_t x);
static 
void print_1(char c);
static void println(int32_t x);
static void println_1(void);
static void run(Robot* r, array_Command cmds);
static void step(Robot* r, Command c);
static STAINLESS_FUNC_PURE enum_Direction turnLeft(enum_Direction d);
static STAINLESS_FUNC_PURE enum_Direction turnRight(enum_Direction d);


/* ----------------------- function definitions ----- */

static STAINLESS_FUNC_PURE int32_t boolToInt(bool b) {
    if (b) {
        return 1;
    } else {
        return 0;
    }
}

static STAINLESS_FUNC_PURE int32_t dirCode(enum_Direction d) {
    if (d == tag_North) {
        return 0;
    } else if (d == tag_East) {
        return 1;
    } else if (d == tag_South) {
        return 2;
    } else if (d == tag_West) {
        return 3;
    }
}

static STAINLESS_FUNC_PURE bool equals_Command(Command lhs, Command rhs) {
    return (lhs.tag == tag_Teleport && rhs.tag == tag_Teleport) && (lhs.value.Teleport_v.x == rhs.value.Teleport_v.x && lhs.value.Teleport_v.y == rhs.value.Teleport_v.y) || ((lhs.tag == tag_TurnLeft && rhs.tag == tag_TurnLeft) && true || ((lhs.tag == tag_TurnRight && rhs.tag == tag_TurnRight) && true || (lhs.tag == tag_Move && rhs.tag == tag_Move) && lhs.value.Move_v.steps == rhs.value.Move_v.steps));
}

static STAINLESS_FUNC_PURE bool equals_Direction(enum_Direction lhs, enum_Direction rhs) {
    return (lhs == tag_West && rhs == tag_West) && true || ((lhs == tag_South && rhs == tag_South) && true || ((lhs == tag_East && rhs == tag_East) && true || (lhs == tag_North && rhs == tag_North) && true));
}

void main(void) {
    Robot r = (Robot) { .x = 0, .y = 0, .dir = tag_North, .moves = 0 };
    Command stainless_buffer_0[8] = { (Command) { .tag = tag_Move, .value = (union_Command) { .Move_v = (Move) { .steps = 3 } } }, (Command) { .tag = tag_TurnRight, .value = (union_Command) { .TurnRight_v = (TurnRight) { .extra = 0 } } }, (Command) { .tag = tag_Move, .value = (union_Command) { .Move_v = (Move) { .steps = 2 } } }, (Command) { .tag = tag_TurnRight, .value = (union_Command) { .TurnRight_v = (TurnRight) { .extra = 0 } } }, (Command) { .tag = tag_Move, .value = (union_Command) { .Move_v = (Move) { .steps = 1 } } }, (Command) { .tag = tag_Teleport, .value = (union_Command) { .Teleport_v = (Teleport) { .x = 10, .y = -5 } } }, (Command) { .tag = tag_TurnLeft, .value = (union_Command) { .TurnLeft_v = (TurnLeft) { .extra = 0 } } }, (Command) { .tag = tag_Move, .value = (union_Command) { .Move_v = (Move) { .steps = 4 } } } };
    array_Command cmds = (array_Command) { .data = stainless_buffer_0, .length = 8 };
    run(&r, cmds);
    println(r.x);
    println(r.y);
    println(dirCode(r.dir));
    println(r.moves);
    println(boolToInt(equals_Direction(r.dir, tag_East)));
    println(boolToInt(equals_Direction(r.dir, tag_North)));
    println(boolToInt(equals_Direction(turnLeft(turnRight(r.dir)), r.dir)));
    println(boolToInt(equals_Command(cmds.data[0], (Command) { .tag = tag_Move, .value = (union_Command) { .Move_v = (Move) { .steps = 3 } } })));
    println(boolToInt(equals_Command(cmds.data[0], (Command) { .tag = tag_Move, .value = (union_Command) { .Move_v = (Move) { .steps = 4 } } })));
    println(boolToInt(equals_Command(cmds.data[1], cmds.data[3])));
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

static void run(Robot* r, array_Command cmds) {
    int32_t i = 0;
    while (i < cmds.length) {
        step(r, cmds.data[i]);
        i = i + 1;
    }
}

static void step(Robot* r, Command c) {
    if (c.tag == tag_Move) {
        enum_Direction d = r->dir;
        if (d == tag_North) {
            r->y = r->y + c.value.Move_v.steps;
        } else if (d == tag_South) {
            r->y = r->y - c.value.Move_v.steps;
        } else if (d == tag_East) {
            r->x = r->x + c.value.Move_v.steps;
        } else if (d == tag_West) {
            r->x = r->x - c.value.Move_v.steps;
        }
        r->moves = r->moves + 1;
    } else if (c.tag == tag_TurnLeft) {
        r->dir = turnLeft(r->dir);
    } else if (c.tag == tag_TurnRight) {
        r->dir = turnRight(r->dir);
    } else if (c.tag == tag_Teleport) {
        r->x = c.value.Teleport_v.x;
        r->y = c.value.Teleport_v.y;
    }
}

static STAINLESS_FUNC_PURE enum_Direction turnLeft(enum_Direction d) {
    if (d == tag_North) {
        return tag_West;
    } else if (d == tag_West) {
        return tag_South;
    } else if (d == tag_South) {
        return tag_East;
    } else if (d == tag_East) {
        return tag_North;
    }
}

static STAINLESS_FUNC_PURE enum_Direction turnRight(enum_Direction d) {
    if (d == tag_North) {
        return tag_East;
    } else if (d == tag_East) {
        return tag_South;
    } else if (d == tag_South) {
        return tag_West;
    } else if (d == tag_West) {
        return tag_North;
    }
}
