/* --------------------------- GenC requirements ----- */

#include <limits.h>
#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
#error "Your compiler does not meet the minimum requirements of GenC. Please see"
#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
#endif

/* ---------------------------- include header ------- */

#include "ImageProcessing.h"

/* ----------------------------------- includes ----- */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>



/* ------------------------------- type aliases ----- */

typedef void* State;
typedef FILE* FileInputStream;
typedef FILE* FileOutputStream;


/* -------------------------------------- enums ----- */

typedef enum {
  tag_Failure_BitmapHeader,
  tag_Result_BitmapHeader
} enum_MaybeResult_BitmapHeader;

typedef enum {
  tag_Failure_FileHeader,
  tag_Result_FileHeader
} enum_MaybeResult_FileHeader;

typedef enum {
  tag_Failure_Tuple_FileHeader_BitmapHeader,
  tag_Result_Tuple_FileHeader_BitmapHeader
} enum_MaybeResult_Tuple_FileHeader_BitmapHeader;

typedef enum {
  tag_Failure_Tuple_Tuple_int32_int32_int32,
  tag_Result_Tuple_Tuple_int32_int32_int32
} enum_MaybeResult_Tuple_Tuple_int32_int32_int32;

typedef enum {
  tag_Failure_Tuple_Tuple_int32_int32_int32_int32,
  tag_Result_Tuple_Tuple_int32_int32_int32_int32
} enum_MaybeResult_Tuple_Tuple_int32_int32_int32_int32;

typedef enum {
  tag_Failure_Tuple_int32_int32,
  tag_Result_Tuple_int32_int32
} enum_MaybeResult_Tuple_int32_int32;

typedef enum {
  tag_Failure_Tuple_int32_int32_int32,
  tag_Result_Tuple_int32_int32_int32
} enum_MaybeResult_Tuple_int32_int32_int32;

typedef enum {
  tag_Failure_Tuple_int32_int32_int32_int32,
  tag_Result_Tuple_int32_int32_int32_int32
} enum_MaybeResult_Tuple_int32_int32_int32_int32;

typedef enum {
  tag_Failure_int32,
  tag_Result_int32
} enum_MaybeResult_int32;

typedef enum {
  tag_None_int8,
  tag_Some_int8
} enum_Option_int8;

typedef enum {
  tag_CorruptedDataError,
  tag_DomainError,
  tag_ImageTooBigError,
  tag_InvalidBitmapHeaderError,
  tag_InvalidFileHeaderError,
  tag_NotImplementedError,
  tag_OpenError,
  tag_ReadError,
  tag_Success,
  tag_WriteError
} enum_Status;


/* ---------------------- data type definitions ----- */

typedef struct {
  int32_t* data;
  int32_t length;
} array_int32;

typedef struct {
  int32_t size;
  int32_t scale;
  array_int32 kernel;
} Kernel;

typedef struct {
  int8_t r[262144];
  int8_t g[262144];
  int8_t b[262144];
  int32_t w;
  int32_t h;
} Image;

typedef struct {
  int8_t* data;
  int32_t length;
} array_int8;

typedef struct {
  enum_Status status;
} Failure_Tuple_FileHeader_BitmapHeader;

typedef struct {
  int32_t size;
  int32_t offset;
} FileHeader;

typedef struct {
  int32_t width;
  int32_t height;
} BitmapHeader;

typedef struct {
  FileHeader _1;
  BitmapHeader _2;
} Tuple_FileHeader_BitmapHeader;

typedef struct {
  Tuple_FileHeader_BitmapHeader result;
} Result_Tuple_FileHeader_BitmapHeader;

typedef union {
  Failure_Tuple_FileHeader_BitmapHeader Failure_Tuple_FileHeader_BitmapHeader_v;
  Result_Tuple_FileHeader_BitmapHeader Result_Tuple_FileHeader_BitmapHeader_v;
} union_MaybeResult_Tuple_FileHeader_BitmapHeader;

typedef struct {
  enum_MaybeResult_Tuple_FileHeader_BitmapHeader tag;
  union_MaybeResult_Tuple_FileHeader_BitmapHeader value;
} MaybeResult_Tuple_FileHeader_BitmapHeader;

typedef struct {
  enum_Status status;
} Failure_FileHeader;

typedef struct {
  FileHeader result;
} Result_FileHeader;

typedef union {
  Failure_FileHeader Failure_FileHeader_v;
  Result_FileHeader Result_FileHeader_v;
} union_MaybeResult_FileHeader;

typedef struct {
  enum_MaybeResult_FileHeader tag;
  union_MaybeResult_FileHeader value;
} MaybeResult_FileHeader;

typedef struct {
  enum_Status status;
} Failure_BitmapHeader;

typedef struct {
  BitmapHeader result;
} Result_BitmapHeader;

typedef union {
  Failure_BitmapHeader Failure_BitmapHeader_v;
  Result_BitmapHeader Result_BitmapHeader_v;
} union_MaybeResult_BitmapHeader;

typedef struct {
  enum_MaybeResult_BitmapHeader tag;
  union_MaybeResult_BitmapHeader value;
} MaybeResult_BitmapHeader;

typedef struct {
  enum_Status status;
} Failure_Tuple_Tuple_int32_int32_int32;

typedef struct {
  int32_t _1;
  int32_t _2;
} Tuple_int32_int32;

typedef struct {
  Tuple_int32_int32 _1;
  int32_t _2;
} Tuple_Tuple_int32_int32_int32;

typedef struct {
  Tuple_Tuple_int32_int32_int32 result;
} Result_Tuple_Tuple_int32_int32_int32;

typedef union {
  Failure_Tuple_Tuple_int32_int32_int32 Failure_Tuple_Tuple_int32_int32_int32_v;
  Result_Tuple_Tuple_int32_int32_int32 Result_Tuple_Tuple_int32_int32_int32_v;
} union_MaybeResult_Tuple_Tuple_int32_int32_int32;

typedef struct {
  enum_MaybeResult_Tuple_Tuple_int32_int32_int32 tag;
  union_MaybeResult_Tuple_Tuple_int32_int32_int32 value;
} MaybeResult_Tuple_Tuple_int32_int32_int32;

typedef struct {
  enum_Status status;
} Failure_Tuple_int32_int32;

typedef struct {
  Tuple_int32_int32 result;
} Result_Tuple_int32_int32;

typedef union {
  Failure_Tuple_int32_int32 Failure_Tuple_int32_int32_v;
  Result_Tuple_int32_int32 Result_Tuple_int32_int32_v;
} union_MaybeResult_Tuple_int32_int32;

typedef struct {
  enum_MaybeResult_Tuple_int32_int32 tag;
  union_MaybeResult_Tuple_int32_int32 value;
} MaybeResult_Tuple_int32_int32;

typedef struct {
  enum_Status status;
} Failure_int32;

typedef struct {
  int32_t result;
} Result_int32;

typedef union {
  Failure_int32 Failure_int32_v;
  Result_int32 Result_int32_v;
} union_MaybeResult_int32;

typedef struct {
  enum_MaybeResult_int32 tag;
  union_MaybeResult_int32 value;
} MaybeResult_int32;

typedef struct {
  enum_Status status;
} Failure_Tuple_Tuple_int32_int32_int32_int32;

typedef struct {
  int32_t _1;
  int32_t _2;
  int32_t _3;
} Tuple_int32_int32_int32;

typedef struct {
  Tuple_int32_int32_int32 _1;
  int32_t _2;
} Tuple_Tuple_int32_int32_int32_int32;

typedef struct {
  Tuple_Tuple_int32_int32_int32_int32 result;
} Result_Tuple_Tuple_int32_int32_int32_int32;

typedef union {
  Failure_Tuple_Tuple_int32_int32_int32_int32 Failure_Tuple_Tuple_int32_int32_int32_int32_v;
  Result_Tuple_Tuple_int32_int32_int32_int32 Result_Tuple_Tuple_int32_int32_int32_int32_v;
} union_MaybeResult_Tuple_Tuple_int32_int32_int32_int32;

typedef struct {
  enum_MaybeResult_Tuple_Tuple_int32_int32_int32_int32 tag;
  union_MaybeResult_Tuple_Tuple_int32_int32_int32_int32 value;
} MaybeResult_Tuple_Tuple_int32_int32_int32_int32;

typedef struct {
  enum_Status status;
} Failure_Tuple_int32_int32_int32;

typedef struct {
  Tuple_int32_int32_int32 result;
} Result_Tuple_int32_int32_int32;

typedef union {
  Failure_Tuple_int32_int32_int32 Failure_Tuple_int32_int32_int32_v;
  Result_Tuple_int32_int32_int32 Result_Tuple_int32_int32_int32_v;
} union_MaybeResult_Tuple_int32_int32_int32;

typedef struct {
  enum_MaybeResult_Tuple_int32_int32_int32 tag;
  union_MaybeResult_Tuple_int32_int32_int32 value;
} MaybeResult_Tuple_int32_int32_int32;

typedef struct {
  enum_Status status;
} Failure_Tuple_int32_int32_int32_int32;

typedef struct {
  int32_t _1;
  int32_t _2;
  int32_t _3;
  int32_t _4;
} Tuple_int32_int32_int32_int32;

typedef struct {
  Tuple_int32_int32_int32_int32 result;
} Result_Tuple_int32_int32_int32_int32;

typedef union {
  Failure_Tuple_int32_int32_int32_int32 Failure_Tuple_int32_int32_int32_int32_v;
  Result_Tuple_int32_int32_int32_int32 Result_Tuple_int32_int32_int32_int32_v;
} union_MaybeResult_Tuple_int32_int32_int32_int32;

typedef struct {
  enum_MaybeResult_Tuple_int32_int32_int32_int32 tag;
  union_MaybeResult_Tuple_int32_int32_int32_int32 value;
} MaybeResult_Tuple_int32_int32_int32_int32;

typedef struct {
  int8_t _1;
  int8_t _2;
} Tuple_int8_int8;

typedef struct {
  int8_t extra;
} None_int8;

typedef struct {
  int8_t v;
} Some_int8;

typedef union {
  None_int8 None_int8_v;
  Some_int8 Some_int8_v;
} union_Option_int8;

typedef struct {
  enum_Option_int8 tag;
  union_Option_int8 value;
} Option_int8;



/* ---------------------- function declarations ----- */

static void apply(Kernel* thiss, Image* src, Image* dest);
static STAINLESS_FUNC_PURE int8_t apply_1(Kernel* thiss, array_int8 channel, int32_t width, int32_t height, int32_t index);
static STAINLESS_FUNC_PURE int32_t at(Kernel* thiss, array_int8 channel, int32_t* width, int32_t* height, int32_t* index, int32_t col, int32_t row);
static STAINLESS_FUNC_PURE int32_t buildInt(FileInputStream* fis, State* state, int8_t b1, int8_t b2, int8_t b3, int8_t b4);
static STAINLESS_FUNC_PURE int32_t buildInt_1(FileInputStream* fis, State* state, int8_t b1, int8_t b2, int8_t b3, int8_t b4);
static STAINLESS_FUNC_PURE void check(bool prop);
static STAINLESS_FUNC_PURE int32_t clamp(int32_t x, int32_t down, int32_t up);
static 
bool close(FILE* this);
static 
bool close_1(FILE* this, void* unused);
static STAINLESS_FUNC_PURE MaybeResult_Tuple_FileHeader_BitmapHeader combine_FileHeader_BitmapHeader(MaybeResult_FileHeader a, MaybeResult_BitmapHeader b);
static STAINLESS_FUNC_PURE MaybeResult_Tuple_Tuple_int32_int32_int32 combine_Tuple_int32_int32_int32(MaybeResult_Tuple_int32_int32 a, MaybeResult_int32 b);
static STAINLESS_FUNC_PURE MaybeResult_Tuple_Tuple_int32_int32_int32_int32 combine_Tuple_int32_int32_int32_int32(MaybeResult_Tuple_int32_int32_int32 a, MaybeResult_int32 b);
static STAINLESS_FUNC_PURE MaybeResult_Tuple_int32_int32 combine_int32_int32(MaybeResult_int32 a, MaybeResult_int32 b);
static STAINLESS_FUNC_PURE MaybeResult_Tuple_int32_int32_int32 combine_int32_int32_int32(MaybeResult_int32 a, MaybeResult_int32 b, MaybeResult_int32 c);
static STAINLESS_FUNC_PURE MaybeResult_Tuple_int32_int32_int32_int32 combine_int32_int32_int32_int32(MaybeResult_int32 a, MaybeResult_int32 b, MaybeResult_int32 c, MaybeResult_int32 d);
static STAINLESS_FUNC_PURE int32_t constructWord(int8_t byte1, int8_t byte2);
static STAINLESS_FUNC_PURE Tuple_int8_int8 destructWord(int32_t word);
static STAINLESS_FUNC_PURE int32_t fix(Kernel* thiss, array_int8 channel, int32_t* width, int32_t* height, int32_t* index, int32_t x, int32_t side);
static STAINLESS_FUNC_PURE BitmapHeader getResult_BitmapHeader(MaybeResult_BitmapHeader thiss);
static STAINLESS_FUNC_PURE FileHeader getResult_FileHeader(MaybeResult_FileHeader thiss);
static STAINLESS_FUNC_PURE Tuple_int32_int32 getResult_Tuple_int32_int32(MaybeResult_Tuple_int32_int32 thiss);
static STAINLESS_FUNC_PURE Tuple_int32_int32_int32 getResult_Tuple_int32_int32_int32(MaybeResult_Tuple_int32_int32_int32 thiss);
static STAINLESS_FUNC_PURE int32_t getResult_int32(MaybeResult_int32 thiss);
static STAINLESS_FUNC_PURE enum_Status getStatus_BitmapHeader(MaybeResult_BitmapHeader thiss);
static STAINLESS_FUNC_PURE enum_Status getStatus_FileHeader(MaybeResult_FileHeader thiss);
static STAINLESS_FUNC_PURE enum_Status getStatus_Tuple_int32_int32(MaybeResult_Tuple_int32_int32 thiss);
static STAINLESS_FUNC_PURE enum_Status getStatus_Tuple_int32_int32_int32(MaybeResult_Tuple_int32_int32_int32 thiss);
static STAINLESS_FUNC_PURE enum_Status getStatus_int32(MaybeResult_int32 thiss);
static STAINLESS_FUNC_PURE int8_t get_int8(Option_int8 thiss);
static 
int8_t impl(FILE** this, void** unused, bool* valid);
static STAINLESS_FUNC_PURE bool inRange(int32_t x, int32_t min_1, int32_t max_1);
static STAINLESS_FUNC_PURE bool isDefined_BitmapHeader(MaybeResult_BitmapHeader thiss);
static STAINLESS_FUNC_PURE bool isDefined_FileHeader(MaybeResult_FileHeader thiss);
static STAINLESS_FUNC_PURE bool isDefined_Tuple_int32_int32(MaybeResult_Tuple_int32_int32 thiss);
static STAINLESS_FUNC_PURE bool isDefined_Tuple_int32_int32_int32(MaybeResult_Tuple_int32_int32_int32 thiss);
static STAINLESS_FUNC_PURE bool isDefined_int32(MaybeResult_int32 thiss);
static STAINLESS_FUNC_PURE bool isDefined_int8(Option_int8 thiss);
static STAINLESS_FUNC_PURE bool isEmpty_int8(Option_int8 thiss);
static 
bool isOpen(FILE* this);
static 
bool isOpen_1(FILE* this);
static STAINLESS_FUNC_PURE bool isSuccess(enum_Status thiss);
static enum_Status loadImageData(FileInputStream fis, Image* image, State state);
static void log(char* msg, int32_t x);
static void log_1(FileHeader h);
static void log_2(BitmapHeader h);
static STAINLESS_FUNC_PURE int32_t max(int32_t x, int32_t y);
static MaybeResult_BitmapHeader maybeReadBitmapHeader(FileInputStream fis, State state);
static MaybeResult_int32 maybeReadDword(FileInputStream fis, State state);
static MaybeResult_FileHeader maybeReadFileHeader(FileInputStream fis, State state);
static MaybeResult_int32 maybeReadLong(FileInputStream fis, State state);
static MaybeResult_int32 maybeReadWord(FileInputStream fis, State state);
static STAINLESS_FUNC_PURE int32_t min(int32_t x, int32_t y);
static void* newState(void);
static 
FILE* open(char* filename, void* unused);
static 
FILE* open_1(char* filename);
static 
void print(char* s);
static 
void print_1(int32_t x);
static 
void print_2(char c);
static void println(int32_t x);
static void println_1(void);
static void println_2(char* s);
static enum_Status process(FileInputStream fis, FileOutputStream fos, State state);
static enum_Status processImage(FileInputStream* fis, FileOutputStream* fos, State* state, Kernel* kernel, Image* src);
static enum_Status saveImage(FileOutputStream fos, Image* image);
static bool skipBytes(FileInputStream fis, int32_t count, State state);
static int32_t statusCode(enum_Status s);
static Option_int8 tryReadByte(FileInputStream thiss, State state);
static 
bool write(FILE* this, int8_t x);
static bool writeBitmapHeader(FileOutputStream* fos, Image* image);
static bool writeBytes(FileOutputStream fos, int8_t byte, int32_t count);
static bool writeDword(FileOutputStream fos, int32_t dword);
static bool writeFileHeader(FileOutputStream* fos, Image* image);
static bool writeImage(FileOutputStream* fos, Image* image);
static bool writeLong(FileOutputStream fos, int32_t long_1);
static bool writeWord(FileOutputStream fos, int32_t word);


/* ----------------------- function definitions ----- */

static void apply(Kernel* thiss, Image* src, Image* dest) {
    int32_t size = src->w * src->h;
    int32_t i = 0;
    while (i < size) {
        int32_t norm_1 = i;
        int8_t norm_0 = apply_1(thiss, (array_int8) { .data = src->r, .length = 262144 }, src->w, src->h, i);
        int8_t norm_2 = norm_0;
        dest->r[norm_1] = norm_2;
        int32_t norm_4 = i;
        int8_t norm_3 = apply_1(thiss, (array_int8) { .data = src->g, .length = 262144 }, src->w, src->h, i);
        int8_t norm_5 = norm_3;
        dest->g[norm_4] = norm_5;
        int32_t norm_7 = i;
        int8_t norm_6 = apply_1(thiss, (array_int8) { .data = src->b, .length = 262144 }, src->w, src->h, i);
        int8_t norm_8 = norm_6;
        dest->b[norm_7] = norm_8;
        i = i + 1;
    }
}

static STAINLESS_FUNC_PURE int8_t apply_1(Kernel* thiss, array_int8 channel, int32_t width, int32_t height, int32_t index) {
    int32_t mid = thiss->size / 2;
    int32_t i = index % width;
    int32_t j = index / width;
    int32_t res = 0;
    int32_t p = -mid;
    while (p <= mid) {
        int32_t q = -mid;
        int32_t oldP = p;
        while (q <= mid) {
            int32_t kcol = p + mid;
            int32_t krow = q + mid;
            int32_t kidx = krow * thiss->size + kcol;
            res = res + at(thiss, channel, &width, &height, &index, i + p, j + q) * thiss->kernel.data[kidx];
            q = q + 1;
            check(inRange(q, -mid, mid + 1));
        }
        p = p + 1;
        check(inRange(p, -mid, mid + 1));
    }
    res = clamp(res / thiss->scale, 0, 255);
    return (int8_t)res;
}

static STAINLESS_FUNC_PURE int32_t at(Kernel* thiss, array_int8 channel, int32_t* width, int32_t* height, int32_t* index, int32_t col, int32_t row) {
    int32_t c = fix(thiss, channel, width, height, index, col, *width);
    int32_t r = fix(thiss, channel, width, height, index, row, *height);
    int8_t component = channel.data[r * (*width) + c];
    if (((int32_t)component) < 0) {
        return ((int32_t)component) + 255;
    } else {
        return (int32_t)component;
    }
}

static STAINLESS_FUNC_PURE int32_t buildInt(FileInputStream* fis, State* state, int8_t b1, int8_t b2, int8_t b3, int8_t b4) {
    return ((((int32_t)(((uint32_t)((int32_t)b4)) << 24)) | ((int32_t)(((uint32_t)(((int32_t)b3) & 255)) << 16))) | ((int32_t)(((uint32_t)(((int32_t)b2) & 255)) << 8))) | (((int32_t)b1) & 255);
}

static STAINLESS_FUNC_PURE int32_t buildInt_1(FileInputStream* fis, State* state, int8_t b1, int8_t b2, int8_t b3, int8_t b4) {
    return ((((int32_t)(((uint32_t)((int32_t)b4)) << 24)) | ((int32_t)(((uint32_t)(((int32_t)b3) & 255)) << 16))) | ((int32_t)(((uint32_t)(((int32_t)b2) & 255)) << 8))) | (((int32_t)b1) & 255);
}

static STAINLESS_FUNC_PURE void check(bool prop) {
    
}

static STAINLESS_FUNC_PURE int32_t clamp(int32_t x, int32_t down, int32_t up) {
    return max(down, min(x, up));
}


bool close(FILE* this) {
  if (this != NULL)
    return fclose(this) == 0;
  else
    return true;
}
    


bool close_1(FILE* this, void* unused) {
  if (this != NULL)
    return fclose(this) == 0;
  else
    return true;
}
      

static STAINLESS_FUNC_PURE MaybeResult_Tuple_FileHeader_BitmapHeader combine_FileHeader_BitmapHeader(MaybeResult_FileHeader a, MaybeResult_BitmapHeader b) {
    if (isDefined_FileHeader(a)) {
        if (isDefined_BitmapHeader(b)) {
            return (MaybeResult_Tuple_FileHeader_BitmapHeader) { .tag = tag_Result_Tuple_FileHeader_BitmapHeader, .value = (union_MaybeResult_Tuple_FileHeader_BitmapHeader) { .Result_Tuple_FileHeader_BitmapHeader_v = (Result_Tuple_FileHeader_BitmapHeader) { .result = (Tuple_FileHeader_BitmapHeader) { ._1 = getResult_FileHeader(a), ._2 = getResult_BitmapHeader(b) } } } };
        } else {
            return (MaybeResult_Tuple_FileHeader_BitmapHeader) { .tag = tag_Failure_Tuple_FileHeader_BitmapHeader, .value = (union_MaybeResult_Tuple_FileHeader_BitmapHeader) { .Failure_Tuple_FileHeader_BitmapHeader_v = (Failure_Tuple_FileHeader_BitmapHeader) { .status = getStatus_BitmapHeader(b) } } };
        }
    } else {
        return (MaybeResult_Tuple_FileHeader_BitmapHeader) { .tag = tag_Failure_Tuple_FileHeader_BitmapHeader, .value = (union_MaybeResult_Tuple_FileHeader_BitmapHeader) { .Failure_Tuple_FileHeader_BitmapHeader_v = (Failure_Tuple_FileHeader_BitmapHeader) { .status = getStatus_FileHeader(a) } } };
    }
}

static STAINLESS_FUNC_PURE MaybeResult_Tuple_Tuple_int32_int32_int32 combine_Tuple_int32_int32_int32(MaybeResult_Tuple_int32_int32 a, MaybeResult_int32 b) {
    if (isDefined_Tuple_int32_int32(a)) {
        if (isDefined_int32(b)) {
            return (MaybeResult_Tuple_Tuple_int32_int32_int32) { .tag = tag_Result_Tuple_Tuple_int32_int32_int32, .value = (union_MaybeResult_Tuple_Tuple_int32_int32_int32) { .Result_Tuple_Tuple_int32_int32_int32_v = (Result_Tuple_Tuple_int32_int32_int32) { .result = (Tuple_Tuple_int32_int32_int32) { ._1 = getResult_Tuple_int32_int32(a), ._2 = getResult_int32(b) } } } };
        } else {
            return (MaybeResult_Tuple_Tuple_int32_int32_int32) { .tag = tag_Failure_Tuple_Tuple_int32_int32_int32, .value = (union_MaybeResult_Tuple_Tuple_int32_int32_int32) { .Failure_Tuple_Tuple_int32_int32_int32_v = (Failure_Tuple_Tuple_int32_int32_int32) { .status = getStatus_int32(b) } } };
        }
    } else {
        return (MaybeResult_Tuple_Tuple_int32_int32_int32) { .tag = tag_Failure_Tuple_Tuple_int32_int32_int32, .value = (union_MaybeResult_Tuple_Tuple_int32_int32_int32) { .Failure_Tuple_Tuple_int32_int32_int32_v = (Failure_Tuple_Tuple_int32_int32_int32) { .status = getStatus_Tuple_int32_int32(a) } } };
    }
}

static STAINLESS_FUNC_PURE MaybeResult_Tuple_Tuple_int32_int32_int32_int32 combine_Tuple_int32_int32_int32_int32(MaybeResult_Tuple_int32_int32_int32 a, MaybeResult_int32 b) {
    if (isDefined_Tuple_int32_int32_int32(a)) {
        if (isDefined_int32(b)) {
            return (MaybeResult_Tuple_Tuple_int32_int32_int32_int32) { .tag = tag_Result_Tuple_Tuple_int32_int32_int32_int32, .value = (union_MaybeResult_Tuple_Tuple_int32_int32_int32_int32) { .Result_Tuple_Tuple_int32_int32_int32_int32_v = (Result_Tuple_Tuple_int32_int32_int32_int32) { .result = (Tuple_Tuple_int32_int32_int32_int32) { ._1 = getResult_Tuple_int32_int32_int32(a), ._2 = getResult_int32(b) } } } };
        } else {
            return (MaybeResult_Tuple_Tuple_int32_int32_int32_int32) { .tag = tag_Failure_Tuple_Tuple_int32_int32_int32_int32, .value = (union_MaybeResult_Tuple_Tuple_int32_int32_int32_int32) { .Failure_Tuple_Tuple_int32_int32_int32_int32_v = (Failure_Tuple_Tuple_int32_int32_int32_int32) { .status = getStatus_int32(b) } } };
        }
    } else {
        return (MaybeResult_Tuple_Tuple_int32_int32_int32_int32) { .tag = tag_Failure_Tuple_Tuple_int32_int32_int32_int32, .value = (union_MaybeResult_Tuple_Tuple_int32_int32_int32_int32) { .Failure_Tuple_Tuple_int32_int32_int32_int32_v = (Failure_Tuple_Tuple_int32_int32_int32_int32) { .status = getStatus_Tuple_int32_int32_int32(a) } } };
    }
}

static STAINLESS_FUNC_PURE MaybeResult_Tuple_int32_int32 combine_int32_int32(MaybeResult_int32 a, MaybeResult_int32 b) {
    if (isDefined_int32(a)) {
        if (isDefined_int32(b)) {
            return (MaybeResult_Tuple_int32_int32) { .tag = tag_Result_Tuple_int32_int32, .value = (union_MaybeResult_Tuple_int32_int32) { .Result_Tuple_int32_int32_v = (Result_Tuple_int32_int32) { .result = (Tuple_int32_int32) { ._1 = getResult_int32(a), ._2 = getResult_int32(b) } } } };
        } else {
            return (MaybeResult_Tuple_int32_int32) { .tag = tag_Failure_Tuple_int32_int32, .value = (union_MaybeResult_Tuple_int32_int32) { .Failure_Tuple_int32_int32_v = (Failure_Tuple_int32_int32) { .status = getStatus_int32(b) } } };
        }
    } else {
        return (MaybeResult_Tuple_int32_int32) { .tag = tag_Failure_Tuple_int32_int32, .value = (union_MaybeResult_Tuple_int32_int32) { .Failure_Tuple_int32_int32_v = (Failure_Tuple_int32_int32) { .status = getStatus_int32(a) } } };
    }
}

static STAINLESS_FUNC_PURE MaybeResult_Tuple_int32_int32_int32 combine_int32_int32_int32(MaybeResult_int32 a, MaybeResult_int32 b, MaybeResult_int32 c) {
    MaybeResult_Tuple_Tuple_int32_int32_int32 tmp = combine_Tuple_int32_int32_int32(combine_int32_int32(a, b), c);
    if (tmp.tag == tag_Result_Tuple_Tuple_int32_int32_int32) {
        return (MaybeResult_Tuple_int32_int32_int32) { .tag = tag_Result_Tuple_int32_int32_int32, .value = (union_MaybeResult_Tuple_int32_int32_int32) { .Result_Tuple_int32_int32_int32_v = (Result_Tuple_int32_int32_int32) { .result = (Tuple_int32_int32_int32) { ._1 = tmp.value.Result_Tuple_Tuple_int32_int32_int32_v.result._1._1, ._2 = tmp.value.Result_Tuple_Tuple_int32_int32_int32_v.result._1._2, ._3 = tmp.value.Result_Tuple_Tuple_int32_int32_int32_v.result._2 } } } };
    } else if (tmp.tag == tag_Failure_Tuple_Tuple_int32_int32_int32) {
        return (MaybeResult_Tuple_int32_int32_int32) { .tag = tag_Failure_Tuple_int32_int32_int32, .value = (union_MaybeResult_Tuple_int32_int32_int32) { .Failure_Tuple_int32_int32_int32_v = (Failure_Tuple_int32_int32_int32) { .status = tmp.value.Failure_Tuple_Tuple_int32_int32_int32_v.status } } };
    }
}

static STAINLESS_FUNC_PURE MaybeResult_Tuple_int32_int32_int32_int32 combine_int32_int32_int32_int32(MaybeResult_int32 a, MaybeResult_int32 b, MaybeResult_int32 c, MaybeResult_int32 d) {
    MaybeResult_Tuple_Tuple_int32_int32_int32_int32 tmp = combine_Tuple_int32_int32_int32_int32(combine_int32_int32_int32(a, b, c), d);
    if (tmp.tag == tag_Result_Tuple_Tuple_int32_int32_int32_int32) {
        return (MaybeResult_Tuple_int32_int32_int32_int32) { .tag = tag_Result_Tuple_int32_int32_int32_int32, .value = (union_MaybeResult_Tuple_int32_int32_int32_int32) { .Result_Tuple_int32_int32_int32_int32_v = (Result_Tuple_int32_int32_int32_int32) { .result = (Tuple_int32_int32_int32_int32) { ._1 = tmp.value.Result_Tuple_Tuple_int32_int32_int32_int32_v.result._1._1, ._2 = tmp.value.Result_Tuple_Tuple_int32_int32_int32_int32_v.result._1._2, ._3 = tmp.value.Result_Tuple_Tuple_int32_int32_int32_int32_v.result._1._3, ._4 = tmp.value.Result_Tuple_Tuple_int32_int32_int32_int32_v.result._2 } } } };
    } else if (tmp.tag == tag_Failure_Tuple_Tuple_int32_int32_int32_int32) {
        return (MaybeResult_Tuple_int32_int32_int32_int32) { .tag = tag_Failure_Tuple_int32_int32_int32_int32, .value = (union_MaybeResult_Tuple_int32_int32_int32_int32) { .Failure_Tuple_int32_int32_int32_int32_v = (Failure_Tuple_int32_int32_int32_int32) { .status = tmp.value.Failure_Tuple_Tuple_int32_int32_int32_int32_v.status } } };
    }
}

static STAINLESS_FUNC_PURE int32_t constructWord(int8_t byte1, int8_t byte2) {
    int32_t signed_1 = ((int32_t)(((uint32_t)((int32_t)byte1)) << 8)) | (((int32_t)byte2) & 255);
    int32_t unsigned_1;
    if (signed_1 < 0) {
        unsigned_1 = signed_1 + 2 * 32768;
    } else {
        unsigned_1 = signed_1;
    }
    return unsigned_1;
}

static STAINLESS_FUNC_PURE Tuple_int8_int8 destructWord(int32_t word) {
    int32_t signed_1;
    if (word >= 32768) {
        signed_1 = word - 2 * 32768;
    } else {
        signed_1 = word;
    }
    int8_t b1 = (int8_t)((int32_t)(((uint32_t)signed_1) >> 8));
    int8_t b2 = (int8_t)signed_1;
    return (Tuple_int8_int8) { ._1 = b1, ._2 = b2 };
}

static STAINLESS_FUNC_PURE int32_t fix(Kernel* thiss, array_int8 channel, int32_t* width, int32_t* height, int32_t* index, int32_t x, int32_t side) {
    return clamp(x, 0, side - 1);
}

static STAINLESS_FUNC_PURE BitmapHeader getResult_BitmapHeader(MaybeResult_BitmapHeader thiss) {
    return thiss.value.Result_BitmapHeader_v.result;
}

static STAINLESS_FUNC_PURE FileHeader getResult_FileHeader(MaybeResult_FileHeader thiss) {
    return thiss.value.Result_FileHeader_v.result;
}

static STAINLESS_FUNC_PURE Tuple_int32_int32 getResult_Tuple_int32_int32(MaybeResult_Tuple_int32_int32 thiss) {
    return thiss.value.Result_Tuple_int32_int32_v.result;
}

static STAINLESS_FUNC_PURE Tuple_int32_int32_int32 getResult_Tuple_int32_int32_int32(MaybeResult_Tuple_int32_int32_int32 thiss) {
    return thiss.value.Result_Tuple_int32_int32_int32_v.result;
}

static STAINLESS_FUNC_PURE int32_t getResult_int32(MaybeResult_int32 thiss) {
    return thiss.value.Result_int32_v.result;
}

static STAINLESS_FUNC_PURE enum_Status getStatus_BitmapHeader(MaybeResult_BitmapHeader thiss) {
    return thiss.value.Failure_BitmapHeader_v.status;
}

static STAINLESS_FUNC_PURE enum_Status getStatus_FileHeader(MaybeResult_FileHeader thiss) {
    return thiss.value.Failure_FileHeader_v.status;
}

static STAINLESS_FUNC_PURE enum_Status getStatus_Tuple_int32_int32(MaybeResult_Tuple_int32_int32 thiss) {
    return thiss.value.Failure_Tuple_int32_int32_v.status;
}

static STAINLESS_FUNC_PURE enum_Status getStatus_Tuple_int32_int32_int32(MaybeResult_Tuple_int32_int32_int32 thiss) {
    return thiss.value.Failure_Tuple_int32_int32_int32_v.status;
}

static STAINLESS_FUNC_PURE enum_Status getStatus_int32(MaybeResult_int32 thiss) {
    return thiss.value.Failure_int32_v.status;
}

static STAINLESS_FUNC_PURE int8_t get_int8(Option_int8 thiss) {
    if (thiss.tag == tag_Some_int8) {
        return thiss.value.Some_int8_v.v;
    }
}


int8_t impl(FILE** this, void** unused, bool* valid) {
  int8_t x;
  *valid = fscanf(*this, "%c", &x) == 1;
  return x;
}
      

static STAINLESS_FUNC_PURE bool inRange(int32_t x, int32_t min_1, int32_t max_1) {
    return min_1 <= x && x <= max_1;
}

static STAINLESS_FUNC_PURE bool isDefined_BitmapHeader(MaybeResult_BitmapHeader thiss) {
    if (thiss.tag == tag_Result_BitmapHeader) {
        return true;
    } else {
        return false;
    }
}

static STAINLESS_FUNC_PURE bool isDefined_FileHeader(MaybeResult_FileHeader thiss) {
    if (thiss.tag == tag_Result_FileHeader) {
        return true;
    } else {
        return false;
    }
}

static STAINLESS_FUNC_PURE bool isDefined_Tuple_int32_int32(MaybeResult_Tuple_int32_int32 thiss) {
    if (thiss.tag == tag_Result_Tuple_int32_int32) {
        return true;
    } else {
        return false;
    }
}

static STAINLESS_FUNC_PURE bool isDefined_Tuple_int32_int32_int32(MaybeResult_Tuple_int32_int32_int32 thiss) {
    if (thiss.tag == tag_Result_Tuple_int32_int32_int32) {
        return true;
    } else {
        return false;
    }
}

static STAINLESS_FUNC_PURE bool isDefined_int32(MaybeResult_int32 thiss) {
    if (thiss.tag == tag_Result_int32) {
        return true;
    } else {
        return false;
    }
}

static STAINLESS_FUNC_PURE bool isDefined_int8(Option_int8 thiss) {
    return !isEmpty_int8(thiss);
}

static STAINLESS_FUNC_PURE bool isEmpty_int8(Option_int8 thiss) {
    if (thiss.tag == tag_Some_int8) {
        return false;
    } else if (thiss.tag == tag_None_int8) {
        return true;
    }
}


bool isOpen(FILE* this) {
  return this != NULL;
}
      


bool isOpen_1(FILE* this) {
  return this != NULL;
}
    

static STAINLESS_FUNC_PURE bool isSuccess(enum_Status thiss) {
    return thiss == tag_Success;
}

static enum_Status loadImageData(FileInputStream fis, Image* image, State state) {
    int32_t size = image->w * image->h;
    int32_t i = 0;
    enum_Status status = tag_Success;
    while (isSuccess(status) && i < size) {
        Option_int8 rOpt = tryReadByte(fis, state);
        Option_int8 gOpt = tryReadByte(fis, state);
        Option_int8 bOpt = tryReadByte(fis, state);
        if ((isEmpty_int8(rOpt) || isEmpty_int8(gOpt)) || isEmpty_int8(bOpt)) {
            status = tag_ReadError;
            log("stopped reading data abruptly after", i);
        } else {
            int32_t norm_10 = i;
            int8_t norm_9 = get_int8(rOpt);
            int8_t norm_11 = norm_9;
            image->r[norm_10] = norm_11;
            int32_t norm_13 = i;
            int8_t norm_12 = get_int8(gOpt);
            int8_t norm_14 = norm_12;
            image->g[norm_13] = norm_14;
            int32_t norm_16 = i;
            int8_t norm_15 = get_int8(bOpt);
            int8_t norm_17 = norm_15;
            image->b[norm_16] = norm_17;
        }
        i = i + 1;
    }
    return status;
}

static void log(char* msg, int32_t x) {
    print(msg);
    print(": ");
    println(x);
}

static void log_1(FileHeader h) {
    log("size", h.size);
    log("offset", h.offset);
}

static void log_2(BitmapHeader h) {
    log("width", h.width);
    log("height", h.height);
}

int32_t main(void) {
    State state = newState();
    FileInputStream input = open("input.bmp", state);
    FileOutputStream output = open_1("output.bmp");
    enum_Status status;
    if (isOpen(input) && isOpen_1(output)) {
        status = process(input, output, state);
    } else {
        status = tag_OpenError;
    }
    close(output);
    close_1(input, state);
    return statusCode(status);
}

static STAINLESS_FUNC_PURE int32_t max(int32_t x, int32_t y) {
    if (x < y) {
        return y;
    } else {
        return x;
    }
}

static MaybeResult_BitmapHeader maybeReadBitmapHeader(FileInputStream fis, State state) {
    bool skipSuccess = skipBytes(fis, 4, state);
    MaybeResult_int32 widthRes = maybeReadLong(fis, state);
    MaybeResult_int32 heightRes = maybeReadLong(fis, state);
    if (skipSuccess) {
        skipSuccess = skipBytes(fis, 2, state);
    }
    MaybeResult_int32 bppRes = maybeReadWord(fis, state);
    MaybeResult_int32 compressionRes = maybeReadWord(fis, state);
    MaybeResult_Tuple_int32_int32_int32_int32 tmp = combine_int32_int32_int32_int32(widthRes, heightRes, bppRes, compressionRes);
    if (!skipSuccess) {
        return (MaybeResult_BitmapHeader) { .tag = tag_Failure_BitmapHeader, .value = (union_MaybeResult_BitmapHeader) { .Failure_BitmapHeader_v = (Failure_BitmapHeader) { .status = tag_ReadError } } };
    } else if (tmp.tag == tag_Failure_Tuple_int32_int32_int32_int32) {
        return (MaybeResult_BitmapHeader) { .tag = tag_Failure_BitmapHeader, .value = (union_MaybeResult_BitmapHeader) { .Failure_BitmapHeader_v = (Failure_BitmapHeader) { .status = tmp.value.Failure_Tuple_int32_int32_int32_int32_v.status } } };
    } else if (tmp.tag == tag_Result_Tuple_int32_int32_int32_int32) {
        if (((tmp.value.Result_Tuple_int32_int32_int32_int32_v.result._1 < 0 || tmp.value.Result_Tuple_int32_int32_int32_int32_v.result._2 < 0) || tmp.value.Result_Tuple_int32_int32_int32_int32_v.result._3 != 24) || tmp.value.Result_Tuple_int32_int32_int32_int32_v.result._4 != 0) {
            log("width", tmp.value.Result_Tuple_int32_int32_int32_int32_v.result._1);
            log("height", tmp.value.Result_Tuple_int32_int32_int32_int32_v.result._2);
            log("bpp", tmp.value.Result_Tuple_int32_int32_int32_int32_v.result._3);
            log("compression", tmp.value.Result_Tuple_int32_int32_int32_int32_v.result._4);
            return (MaybeResult_BitmapHeader) { .tag = tag_Failure_BitmapHeader, .value = (union_MaybeResult_BitmapHeader) { .Failure_BitmapHeader_v = (Failure_BitmapHeader) { .status = tag_InvalidBitmapHeaderError } } };
        } else {
            return (MaybeResult_BitmapHeader) { .tag = tag_Result_BitmapHeader, .value = (union_MaybeResult_BitmapHeader) { .Result_BitmapHeader_v = (Result_BitmapHeader) { .result = (BitmapHeader) { .width = tmp.value.Result_Tuple_int32_int32_int32_int32_v.result._1, .height = tmp.value.Result_Tuple_int32_int32_int32_int32_v.result._2 } } } };
        }
    }
}

static MaybeResult_int32 maybeReadDword(FileInputStream fis, State state) {
    Option_int8 byte1 = tryReadByte(fis, state);
    Option_int8 byte2 = tryReadByte(fis, state);
    Option_int8 byte3 = tryReadByte(fis, state);
    Option_int8 byte4 = tryReadByte(fis, state);
    if (((isDefined_int8(byte1) && isDefined_int8(byte2)) && isDefined_int8(byte3)) && isDefined_int8(byte4)) {
        if (((int32_t)get_int8(byte4)) >= 0) {
            int32_t dword = buildInt(&fis, &state, get_int8(byte1), get_int8(byte2), get_int8(byte3), get_int8(byte4));
            return (MaybeResult_int32) { .tag = tag_Result_int32, .value = (union_MaybeResult_int32) { .Result_int32_v = (Result_int32) { .result = dword } } };
        } else {
            return (MaybeResult_int32) { .tag = tag_Failure_int32, .value = (union_MaybeResult_int32) { .Failure_int32_v = (Failure_int32) { .status = tag_DomainError } } };
        }
    } else {
        return (MaybeResult_int32) { .tag = tag_Failure_int32, .value = (union_MaybeResult_int32) { .Failure_int32_v = (Failure_int32) { .status = tag_ReadError } } };
    }
}

static MaybeResult_FileHeader maybeReadFileHeader(FileInputStream fis, State state) {
    bool skipSuccess = skipBytes(fis, 2, state);
    MaybeResult_int32 sizeRes = maybeReadDword(fis, state);
    if (skipSuccess) {
        skipSuccess = skipBytes(fis, 2 * 2, state);
    }
    MaybeResult_int32 offsetRes = maybeReadDword(fis, state);
    MaybeResult_Tuple_int32_int32 tmp = combine_int32_int32(sizeRes, offsetRes);
    if (!skipSuccess) {
        return (MaybeResult_FileHeader) { .tag = tag_Failure_FileHeader, .value = (union_MaybeResult_FileHeader) { .Failure_FileHeader_v = (Failure_FileHeader) { .status = tag_ReadError } } };
    } else if (tmp.tag == tag_Failure_Tuple_int32_int32) {
        return (MaybeResult_FileHeader) { .tag = tag_Failure_FileHeader, .value = (union_MaybeResult_FileHeader) { .Failure_FileHeader_v = (Failure_FileHeader) { .status = tmp.value.Failure_Tuple_int32_int32_v.status } } };
    } else if (tmp.tag == tag_Result_Tuple_int32_int32) {
        if ((14 <= tmp.value.Result_Tuple_int32_int32_v.result._1 && 14 + 40 <= tmp.value.Result_Tuple_int32_int32_v.result._2) && tmp.value.Result_Tuple_int32_int32_v.result._2 <= tmp.value.Result_Tuple_int32_int32_v.result._1) {
            return (MaybeResult_FileHeader) { .tag = tag_Result_FileHeader, .value = (union_MaybeResult_FileHeader) { .Result_FileHeader_v = (Result_FileHeader) { .result = (FileHeader) { .size = tmp.value.Result_Tuple_int32_int32_v.result._1, .offset = tmp.value.Result_Tuple_int32_int32_v.result._2 } } } };
        } else {
            return (MaybeResult_FileHeader) { .tag = tag_Failure_FileHeader, .value = (union_MaybeResult_FileHeader) { .Failure_FileHeader_v = (Failure_FileHeader) { .status = tag_InvalidFileHeaderError } } };
        }
    }
}

static MaybeResult_int32 maybeReadLong(FileInputStream fis, State state) {
    Option_int8 byte1 = tryReadByte(fis, state);
    Option_int8 byte2 = tryReadByte(fis, state);
    Option_int8 byte3 = tryReadByte(fis, state);
    Option_int8 byte4 = tryReadByte(fis, state);
    if (((isDefined_int8(byte1) && isDefined_int8(byte2)) && isDefined_int8(byte3)) && isDefined_int8(byte4)) {
        int32_t long_1 = buildInt_1(&fis, &state, get_int8(byte1), get_int8(byte2), get_int8(byte3), get_int8(byte4));
        return (MaybeResult_int32) { .tag = tag_Result_int32, .value = (union_MaybeResult_int32) { .Result_int32_v = (Result_int32) { .result = long_1 } } };
    } else {
        return (MaybeResult_int32) { .tag = tag_Failure_int32, .value = (union_MaybeResult_int32) { .Failure_int32_v = (Failure_int32) { .status = tag_ReadError } } };
    }
}

static MaybeResult_int32 maybeReadWord(FileInputStream fis, State state) {
    Option_int8 byte2 = tryReadByte(fis, state);
    Option_int8 byte1 = tryReadByte(fis, state);
    if (isDefined_int8(byte1) && isDefined_int8(byte2)) {
        return (MaybeResult_int32) { .tag = tag_Result_int32, .value = (union_MaybeResult_int32) { .Result_int32_v = (Result_int32) { .result = constructWord(get_int8(byte1), get_int8(byte2)) } } };
    } else {
        return (MaybeResult_int32) { .tag = tag_Failure_int32, .value = (union_MaybeResult_int32) { .Failure_int32_v = (Failure_int32) { .status = tag_ReadError } } };
    }
}

static STAINLESS_FUNC_PURE int32_t min(int32_t x, int32_t y) {
    if (x <= y) {
        return x;
    } else {
        return y;
    }
}

void* newState(void) {
  return NULL;
}


FILE* open(char* filename, void* unused) {
  FILE* this = fopen(filename, "r");
  /* this == NULL on failure */
  return this;
}
    


FILE* open_1(char* filename) {
  FILE* this = fopen(filename, "w");
  /* this == NULL on failure */
  return this;
}
    


void print(char* s) {
  printf("%s", s);
}
      


void print_1(int32_t x) {
  printf("%"PRIi32, x);
}
     


void print_2(char c) {
  printf("%c", c);
}
      

static void println(int32_t x) {
    print_1(x);
    println_1();
}

static void println_1(void) {
    print_2('\n');
}

static void println_2(char* s) {
    print(s);
    println_1();
}

static enum_Status process(FileInputStream fis, FileOutputStream fos, State state) {
    int32_t stainless_buffer_4[25] = { 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 };
    array_int32 norm_18 = (array_int32) { .data = stainless_buffer_4, .length = 25 };
    array_int32 norm_19 = norm_18;
    Kernel kernel = (Kernel) { .size = 5, .scale = 25, .kernel = norm_19 };
    MaybeResult_FileHeader fileHeaderRes = maybeReadFileHeader(fis, state);
    MaybeResult_BitmapHeader bitmapHeaderRes = maybeReadBitmapHeader(fis, state);
    enum_Status status;
    MaybeResult_Tuple_FileHeader_BitmapHeader tmp = combine_FileHeader_BitmapHeader(fileHeaderRes, bitmapHeaderRes);
    if (tmp.tag == tag_Failure_Tuple_FileHeader_BitmapHeader) {
        status = tmp.value.Failure_Tuple_FileHeader_BitmapHeader_v.status;
    } else if (tmp.tag == tag_Result_Tuple_FileHeader_BitmapHeader && tmp.value.Result_Tuple_FileHeader_BitmapHeader_v.result._1.size <= 14 + 40) {
        status = tag_CorruptedDataError;
    } else if (tmp.tag == tag_Result_Tuple_FileHeader_BitmapHeader) {
        log_1(tmp.value.Result_Tuple_FileHeader_BitmapHeader_v.result._1);
        log_2(tmp.value.Result_Tuple_FileHeader_BitmapHeader_v.result._2);
        int32_t toSkip = tmp.value.Result_Tuple_FileHeader_BitmapHeader_v.result._1.offset - (14 + 18);
        bool success = skipBytes(fis, toSkip, state);
        if (!success) {
            status = tag_CorruptedDataError;
        } else if (tmp.value.Result_Tuple_FileHeader_BitmapHeader_v.result._2.width > 512 || tmp.value.Result_Tuple_FileHeader_BitmapHeader_v.result._2.height > 512) {
            status = tag_ImageTooBigError;
        } else if (tmp.value.Result_Tuple_FileHeader_BitmapHeader_v.result._2.width * tmp.value.Result_Tuple_FileHeader_BitmapHeader_v.result._2.height > 512 * 512) {
            status = tag_ImageTooBigError;
        } else {
            Image image = (Image) { .r = { 0 }, .g = { 0 }, .b = { 0 }, .w = tmp.value.Result_Tuple_FileHeader_BitmapHeader_v.result._2.width, .h = tmp.value.Result_Tuple_FileHeader_BitmapHeader_v.result._2.height };
            enum_Status status_1 = loadImageData(fis, &image, state);
            if (isSuccess(status_1)) {
                status = processImage(&fis, &fos, &state, &kernel, &image);
            } else {
                status = status_1;
            }
        }
    }
    return status;
}

static enum_Status processImage(FileInputStream* fis, FileOutputStream* fos, State* state, Kernel* kernel, Image* src) {
    Image dest = (Image) { .r = { 0 }, .g = { 0 }, .b = { 0 }, .w = src->w, .h = src->h };
    apply(kernel, src, &dest);
    return saveImage(*fos, &dest);
}

static enum_Status saveImage(FileOutputStream fos, Image* image) {
    bool ok1 = writeFileHeader(&fos, image);
    if (!ok1) {
        return tag_WriteError;
    }
    bool ok2 = writeBitmapHeader(&fos, image);
    if (!ok2) {
        return tag_WriteError;
    }
    bool ok3 = writeImage(&fos, image);
    if (ok3) {
        return tag_Success;
    } else {
        return tag_WriteError;
    }
}

static bool skipBytes(FileInputStream fis, int32_t count, State state) {
    int32_t i = 0;
    bool success = true;
    while (success && i < count) {
        Option_int8 opt = tryReadByte(fis, state);
        success = isDefined_int8(opt);
        i = i + 1;
    }
    return success;
}

static int32_t statusCode(enum_Status s) {
    if (s == tag_Success) {
        println_2("success");
        return 0;
    } else if (s == tag_OpenError) {
        println_2("couldn't open file");
        return 1;
    } else if (s == tag_ReadError) {
        println_2("couldn't read some expected data");
        return 2;
    } else if (s == tag_DomainError) {
        println_2("integer out of range");
        return 3;
    } else if (s == tag_InvalidFileHeaderError) {
        println_2("file format unsupported");
        return 4;
    } else if (s == tag_InvalidBitmapHeaderError) {
        println_2("bitmap format unsupported");
        return 5;
    } else if (s == tag_CorruptedDataError) {
        println_2("the file appears to be corrupted");
        return 6;
    } else if (s == tag_ImageTooBigError) {
        println_2("the image is too big");
        return 7;
    } else if (s == tag_WriteError) {
        println_2("couldn't write image");
        return 8;
    } else if (s == tag_NotImplementedError) {
        println_2("not yet implemented");
        return 99;
    }
}

static Option_int8 tryReadByte(FileInputStream thiss, State state) {
    bool valid = true;
    int8_t res = impl(&thiss, &state, &valid);
    if (valid) {
        return (Option_int8) { .tag = tag_Some_int8, .value = (union_Option_int8) { .Some_int8_v = (Some_int8) { .v = res } } };
    } else {
        return (Option_int8) { .tag = tag_None_int8, .value = (union_Option_int8) { .None_int8_v = (None_int8) { .extra = 0 } } };
    }
}


bool write(FILE* this, int8_t x) {
  return fprintf(this, "%c", x) >= 0;
}
    

static bool writeBitmapHeader(FileOutputStream* fos, Image* image) {
    int32_t size = 40;
    int32_t w = image->w;
    int32_t h = image->h;
    int32_t planes = 1;
    int32_t bpp = 24;
    int32_t comp = 0;
    bool ok1 = writeDword(*fos, size);
    if (!ok1) {
        return false;
    }
    bool ok2 = writeLong(*fos, w);
    if (!ok2) {
        return false;
    }
    bool ok3 = writeLong(*fos, h);
    if (!ok3) {
        return false;
    }
    bool ok4 = writeWord(*fos, planes);
    if (!ok4) {
        return false;
    }
    bool ok5 = writeWord(*fos, bpp);
    if (!ok5) {
        return false;
    }
    bool ok6 = writeWord(*fos, comp);
    if (!ok6) {
        return false;
    }
    return writeBytes(*fos, 0, 22);
}

static bool writeBytes(FileOutputStream fos, int8_t byte, int32_t count) {
    FileOutputStream fos_0 = fos;
    int8_t byte_0 = byte;
    int32_t count_0 = count;
    while (true) {
        label_0: ;
            if (count_0 == 0) {
                return true;
            } else {
                bool ok1 = write(fos_0, byte_0);
                if (ok1) {
                    FileOutputStream fos_0_0 = fos_0;
                    int8_t byte_0_0 = byte_0;
                    int32_t count_0_0 = count_0 - 1;
                    fos_0 = fos_0_0;
                    byte_0 = byte_0_0;
                    count_0 = count_0_0;
                    goto label_0;
                } else {
                    return false;
                }
            };
    }
}

static bool writeDword(FileOutputStream fos, int32_t dword) {
    int8_t b4 = (int8_t)((int32_t)(((uint32_t)dword) >> 24));
    int8_t b3 = (int8_t)((int32_t)(((uint32_t)dword) >> 16));
    int8_t b2 = (int8_t)((int32_t)(((uint32_t)dword) >> 8));
    int8_t b1 = (int8_t)dword;
    bool ok1 = write(fos, b1);
    if (!ok1) {
        return false;
    }
    bool ok2 = write(fos, b2);
    if (!ok2) {
        return false;
    }
    bool ok3 = write(fos, b3);
    if (!ok3) {
        return false;
    }
    return write(fos, b4);
}

static bool writeFileHeader(FileOutputStream* fos, Image* image) {
    int32_t size = (14 + 40) + (image->w * image->h) * 3;
    int32_t reserved = 0;
    int32_t offset = 14 + 40;
    bool ok1 = write(*fos, (int8_t)66);
    if (!ok1) {
        return false;
    }
    bool ok2 = write(*fos, (int8_t)77);
    if (!ok2) {
        return false;
    }
    bool ok3 = writeDword(*fos, size);
    if (!ok3) {
        return false;
    }
    bool ok4 = writeWord(*fos, reserved);
    if (!ok4) {
        return false;
    }
    bool ok5 = writeWord(*fos, reserved);
    if (!ok5) {
        return false;
    }
    return writeDword(*fos, offset);
}

static bool writeImage(FileOutputStream* fos, Image* image) {
    int32_t count = image->w * image->h;
    int32_t i = 0;
    bool success = true;
    while (success && i < count) {
        bool ok1 = write(*fos, image->r[i]);
        bool ok2;
        if (ok1) {
            ok2 = write(*fos, image->g[i]);
        } else {
            ok2 = false;
        }
        bool ok3;
        if (ok2) {
            ok3 = write(*fos, image->b[i]);
        } else {
            ok3 = false;
        }
        success = ok3;
        i = i + 1;
    }
    return success;
}

static bool writeLong(FileOutputStream fos, int32_t long_1) {
    int8_t b4 = (int8_t)((int32_t)(((uint32_t)long_1) >> 24));
    int8_t b3 = (int8_t)((int32_t)(((uint32_t)long_1) >> 16));
    int8_t b2 = (int8_t)((int32_t)(((uint32_t)long_1) >> 8));
    int8_t b1 = (int8_t)long_1;
    bool ok1 = write(fos, b1);
    if (!ok1) {
        return false;
    }
    bool ok2 = write(fos, b2);
    if (!ok2) {
        return false;
    }
    bool ok3 = write(fos, b3);
    if (!ok3) {
        return false;
    }
    return write(fos, b4);
}

static bool writeWord(FileOutputStream fos, int32_t word) {
    Tuple_int8_int8 tmp = destructWord(word);
    Tuple_int8_int8 _2_ = tmp;
    int8_t b1 = _2_._1;
    int8_t b2 = _2_._2;
    bool ok1 = write(fos, b2);
    if (!ok1) {
        return false;
    }
    return write(fos, b1);
}
