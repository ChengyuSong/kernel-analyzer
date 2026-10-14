// t_cells_structarr.c — a declared segment the site indexes by a stride of
// its struct is an array of it without an extent, the struct analogue of
// the scalar and pointer-slot array clauses (plan 3.53, Fable 2026-10-13,
// sqlite3 #515). sqlite3's OP_Program block: sqlite3DbMallocZero(
// ROUND8(sizeof(VdbeFrame)) + nMem * sizeof(Mem) + nCsr * sizeof(VdbeCursor
// *) + ...), its segment at 128 cast to Mem (VdbeFrameMem) and indexed
// (`pEnd = &VdbeFrameMem(pFrame)[n]`), walked by a cursor. The slot
// receiving the result (pFrame) is assigned elsewhere too; the reloads only
// the allocation's store reaches declare the segment. The cursor slots
// after the array (`p->apCsr = (VdbeCursor **)&aMem[nMem]`, a field
// receiver, so not a carve; a pointer stride at a variable offset past the
// array) fold into Mem's element cells (rule (b), flow kept: cfn reaches
// xDel); xA and xDel stay apart.
// LOG: [1-9][0-9]* of them segments the site declares \([1-9][0-9]* arrays of their struct
// LOG: [1-9][0-9]* of them have reloads only their own store reaches \(followed for segments\)
// LOG: [1-9][0-9]* other strides over a segment array of a struct
// NOLOG: tail@152
#include <stdlib.h>
#include <string.h>
typedef void (*fn)(void);
struct Mem { fn xA; int flags; fn xDel; };
struct Frame { struct Frame *parent; int nMem; fn hook; fn *apCsr; long pad[12]; };
#define FRAMEMEM(p) ((struct Mem *)&((char *)(p))[sizeof(struct Frame)])
void mfn(void) {}
void afn(void) {}
void hfn(void) {}
void cfn(void) {}
struct Frame *frames;
void *(*xMalloc)(size_t) = malloc;
__attribute__((noinline)) void *sqlite3Malloc(size_t n) { return xMalloc(n); }
int main(int argc, char **argv) {
  int nMem = argc + 2;
  struct Frame *pFrame = frames;
  if (argc > 7) {
    pFrame = pFrame->parent;
  } else {
    size_t n = sizeof(struct Frame) + nMem * sizeof(struct Mem) + argc * sizeof(fn);
    pFrame = sqlite3Malloc(n);
    memset(pFrame, 0, n);
    struct Mem *pEnd = &FRAMEMEM(pFrame)[nMem];
    for (struct Mem *pMem = FRAMEMEM(pFrame); pMem != pEnd; pMem++) {
      pMem->xA = afn;
      pMem->flags = 0;
      pMem->xDel = mfn;
    }
    pFrame->hook = hfn;
    frames = pFrame;
  }
  struct Mem *aMem = FRAMEMEM(pFrame);
  pFrame->apCsr = (fn *)&aMem[nMem]; // a field receiver: not a carve
  pFrame->apCsr[argc] = cfn;
  aMem[argc].xDel(); // CHECK: mfn cfn CHECK-NOT: afn hfn
  return 0;
}
