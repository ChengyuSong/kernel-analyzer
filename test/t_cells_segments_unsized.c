// t_cells_segments_unsized.c — row (3) (plan 3.53, Fable 2026-10-13): the
// 1b segment extension applies whether or not the block's size is known.
// sqlite3Fts3Incrmerge: sqlite3_malloc(808), whose size term dies at
// sqlite3Malloc's indirect xMalloc (unknown, ruling B), then
// `pFilter = (Fts3SegFilter *)&pWriter[1]; pCsr = (...)&pFilter[1]`. Here
// the wrapper (named for its func_summaries.txt row, FRESH BODY) allocates
// through a function pointer, so the size is unknown; the site's casts at
// constant offsets still declare B and C, and a variable index on A's last
// array field stays in A (B and C are labeled segments; the remainder
// after C stays unknown and holds nothing).
// LOG: [1-9][0-9]* of them segments the site declares
#include <stdlib.h>
#include <string.h>
typedef void (*fn)(void);
struct A { long n; fn arr[2]; };
struct B { int k; fn fb; long pad; };
struct C { fn fc; long m[3]; };
void afn(void) {}
void bfn(void) {}
void cfn(void) {}
void *(*xMalloc)(size_t) = malloc;
__attribute__((noinline)) void *sqlite3Malloc(size_t n) { return xMalloc(n); }
int main(int argc, char **argv) {
  size_t n = sizeof(struct A) + sizeof(struct B) + sizeof(struct C);
  struct A *a = sqlite3Malloc(n);
  memset(a, 0, n);
  struct B *b = (struct B *)&a[1];
  struct C *c = (struct C *)&b[1];
  a->arr[0] = afn;
  b->fb = bfn;
  c->fc = cfn;
  a->arr[argc](); // CHECK: afn CHECK-NOT: bfn cfn
  return 0;
}
