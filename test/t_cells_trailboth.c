// t_cells_trailboth.c — gap 2 (Fable 2026-10-20): malloc(sizeof(struct M) +
// 2 * sizeof(fn)) is 2 * sizeof(struct M), so the extent rule reads an
// array of two M; M ends in `fn secs[1]` (the pre-C99 struct hack), so
// the index may also run on past secs[0] into the data after it. Both
// readings are legal C: the index on secs reaches every element offset of
// M its stride lands on (n and secs), so s[1] = bfn (element 1's n under
// the array reading) is seen. A premise row names the site.
#include <stdlib.h>
typedef void (*fn)(void);
struct M { long n; fn secs[1]; };
void afn(void) {}
void bfn(void) {}
void cfn(void) {}
int main(int argc, char **argv) {
  struct M *m = malloc(sizeof(struct M) + 2 * sizeof(fn));
  m->n = 2;
  fn *s = m->secs;
  s[0] = afn;
  s[1] = bfn;
  s[2] = cfn;
  m->secs[argc](); // CHECK: afn bfn cfn
  return 0;
}
// LOG: Cells: trailing \[1\] arrays \(gap 2\): 1 indexes on an array of T reach every element offset
