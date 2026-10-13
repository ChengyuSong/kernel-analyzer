// t_cells_wrapsize.c — plan 3.53 ruling B: a fresh wrapper's size is the
// term of its inner allocation (here the constant sizeof(struct S)),
// evaluated at the call, never the call's integer arguments by position:
// new_obj(ctx, code) passes an opcode (100: larger than S, not a multiple),
// which read as a size made the object "S plus trailing data".
// LOG: extents: 0 arrays by size, 1 one by size, 0 header \+ data by size
#include <stdlib.h>
typedef void (*fn)(void);
struct S { long a; fn f; long b; };
void sfn(void) {}
struct S *new_obj(void *ctx, int code) {
  struct S *p = malloc(sizeof(struct S));
  p->a = code;
  return p;
}
int main(int argc, char **argv) {
  struct S *s = new_obj(0, 100);
  s->f = sfn;
  s->f(); // CHECK: sfn
  return 0;
}
