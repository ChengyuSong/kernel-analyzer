// t_cells_readings.c — A5a (Fable 2026-10-21): a constant size that is k x
// the label's and also a container's (struct cont and struct other embed
// struct head at offset 0, 32 = 2 x 16) has two readings; the site's own
// receivers select. mk: the label comes from the inlined init_head's formal
// (struct head *), the receiver `c` in mk's own frame declares struct cont:
// named struct cont. mk2: the receiver is a void *: no declaration, a
// conflict, unlabeled. mk3: the receiver declares struct head, the label
// itself, in both readings: selects nothing, a conflict.
// CFLAGS: -O2
// LOG: 2 whose size is k x their label and a container's, no receiver naming one, A5; 0 kmem_cache_\* objects whose cache size several or no structs embedding their label have, A5b\), 0 relabeled to the container their size names, 1 to the container their receiver declares where the size is k x the label \(A5\)
#include <stdlib.h>
struct head { long a; long b; };
struct cont { struct head h; void (*f)(void); long pad; };
struct other { struct head h; void (*g)(void); long pad; };
void fa(void) {}
void fb(void) {}
static void init_head(struct head *h) { h->a = 1; h->b = 2; }
struct cont *gc;
struct other *go;
void *gv;
__attribute__((noinline)) void mk(void) {
  struct cont *c = malloc(sizeof *c);
  init_head(&c->h);
  gc = c;
}
__attribute__((noinline)) void mk2(void) {
  void *v = malloc(sizeof(struct cont));
  init_head(v);
  gv = v;
}
__attribute__((noinline)) void mk3(void) {
  struct head *h = malloc(sizeof(struct other));
  init_head(h);
  go = (struct other *)h;
}
__attribute__((noinline)) void set(void) { gc->f = fa; go->g = fb; }
int main(void) {
  mk(); mk2(); mk3(); set();
  gc->f(); // CHECK: fa CHECK-NOT: fb
  go->g();
  return 0;
}
