// t_cells_allocsite.c — an object's Value is its allocation site (Fable
// 2026-10-14). The global dedup merges each single-callsite formal with
// its actual, and union by rank chose the formals' class (mid's and
// leaf's, each already merged with touch's zero-offset GEP) to represent
// the malloc result. Objects were seeded from the representative's
// value: the malloc object was named by `mid`'s formal and labeled by its
// first typed use (the kernel's azx bus object labeled hdac_bus, its
// embedded struct). The object is now seeded by the site's own node.
// CFLAGS: -O1
// LOG: allocation sites: 1 seeded by their own node under a class representative that is not the site \(formal 1\)
// LOG: object main::call malloc \[struct\.outer, 56 B\]
typedef void (*fn)(void);
void *malloc(unsigned long);
struct inner { struct inner *next; long a; };
struct outer { struct inner bus; fn ops; long more[4]; };
void g(void) {}
void h(void) {}
fn sink;
__attribute__((noinline)) void touch(struct inner *b) { b->next = b; }
__attribute__((noinline)) void leaf(struct inner *b) { touch(b); b->a = 1; }
__attribute__((noinline)) void mid(struct inner *b) { touch(b); leaf(b); }
__attribute__((noinline)) void run(struct outer *c) {
  c->ops(); // CHECK: g CHECK-NOT: h
}
int main(void) {
  struct outer *s = malloc(sizeof *s);
  mid(&s->bus);
  s->ops = g;
  sink = h;
  run(s);
  return 0;
}
