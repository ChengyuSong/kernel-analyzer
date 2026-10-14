// t_cells_freshinit.c — an init atom carries the byte offset of its store
// from the fresh pointer (Fable 2026-10-14). A promoted alloc-init
// wrapper's atoms ST(*ret <- @g), ST(*ret <- argI) were built at offset 0,
// and under cells the allocation inside the kept body has no object (the
// outer FRESH stands for it), so the atoms are the stores' only effect:
// `c->ops` read nothing. A helper's stores compose with the offset of the
// helper's object inside the fresh one. A stored loaded pointer is no
// atom kind: that wrapper is refused, not promoted with the store dropped.
// CFLAGS: -O2
// LOG: ConfirmFresh: LINE create_g FRESH BODY # ST\(\*ret@16<-g\)
// LOG: ConfirmFresh: LINE create_f FRESH BODY # ST\(\*ret@40<-f1\)
// LOG: ConfirmFresh ESCAPE: create_loaded \[init-from-load\]
// NOLOG: ConfirmFresh: LINE create_loaded
typedef void (*fn)(void);
void *calloc(unsigned long, unsigned long);
struct sub { long tag; fn cb; };
struct outer { long a, b; fn ops; long c; struct sub s; };
void g(void) {}
void f1(void) {}
void h(void) {}
fn sink;
fn *table;
__attribute__((noinline)) static struct outer *create_g(void) {
  struct outer *c = calloc(1, sizeof *c);
  if (c) c->ops = g;
  return c;
}
__attribute__((noinline)) static void set_cb(struct sub *s, fn f) { s->tag = 1; s->cb = f; }
__attribute__((noinline)) static struct outer *create_f(fn f) {
  struct outer *c = calloc(1, sizeof *c);
  if (c) set_cb(&c->s, f);
  return c;
}
__attribute__((noinline)) static struct outer *create_loaded(void) {
  struct outer *c = calloc(1, sizeof *c);
  if (c) c->ops = *table;
  return c;
}
int main(int argc, char **argv) {
  fn local[1] = {h};
  table = local;
  sink = h;
  struct outer *a = create_g();
  struct outer *b = create_f(f1);
  struct outer *d = create_loaded();
  fn x = argc > 1 ? a->ops : b->s.cb;
  x(); // CHECK: g f1 CHECK-NOT: h
  d->ops();
  return 0;
}
