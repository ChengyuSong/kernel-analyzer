// t_cells_freshinit_int.c — a pointer-carrying integer stored through the
// fresh pointer is an init store (Fable 2026-10-14). The confirmer passed
// every non-pointer stored value as data, so `c->addr = (unsigned long)g`
// was dropped: both wrappers were promoted with no atom and the read lost
// g (and, at -O2, h). The confirmer now uses graph build's int-store rule:
// a constant ptrtoint is classified as its pointer (a ptrtoint instruction
// is a side effect R3 refuses); any other carrier as itself.
// CFLAGS: -O2
// LOG: ConfirmFresh: LINE create FRESH BODY # ST\(\*ret@8<-g\)
// LOG: ConfirmFresh: LINE create2 FRESH BODY # ST\(\*ret@8<-h\)
typedef void (*fn)(void);
void *calloc(unsigned long, unsigned long);
struct outer { long a; unsigned long addr; };
void g(void) {}
void h(void) {}
fn sink;
__attribute__((noinline)) static struct outer *create(void) {
  struct outer *c = calloc(1, sizeof *c);
  if (c) c->addr = (unsigned long)g;
  return c;
}
__attribute__((noinline)) static struct outer *create2(fn f) {
  struct outer *c = calloc(1, sizeof *c);
  if (c) c->addr = (unsigned long)f;
  return c;
}
int main(int argc, char **argv) {
  sink = h;
  struct outer *a = create();
  struct outer *b = create2(h);
  ((fn)(argc > 1 ? a->addr : b->addr))(); // CHECK: g h
  return 0;
}
