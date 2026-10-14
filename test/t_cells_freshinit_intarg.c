// t_cells_freshinit_intarg.c — an integer formal stored through the fresh
// pointer is an argument atom (Fable 2026-10-14). The formal carries a
// pointer from its caller (graph build's int-store rule); the confirmer
// passed it as data, promoted create3 with no atom, and the read found
// nothing in both configurations. At -O0 the stored value is the reload
// of the spilled formal, resolved through its slot. An integer computed
// from the formal (cflow's depmap_alloc: `dmap->rowlen = size`) has the
// formal as its source: casts, arithmetic, joins and slots are followed;
// only a load from memory or a call refuses.
// CFLAGS: -O0
// LOG: ConfirmFresh: LINE create3 FRESH ST\(\*ret<-arg0\) ST\(\*ret@8<-arg0\) BODY
typedef void (*fn)(void);
void *calloc(unsigned long, unsigned long);
struct outer { long a; unsigned long addr; };
void g(void) {}
void k(void) {}
fn sink;
__attribute__((noinline)) static struct outer *create3(unsigned long n) {
  struct outer *c = calloc(1, sizeof *c);
  if (c) {
    c->a = (long)((n + 7) / 8); // arithmetic on the formal: the same source
    c->addr = n;
  }
  return c;
}
int main(int argc, char **argv) {
  struct outer *d = create3(argc > 2 ? (unsigned long)k : (unsigned long)g);
  ((fn)d->addr)(); // CHECK: g k
  return 0;
}
