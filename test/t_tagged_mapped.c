// t_tagged_mapped.c — plan 3.51 last-writer rule, soundness: a writer
// whose only later tag write maps the tag it found (flags |= 2) takes
// that tag as the map's input, read under it or not. putR's content is
// read under flags 1|2 = 3, so the read tested on bit 0 admits it.
// PAIR: struct.M+8 by +0
#include <stdlib.h>
struct R { void (*fn)(void); };
struct B { void (*fn)(void); };
struct C { void (*fn)(void); };
struct M { int flags; void *z; };
void rfn(void) {}
void bfn(void) {}
void cfn(void) {}
void init(struct M *m, struct B *b) { m->z = b; m->flags = 1; }
void putR(struct M *m, struct R *r) { m->z = r; m->flags |= 2; }
void putC(struct M *m, struct C *c) { m->z = c; m->flags = 4; }
void use(struct M *m) {
  if (m->flags & 1) {
    struct R *r = m->z;
    r->fn(); // CHECK: rfn bfn CHECK-NOT: cfn
  }
}
int main(int argc, char **argv) {
  struct M *m = malloc(sizeof *m);
  struct R *r = malloc(sizeof *r);
  struct B *b = malloc(sizeof *b);
  struct C *c = malloc(sizeof *c);
  r->fn = rfn;
  b->fn = bfn;
  c->fn = cfn;
  init(m, b);
  if (argc > 1) putR(m, r); else if (argc > 2) putC(m, c);
  use(m);
  return 0;
}
