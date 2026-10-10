// t_tagged_union.c — plan 3.51, Mem.u: a union member read as one pointer
// field. Every access of any width is an access of the one field; an
// integer write is a writer (sqlite3's u.i next to u.pFrame), and a
// pointer-width integer read under the integer tag admits only the
// integer writers, so the frame's function never reaches it. The union
// is at offset 0, as Mem.u is; db (Mem.db) is a pointer field past it.
// PAIR: struct.M+0 by +8
#include <stdlib.h>
#define M_INT 1
#define M_FRAME 2
struct F { void (*fn)(void); };
struct G { void (*fn)(void); };
struct M { union { long i; struct F *pFrame; } u; int flags; struct M *db; };
void ffn(void) {}
void gfn(void) {}
void setFrame(struct M *m, struct F *f) { m->u.pFrame = f; m->flags = M_FRAME; }
void setInt(struct M *m, struct G *g) { m->u.i = (long)g; m->flags = M_INT; }
void useInt(struct M *m) {
  if (m->flags & M_INT) {
    struct G *g = (struct G *)m->u.i;
    g->fn(); // CHECK: gfn CHECK-NOT: ffn
  }
}
int main(int argc, char **argv) {
  struct M *m = malloc(sizeof *m);
  struct F *f = malloc(sizeof *f);
  struct G *g = malloc(sizeof *g);
  m->db = m;
  f->fn = ffn;
  g->fn = gfn;
  if (argc > 1) setFrame(m, f); else setInt(m, g);
  useInt(m);
  return 0;
}
