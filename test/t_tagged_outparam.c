// t_tagged_outparam.c — plan 3.51, Mem.u: a content write through an out
// parameter (sqlite3's `sqlite3Atoi64(z, &pMem->u.i, ..); MemSetTypeFlag(
// pMem, MEM_Int)`). atoi64 writes through its parameter on every path, so
// the call is a writer of u and the flags write after it is a co-write,
// not an in-place retag of whatever u held (the frame pointer).
// PAIR: struct.M+0 by +8
#include <stdlib.h>
#define M_INT 1
#define M_FRAME 2
#define M_TYPE 3
struct F { void (*fn)(void); };
struct G { void (*fn)(void); };
struct M { union { long i; struct F *pFrame; } u; int flags; struct M *db; };
void ffn(void) {}
void gfn(void) {}
static void atoi64(const char *z, long *p) { *p = strtol(z, 0, 10); }
void setFrame(struct M *m, struct F *f) { m->u.pFrame = f; m->flags = M_FRAME; }
void setInt(struct M *m, struct G *g) { m->u.i = (long)g; m->flags = M_INT; }
void toInt(struct M *m, const char *z) { atoi64(z, &m->u.i); m->flags = (m->flags & ~M_TYPE) | M_INT; }
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
  if (argc > 2) setInt(m, g);
  else { setFrame(m, f); toInt(m, argv[1]); }
  useInt(m);
  return 0;
}
