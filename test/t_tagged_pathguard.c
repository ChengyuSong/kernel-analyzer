// t_tagged_pathguard.c — plan 3.51 ruling (i), per-path guards (sqlite3's
// OP_MustBeInt): `if ((flags & INT) == 0) atoi64(z, &u.i);` then
// `flags = (flags & ~TYPE) | INT`. One path writes u (a co-write); the
// other already had INT, so its guard is the test's false edge: the retag
// applies only to INT tags, and the frame writer (FRAME) is not retagged.
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
void mustBeInt(struct M *m, const char *z) {
  if ((m->flags & M_INT) == 0) atoi64(z, &m->u.i);
  m->flags = (m->flags & ~M_TYPE) | M_INT;
}
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
  if (argc > 2) setInt(m, g); else setFrame(m, f);
  mustBeInt(m, argv[1]);
  useInt(m);
  return 0;
}
