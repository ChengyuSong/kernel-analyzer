// t_cells_union_member_by_step_clash.c — item 0 (Fable 2026-10-18): the
// address steps through member i's struct, but the value read there is
// used as a def section (a call taking void *section's type, struct sec *):
// the step and the value use name different members, so the access is
// ambiguous, with no precedence.
// LOG: UnionKeys: .* by the member struct their address steps through \(1 made ambiguous
#include <stdlib.h>
struct sec { int id; };
struct ent {
  int type;
  union {
    struct { struct ent *next; struct ent *link; const char *warning; } i;
    struct { struct ent *next; struct sec *section; long value; } def;
  } u;
};
int use_sec(struct sec *s) { return s ? s->id : 0; }
int peek(struct ent *e) { return use_sec((struct sec *)e->u.i.link); }
int main(void) {
  struct ent *e = calloc(1, sizeof *e);
  e->u.i.link = calloc(1, sizeof *e);
  return peek(e);
}
