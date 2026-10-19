// t_cells_union_member_by_step.c — item 0 (Fable 2026-10-18, a gap): the
// read of e->u.i.link is only copied (memcpy's source), so its value use
// names no member; its address steps through member i's struct, whose
// layout {ptr, ptr, ptr} only i has (def is {ptr, long, ptr}): the read is
// member i, and so is the write of e->u.i.link in main, whose calloc value
// names none (at the commit before: no member, "?", both).
// LOG: UnionKeys: .* 2 by the member struct their address steps through \(0 made ambiguous
#include <stdlib.h>
#include <string.h>
struct ent {
  int type;
  union {
    struct { struct ent *next; struct ent *link; const char *warning; } i;
    struct { struct ent *next; long value; void *section; } def;
  } u;
};
struct ent *g;
void copy_link(struct ent *e, struct ent *out) {
  if (e->type == 7) memcpy(out, e->u.i.link, sizeof *out);
}
int main(void) {
  struct ent *e = calloc(1, sizeof *e), *o = calloc(1, sizeof *o);
  e->type = 7;
  e->u.i.link = calloc(1, sizeof *e);
  copy_link(e, o);
  g = o;
  return 0;
}
