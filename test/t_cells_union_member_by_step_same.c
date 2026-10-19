// t_cells_union_member_by_step_same.c — item 0 (Fable 2026-10-18): as
// t_cells_union_member_by_step.c, but def has i's layout {ptr, ptr, ptr}:
// two members match the struct the read steps through, so it types
// nothing, as before (matched by layout, never by the IR name).
// LOG: UnionKeys: .* 0 by the member struct their address steps through \(0 made ambiguous
#include <stdlib.h>
#include <string.h>
struct ent {
  int type;
  union {
    struct { struct ent *next; struct ent *link; const char *warning; } i;
    struct { struct ent *next; struct ent *value; void *section; } def;
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
