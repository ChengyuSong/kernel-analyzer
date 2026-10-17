// t_cells_report_node_kinds.c — every solver node is described by its kind
// (Fable 2026-10-17: 9,387 undescribed nodes held 82% of a tiffsplit-O3
// stop's facts). The node-facts dump (--cfl-cell-node-facts, here to
// stdout) and the facts-by-node-class line name every node; no node is a
// "store collector" by default or of no kind. A union slot keyed in both
// schemes gives content, key and hub nodes.
// KAFLAGS: --cfl-cell-node-facts=/dev/stdout
// LOG: Cells: facts by node class: .*solver content
// LOG: ^content struct.S\+16 .*[[:space:]][0-9]+$
// NOLOG: store collector|<no kind|<other>
#include <stdlib.h>
struct S {
  int kind;
  union {
    struct { void *next; void (*fp)(void); } a;
    struct { void *next; char *s; } b;
  } u;
};
void f1(void) {}
void w1(struct S *s) { s->kind = 1; s->u.a.fp = f1; }
void w2(struct S *s, char *str) { s->kind = 2; s->u.b.s = str; }
void use(struct S *s) {
  if (s->kind == 1)
    s->u.a.fp(); // CHECK: f1
}
int main(int argc, char **argv) {
  struct S *s = malloc(sizeof *s);
  if (argc > 1) w1(s); else w2(s, argv[0]);
  use(s);
  return 0;
}
