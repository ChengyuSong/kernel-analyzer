// t_cells_union_member_layout.c — a union whose members are structs (plan
// 3.51 (2), Fable 2026-10-16): binutils' bfd_link_hash_entry.u is
// { undef, def, i, c }, each a struct, and an access is to a field inside
// one (u.i.link, u.def.section). The union census typed an access by
// comparing its debug type with each member's, so none was typed ("0
// used", reported as "one member used"). Now an access at byte o of the
// union with debug type T is of member m when m's layout holds a field of
// type T at o (nested structs, arrays): u.a.name (char *) and u.b.val
// (long) are typed by member layout; u.a.next, at +0 of both members, is a
// field several members share: not typed, its own class. Debug info only.
// KAFLAGS: --cfl-census-unions
// LOG: UNION s.u \(2 members, 2 used\).*by member layout \(debug info\): writes 2, reads 2 typed; a field several members share \(not typed\): writes 1, reads 0
#include <stdlib.h>
struct s {
  int kind;
  union {
    struct { void *next; char *name; } a;
    struct { void *next; long val; } b;
  } u;
};
int main(int argc, char **argv) {
  struct s *x = malloc(sizeof *x), *y = malloc(sizeof *y);
  char *nm = argv[0];
  long v = argc;
  x->kind = 1;
  x->u.a.name = nm;
  void *p = y;
  x->u.a.next = p;
  y->kind = 2;
  y->u.b.val = v;
  char *n2 = x->u.a.name;
  long v2 = y->u.b.val;
  return (int)(n2 != NULL) + (int)v2;
}
