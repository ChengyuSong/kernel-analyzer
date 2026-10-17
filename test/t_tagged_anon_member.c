// t_tagged_anon_member.c — plan 3.51, Fable 2026-10-16: the object of an
// access is the one its name belongs to. A field inside an anonymous member
// (binutils' bfd_link_hash_entry.u.i.link) is named by the enclosing named
// struct and its offset (accessSlot), but its object was the anonymous
// member's address (&s->m: the base of the access's own GEP), never the
// object the tag store names (s), so no writer co-wrote its tag and the
// pair never formed. Now the object steps through anonymous structs to the
// enclosing named struct's base, by the same walk as the name.
// PAIR: struct.S+16 by +8
#include <stdlib.h>
struct S { void *name; int a; struct { void (*fp)(void); } m; };
void f1(void) {}
void f2(void) {}
void w1(struct S *s) { s->m.fp = f1; s->a = 1; }
void w2(struct S *s) { s->m.fp = f2; s->a = 2; }
void use(struct S *s) {
  if (s->a == 1)
    s->m.fp(); // CHECK: f1 CHECK-NOT: f2
}
int main(int argc, char **argv) {
  (void)argv;
  struct S *s = malloc(sizeof *s);
  if (argc > 1) w1(s); else w2(s);
  use(s);
  return 0;
}
