// t_cells_tag_union_census.c — plan 3.51, Fable 2026-10-16: a tag over a union
// whose members the union census types (by member layout). The census keys
// the union slot by the union's own offset (struct.S+8#a), the tag pair keys
// the field it tests (struct.S+16); the tag keying dropped census keys only
// under the field's own prefix (S+16#), so the census keys stayed and the
// pair was refused ("an access already keyed otherwise"). Now the census
// keys of the union slot holding the field are dropped for the accesses over
// the field's bytes, the tag keys go in, and u.a.next / u.b.next (other
// bytes) keep their member keys.
// LOG: TaggedFields:   KEYS struct.S\+16 by \+0: 1 reads keyed
// NOLOG: already keyed otherwise
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
