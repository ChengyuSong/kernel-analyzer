// Rule 4 (plan 3.53): a copy between storage of one label moves cell to
// cell, union members included; a copy into bytes and back out of them
// (a pun) still carries the pointer, and each is a relay row.
#include <stdlib.h>
#include <string.h>
union nm { char name[8]; struct { long zeroes, offset; } n; void (*ptr[2])(void); };
struct sym { void (*a)(void); union nm u; void (*b)(void); };
void fa(void) {}
void fb(void) {}
void fe(void) {}
void ff(void) {}
int main(void) {
  struct sym *s = malloc(sizeof *s);
  s->a = fa; s->b = fb; s->u.ptr[0] = fe; s->u.ptr[1] = ff;
  struct sym *t = malloc(sizeof *t);
  memcpy(t, s, sizeof *s);
  struct sym u;
  memcpy(&u, t, sizeof u);
  t->u.ptr[0]();
  u.u.ptr[1]();
  char buf[9];
  memcpy(buf, u.u.name, 8);
  void (*g)(void);
  memcpy(&g, buf, sizeof g);
  g(); // CHECK: fe
  return 0;
}
