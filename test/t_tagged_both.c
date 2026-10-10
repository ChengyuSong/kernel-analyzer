// t_tagged_both.c — plan 3.51: a read tested on two tags admits the
// writers both tests admit (the intersection of the two keyings).
// PAIR: struct.S+8 by +4
#include <stdlib.h>
struct S { int a; int b; void (*fp)(void); };
void f1(void) {}
void f2(void) {}
void f3(void) {}
void w1(struct S *s) { s->fp = f1; s->a = 1; s->b = 1; }
void w2(struct S *s) { s->fp = f2; s->a = 2; s->b = 1; }
void w3(struct S *s) { s->fp = f3; s->a = 1; s->b = 2; }
void use(struct S *s) {
  if (s->a == 1)
    if (s->b == 1)
      s->fp(); // CHECK: f1 CHECK-NOT: f2 f3
}
int main(int argc, char **argv) {
  struct S *s = malloc(sizeof *s);
  if (argc > 2) w1(s); else if (argc > 1) w2(s); else w3(s);
  use(s);
  return 0;
}
