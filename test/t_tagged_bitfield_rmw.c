// t_tagged_bitfield_rmw.c — plan 3.51 (3), Fable 2026-10-16: a tag beside
// another bitfield in one word. binutils' bfd_link_hash_entry keeps
// `type:8` and `non_ir_ref_dynamic:1` together, and elflink.c:5250's
// `h->root.non_ir_ref_dynamic = x` stores `(old & -513) | ((x & 1) << 9)`
// (here bit 8): the flag bit only, the tag's bits unchanged. As there, the
// tag word is not at +0 (clang writes a bitfield word at +0 through the
// struct pointer itself, with no GEP, which names nothing). The evaluator could not
// evaluate the inserted bit (x is no constant): the retag was unevaluable,
// the tag widened and the pair unkeyed. Now a value it cannot evaluate by
// its operands gets LLVM's known bits (the flag bit free, the rest zero),
// so the retag keeps every tag, and the pair keys.
// PAIR: struct.S+16 by +8
#include <stdlib.h>
struct S { void *name; unsigned a : 8; unsigned flag : 1; void (*fp)(void); };
void f1(void) {}
void f2(void) {}
void w1(struct S *s) { s->fp = f1; s->a = 1; }
void w2(struct S *s) { s->fp = f2; s->a = 2; }
__attribute__((noinline)) void setflag(struct S *s, int x) { s->flag = x; }
void use(struct S *s) {
  if (s->a == 1)
    s->fp(); // CHECK: f1 CHECK-NOT: f2
}
int main(int argc, char **argv) {
  struct S *s = malloc(sizeof *s);
  if (argc > 1) w1(s); else w2(s);
  setflag(s, rand()); // a value the evaluator cannot evaluate
  use(s);
  return 0;
}
