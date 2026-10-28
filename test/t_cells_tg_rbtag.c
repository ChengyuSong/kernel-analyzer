// t_cells_tg_rbtag.c — a pointer tag set by a variable whose known bits lie
// below 8 is a tag, not an offset (TG, Fable 2026-10-27): the kernel's
// rb_node keeps its parent pointer and colour in one word, and
// rb_replace_node sets a child's parent_color = (long)new | (old & 1).
// Before TG the or's operand was not a constant, so the ptrtoint was
// "arith-var" and the stored parent went any-offset (every cell of every
// node holder): the dispatch in run_a read A's fn and also B's fn, at +8 of
// a B whose node is at +16 (before TG: fa fb). Now (old & 1) has its known
// bits below 8, the or sets a tag and the parent keeps its offset: the
// confluence through replace_node's formal still holds both nodes, and
// container_of(-16) of B's node is B's x, which holds no function. One
// CHECK per case (cells-cases.sh): the dispatch in run_a.
// CFLAGS: -O2
// LOG: 1 pointer tag sets by a variable whose known bits lie below 8 \(TG\); 0 variable or/xor refused: bits unbounded
// LOG: TG tag set at replace_node t_cells_tg_rbtag.c:[0-9]+ %
// LOG: ConstraintGraph: iteration 0: .* 0 field-any\)
struct rbn { unsigned long pc; struct rbn *l, *r; };
struct A { void (*fn)(void); long pad; struct rbn node; };
struct B { long x; void (*fn)(void); struct rbn node; };
__attribute__((noinline)) void fa(void) {}
__attribute__((noinline)) void fb(void) {}
__attribute__((noinline)) void replace_node(struct rbn *victim, struct rbn *new) {
  *new = *victim;
  if (victim->l)
    victim->l->pc = (unsigned long)new | (victim->l->pc & 1);
}
__attribute__((noinline)) struct rbn *parent(struct rbn *n) {
  return (struct rbn *)(n->pc & ~3UL);
}
#define container_of(p, T, m) ((T *)((char *)(p) - __builtin_offsetof(T, m)))
__attribute__((noinline)) void run_a(struct A *c) {
  struct A *p = container_of(parent(&c->node), struct A, node);
  p->fn(); // CHECK: fa CHECK-NOT: fb
}
__attribute__((noinline)) void run_b(struct B *c) {
  struct B *p = container_of(parent(&c->node), struct B, node);
  p->fn();
}
struct A a1 = { fa }, a2 = { fa }, a3 = { fa };
struct B b1 = { 0, fb }, b2 = { 0, fb }, b3 = { 0, fb };
int main(void) {
  a1.node.l = &a3.node;
  b1.node.l = &b3.node;
  replace_node(&a1.node, &a2.node);
  replace_node(&b1.node, &b2.node);
  run_a(&a3);
  run_b(&b3);
  return 0;
}
