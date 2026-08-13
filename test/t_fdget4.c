/* Dirty consumer segment: pointer laundered through an int SLOT; the
 * reload side rebases by +8 (field0 -> field1) before the deref. The
 * residue claim at the load is shift-0, which would be WRONG here —
 * the segment-local check must see the +8 and wildcard the loaded
 * node, so fs mode still derives g1 (sound, imprecise). The clean
 * twin (call0, tag round trip only) must stay exact.
 */
struct ops { long (*f0)(long); long (*f1)(long); };
static long g0(long x) { return x; }
static long g1(long x) { return x + 1; }
static struct ops O = { g0, g1 };
static struct ops O2 = { g0, g1 };
static unsigned long slot;

__attribute__((noinline)) void put(int w) {
  slot = w ? (unsigned long)&O | 1 : (unsigned long)&O2 | 1;
}

__attribute__((noinline)) long call0(long x) { /* clean: untag only */
  unsigned long v = slot;
  struct ops *p = (struct ops *)(v & ~3UL);
  return p->f0(x); /* expect g0 exactly in fs mode */
}

__attribute__((noinline)) long call1(long x) { /* dirty: +8 rebase */
  unsigned long v = slot & ~3UL;
  long (**pf)(long) = (long (**)(long))(v + 8);
  return (*pf)(x); /* MUST include g1 in fs mode (wildcard) */
}
