// t_maskwalk.c — the explainable example for "what field sensitivity
// can and cannot split" (task #33, two falsifications + the tag rule).
//
// Three routes, each with its OWN object pair (sharing one pair would
// cross-poison the routes through the (origin,X)<->(origin,s) bridges
// — the #27 ensemble effect in miniature; isolating origins isolates
// the mechanisms):
//
// Route 1 (use_gep): plain struct-field access after a two-way merge.
//   A's fptr is at offset 8, B's at offset 16; reading residue 8 of
//   {gaN, gbN} finds only A's. fs13 -> {fa1}; FI -> {fa1, fb1}.
//   LESSON: merges/arrays are not the problem; struct offsets survive
//   value merging under fs.
//
// Route 2 (use_mask): the kernel's address-translation shape —
//   pmd = (pmd_t *)__va(pud_val(*pud) & PTE_PFN_MASK) + idx
// modeled as ptrtoint; & ~0xfff; inttoptr; ->f. The mask ERASES the
// offset by design (frame-number extraction — there is no field
// offset to preserve), so the encoding must wildcard: both modes ->
// {fa2, fb2}, and no offset-keyed refinement (any P, any grammar) can
// do better. LESSON: the blob's glue is offset-erasing translation +
// escaped addresses; its conflation is REAL at the offset
// abstraction. km census: ESCAPE 58%, VARIABLE 13%, MASK 10%,
// const-chain "GEPs in disguise" 1%.
//
// Route 3 (use_tag): the TAGGED-POINTER idiom — p|1 to mark, p&~1 to
//   clear (rb-tree colors, RCU markers, XArray entries). Sub-alignment
//   constant bit-twiddling never changes the field offset, so
//   (p|1)&~1 must equal p: the tag-round-trip rule suppresses the
//   ptrtoint wildcard and the plain a-edges (shift 0) model it
//   exactly. fs13 -> {fa3}; FI -> {fa3, fb3}.
//
// Expected (--cfl-flows-to --cfl-compositional=false --cfl-dump-icalls):
//   FI:    use_gep -> fa1,fb1   use_mask -> fa2,fb2   use_tag -> fa3,fb3
//   fs13:  use_gep -> fa1       use_mask -> fa2,fb2   use_tag -> fa3
//                    ^ fields pay          ^ irreducible       ^ tag rule
typedef void (*fp)(void);
__attribute__((noinline)) void fa1(void) {}
__attribute__((noinline)) void fb1(void) {}
__attribute__((noinline)) void fa2(void) {}
__attribute__((noinline)) void fb2(void) {}
__attribute__((noinline)) void fa3(void) {}
__attribute__((noinline)) void fb3(void) {}

struct A { long pad; fp f; };       // f at offset 8
struct B { long pad[2]; fp f; };    // f at offset 16

struct A ga1 = {0, fa1}; struct B gb1 = {{0, 0}, fb1};
struct A ga2 = {0, fa2}; struct B gb2 = {{0, 0}, fb2};
struct A ga3 = {0, fa3}; struct B gb3 = {{0, 0}, fb3};

volatile int FLAG = 0;

__attribute__((noinline)) fp pick_gep(void) {
  struct A *x = FLAG ? &ga1 : (struct A *)&gb1; // {&ga1, &gb1}, shift 0
  return x->f;                                  // residue-8 read
}

__attribute__((noinline)) fp pick_mask(void) {
  void *p = FLAG ? (void *)&ga2 : (void *)&gb2;
  unsigned long v = (unsigned long)p; // ptrtoint
  v &= ~0xFFFUL;                      // page-align: offset ERASED
  struct A *x = (struct A *)v;        // inttoptr
  return x->f;
}

__attribute__((noinline)) fp pick_tag(void) {
  void *p = FLAG ? (void *)&ga3 : (void *)&gb3;
  unsigned long v = (unsigned long)p; // ptrtoint
  v |= 1;                             // mark (low tag bit)
  v &= ~1UL;                          // clear before deref
  struct A *x = (struct A *)v;        // inttoptr
  return x->f;
}

__attribute__((noinline)) void use_gep(void) { pick_gep()(); }
__attribute__((noinline)) void use_mask(void) { pick_mask()(); }
__attribute__((noinline)) void use_tag(void) { pick_tag()(); }

int main(void) {
  use_gep();
  use_mask();
  use_tag();
  return 0;
}
