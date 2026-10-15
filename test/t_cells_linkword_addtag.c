// CFLAGS: -O2
// Plan 3.55 R1, negative: adding a tag onto a word that may already carry
// one (a copy of another node's word, + 1) can carry into the pointer bits:
// "add to tagged word" fails the field.
// LOG: LinkWord: struct.tw\+0: FAIL
// LOG: FAIL struct.tw\+0: (store|load): add to tagged word at bump:
struct tw { unsigned long w; struct tw *n; } __attribute__((aligned(8)));
void bump(struct tw *a, struct tw *b) { a->w = b->w + 1; }
struct tw *par(struct tw *a) { return (struct tw *)(a->w & ~3UL); }
struct tw x, y;
int main(void) {
  x.w = (unsigned long)&y;
  bump(&y, &x);
  return par(&y) == &y;
}
