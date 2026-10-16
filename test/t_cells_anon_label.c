// t_cells_anon_label.c — an anonymous struct names nothing (Fable
// 2026-10-16). clang numbers anonymous structs (`struct.anon`,
// `struct.anon.0`) and the link rename's strip made every one
// `struct.anon`: A and B below, two unrelated anonymous types, were both
// labeled struct.anon (one label, so one cell name per offset for both, and
// any struct.anon step fit either). Now an object of an anonymous type is
// unlabeled, its cells by byte offset (16 bytes each, size kept), and the
// answer is unchanged.
// LOG: anonymous structs label nothing: 2 globals and stack objects unlabeled
// LOG: object A \[unlabeled, 16 B\]
// NOLOG: \[struct\.anon
static struct {
  void (*f)(void);
  int x;
} A;
static struct {
  void (*f)(void);
  long y;
} B;
void fa(void) {}
void fb(void) {}
void (**volatile sink)(void);
int main(int argc, char **argv) {
  (void)argv;
  A.f = fa;
  B.f = fb;
  sink = argc ? &A.f : &B.f;
  A.f(); // CHECK: fa CHECK-NOT: fb
  return 0;
}
