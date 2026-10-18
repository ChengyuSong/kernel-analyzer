// t_cells_bytecopy_any_range_a.c — a byte copy with an any-offset side
// (Fable 2026-10-17, a soundness fix): fill copies a whole struct T into buf
// at a runtime offset (buf's any-offset cell), use copies it back out at a
// runtime offset into a local T. The any-offset cell meets every cell of
// the other side's range: both of T's fields on the way in and on the way
// out. Before, only the cell at the copy's start: buf got t0.a alone and
// t.a alone was filled (t.a() {f1}, t.b() {}: f2 lost).
#include <stdlib.h>
#include <string.h>
struct T { void (*a)(void); void (*b)(void); };
void f1(void) {}
void f2(void) {}
__attribute__((noinline)) void fill(char *buf, int k) {
  struct T t0 = {f1, f2};
  memcpy(buf + k, &t0, sizeof t0);
}
__attribute__((noinline)) void use(char *buf, int k) {
  struct T t;
  memcpy(&t, buf + k, sizeof t);
  t.a(); // CHECK: f1 f2
}
int main(int argc, char **argv) {
  char *buf = malloc(256);
  (void)argv;
  fill(buf, argc * 16);
  use(buf, argc * 16 + 16);
  return 0;
}
