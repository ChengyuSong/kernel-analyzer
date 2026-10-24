// t_cells_slot_join.c — rule S (Fable 2026-10-24): a slot written in two
// branches and read after the join: both stores reach the load, so the
// call keeps both targets. Not a cut: 2 writes x 1 load = 2 pairs, both
// reaching.
// Executed (clang -O0 -fsanitize=address): g once (no argument), exit 0, no report.
typedef void (*fn)(void);
void f(void) {}
void g(void) {}
int main(int argc, char **argv) {
  (void)argv;
  fn p;
  if (argc > 1)
    p = f;
  else
    p = g;
  p(); // CHECK: f g
  return 0;
}
