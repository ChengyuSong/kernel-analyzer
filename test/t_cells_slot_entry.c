// t_cells_slot_entry.c — rule S (Fable 2026-10-24): a load of a slot that
// a path from the function entry reaches with no store reads an
// indeterminate value; that path adds nothing (no fact), the stores that
// do reach it add theirs, and the load is counted as reached from entry.
// p is written only when argc > 5; the call (also guarded) is reached from
// the entry through the path that skips the store.
// Executed (clang -O0 -fsanitize=address): no call (no argument), exit 0, no report.
typedef void (*fn)(void);
void f(void) {}
int main(int argc, char **argv) {
  (void)argv;
  fn p;
  if (argc > 5)
    p = f;
  if (argc > 5)
    p(); // CHECK: f
  return 0;
}
// LOG: loads reached from entry [1-9][0-9]* \(rule S\)
