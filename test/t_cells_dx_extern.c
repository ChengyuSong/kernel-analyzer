// t_cells_dx_extern.c — a function with no body in any module (the kernel's
// copy_user_generic_unrolled, defined only in assembly) is declared in two
// modules, and each takes its address (DX, Fable 2026-10-27): one symbol is
// one function object, minted from its canonical declaration, so XN's
// census finds "fn asm_only" once and the call answers name it once.
// MODULE: t2_cells_dx_extern.c
// KAFLAGS: --cfl-cell-node-facts=/dev/null
// LOG: object names \(XN\): [0-9]+ objects, all distinct; .*; 1 declaration objects collapsed into their canonical declaration \(1 symbols\)
// NOLOG: share the name
struct ops { void (*f)(void); };
void asm_only(void);
static struct ops ops_a = { asm_only };
void run_b(void);
struct ops *get_b(void);
// One site that reads both modules' tables: before DX it held two objects
// for asm_only.
__attribute__((noinline)) void run_a(int c) { (c ? &ops_a : get_b())->f(); } // CHECK: asm_only
int main(int argc, char **argv) {
  run_a(argc);
  run_b();
  return 0;
}
