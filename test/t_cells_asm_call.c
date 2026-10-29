// AC (Fable 2026-10-28): an inline asm that calls a function named by an
// "i" operand is a call to it, its actuals bound by register. The kernel's
// call_on_irqstack shape: the argument moved into %rdi by the text
// ("movq $1, %rdi" then "call ${0:P}"). Before AC no call reached
// handler (a '$' after "call" was skipped), so its read resolved to
// nothing. Siblings: t_cells_asm_call_tie.c, t_cells_asm_call_unbound.c.
// CFLAGS: -O1
// LOG: asm call in main to handler \(by operand\); formal 0 <- text move; return void
// LOG: asm calls wired by register: 1 sites, 1 callees \(by operand: 1, by literal name: 0\); formals bound by constraint 0, by tie 0, by text move 1;
struct regs { void (*cb)(void); };
void fa(void) {}

__attribute__((used, noinline)) static void handler(struct regs *r) {
  r->cb(); // CHECK: fa
}

struct regs R;

int main(void) {
  R.cb = fa;
  struct regs *rp = &R;
  asm volatile("movq %[arg], %%rdi\n\tcall %P[fn]"
               :
               : [fn] "i"(handler), [arg] "r"(rp)
               : "rdi", "rsi", "rax", "rcx", "rdx", "r8", "r9", "r10", "r11", "memory");
  return 0;
}
