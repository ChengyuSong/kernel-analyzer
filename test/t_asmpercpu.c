/* Inline-asm pointer flows (census top levers):
 * 1. percpu-style asm store/load of a pointer slot: "=m"/"m" indirect
 *    with ptr elementtype (this_cpu_write/read shape).
 * 2. "p"-constraint raw-address read (this_cpu_read_stable shape) —
 *    the asm reads through a pointer passed by register/immediate.
 * 3. asm xchg on an i64 slot holding a laundered fptr (atomic-asm
 *    shape: ptr-width witness).
 * Expected: all three icalls resolve to {op1} (and op2 for xchg'd). */
struct task { int (*op)(int); };
static struct task t0, t1;
static struct task *cur;
static unsigned long slot; /* i64 slot laundering a task ptr */

static inline void set_current(struct task *t) {
  asm volatile("movq %1, %%gs:%0" : "=m"(cur) : "r"(t));
}
static inline struct task *get_current(void) {
  struct task *r;
  asm volatile("movq %%gs:%1, %0" : "=r"(r) : "m"(cur));
  return r;
}
static inline struct task *get_current_stable(void) {
  struct task *r;
  asm("movq %%gs:%P1, %0" : "=r"(r) : "p"(&cur));
  return r;
}
static inline unsigned long xchg_slot(unsigned long v) {
  asm volatile("xchgq %0, %1" : "+r"(v), "+m"(slot) :: "memory");
  return v;
}
static int op1(int x) { return x; }
static int op2(int x) { return x + 1; }

int main(void) {
  t0.op = op1;
  t1.op = op2;
  set_current(&t0);
  int s = get_current()->op(1) + get_current_stable()->op(2);
  xchg_slot((unsigned long)&t1);
  struct task *old = (struct task *)xchg_slot(0);
  if (old) s += old->op(3);
  return s;
}
