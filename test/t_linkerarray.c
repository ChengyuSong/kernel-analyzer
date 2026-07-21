/* Linker-array flows (task #22): both consumption shapes.
 * 1. PREL32 initcall pattern: module-level asm places ".long fn - ."
 *    into .initcall5.init; consumer computes fn = entry + *entry from
 *    the linker-defined bounds symbol (offset_to_ptr).
 * 2. ABS64 __param pattern: section-attributed globals hold fptrs;
 *    consumer iterates __start___param..__stop___param and calls ops.
 * Expected: run_initcalls' icall resolves to {my_init_a, my_init_b},
 * run_params' to {set_x, set_y}. Without --cfl-linker-arrays both are
 * empty (the pre-#22 unsoundness). */
typedef int (*initcall_t)(void);
typedef int initcall_entry_t;

__attribute__((used)) static int my_init_a(void) { return 1; }
__attribute__((used)) static int my_init_b(void) { return 2; }

asm(".section \".initcall5.init\",\"a\"\n"
    ".long my_init_a - .\n"
    ".long my_init_b - .\n"
    ".previous\n");

extern initcall_entry_t __initcall5_start[], __initcall5_end[];

static initcall_t initcall_from_entry(initcall_entry_t *entry) {
  return (initcall_t)((unsigned long)entry + *entry);
}

int run_initcalls(void) {
  int s = 0;
  for (initcall_entry_t *e = __initcall5_start; e < __initcall5_end; e++)
    s += initcall_from_entry(e)();
  return s;
}

struct kparam {
  const char *name;
  int (*set)(int);
};
static int set_x(int v) { return v; }
static int set_y(int v) { return v + 1; }
__attribute__((section("__param"), used)) static const struct kparam p1 = {
    "x", set_x};
__attribute__((section("__param"), used)) static const struct kparam p2 = {
    "y", set_y};
extern const struct kparam __start___param[], __stop___param[];

int run_params(void) {
  int s = 0;
  for (const struct kparam *p = __start___param; p < __stop___param; p++)
    s += p->set(1);
  return s;
}

int main(void) { return run_initcalls() + run_params(); }
