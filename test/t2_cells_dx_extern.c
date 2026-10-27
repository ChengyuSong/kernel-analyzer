// The second module of t_cells_dx_extern.c: its own declaration of asm_only
// and its own table holding it; get_b hands that table to run_a.
struct ops { void (*f)(void); };
void asm_only(void);
static struct ops ops_b = { asm_only };
struct ops *get_b(void) { return &ops_b; }
__attribute__((noinline)) void run_b(void) { ops_b.f(); }
