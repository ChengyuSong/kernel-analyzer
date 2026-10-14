// t_cells_p2iconst.c — a constant integer is not a carrier (Fable
// 2026-10-13, the kernel's dominant soup root). `th.start = (unsigned
// long)entry64` stores a ptrtoint CONSTANT; it used to map to the shared
// constant-int node, the store seeded that node with entry64, and every
// integer constant read it: ERR_PTR's -1/-2 arms (xfrm_lookup_with_ifid)
// made the call below reach entry64. A ptrtoint constant is now a value
// node of its object; the constant-int node ends the solve empty.
// CFLAGS: -O2
// LOG: [1-9][0-9]* integer constants derived from one pointer given their pointer's node
// LOG: the constant-int node holds no fact
typedef void (*fn)(void);
struct hdr { unsigned long start; };
struct hdr th;
void entry64(void) {}
void good(void) {}
fn table[2] = {good, good};
void setup(void) { th.start = (unsigned long)entry64; }
__attribute__((noinline)) fn lookup(int k) {
  long err;
  if (k > 3) err = -1; else if (k > 1) err = -2; else return table[k];
  return (fn)err;
}
int main(int argc, char **argv) {
  setup();
  fn f = lookup(argc);
  if ((unsigned long)f < (unsigned long)-4095) f(); // CHECK: good CHECK-NOT: entry64
  return 0;
}
