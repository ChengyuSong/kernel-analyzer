// Two modules (the shape of kernel/time/tick-broadcast.o reading
// tick_next_period, defined in tick-common.o): this module reads the
// pointer-width integer gl, which may become a pointer, before the module
// that defines gl is read, so the read asks for gl's dereference node
// first; the defining module's initializer then asked again, and the
// factory appended a node before finding the cached one (a dereference
// node with no pointer and no edges).
// MODULE: t2_cells_orphan_deref_def.c
// LOG: orphan dereference nodes: 0
extern unsigned long gl;
void *get(void) { return (void *)gl; }
int main(void) { return get() != 0; }
