/* Two-hop laundered int-return chain (the real 5.18 shape):
 *   __fget_light: ptrtoint return (witnessed directly)
 *   __fdget:      returns a CALL RESULT  (hole #1: mayCarryPtrProvenance
 *                 declined CallBase)
 *   __fdget_pos:  returns a local holding a call result (second hop)
 * Caller is defined FIRST so handleCall wires the callsite before any
 * callee's visitReturnInst runs (hole #2: order-dependent wiring).
 * Expect: the icall in ksys_lseek derives my_llseek.
 */
typedef long loff_t;
struct file;
struct file_operations { loff_t (*llseek)(struct file *, loff_t, int); };
struct file { const struct file_operations *f_op; };

unsigned long __fget_light(unsigned int fd);
unsigned long __fdget(unsigned int fd);
unsigned long __fdget_pos(unsigned int fd);

loff_t ksys_lseek(unsigned int fd, loff_t off, int whence) {
  unsigned long v = __fdget_pos(fd);
  struct file *f = (struct file *)(v & ~3UL);
  if (f) {
    loff_t (*fn)(struct file *, loff_t, int) = f->f_op->llseek;
    return fn(f, off, whence);
  }
  return -9;
}

static loff_t my_llseek(struct file *f, loff_t off, int whence) { return off; }
static const struct file_operations my_fops = { .llseek = my_llseek };
static struct file myfile = { .f_op = &my_fops };
static struct file myfile2 = { .f_op = &my_fops };

__attribute__((noinline)) unsigned long __fget_light(unsigned int fd) {
  return fd ? (unsigned long)&myfile : (unsigned long)&myfile2;
}
__attribute__((noinline)) unsigned long __fdget(unsigned int fd) {
  return __fget_light(fd);
}
__attribute__((noinline)) unsigned long __fdget_pos(unsigned int fd) {
  unsigned long v = __fdget(fd);
  return v;
}
