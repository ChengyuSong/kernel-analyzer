/* Laundered-pointer int ARGUMENT: the boundary symmetric to the
 * __fdget return idiom. entry() passes a tagged word BY VALUE;
 * dispatch() untags and calls through f_op. Also a two-hop variant
 * (helper forwards the arg) to check formal->actual->formal chains.
 * Expect both icalls to derive my_llseek.
 */
typedef long loff_t;
struct file;
struct file_operations { loff_t (*llseek)(struct file *, loff_t, int); };
struct file { const struct file_operations *f_op; };

static loff_t my_llseek(struct file *f, loff_t off, int whence) { return off; }
static const struct file_operations my_fops = { .llseek = my_llseek };
static struct file myfile = { .f_op = &my_fops };
static struct file myfile2 = { .f_op = &my_fops };

__attribute__((noinline)) loff_t dispatch(unsigned long v, loff_t off, int wh) {
  struct file *f = (struct file *)(v & ~3UL);
  if (f)
    return f->f_op->llseek(f, off, wh);
  return -9;
}

__attribute__((noinline)) loff_t forward(unsigned long v, loff_t off) {
  return dispatch(v, off, 1); /* two-hop: formal -> actual -> formal */
}

loff_t entry(int which, loff_t off) {
  unsigned long v =
      which ? (unsigned long)&myfile | 1 : (unsigned long)&myfile2 | 1;
  return dispatch(v, off, 0);
}

loff_t entry2(int which, loff_t off) {
  unsigned long v =
      which ? (unsigned long)&myfile | 2 : (unsigned long)&myfile2 | 2;
  return forward(v, off);
}
