typedef long (*seek_fn)(void *f, long off, int wh);
struct fops { void *read; seek_fn llseek; };
struct file { int mode; struct fops *f_op; };
long my_llseek(void *f, long off, int wh) { return off; }
long no_seek(void *f, long off, int wh) { return -1; }
struct fops my_fops = { 0, my_llseek };
struct file GF = { 4, &my_fops };
struct file *file_table[16];

__attribute__((noinline)) unsigned long __fdget(int fd) {          /* tagged ptr in an int return */
  return (unsigned long)file_table[fd & 15] | 3;
}
void install(void) { file_table[0] = &GF; }

long do_lseek(int fd, long off, int wh) {
  unsigned long word = __fdget(fd);
  struct file *fp = (struct file *)(word & ~3UL);
  seek_fn fn = no_seek;
  if (fp->mode & 4) {
    if (fp->f_op->llseek)
      fn = fp->f_op->llseek;
  }
  return fn(fp, off, wh);
}
