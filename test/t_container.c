/* Minimal kernel-style intrusive list: handler stored via the container,
 * called via container_of() after list traversal. A sound field-sensitive
 * analysis must resolve the icall to both handlers. */
#include <stddef.h>

typedef void (*fptr_t)(void);
struct list_head { struct list_head *next; };
struct widget {
  long pad;
  struct list_head link;
  fptr_t handler;
};

#define container_of(ptr, type, member) \
  ((type *)((char *)(ptr) - offsetof(type, member)))

static struct list_head *global_list;

void handler_a(void) {}
void handler_b(void) {}

__attribute__((noinline)) void register_widget(struct widget *w, int kind) {
  w->handler = kind ? handler_a : handler_b;
  w->link.next = global_list;
  global_list = &w->link;
}

__attribute__((noinline)) void dispatch(void) {
  for (struct list_head *it = global_list; it; it = it->next) {
    struct widget *w = container_of(it, struct widget, link);
    w->handler(); /* icall: must see handler_a and handler_b */
  }
}

static struct widget slots[4];

int main(int argc, char **argv) {
  (void)argv;
  for (int i = 0; i < 4; i++)
    register_widget(&slots[i], (argc + i) & 1);
  dispatch();
  return 0;
}
