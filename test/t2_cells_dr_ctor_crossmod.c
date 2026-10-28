// The second module of t_cells_dr_ctor_crossmod.c: the constructor and the
// functions it installs.
#include <stdlib.h>
typedef void (*fn)(void);
struct bfd_hash_entry { struct bfd_hash_entry *next; const char *string; unsigned long hash; };
struct bfd_hash_table;
struct my_entry { struct bfd_hash_entry root; fn fa; fn fb; };
void ga(void) {}
void gb(void) {}
struct bfd_hash_entry *my_newfunc(struct bfd_hash_entry *entry, struct bfd_hash_table *table, const char *string) {
  (void)table;
  (void)string;
  if (entry == NULL) entry = (struct bfd_hash_entry *)malloc(sizeof(struct my_entry));
  if (entry != NULL) {
    ((struct my_entry *)entry)->fa = ga;
    ((struct my_entry *)entry)->fb = gb;
  }
  return entry;
}
