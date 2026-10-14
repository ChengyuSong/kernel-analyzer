// t_cells_container_hash.c — a verified container's rows applied per call
// site (plan 3.55 deliverable 1): sqlite3's Hash, copied in its shape
// (findElementWithHash's static nullElement sentinel, insertElement,
// rehash, removeElementGivenHash), under the rows of func_summaries.txt's
// sqlite3_hash container. Two Hash owners of one object (db.aFunc,
// db.aColl) hold two data objects of one type; a lookup on db.aFunc
// returns only what was inserted into db.aFunc (the owner's element cell),
// where the body alone returns every Hash's data (one HashElem site).
// LOG: Container: sqlite3_hash .* body \{
// LOG: sentinel element .*nullElement: s1 PASS; s2 PASS.*; s3 PASS; s4 PASS
// LOG: VERIFIED \(rows applied\)
// LOG: container rows: [1-9][0-9]* row links
#include <stdlib.h>
#include <string.h>
typedef void (*fn)(void);
typedef struct HashElem HashElem;
typedef struct Hash { unsigned int htsize; unsigned int count; HashElem *first;
  struct _ht { unsigned int count; HashElem *chain; } *ht; } Hash;
struct HashElem { HashElem *next, *prev; void *data; const char *pKey; };
__attribute__((noinline)) void *sqlite3Malloc(unsigned long n) { return malloc(n); }
__attribute__((noinline)) void sqlite3_free(void *p) { free(p); }
__attribute__((noinline)) int sqlite3StrICmp(const char *a, const char *b) { return strcmp(a, b); }
void sqlite3HashClear(Hash *pH) {
  HashElem *elem = pH->first;
  pH->first = 0;
  sqlite3_free(pH->ht);
  pH->ht = 0;
  pH->htsize = 0;
  while (elem) { HashElem *next_elem = elem->next; sqlite3_free(elem); elem = next_elem; }
  pH->count = 0;
}
static unsigned int strHash(const char *z) {
  unsigned int h = 0; unsigned char c;
  while ((c = (unsigned char)*z++) != 0) { h += c; h *= 0x9e3779b1; }
  return h;
}
static void insertElement(Hash *pH, struct _ht *pEntry, HashElem *pNew) {
  HashElem *pHead;
  if (pEntry) { pHead = pEntry->count ? pEntry->chain : 0; pEntry->count++; pEntry->chain = pNew; }
  else pHead = 0;
  if (pHead) {
    pNew->next = pHead; pNew->prev = pHead->prev;
    if (pHead->prev) pHead->prev->next = pNew; else pH->first = pNew;
    pHead->prev = pNew;
  } else {
    pNew->next = pH->first;
    if (pH->first) pH->first->prev = pNew;
    pNew->prev = 0; pH->first = pNew;
  }
}
static int rehash(Hash *pH, unsigned int new_size) {
  struct _ht *new_ht = (struct _ht *)sqlite3Malloc(new_size * sizeof(struct _ht));
  HashElem *elem, *next_elem;
  if (new_ht == 0) return 0;
  sqlite3_free(pH->ht);
  pH->ht = new_ht;
  pH->htsize = new_size;
  memset(new_ht, 0, new_size * sizeof(struct _ht));
  for (elem = pH->first, pH->first = 0; elem; elem = next_elem) {
    unsigned int h = strHash(elem->pKey) % new_size;
    next_elem = elem->next;
    insertElement(pH, &new_ht[h], elem);
  }
  return 1;
}
static HashElem *findElementWithHash(const Hash *pH, const char *pKey, unsigned int *pHash) {
  HashElem *elem; unsigned int count, h;
  static HashElem nullElement = {0, 0, 0, 0};
  if (pH->ht) { struct _ht *pEntry; h = strHash(pKey) % pH->htsize; pEntry = &pH->ht[h]; elem = pEntry->chain; count = pEntry->count; }
  else { h = 0; elem = pH->first; count = pH->count; }
  if (pHash) *pHash = h;
  while (count--) { if (sqlite3StrICmp(elem->pKey, pKey) == 0) return elem; elem = elem->next; }
  return &nullElement;
}
static void removeElementGivenHash(Hash *pH, HashElem *elem, unsigned int h) {
  struct _ht *pEntry;
  if (elem->prev) elem->prev->next = elem->next; else pH->first = elem->next;
  if (elem->next) elem->next->prev = elem->prev;
  if (pH->ht) { pEntry = &pH->ht[h]; if (pEntry->chain == elem) pEntry->chain = elem->next; pEntry->count--; }
  sqlite3_free(elem);
  pH->count--;
  if (pH->count == 0) sqlite3HashClear(pH);
}
void *sqlite3HashFind(const Hash *pH, const char *pKey) { return findElementWithHash(pH, pKey, 0)->data; }
void *sqlite3HashInsert(Hash *pH, const char *pKey, void *data) {
  unsigned int h; HashElem *elem, *new_elem;
  elem = findElementWithHash(pH, pKey, &h);
  if (elem->data) {
    void *old_data = elem->data;
    if (data == 0) removeElementGivenHash(pH, elem, h);
    else { elem->data = data; elem->pKey = pKey; }
    return old_data;
  }
  if (data == 0) return 0;
  new_elem = (HashElem *)sqlite3Malloc(sizeof(HashElem));
  if (new_elem == 0) return data;
  new_elem->pKey = pKey; new_elem->data = data;
  pH->count++;
  if (pH->count >= 10 && pH->count > 2 * pH->htsize) {
    if (rehash(pH, pH->count * 2)) h = strHash(pKey) % pH->htsize;
  }
  insertElement(pH, pH->ht ? &pH->ht[h] : 0, new_elem);
  return 0;
}
struct Def { fn x; };
struct Db { Hash aFunc; Hash aColl; };
void ffn(void) {}
void cfn(void) {}
int main(int argc, char **argv) {
  struct Db *db = calloc(1, sizeof *db);
  struct Def *d1 = malloc(sizeof *d1), *d2 = malloc(sizeof *d2);
  d1->x = ffn;
  d2->x = cfn;
  sqlite3HashInsert(&db->aFunc, "f", d1);
  sqlite3HashInsert(&db->aColl, "c", d2);
  struct Def *p = sqlite3HashFind(&db->aFunc, argv[0]);
  if (p) p->x(); // CHECK: ffn CHECK-NOT: cfn
  sqlite3HashClear(&db->aColl);
  return 0;
}
