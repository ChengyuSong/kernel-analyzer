# Case-local summary file of t_cells_container_ca.c and t_cells_container_ca_atomic.ll
# (CA, Fable 2026-10-28): an llist-shaped container that verifies (rows
# applied), with two insert rows: ca_llist_add (the x86 cmpxchg asm on the
# handle, the .c case) and ca_llist_add2 (an IR cmpxchg ptr, the .ll case).
@container ca_llist
@storage HANDLE(ca_head+0) LINK(ca_node+0)
ca_llist_add ROLE(insert) OWNER(arg1) ELEM(arg0)
ca_llist_add2 ROLE(insert) OWNER(arg1) ELEM(arg0)
ca_llist_del_first ROLE(remove) OWNER(arg0) ELEM(ret)
@container end
