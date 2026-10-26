// t_cells_walk_flags_off.c — WF (Fable 2026-10-26, plan 3.127):
// t_cells_walk_flags.c with --cfl-cell-collapse=false (no periodic cycle
// pass, flags only from the final pass): the same redo, the same cells.
// KAFLAGS: --cfl-cell-node-facts=- --cfl-cell-collapse=false
#include "t_cells_walk_flags.c"
// LOG: Cells: walk flags \(WF\): [0-9]+ at the end of this solve, 0 seeded, [1-9][0-9]* differ from the seed; the solve is redone from them
// LOG: Cells: walk flags: [1-9][0-9]* flags at the fixpoint, [0-9]+ solves \(1 redone for flags\)
// LOG: ^walk:   %10 = load ptr, ptr @S, align 8, !dbg ![0-9]+	2$
// LOG: ^walk:   %12 = getelementptr inbounds i8, ptr %11, i64 1, !dbg ![0-9]+	1$
