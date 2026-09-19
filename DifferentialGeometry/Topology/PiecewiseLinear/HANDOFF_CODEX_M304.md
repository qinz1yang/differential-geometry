# Spherical-shell proof lane

## Scope and source (2026-09-19 UTC)

The owner explicitly added this single independent lane until 14:19 UTC.
The clean starting point was cbfe4a73f5c5074805cc4db729f8fed5146322ef,
on codex/moise-304 in the ef23 worktree. E3 retains the actual 30.3
splitting geometry. This lane does not edit MoiseChain or the other lanes'
owned source and does not create subagents.

The complete proof of Moise 30.4 is on printed page 216, PDF index 225.
The preceding 30.3 is on page 215. The annular-neighborhood input 28.19
is on page 209. The proof constructs an initial connected separating
surface, compresses using 26.4, uses 28.19 and 30.3 to preserve the
geometric separation, and descends in the first Betti number. The general
wild-cell complement problem is not an extra input to the accepted tame
30.5 consumer. None of 26.4, 28.19, or the complete 30.4 is asserted here.

## Constructed compact-set separators (2026-09-19 UTC)

`Connected/SeparatorLocation.lean` proves three general topological results:
`separates_frontier`, `Separates.inter_nonempty_of_isPreconnected`, and
`Separates.subset_interior_of_disjoint_frontier`. The last result supplies
the exact justification for placing a connected separator inside a
connected shell when it avoids that shell's frontier.

`SeparatingSurface.lean` proves
`exists_isCombinatorialManifoldWithBoundary_neighborhood` in every positive
finite dimension and `exists_connected_separating_surface` in dimension
three. The latter takes a compact connected set A, a disjoint closed
connected set B, and any open neighborhood U of A. It actually constructs
a finite, connected, orientable, two-sided closed combinatorial surface
inside U separating A and B. It encloses A in a finite simplex, refines
an actual derived neighborhood inside U minus B, identifies its frontier,
and selects a genuine separating connected boundary component. There is
no assumed separator, triangulated neighborhood, or equivalent conclusion.

Both new modules compile with zero diagnostics through the M304 leased
checker; all five nonautomatic declarations and ten critical reused
declarations pass the transitive axiom audit, with only propext,
Classical.choice, and Quot.sound. All 13 applicable environment linters
pass. A concrete closed unit ball / radius-three sphere instance constructs
a separating surface inside the radius-two open ball. The final silent
audit took 45.809 seconds including admission. The individual source-check
wall totals were not persisted; the first completed in 7.849 seconds and
the second completed after the command yielded. An earlier external-model
attempt used two unqualified Metric names and was corrected; no source
proof failure remains. The first surface-signature attempt omitted the
local Finite instance required by IsOrientable; the final existential
explicitly installs the constructed finite-face proof.

Verification files are outside the project at
`C:/Users/liao9/AppData/Local/Temp/moise304-reading/` and private objects at
`C:/Users/liao9/AppData/Local/Temp/codex-moise-304-20260919/lib/`.
The audit source is `AuditSeparatingSurface.lean` and the full declaration
census is `separating-surface-census.json`. Frozen receipt and source copies
are retained in `separator-checkpoint/`. Shared E: artifacts are read-only.
Both leaves are registered in the flat root. The owner-stopped full-root
build was not restarted; independent integration/root acceptance remains
separate from these focused checks.

Next: construct the radial closed-annulus model and transport its interior
and frontier through the actual spherical-shell homeomorphism. This will
specialize the constructed separator to a surface inside interior X.
Compression geometry and strict Betti descent remain later obligations.
