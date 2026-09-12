# TerminalSurfaceProduct.lean

Reviewer, 2026-09-11. Data record for the output of `lem:ksol-terminal-rank-one-product`
(`eq:ksol-KLim-terminal-product`): the universal cover of a static three-manifold `(N, g)`
is an isometric product of a complete connected positively curved surface `(S, h)` with a
line, with the product identity stated exactly as consumed by
`bddAbove_scalar_iff_of_universalCover_product` and
`universalCover_split_surface_tensor_half_noncollapsed`. No existence claim; shared by the
candidate-branch interface `UpstreamTerminalTrichotomy` (producer, left empty by owner
instruction) and the native rank-one branch `RankOneTerminalBounded` (consumer).

Pitfall: `Σ` is a reserved token in Lean 4 (sigma types); the field is named `S`.
Verification: `LEAN_NUM_THREADS=2 lake env lean` empty output; named build 15 s, clean.
Contains only a structure and instance attributes; no axiom audit needed.
