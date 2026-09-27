# S13B fill log (strong C, strong S, spatial leaf)

- 2026-09-25: wrote `Topology/SpatialCanonicalContinuation.lean` (spatial Before/On predicates,
  threshold and η monotonicity, four-predicate closure `canonicalBefore_end_of_continuation_spatial`,
  `EventSlabsSpatiallyCanonical`, leaf `SpatialCanonicalContinuation`) and
  `Topology/CanonicalNeighborhoodsThroughSurgeryStrong.lean` (strong C, `…OfRecenter Λ` projection,
  strong S, S+C assembly, hext, smoothPoincare, C-from-four-leaves assembly).
- Compiled read-only as one scratch concatenation (SpatialCanonicalWitness source + both files, since
  the SpatialCanonicalWitness olean was absent): 0 errors, 0 warnings; axioms of all assemblies
  propext, Classical.choice, Quot.sound. Not yet compiled as modules (needs the olean); 13 linters not run.
- Gaps found: (1) C3 and the spatial leaf cannot share constants through separate `∃`s, so the
  spatial leaf takes C3's `C1 C2 τmin Ctime Cgrad` and `qcan` as inputs and outputs its own
  `C1s C2s` and threshold `qs ≥ qcan`; (2) `recenterConstant` has no upper bound (only `4 ≤`), so
  the old C is not a projection of the strong C; projection to `…OfRecenter Λ` instead;
  (3) S's order `∀ B Ctime, ∃ ε Λ` is circular with C's Λ-dependence (first call `hcn B (1/22) Λ₀`
  needs `Λ₀ ≥ Λ` before Λ exists; `Λ₀ < 4` makes it vacuous); S restated `∀ B, ∃ Λ, ∀ Ctime, ∃ ε`.
- 2026-09-26: with the real SpatialCanonicalWitness olean, `SpatialCanonicalContinuation.lean`
  compiles clean via `lake env lean` (0 diagnostics). The strong file needs that module's olean
  (no lake build here); compiled as a scratch concatenation (File 1 body + File 2 body on real
  imports): 0 diagnostics; axioms of all assemblies propext, Classical.choice, Quot.sound.
