# I28c log (DESIGN_C4 failure 1: C3 output as a C4 hypothesis)

- SpatialCanonicalContinuation: both branches gain, after the noncollapsing hypothesis, C3's own
  output `(∃ η, 0 < η ∧ DerivativeBoundOn Ctime qcan t₀ η ∧ GradientBoundOn Cgrad qcan t₀ η ∧
  CanonicalOn ε C1 C2 qcan τmin t₀ η) →` (event branch on `(H.toHistory.event j).incoming`,
  terminal branch on `G`), verbatim from CanonicalNeighborhoodContinuation's conclusion.
- Strong assembly: in both `hcont` lambdas, `have hF₀ := hF'.i …` and pass it to the combiner and to
  `hS'.i … hn hF₀`. PoincareEndgame unchanged (leaf states the predicate by name).
- Compile: hard-link mirror E:\i28c-mirror of the pc3 oleans; Spatial, Strong, PoincareEndgame
  compiled with `lean -o` into the mirror (LEAN_NUM_THREADS=2); Spatial and Strong rechecked with the
  standard linter set: no output. PoincareEndgame: only the 8 leaf sorry warnings.
- Axioms: `canonicalNeighborhoodsThroughSurgeryStrong_of_leaves` [propext, Classical.choice,
  Quot.sound]; `smoothPoincareConjecture_holds` adds sorryAx (8 leaves). Mirror removed.
- Shared build dir oleans for these 3 modules are now stale (not rebuilt; no lake build).
