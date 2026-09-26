# I28 log (DESIGN_28 implementation)

- 01:40 Compile method: hard-link mirror of E:\differential-geometry-pc3-lake\build\lib\lean oleans at
  E:\i28-scratch-olean (outside repo); changed modules compiled with `lean -o` into the mirror (link
  removed first). Build dir was mid-rebuild (SpatialCanonicalWitness olean absent), so that module was
  compiled into the mirror from the working tree.
- Deviation (imports): `SpatiallyCanonicalBefore/On`, `spatiallyCanonicalBefore_mono/_start`,
  `EventSlabsSpatiallyCanonical` moved from SpatialCanonicalContinuation to CanonicalNeighborhoodInduction
  (the C2/C3 aggregates there need them; Spatial imports Induction). Names unchanged.
- Coordinator refinement (3): `CrossingContinuation` and `CanonicalNeighborhoodContinuation` now begin
  `∃ εbar, 0 < εbar ∧ ∀ B ε, … → ε ≤ εbar →`. Monotonicity in ε of the strong conclusion needs
  SpatialCanonicalWitness.mono_eps, alpha-monotonicity of both neck-chart predicates and radius
  monotonicity of NoncollapsedBefore (>80 lines): deferred as the new skeleton leaf
  `CanonicalNeighborhoodsThroughSurgeryAccuracyReduction`. Strong body factored into
  `CanonicalNeighborhoodsThroughSurgeryStrongAt P₀ g₀ B ε Λ` (Strong unfolds to the same statement).
- Steps 1-6 done, all compiled; axioms of assemblies without sorryAx; smoothPoincareConjecture_holds
  has sorryAx only through skeleton leaves.
- (v) done in Topology/CanonicalCapScalar.lean (+ import StandardCap.StaticWindowRestriction; no cycle):
  `exists_presented_cap_scalar_lower_bound_of_canonical_window_core`, as in DESIGN_28 (v); proof by
  `restrictWindow` to Dstar and the local-isometry argument on `S.window ∘ inclusion`. Axioms clean.
- (vi) done: private backward lemma switched to `exists_threshold_uniform_selected_neck_append_backward`
  (import VariableThreshold replaces ProspectiveNeckSurvival); five theorems + factory restated with
  `∃ δ ε₀ Λq … 0 < Λq ∧ ∀ q0, 0 < q0 → …` and `Λq * max q0 1 ≤ Q`; in theorem 5 and the factory q0 sits
  in `∀ q0 qcan originalCoreFloor protectedFloor, 0 < q0 → …`. All compile, axioms clean.
- `CutoffParameters.recenterConstant_mul_le_half` lives in the Strong module (its only consumer).
- ReducedVolumeTruncation.lean (untracked, another lane's file) edited only at the `.2.2.2.1` site.
- Not recompiled: ProspectiveNeckSurvival* (CanonicalCapScalar change is additive).
- Scratch mirror E:\i28-scratch-olean removed at the end.
- I28b: accuracy-reduction leaf and predicate removed. `CanonicalNeighborhoodsThroughSurgeryStrong` is now
  `∃ εbar, 0 < εbar ∧ ∀ B ε Λ, … ε ≤ εbar → 0 < Λ → StrongAt` (StrongAt kept as the body);
  `UniformDebitSurgeryStepStrong` takes `∀ B εbar, 0 < B → 0 < εbar →` and returns `ε ≤ εbar`; hext
  uses `min (1/22) εbar`; recenter projection gives `∃ εbar, 0 < εbar ∧ OfRecenter P₀ g₀ Λ εbar`
  (OfRecenter gained `εbar` and `ε ≤ εbar`). Skeleton back to 8 sorry leaves. All recompiled, axioms clean.
