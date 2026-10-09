import DifferentialGeometry.Geometry.Collapse.Inhabitants.DoubleCuspBoundaryInst
import DifferentialGeometry.Geometry.Collapse.StaticCounterexamples

/-!
# Consumer of the level-1 boundary instance (lane BDRY-INST)

The boundary clause of the corrected standing sequence (ratio
`boundaryCounterexampleRatio δ₀ (n + 1)`, lane BDRY-IDX) on connected universe-`0` carriers is
inhabited without any counterfactual: every member is the double cusp at its own torus scale, with
two boundary components.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry GC.Seifert GC.GraphManifold GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

/-- The boundary clause of the corrected standing sequence, inhabited by double cusps at the
ratios `δ_{n+1}` (each member with two boundary components). -/
theorem exists_doubleCusp_boundary_sequence_INST (K : ℕ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    ∃ (W : ℕ → CompactCarrier.{0}) (_ : ∀ n, ConnectedSpace (W n).Carrier)
      (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
      (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
      ∀ n, (B n).count = 2 := by
  have hmem (n : ℕ) := exists_doubleCuspNearlyCuspidalBoundary_INST.{0} K
    (boundaryCounterexampleRatio_pos hδ₀ (Nat.le_add_left 1 n))
  choose a ha _ B hc _ using hmem
  exact ⟨fun _ => annulusCircleCarrier.{0}, fun _ => connectedSpace_productSet (Or.inl rfl),
    fun n => doubleCuspMetric.{0} (a n) (ha n), B, hc⟩

end DifferentialGeometry.Geometry.Collapse
