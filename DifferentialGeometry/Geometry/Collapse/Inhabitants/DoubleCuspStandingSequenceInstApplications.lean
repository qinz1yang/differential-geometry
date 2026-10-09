import DifferentialGeometry.Geometry.Collapse.Inhabitants.DoubleCuspStandingSequenceInst
import DifferentialGeometry.Geometry.Collapse.StaticCounterexamples

/-!
# Consumer of the level-2 instance: the corrected standing sequence (lane BDRY-INST)

The three standing hypotheses of the index-shifted boundary producers (lane BDRY-IDX), at the
ratios `boundaryCounterexampleRatio δ₀ (n + 1)` on connected universe-`0` carriers, with ONE
derivative-control function `A` chosen before `δ₀`, are inhabited by double cusps. No
counterfactual hypothesis.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry GC.Endpoint GC.Seifert GC.GraphManifold

namespace DifferentialGeometry.Geometry.Collapse

/-- **The corrected boundary standing sequence, unconditionally (review 54 §4, level 2).** One
`A` (positive everywhere), then for every `δ₀ > 0` a sequence of connected universe-`0` carriers
with nearly cuspidal boundary (two components each), volume collapse and derivative control with
`A`, all at the ratios `δ_{n+1}`. -/
theorem exists_doubleCusp_standing_sequence_ratio_INST (K : ℕ) :
    ∃ A : ℝ → ℝ, (∀ w, 0 < A w) ∧ ∀ δ₀ : ℝ, 0 < δ₀ →
      ∃ (W : ℕ → CompactCarrier.{0}) (_ : ∀ n, ConnectedSpace (W n).Carrier)
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, (B n).count = 2) ∧
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) ∧
        ∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1)) := by
  obtain ⟨A, hA, hseq⟩ := exists_doubleCusp_standing_sequence_INST.{0} K
  refine ⟨A, hA, fun δ₀ hδ₀ => ?_⟩
  obtain ⟨a, ha, B, hc, hvol, hder⟩ := hseq (fun n => boundaryCounterexampleRatio δ₀ (n + 1))
    (fun n => boundaryCounterexampleRatio_pos hδ₀ (Nat.le_add_left 1 n))
  exact ⟨fun _ => annulusCircleCarrier.{0}, fun _ => connectedSpace_productSet (Or.inl rfl),
    fun n => doubleCuspMetric.{0} (a n) (ha n), B, hc, hvol, hder⟩

end DifferentialGeometry.Geometry.Collapse
