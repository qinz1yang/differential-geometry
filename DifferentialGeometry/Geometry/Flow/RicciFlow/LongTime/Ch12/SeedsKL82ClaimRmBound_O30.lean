import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84Sub86RmBound_O22
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRicciShift
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Background

/-!
# CH12-O30, G3b-2: `|Rm|` from `sec ≥ -κ` and `R ≤ Λ` in dimension three

Source: corrected w-dependent local variant of KL 82.1 / Perelman II.6.5 (blow-up step of the
proof of claim (C)); not a verbatim transcription.  The reference PDFs named in AGENTS.md are not
on this machine.

`rm_normSq_le_of_sec_O30` is the stage clause of `isRmBoundedBy` at the blow-up scale: in
dimension three `sec ≥ -κ` is the curvature-operator lower bound `κ`
(`sectionalBoundedBelowAt_iff_curvatureOperatorLowerBoundAt`), and with `R ≤ Λ` the ordered
sectional curvatures satisfy `|kᵢ| ≤ Λ/2 + 2κ` (`sqrt_normSq_le_of_lowerBound_O22`).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature.DimensionThree
  (sectionalBoundedBelowAt_iff_curvatureOperatorLowerBoundAt)
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

/-- **G3b-2**: `|Rm|² ≤ (2√3 (Λ/2 + 2κ))²` from `sec ≥ -κ` and `R ≤ Λ` (dimension three). -/
theorem rm_normSq_le_of_sec_O30 {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M) (z : M) {κ Λ : ℝ} (hκ : 0 ≤ κ) (hΛ : 0 ≤ Λ)
    (hsec : SectionalBoundedBelowAt g z (-κ)) (hR : metricScalarAt g z ≤ Λ) :
    normSq0S g z 4 (metricRm04At g z) ≤ (2 * Real.sqrt 3 * (Λ / 2 + 2 * κ)) ^ 2 := by
  have hdim : Module.finrank ℝ (TangentSpace ThreeModel z) = 3 := finrank_euclideanSpace_fin
  have hlow := (sectionalBoundedBelowAt_iff_curvatureOperatorLowerBoundAt hdim).mp hsec
  have h := sqrt_normSq_le_of_lowerBound_O22 g z hdim hκ hΛ hlow hR
  by_cases h0 : 0 ≤ normSq0S g z 4 (metricRm04At g z)
  · rw [← Real.sq_sqrt h0]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  · have : 0 ≤ (2 * Real.sqrt 3 * (Λ / 2 + 2 * κ)) ^ 2 := sq_nonneg _
    linarith [not_le.mp h0]

end GC.LongTime.Ch12
