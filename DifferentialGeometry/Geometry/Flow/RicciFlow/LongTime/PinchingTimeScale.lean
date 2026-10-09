import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyCurvatureBound

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff
namespace FILL910
section StaticPinching
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]
theorem A04b_rm_le_of_pinching_at_time_scale (g : SmoothRiemannianMetric ThreeModel X) (x : X)
    {a₀ t u s b CR : ℝ} (ha₀ : 0 ≤ a₀) (ht : 0 < t) (hu : t / 2 ≤ u) (hs : 0 < s)
    (hb : 0 < b) (hsb : s ≤ b * Real.sqrt t) (hCR : 0 ≤ CR)
    (hfixed : InFixedHamiltonIveyRegion g (a₀ + u) x)
    (hscalar : metricScalarAt g x ≤ CR / s ^ 2) :
    Real.sqrt (normSq0S g x 4 (metricRm04At g x)) ≤
      2 * Real.sqrt 3 * (CR / 2 + max CR (2 * Real.exp 4 * b ^ 2)) / s ^ 2
 := by
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
  have hB : 0 ≤ CR / s ^ 2 := div_nonneg hCR hs2.le
  have hbt : 0 < b * Real.sqrt t := mul_pos hb (Real.sqrt_pos.mpr ht)
  have hsq : s ^ 2 ≤ b ^ 2 * t := by
    nlinarith [Real.sq_sqrt ht.le]
  have hexp : Real.exp 4 / (t / 2) ≤ (2 * Real.exp 4 * b ^ 2) / s ^ 2 := by
    apply (div_le_div_iff₀ (by linarith : 0 < t / 2) hs2).mpr
    nlinarith [Real.exp_pos (4 : ℝ)]
  have hmax : max (CR / s ^ 2) (Real.exp 4 / (t / 2)) ≤
      max CR (2 * Real.exp 4 * b ^ 2) / s ^ 2 := by
    apply max_le
    · exact div_le_div_of_nonneg_right (le_max_left _ _) hs2.le
    · exact hexp.trans (div_le_div_of_nonneg_right (le_max_right _ _) hs2.le)
  have h := sqrt_normSq0S_le_of_fixedHamiltonIveyRegion g x
    (by linarith : 0 < t / 2) (by linarith : t / 2 ≤ a₀ + u) hfixed hscalar
  rw [max_eq_left hB] at h
  refine h.trans ?_
  calc
    _ ≤ 2 * Real.sqrt 3 * (CR / s ^ 2 / 2 +
        max CR (2 * Real.exp 4 * b ^ 2) / s ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add_right hmax _) (by positivity)
    _ = _ := by ring
end StaticPinching
end FILL910
