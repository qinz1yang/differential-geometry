import DifferentialGeometry.Geometry.Metric.Approximation.EdgeDiskCoverage
import DifferentialGeometry.Geometry.Metric.Approximation.IsometricKleinerLottApproximation

set_option autoImplicit false
open Set Metric GC.MetricGeometry DifferentialGeometry.Analysis

example :
    let X := WithLp 2 (ℝ × ℝ)
    let f : ball (0 : X) (100 * (1 : ℝ)) → ℝ := fun x => x.val.fst
    let P : X → ℝ := fun x => dist x 0
    let ρ : X → ℝ := fun _ => 1
    let ζ := (Subtype.val : ball (0 : X) (100 * (1 : ℝ)) → X).extend
      (fun x => edgeCoordinateProfile (f x / 1) * edgeHeightProfile (P x.val / (1 * ρ x.val))) 0
    ball (0 : X) (3 * (1 : ℝ)) ⊆ edgeDiskDomain 0 1 f P ρ ∧
      EqOn ζ 1 (ball (0 : X) (3 * (1 : ℝ))) := by
  let X := WithLp 2 (ℝ × ℝ)
  let F : KleinerLottApprox (0 : X) (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) (1 / 1000000) :=
    (IsometryEquiv.refl X).toKleinerLottApprox rfl (by norm_num) (by norm_num)
  apply ball_subset_edgeDiskDomain_and_cutoff_one (Δ := 1) (μ := 0) (Λ := 0) F
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ => (1 : ℝ)) (fun x => dist x 0) (LipschitzWith.const 1) (fun _ => by norm_num)
    rfl (by norm_num) {0} (mem_singleton 0) ?_ (fun x => x.val.fst) ?_
  · intro x _
    simp only [infDist_singleton, sub_self, abs_zero, zero_mul, le_refl]
  · intro x
    have hf : (F.toFun x.val).fst = x.val.fst := rfl
    rw [hf, sub_self, abs_zero, zero_mul]
