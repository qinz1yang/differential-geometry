import DifferentialGeometry.Geometry.Comparison.HingeModel

set_option autoImplicit false

open Set

namespace Metric.MinimizingHinge

open DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] {p q : X}

theorem exists_hinge_with_forward_right (H : MinimizingHinge p q) (κ : ℝ)
    {h : ℝ} (hh : 0 < h) (hhb : h < dist H.center q)
    (τ : Icc (0 : ℝ) (dist (H.right ⟨h, ⟨hh.le, hhb.le⟩⟩) p) → X)
    (hτ : Isometry τ)
    (hτ0 : τ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = H.right ⟨h, ⟨hh.le, hhb.le⟩⟩)
    (hτp : τ ⟨dist (H.right ⟨h, ⟨hh.le, hhb.le⟩⟩) p, ⟨dist_nonneg, le_rfl⟩⟩ = p) :
    ∃ K : MinimizingHinge p q,
      K.center = H.right ⟨h, ⟨hh.le, hhb.le⟩⟩ ∧
      K.germAngle κ = germComparisonAngle κ (IccExtend dist_nonneg τ)
        (fun t => IccExtend dist_nonneg H.right (h + t)) ∧
      K.modelSide κ = modelSideNegCurvature κ
        (dist (H.right ⟨h, ⟨hh.le, hhb.le⟩⟩) p) (dist H.center q - h)
        (germComparisonAngle κ (IccExtend dist_nonneg τ)
          (fun t => IccExtend dist_nonneg H.right (h + t))) := by
  let z := H.right ⟨h, ⟨hh.le, hhb.le⟩⟩
  have hzq : dist z q = dist H.center q - h := by
    have he := H.right_isometry.dist_eq (⟨h, ⟨hh.le, hhb.le⟩⟩ : Icc (0 : ℝ) (dist H.center q))
      ⟨dist H.center q, ⟨dist_nonneg, le_rfl⟩⟩
    rw [H.right_end] at he
    change dist z q = |h - dist H.center q| at he
    rw [abs_of_neg (sub_neg.mpr hhb)] at he
    linarith
  let ρ : Icc (0 : ℝ) (dist z q) → X := fun t => IccExtend dist_nonneg H.right (h + t)
  have hρ : Isometry ρ := by
    apply Isometry.of_dist_eq
    intro s t
    have hs : (s : ℝ) ∈ Icc (0 : ℝ) (dist H.center q - h) := by rw [← hzq]; exact s.property
    have ht : (t : ℝ) ∈ Icc (0 : ℝ) (dist H.center q - h) := by rw [← hzq]; exact t.property
    change dist (IccExtend dist_nonneg H.right (h + s))
      (IccExtend dist_nonneg H.right (h + t)) = dist s t
    rw [H.right_isometry.IccExtend_forward_dist ⟨hh.le, hhb.le⟩ hs ht,
      Subtype.dist_eq, Real.dist_eq]
  have hρ0 : ρ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = z := by
    change IccExtend dist_nonneg H.right (h + 0) = z
    rw [add_zero]
    exact IccExtend_of_mem _ _ ⟨hh.le, hhb.le⟩
  have hρq : ρ ⟨dist z q, ⟨dist_nonneg, le_rfl⟩⟩ = q := by
    change IccExtend dist_nonneg H.right (h + dist z q) = q
    rw [hzq, show h + (dist H.center q - h) = dist H.center q by ring,
      IccExtend_right, H.right_end]
  let K : MinimizingHinge p q := ⟨z, τ, ρ, hτ, hρ, hτ0, hρ0, hτp, hρq⟩
  have hangle : K.germAngle κ = germComparisonAngle κ (IccExtend dist_nonneg τ)
      (fun t => IccExtend dist_nonneg H.right (h + t)) := by
    apply germComparisonAngle_congr_on (r := 1) (s := dist z q) zero_lt_one
      (by rw [hzq]; exact sub_pos.mpr hhb) (fun _ _ => rfl)
    intro t ht
    exact IccExtend_of_mem _ ρ ⟨ht.1.le, ht.2⟩
  refine ⟨K, rfl, hangle, ?_⟩
  rw [modelSide, hangle]
  change modelSideNegCurvature κ (dist z p) (dist z q) _ = _
  rw [hzq]

end Metric.MinimizingHinge
