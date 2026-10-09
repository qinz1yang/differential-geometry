import DifferentialGeometry.Analysis.SpecialFunctions.Trigonometric.CosineInverseEstimate
import DifferentialGeometry.Geometry.Comparison.ModelAngleFiniteDifference
import DifferentialGeometry.Geometry.Comparison.FourPoint

set_option autoImplicit false

open Set Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X]

theorem abs_comparisonAngleNegCurvature_sum_sub_pi_le
    (x z u : X) {a A : ℝ} (ha : 0 < a)
    (hxu : dist x u ∈ Icc a A) (hzu : dist z u ∈ Icc a A)
    (hs : 0 < dist x z) (hs1 : dist x z ≤ 1) (hsa : dist x z ≤ a / 2) :
    |comparisonAngleNegCurvature 1 (dist z u) (dist z x) (dist u x) +
      comparisonAngleNegCurvature 1 (dist x u) (dist x z) (dist u z) - Real.pi| ≤
      Real.pi * sqrt ((4 * cosh (A + 1) / sinh a) * dist x z) := by
  let θx := comparisonAngleNegCurvature 1 (dist x u) (dist x z) (dist u z)
  let θz := comparisonAngleNegCurvature 1 (dist z u) (dist z x) (dist u x)
  let K := 4 * cosh (A + 1) / sinh a
  have hf := abs_dist_sub_add_cos_comparisonAngleNegCurvature_one_le x z u
    ha hxu.1 hxu.2 hs hs1 hsa
  have hb := abs_dist_sub_add_cos_comparisonAngleNegCurvature_one_le z x u
    ha hzu.1 hzu.2 (by rwa [dist_comm z x]) (by rwa [dist_comm z x]) (by rwa [dist_comm z x])
  rw [dist_comm z u] at hf
  rw [dist_comm x u] at hb
  change |dist u z - dist x u + dist x z * cos θx| ≤ K * (dist x z) ^ 2 at hf
  change |dist u x - dist z u + dist z x * cos θz| ≤ K * (dist z x) ^ 2 at hb
  rw [dist_comm u z] at hf
  rw [dist_comm u x, dist_comm z x] at hb
  have hc : |cos θz + cos θx| ≤ 2 * (K * dist x z) := by
    apply abs_le.mpr
    constructor
    · apply (mul_le_mul_iff_left₀ hs).mp
      nlinarith [(abs_le.mp hf).1, (abs_le.mp hb).1]
    · apply (mul_le_mul_iff_left₀ hs).mp
      nlinarith [(abs_le.mp hf).2, (abs_le.mp hb).2]
  have hx := comparisonAngleNegCurvature_mem_Icc 1 (dist x u) (dist x z) (dist u z)
  have hz := comparisonAngleNegCurvature_mem_Icc 1 (dist z u) (dist z x) (dist u x)
  change θx ∈ Icc 0 Real.pi at hx
  change θz ∈ Icc 0 Real.pi at hz
  have h := abs_sub_le_pi_mul_sqrt_of_abs_cos_sub_le hz
    (show Real.pi - θx ∈ Icc 0 Real.pi by constructor <;> linarith [hx.1, hx.2])
    (by simpa only [cos_pi_sub, sub_neg_eq_add] using hc)
  change |θz + θx - Real.pi| ≤ _
  convert h using 1; congr 1; ring

theorem comparisonAngleNegCurvature_complement_bounds
    {Ω : Set X} (hcomp : fourPointComparison 1 Ω)
    {x z u v : X} (hx : x ∈ Ω) (hz : z ∈ Ω) (hu : u ∈ Ω) (hv : v ∈ Ω)
    {a A δ : ℝ} (ha : 0 < a)
    (hxu : dist x u ∈ Icc a A) (hzu : dist z u ∈ Icc a A)
    (hxv : dist x v ∈ Icc a A) (hzv : dist z v ∈ Icc a A)
    (hs : 0 < dist x z) (hs1 : dist x z ≤ 1) (hsa : dist x z ≤ a / 2)
    (hpairx : Real.pi - δ < comparisonAngleNegCurvature 1 (dist x u) (dist x v) (dist u v))
    (hpairz : Real.pi - δ < comparisonAngleNegCurvature 1 (dist z u) (dist z v) (dist u v)) :
    let ω := Real.pi * sqrt ((4 * cosh (A + 1) / sinh a) * dist x z)
    Real.pi - δ - 2 * ω ≤
      comparisonAngleNegCurvature 1 (dist z u) (dist z x) (dist u x) +
      comparisonAngleNegCurvature 1 (dist z v) (dist z x) (dist v x) ∧
      comparisonAngleNegCurvature 1 (dist z u) (dist z x) (dist u x) +
      comparisonAngleNegCurvature 1 (dist z v) (dist z x) (dist v x) ≤ Real.pi + δ := by
  let θ (p b c : X) := comparisonAngleNegCurvature 1 (dist p b) (dist p c) (dist b c)
  have hsym (p b c : X) : θ p b c = θ p c b := by
    dsimp [θ]
    rw [comparisonAngleNegCurvature_comm, dist_comm b c]
  have hne {p b : X} (h : dist p b ∈ Icc a A) : b ≠ p := (dist_pos.mp (ha.trans_le h.1)).symm
  have hfourx : θ x u z + θ x z v + θ x v u ≤ 2 * Real.pi :=
    hcomp x hx u hu z hz v hv (hne hxu) (dist_pos.mp hs).symm (hne hxv)
  have hfourz : θ z u x + θ z x v + θ z v u ≤ 2 * Real.pi :=
    hcomp z hz u hu x hx v hv (hne hzu) (dist_pos.mp hs) (hne hzv)
  rw [hsym x z v, hsym x v u] at hfourx
  rw [hsym z x v, hsym z v u] at hfourz
  have hru := abs_comparisonAngleNegCurvature_sum_sub_pi_le x z u ha hxu hzu hs hs1 hsa
  have hrv := abs_comparisonAngleNegCurvature_sum_sub_pi_le x z v ha hxv hzv hs hs1 hsa
  change |θ z u x + θ x u z - Real.pi| ≤ _ at hru
  change |θ z v x + θ x v z - Real.pi| ≤ _ at hrv
  change Real.pi - δ < θ x u v at hpairx
  change Real.pi - δ < θ z u v at hpairz
  change Real.pi - δ - 2 * _ ≤ θ z u x + θ z v x ∧ θ z u x + θ z v x ≤ Real.pi + δ
  constructor
  · linarith [(abs_le.mp hru).1, (abs_le.mp hrv).1]
  · linarith

end DifferentialGeometry.Geometry.Comparison.Toponogov
