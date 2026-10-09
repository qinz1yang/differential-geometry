import DifferentialGeometry.Geometry.Metric.EuclideanCone
import DifferentialGeometry.Geometry.Comparison.FourPoint
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped NNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

private theorem sine_interpolation_square {a b : ℝ}
    (hD : Real.sin a + Real.sin b ≠ 0) :
    (Real.sin (a + b) / (Real.sin a + Real.sin b)) ^ 2 + 1 -
      2 * (Real.sin (a + b) / (Real.sin a + Real.sin b)) * Real.cos a =
    (Real.sin a / (Real.sin a + Real.sin b)) ^ 2 * (2 - 2 * Real.cos (a + b)) := by
  rw [Real.sin_add, Real.cos_add]
  field_simp
  linear_combination (Real.sin a)^2 * Real.sin_sq_add_cos_sq b -
    ((Real.sin b)^2 + 2 * Real.sin a * Real.sin b) * Real.sin_sq_add_cos_sq a

private theorem sine_interpolation_cos {a b : ℝ}
    (hD : Real.sin a + Real.sin b ≠ 0) :
    (Real.sin (a + b) / (Real.sin a + Real.sin b)) * Real.cos a =
      1 - Real.sin a / (Real.sin a + Real.sin b) +
        (Real.sin a / (Real.sin a + Real.sin b)) * Real.cos (a + b) := by
  rw [Real.sin_add, Real.cos_add]
  field_simp
  linear_combination Real.sin b * Real.sin_sq_add_cos_sq a


theorem exists_sine_interpolating_cone_point
    {Y : Type*} [MetricSpace Y] {q u x : Y}
    (ha : 0 < dist q u) (hb : 0 < dist u x)
    (hadd : dist q x = dist q u + dist u x) (hshort : dist q x < Real.pi) :
    let t := Real.sin (dist q u) / (Real.sin (dist q u) + Real.sin (dist u x))
    ∃ r : ℝ≥0,
      (r : ℝ) = Real.sin (dist q x) / (Real.sin (dist q u) + Real.sin (dist u x)) ∧
      0 < (r : ℝ) ∧ t ∈ Ioo (0 : ℝ) 1 ∧
      dist (EuclideanCone.mk 1 q) (EuclideanCone.mk r u) =
        t * dist (EuclideanCone.mk 1 q) (EuclideanCone.mk 1 x) ∧
      dist (EuclideanCone.mk r u) (EuclideanCone.mk 1 x) =
        (1-t) * dist (EuclideanCone.mk 1 q) (EuclideanCone.mk 1 x) := by
  let a := dist q u
  let b := dist u x
  let D := Real.sin a + Real.sin b
  let t := Real.sin a / D
  have hab : a + b < Real.pi := by simpa [a, b, hadd] using hshort
  have haπ : a < Real.pi := by dsimp [a, b] at *; linarith
  have hbπ : b < Real.pi := by dsimp [a, b] at *; linarith
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha haπ
  have hsb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb hbπ
  have hsA : 0 < Real.sin (a+b) :=
    Real.sin_pos_of_pos_of_lt_pi (add_pos ha hb) hab
  have hD : 0 < D := add_pos hsa hsb
  have ht : t ∈ Ioo (0 : ℝ) 1 := by
    exact ⟨div_pos hsa hD, (div_lt_one hD).mpr (by dsimp [D]; linarith)⟩
  let r : ℝ≥0 := ⟨Real.sin (a+b) / D, (div_pos hsA hD).le⟩
  have hQX : dist (EuclideanCone.mk 1 q) (EuclideanCone.mk 1 x) ^ 2 =
      2 - 2 * Real.cos (a+b) := by
    rw [EuclideanCone.dist_mk, coneDistance_sq (by norm_num) (by norm_num)]
    change 1^2 + 1^2 - 2*1*1*Real.cos (min Real.pi (dist q x)) = _
    rw [min_eq_right hshort.le, hadd]
    ring
  refine ⟨r, ?_, div_pos hsA hD, ht, ?_, ?_⟩
  · change Real.sin (a+b) / D = _
    rw [hadd]
  · have hQU : dist (EuclideanCone.mk 1 q) (EuclideanCone.mk r u) ^ 2 =
        (r : ℝ)^2 + 1 - 2 * r * Real.cos a := by
      rw [EuclideanCone.dist_mk, coneDistance_sq (by norm_num) r.property]
      change 1^2 + (r : ℝ)^2 - 2*1*r*Real.cos (min Real.pi a) = _
      rw [min_eq_right haπ.le]
      ring
    apply (sq_eq_sq₀ dist_nonneg (mul_nonneg ht.1.le dist_nonneg)).mp
    rw [hQU, mul_pow, hQX]
    exact sine_interpolation_square hD.ne'
  · have hUX : dist (EuclideanCone.mk r u) (EuclideanCone.mk 1 x) ^ 2 =
        (r : ℝ)^2 + 1 - 2 * r * Real.cos b := by
      rw [EuclideanCone.dist_mk, coneDistance_sq r.property (by norm_num)]
      change (r : ℝ)^2 + 1^2 - 2*r*1*Real.cos (min Real.pi b) = _
      rw [min_eq_right hbπ.le]
      ring
    have hbweight : Real.sin b / D = 1-t := by
      dsimp [D, t]
      field_simp
      ring
    apply (sq_eq_sq₀ dist_nonneg (mul_nonneg (sub_nonneg.mpr ht.2.le) dist_nonneg)).mp
    rw [hUX, mul_pow, hQX]
    have hh := sine_interpolation_square (a := b) (b := a)
      (show Real.sin b + Real.sin a ≠ 0 by simpa [add_comm] using hD.ne')
    simp only [add_comm b a, add_comm (Real.sin b) (Real.sin a)] at hh
    change (r : ℝ)^2 + 1 - 2*r*Real.cos b =
      (Real.sin b / D)^2 * (2-2*Real.cos (a+b)) at hh
    rw [hbweight] at hh
    exact hh


theorem sine_weighted_cosine_comparison_of_cone_comparison
    {Y : Type*} [MetricSpace Y]
    (hdiam : ∀ v w : Y, dist v w ≤ Real.pi)
    (hcone : fourPointComparison 0 (univ : Set (EuclideanCone Y)))
    {q u x z : Y} (ha : 0 < dist q u) (hb : 0 < dist u x)
    (hadd : dist q x = dist q u + dist u x) (hshort : dist q x < Real.pi) :
    Real.sin (dist q x) * Real.cos (dist u z) ≤
      Real.sin (dist u x) * Real.cos (dist q z) +
        Real.sin (dist q u) * Real.cos (dist x z) := by
  obtain ⟨r, hr, hrpos, ht, hQU, hUX⟩ :=
    exists_sine_interpolating_cone_point ha hb hadd hshort
  let a := dist q u
  let b := dist u x
  let A := dist q x
  let D := Real.sin a + Real.sin b
  let t := Real.sin a / D
  have hsa : 0 < Real.sin a :=
    Real.sin_pos_of_pos_of_lt_pi ha (by dsimp [a]; linarith)
  have hsb : 0 < Real.sin b :=
    Real.sin_pos_of_pos_of_lt_pi hb (by dsimp [b]; linarith)
  have hD : 0 < D := add_pos hsa hsb
  have hsquare (r s : ℝ≥0) (v w : Y) :
      dist (EuclideanCone.mk r v) (EuclideanCone.mk s w)^2 =
      (r : ℝ)^2 + (s : ℝ)^2 - 2*r*s*Real.cos (dist v w) := by
    rw [EuclideanCone.dist_mk, coneDistance_sq r.property s.property,
      min_eq_right (hdiam v w)]
  have hquad := quadratic_side_comparison_of_fourPointComparison hcone
    (mem_univ (EuclideanCone.mk 1 q)) (mem_univ (EuclideanCone.mk 1 x))
    (mem_univ (EuclideanCone.mk r u)) (mem_univ (EuclideanCone.mk 1 z))
    ⟨ht.1.le, ht.2.le⟩ hQU hUX
  rw [hsquare, hsquare, hsquare, hsquare] at hquad
  simp only [NNReal.coe_one, one_pow, mul_one, dist_comm z q,
    dist_comm z x, dist_comm z u] at hquad
  have hr2 : (r : ℝ)^2 = 1 - 2*t*(1-t)*(1-Real.cos A) := by
    have h1 := sine_interpolation_square (a := a) (b := b) hD.ne'
    have h2 := sine_interpolation_cos (a := a) (b := b) hD.ne'
    have hA : a+b = A := hadd.symm
    rw [hA] at h1 h2
    change (Real.sin A / D)^2 + 1 - 2*(Real.sin A / D)*Real.cos a =
      t^2 * (2-2*Real.cos A) at h1
    change (Real.sin A / D)*Real.cos a = 1-t+t*Real.cos A at h2
    rw [hr]
    change (Real.sin A / D)^2 = _
    nlinarith only [h1,h2]
  have hcos : (r : ℝ)*Real.cos (dist u z) ≤
      (1-t)*Real.cos (dist q z) + t*Real.cos (dist x z) := by
    change (1-t)*(1+1-2*Real.cos (dist q z)) +
      t*(1+1-2*Real.cos (dist x z)) -
      t*(1-t)*(1+1-2*Real.cos A) ≤
      1+(r : ℝ)^2-2*r*Real.cos (dist u z) at hquad
    rw [hr2] at hquad
    nlinarith only [hquad]
  have hmul := mul_le_mul_of_nonneg_left hcos hD.le
  have hweight : D*(1-t) = Real.sin b := by
    dsimp [D,t]
    field_simp
    ring
  have htweight : D*t = Real.sin a := by
    dsimp [t]
    exact mul_div_cancel₀ _ hD.ne'
  have hrweight : D*(r : ℝ) = Real.sin A := by
    rw [hr]
    exact mul_div_cancel₀ _ hD.ne'
  calc
    Real.sin (dist q x) * Real.cos (dist u z) =
        D*((r : ℝ)*Real.cos (dist u z)) := by rw [← mul_assoc,hrweight]
    _ ≤ D*((1-t)*Real.cos (dist q z)+t*Real.cos (dist x z)) := hmul
    _ = _ := by rw [mul_add,← mul_assoc,← mul_assoc,hweight,htweight]

end DifferentialGeometry.Geometry.Comparison.Toponogov
