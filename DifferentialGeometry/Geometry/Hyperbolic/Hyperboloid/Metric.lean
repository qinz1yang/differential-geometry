import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Defs
import DifferentialGeometry.Geometry.Lorentz.InnerProduct
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.SpecialFunctions.Arcosh

noncomputable section

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def coshDistance (x y : Hyperboloid E) : ℝ :=
  x.time * y.time - inner ℝ x.space y.space

private theorem coshDistance_self (x : Hyperboloid E) : coshDistance x x = 1 := by
  simpa only [coshDistance, ← sq] using x.time_sq_sub_inner_self

private theorem coshDistance_comm (x y : Hyperboloid E) :
    coshDistance x y = coshDistance y x := by
  simp only [coshDistance, real_inner_comm y.space x.space, mul_comm]

private theorem one_le_time (x : Hyperboloid E) : 1 ≤ x.time := by
  have ht := x.time_sq
  nlinarith [sq_nonneg ‖x.space‖, x.time_pos]

private theorem one_le_coshDistance (x y : Hyperboloid E) : 1 ≤ coshDistance x y := by
  have ht : 1 ≤ x.time * y.time := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (one_le_time x))
      (sub_nonneg.mpr (one_le_time y)), one_le_time x, one_le_time y]
  have hs : ‖x.space‖ * ‖y.space‖ ≤ x.time * y.time - 1 := by
    have hx := x.time_sq
    have hy := y.time_sq
    have hp : (‖x.space‖ * ‖y.space‖) ^ 2 ≤ (x.time * y.time - 1) ^ 2 := by
      nlinarith [sq_nonneg (x.time - y.time)]
    nlinarith [norm_nonneg x.space, norm_nonneg y.space]
  have hi := real_inner_le_norm x.space y.space
  dsimp [coshDistance]
  linarith

private abbrev ambient (x : Hyperboloid E) : ℝ × E := (x.time, x.space)

private theorem lorentz_ambient (x y : Hyperboloid E) :
    lorentzForm E (ambient x) (ambient y) = -coshDistance x y := by
  simp only [lorentzForm_apply, ambient, coshDistance]
  ring

private theorem lorentz_ambient_self (x : Hyperboloid E) :
    lorentzForm E (ambient x) (ambient x) = -1 := by
  rw [lorentz_ambient, coshDistance_self]

private def tangent (x y : Hyperboloid E) : ℝ × E :=
  ambient y - coshDistance x y • ambient x

private theorem lorentz_ambient_tangent (x y : Hyperboloid E) :
    lorentzForm E (ambient x) (tangent x y) = 0 := by
  simp only [tangent, map_sub, map_smul, lorentz_ambient, coshDistance_self, smul_eq_mul]
  ring

private theorem lorentz_tangent (x y z : Hyperboloid E) :
    lorentzForm E (tangent x y) (tangent x z) =
      coshDistance x y * coshDistance x z - coshDistance y z := by
  simp only [tangent, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    lorentz_ambient, coshDistance_self, smul_eq_mul, coshDistance_comm y x]
  ring

private theorem norm_tangent_sq_le (x y : Hyperboloid E) :
    ‖(tangent x y).2‖ ^ 2 ≤ x.time ^ 2 * (coshDistance x y ^ 2 - 1) := by
  have h := norm_snd_sq_le_mul_lorentzForm_self_of_orthogonal
    (le_of_eq (lorentz_ambient_self x)) (lorentz_ambient_tangent x y)
  simpa only [lorentz_tangent, coshDistance_self, ambient, ← sq] using h

private theorem eq_of_coshDistance_eq_one {x y : Hyperboloid E}
    (h : coshDistance x y = 1) : x = y := by
  have hn := norm_tangent_sq_le x y
  rw [h] at hn
  have hz : (tangent x y).2 = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (tangent x y).2]
  apply ext
  have hs : y.space - x.space = 0 := by
    simpa only [tangent, Prod.snd_sub, Prod.snd_smul, ambient, h, one_smul] using hz
  exact (sub_eq_zero.mp hs).symm

private def distance (x y : Hyperboloid E) : ℝ := Real.arcosh (coshDistance x y)

private theorem distance_nonneg (x y : Hyperboloid E) : 0 ≤ distance x y :=
  Real.arcosh_nonneg (one_le_coshDistance x y)

private theorem distance_self (x : Hyperboloid E) : distance x x = 0 := by
  simp only [distance, coshDistance_self, Real.arcosh_zero]

private theorem distance_comm (x y : Hyperboloid E) : distance x y = distance y x := by
  rw [distance, distance, coshDistance_comm]

private theorem eq_of_distance_eq_zero {x y : Hyperboloid E} (h : distance x y = 0) : x = y :=
  eq_of_coshDistance_eq_one ((Real.arcosh_eq_zero_iff (one_le_coshDistance x y)).mp h)

private theorem cosh_distance (x y : Hyperboloid E) : Real.cosh (distance x y) = coshDistance x y :=
  Real.cosh_arcosh (one_le_coshDistance x y)

private theorem distance_triangle (x y z : Hyperboloid E) :
    distance x z ≤ distance x y + distance y z := by
  have hy0 : ambient y ≠ 0 := by
    intro h
    have ht := congrArg Prod.fst h
    exact y.time_pos.ne' ht
  have hs := lorentzForm_sq_le_of_orthogonal (le_of_eq (lorentz_ambient_self y) |>.trans (by norm_num))
    hy0 (lorentz_ambient_tangent y x) (lorentz_ambient_tangent y z)
  rw [lorentz_tangent, lorentz_tangent, lorentz_tangent,
    coshDistance_self, coshDistance_self, coshDistance_comm y x] at hs
  have hu : 0 ≤ Real.sinh (distance x y) := Real.sinh_nonneg_iff.mpr (distance_nonneg x y)
  have hv : 0 ≤ Real.sinh (distance y z) := Real.sinh_nonneg_iff.mpr (distance_nonneg y z)
  have hu2 : Real.sinh (distance x y) ^ 2 = coshDistance x y ^ 2 - 1 := by
    rw [Real.sinh_sq, cosh_distance]
  have hv2 : Real.sinh (distance y z) ^ 2 = coshDistance y z ^ 2 - 1 := by
    rw [Real.sinh_sq, cosh_distance]
  have hc : coshDistance x z ≤ coshDistance x y * coshDistance y z +
      Real.sinh (distance x y) * Real.sinh (distance y z) := by
    have hp : 0 ≤ Real.sinh (distance x y) * Real.sinh (distance y z) := mul_nonneg hu hv
    have hp2 : (Real.sinh (distance x y) * Real.sinh (distance y z)) ^ 2 =
        (coshDistance x y ^ 2 - 1) * (coshDistance y z ^ 2 - 1) := by
      rw [mul_pow, hu2, hv2]
    nlinarith
  have hc' : Real.cosh (distance x z) ≤ Real.cosh (distance x y + distance y z) := by
    simpa only [Real.cosh_add, cosh_distance] using hc
  simpa only [abs_of_nonneg (distance_nonneg x z),
    abs_of_nonneg (add_nonneg (distance_nonneg x y) (distance_nonneg y z))] using
    Real.cosh_le_cosh.mp hc'

private theorem norm_space_sub_le (x y : Hyperboloid E) :
    ‖y.space - x.space‖ ≤ (Real.cosh (distance x y) - 1) * ‖x.space‖ +
      x.time * Real.sinh (distance x y) := by
  have ht : ‖(tangent x y).2‖ ≤ x.time * Real.sinh (distance x y) := by
    have h := norm_tangent_sq_le x y
    rw [← cosh_distance, ← Real.sinh_sq] at h
    have hp : 0 ≤ x.time * Real.sinh (distance x y) :=
      mul_nonneg x.time_pos.le (Real.sinh_nonneg_iff.mpr (distance_nonneg x y))
    nlinarith [norm_nonneg (tangent x y).2]
  have he : y.space - x.space =
      (tangent x y).2 + (coshDistance x y - 1) • x.space := by
    change y.space - x.space = (y.space - coshDistance x y • x.space) +
      (coshDistance x y - 1) • x.space
    simp only [sub_smul, one_smul]
    abel
  calc
    ‖y.space - x.space‖ = ‖(tangent x y).2 + (coshDistance x y - 1) • x.space‖ := by rw [he]
    _ ≤ ‖(tangent x y).2‖ + ‖(coshDistance x y - 1) • x.space‖ := norm_add_le _ _
    _ ≤ x.time * Real.sinh (distance x y) + (coshDistance x y - 1) * ‖x.space‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (one_le_coshDistance x y))]
      exact add_le_add ht le_rfl
    _ = (Real.cosh (distance x y) - 1) * ‖x.space‖ +
        x.time * Real.sinh (distance x y) := by rw [cosh_distance]; ring

private theorem continuous_distance (x : Hyperboloid E) : Continuous (distance x) := by
  apply Real.continuousOn_arcosh.comp_continuous
  · exact (continuous_const.mul continuous_time).sub
      (continuous_const.inner continuous_space)
  · exact one_le_coshDistance x

private theorem isOpen_iff_distance (s : Set (Hyperboloid E)) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, distance x y < ε → y ∈ s := by
  constructor
  · intro hs x hx
    have ho : IsOpen ((ofSpace : E → Hyperboloid E) ⁻¹' s) := hs.preimage continuous_ofSpace
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ho x.space (by simpa using hx)
    have hc : Continuous (fun r : ℝ => (Real.cosh r - 1) * ‖x.space‖ + x.time * Real.sinh r) :=
      ((Real.continuous_cosh.sub continuous_const).mul continuous_const).add
        (continuous_const.mul Real.continuous_sinh)
    have hn := hc.continuousAt.preimage_mem_nhds (Iio_mem_nhds (show
      (Real.cosh 0 - 1) * ‖x.space‖ + x.time * Real.sinh 0 < ε by simpa using hε))
    obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp hn
    refine ⟨δ, hδ, fun y hy => ?_⟩
    have hd : distance x y ∈ Metric.ball 0 δ := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg (distance_nonneg x y)] using hy
    have hbound := hb hd
    have hyb : y.space ∈ Metric.ball x.space ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_le_of_lt (norm_space_sub_le x y) hbound
    simpa using hball hyb
  · intro hs
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨ε, hε, hb⟩ := hs x hx
    apply Filter.mem_of_superset ((continuous_distance x).continuousAt.preimage_mem_nhds
      (Iio_mem_nhds (by simpa only [distance_self] using hε)))
    exact hb

instance : MetricSpace (Hyperboloid E) :=
  MetricSpace.ofDistTopology distance distance_self distance_comm distance_triangle
    isOpen_iff_distance (fun _ _ => eq_of_distance_eq_zero)

theorem dist_eq_arcosh (x y : Hyperboloid E) :
    dist x y = Real.arcosh (x.time * y.time - inner ℝ x.space y.space) := rfl

theorem cosh_dist (x y : Hyperboloid E) :
    Real.cosh (dist x y) = x.time * y.time - inner ℝ x.space y.space :=
  cosh_distance x y

end DifferentialGeometry.Hyperboloid
