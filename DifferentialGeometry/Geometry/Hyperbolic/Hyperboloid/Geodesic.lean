import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Metric
import Mathlib.Topology.MetricSpace.Isometry

noncomputable section

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem lorentz_self (x : Hyperboloid E) :
    lorentzForm E (x.time, x.space) (x.time, x.space) = -1 := by
  rw [lorentzForm_apply]
  nlinarith [x.time_sq_sub_inner_self]

private theorem lorentz_cosh_sinh (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0)
    (s t : ℝ) :
    lorentzForm E (Real.cosh s • (x.time, x.space) + Real.sinh s • v)
      (Real.cosh t • (x.time, x.space) + Real.sinh t • v) = -Real.cosh (t - s) := by
  have ho' : lorentzForm E v (x.time, x.space) = 0 := by
    have hsym : lorentzForm E v (x.time, x.space) =
        lorentzForm E (x.time, x.space) v := by
      simpa using (lorentzForm_isSymm E).eq v (x.time, x.space)
    exact hsym.trans ho
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, lorentz_self, ho, ho', hv, Real.cosh_sub]
  ring

private theorem time_cosh_sinh_pos (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0)
    (t : ℝ) : 0 < Real.cosh t * x.time + Real.sinh t * v.1 := by
  have hn := norm_snd_sq_le_mul_lorentzForm_self_of_orthogonal (lorentz_self x).le ho
  rw [hv] at hn
  have hv' : ‖v.2‖ ^ 2 - v.1 * v.1 = 1 := by
    simpa only [lorentzForm_apply, real_inner_self_eq_norm_sq] using hv
  have hvt : |v.1| < x.time := by
    nlinarith [sq_abs v.1, abs_nonneg v.1, x.time_pos]
  have hsc : |Real.sinh t| < Real.cosh t := by
    nlinarith [Real.cosh_sq_sub_sinh_sq t, sq_abs (Real.sinh t),
      abs_nonneg (Real.sinh t), Real.cosh_pos t]
  have hprod : |Real.sinh t * v.1| < Real.cosh t * x.time := calc
    |Real.sinh t * v.1| = |Real.sinh t| * |v.1| := abs_mul _ _
    _ ≤ |Real.sinh t| * x.time := mul_le_mul_of_nonneg_left hvt.le (abs_nonneg _)
    _ < Real.cosh t * x.time := mul_lt_mul_of_pos_right hsc x.time_pos
  linarith [neg_abs_le (Real.sinh t * v.1)]

def geodesicLine (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0)
    (t : ℝ) : Hyperboloid E where
  time := Real.cosh t * x.time + Real.sinh t * v.1
  space := Real.cosh t • x.space + Real.sinh t • v.2
  time_pos := time_cosh_sinh_pos x v hv ho t
  time_sq_sub_inner_self := by
    have h := lorentz_cosh_sinh x v hv ho t t
    change inner ℝ (Real.cosh t • x.space + Real.sinh t • v.2)
      (Real.cosh t • x.space + Real.sinh t • v.2) -
      (Real.cosh t * x.time + Real.sinh t * v.1) *
      (Real.cosh t * x.time + Real.sinh t * v.1) = -Real.cosh (t - t) at h
    rw [sub_self, Real.cosh_zero] at h
    nlinarith

@[simp] theorem geodesicLine_time (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0)
    (t : ℝ) : (geodesicLine x v hv ho t).time =
      Real.cosh t * x.time + Real.sinh t * v.1 := rfl

@[simp] theorem geodesicLine_space (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0)
    (t : ℝ) : (geodesicLine x v hv ho t).space =
      Real.cosh t • x.space + Real.sinh t • v.2 := rfl

@[simp] theorem geodesicLine_zero (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0) :
    geodesicLine x v hv ho 0 = x := by
  ext
  simp

theorem lorentzForm_geodesicLine (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0)
    (s t : ℝ) :
    lorentzForm E ((geodesicLine x v hv ho s).time, (geodesicLine x v hv ho s).space)
      ((geodesicLine x v hv ho t).time, (geodesicLine x v hv ho t).space) =
        -Real.cosh (t - s) :=
  lorentz_cosh_sinh x v hv ho s t

theorem isometry_geodesicLine (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0) :
    Isometry (geodesicLine x v hv ho) := by
  apply Isometry.of_dist_eq
  intro s t
  rw [dist_eq_arcosh]
  have h := lorentzForm_geodesicLine x v hv ho s t
  rw [lorentzForm_apply] at h
  have hc : (geodesicLine x v hv ho s).time * (geodesicLine x v hv ho t).time -
      inner ℝ (geodesicLine x v hv ho s).space (geodesicLine x v hv ho t).space =
        Real.cosh (t - s) := by linarith
  rw [hc, ← Real.cosh_abs (t - s), Real.arcosh_cosh (abs_nonneg _), Real.dist_eq, abs_sub_comm]

theorem exists_geodesicLine_through {x y : Hyperboloid E} (hxy : x ≠ y) :
    ∃ (v : ℝ × E) (hv : lorentzForm E v v = 1)
      (ho : lorentzForm E (x.time, x.space) v = 0),
      geodesicLine x v hv ho (dist x y) = y := by
  let q := Real.cosh (dist x y)
  let r := Real.sinh (dist x y)
  let w : ℝ × E := (y.time, y.space) - q • (x.time, x.space)
  let v : ℝ × E := r⁻¹ • w
  have hr : r ≠ 0 := (Real.sinh_pos_iff.mpr (dist_pos.mpr hxy)).ne'
  have hxyB : lorentzForm E (x.time, x.space) (y.time, y.space) = -q := by
    dsimp [q]
    rw [cosh_dist]
    ring
  have hyxB : lorentzForm E (y.time, y.space) (x.time, x.space) = -q := by
    have hsym : lorentzForm E (y.time, y.space) (x.time, x.space) =
        lorentzForm E (x.time, x.space) (y.time, y.space) := by
      simpa using (lorentzForm_isSymm E).eq (y.time, y.space) (x.time, x.space)
    exact hsym.trans hxyB
  have hw : lorentzForm E w w = r ^ 2 := by
    change lorentzForm E ((y.time, y.space) - q • (x.time, x.space))
      ((y.time, y.space) - q • (x.time, x.space)) = r ^ 2
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, lorentz_self, hxyB, hyxB]
    dsimp [r, q]
    rw [Real.sinh_sq]
    ring
  have hwo : lorentzForm E (x.time, x.space) w = 0 := by
    simp only [w, map_sub, map_smul, smul_eq_mul, hxyB, lorentz_self]
    ring
  have hv : lorentzForm E v v = 1 := by
    simp only [v, map_smul, LinearMap.smul_apply, smul_eq_mul, hw]
    field_simp [hr]
  have ho : lorentzForm E (x.time, x.space) v = 0 := by
    simp only [v, map_smul, hwo, smul_zero]
  refine ⟨v, hv, ho, ?_⟩
  apply ext
  change q • x.space + r • (r⁻¹ • (y.space - q • x.space)) = y.space
  rw [smul_smul, mul_inv_cancel₀ hr, one_smul]
  abel

theorem exists_isometry_through {x y : Hyperboloid E} (hxy : x ≠ y) :
    ∃ c : ℝ → Hyperboloid E, Isometry c ∧ c 0 = x ∧ c (dist x y) = y := by
  obtain ⟨v, hv, ho, hy⟩ := exists_geodesicLine_through hxy
  exact ⟨geodesicLine x v hv ho, isometry_geodesicLine x v hv ho,
    geodesicLine_zero x v hv ho, hy⟩

end DifferentialGeometry.Hyperboloid
