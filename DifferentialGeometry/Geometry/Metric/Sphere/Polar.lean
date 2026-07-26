import DifferentialGeometry.Geometry.Metric.Sphere.RoundMetric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Polar coordinates on the round sphere

This file records the ambient algebra needed to read a point of the unit
sphere, away from a pair of antipodes, in polar coordinates about one pole.
The results are deliberately independent of the intrinsic exponential map.
-/

noncomputable section

open Metric Set
open scoped ContDiff InnerProductSpace

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The ambient polar map about `p`. -/
def spherePolar (p : E) (q : ℝ × E) : E :=
  Real.cos q.1 • p + Real.sin q.1 • q.2

/-- The ambient polar-coordinate inverse about `p`, on the locus where it is
defined smoothly. -/
def spherePolarInv (p x : E) : ℝ × E :=
  (Real.arccos ⟪p, x⟫_ℝ,
    (Real.sin (Real.arccos ⟪p, x⟫_ℝ))⁻¹ •
      (x - ⟪p, x⟫_ℝ • p))

/-- The ambient polar map is smooth. -/
theorem spherePolar_smooth (p : E) :
    ContDiff ℝ ∞ (spherePolar p) := by
  exact
    ((Real.contDiff_cos.comp contDiff_fst).smul contDiff_const).add
      ((Real.contDiff_sin.comp contDiff_fst).smul contDiff_snd)

/-- The polar-coordinate inverse is smooth away from the two pole levels. -/
theorem polarInv_smooth (p : E) :
    ContDiffOn ℝ ∞ (spherePolarInv p)
      {x : E | |⟪p, x⟫_ℝ| < 1} := by
  intro x hx
  change |⟪p, x⟫_ℝ| < 1 at hx
  have hne_one : ⟪p, x⟫_ℝ ≠ 1 := by
    intro h
    rw [h] at hx
    simp at hx
  have hne_neg : ⟪p, x⟫_ℝ ≠ -1 := by
    intro h
    rw [h] at hx
    simp at hx
  have hinner :
      ContDiffAt ℝ ∞ (fun y : E => ⟪p, y⟫_ℝ) x :=
    (contDiff_const.inner ℝ contDiff_id).contDiffAt
  have harccos :
      ContDiffAt ℝ ∞ (fun y : E => Real.arccos ⟪p, y⟫_ℝ) x :=
    (Real.contDiffAt_arccos hne_neg hne_one).comp x hinner
  have hsin :
      Real.sin (Real.arccos ⟪p, x⟫_ℝ) ≠ 0 := by
    rw [Real.sin_arccos]
    refine (Real.sqrt_pos.mpr ?_).ne'
    have hb := abs_lt.mp hx
    have hprod :
        0 < (1 - ⟪p, x⟫_ℝ) * (1 + ⟪p, x⟫_ℝ) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have hsecond :
      ContDiffAt ℝ ∞
        (fun y : E =>
          (Real.sin (Real.arccos ⟪p, y⟫_ℝ))⁻¹ •
            (y - ⟪p, y⟫_ℝ • p)) x := by
    refine ContDiffAt.smul ?_ ?_
    · exact
        (Real.contDiff_sin.contDiffAt.comp x harccos).inv hsin
    · exact contDiffAt_id.sub (hinner.smul contDiffAt_const)
  exact (harccos.prodMk hsecond).contDiffWithinAt

/-- Every unit vector other than the two poles has the canonical polar
decomposition about `p`. -/
theorem polar_decomp
    {p x : E} (hp : ‖p‖ = 1) (hx : ‖x‖ = 1)
    (hxp : x ≠ p) (hxnp : x ≠ -p) :
    let r := Real.arccos ⟪p, x⟫_ℝ
    let w := (Real.sin r)⁻¹ • (x - ⟪p, x⟫_ℝ • p)
    r ∈ Ioo 0 Real.pi ∧
      ⟪p, w⟫_ℝ = 0 ∧ ‖w‖ = 1 ∧
        spherePolar p (r, w) = x := by
  let t : ℝ := ⟪p, x⟫_ℝ
  let r : ℝ := Real.arccos t
  let w : E := (Real.sin r)⁻¹ • (x - t • p)
  have ht_le : t ≤ 1 :=
    real_inner_le_one_of_norm_eq_one hp hx
  have ht_ne : t ≠ 1 := by
    intro ht
    apply hxp
    exact ((inner_eq_one_iff_of_norm_eq_one hp hx).mp ht).symm
  have ht_lt : t < 1 := lt_of_le_of_ne ht_le ht_ne
  have hneg_le : -1 ≤ t :=
    neg_one_le_real_inner_of_norm_eq_one hp hx
  have hneg_ne : (-1 : ℝ) ≠ t := by
    intro ht
    apply hxnp
    have hinner : ⟪x, p⟫_ℝ = -1 := by
      rw [real_inner_comm]
      exact ht.symm
    exact (inner_eq_neg_one_iff_of_norm_eq_one hx hp).mp hinner
  have ht_gt : -1 < t := lt_of_le_of_ne hneg_le hneg_ne
  have hr_mem : r ∈ Ioo 0 Real.pi :=
    ⟨Real.arccos_pos.mpr ht_lt, Real.arccos_lt_pi.mpr ht_gt⟩
  have hcos : Real.cos r = t :=
    Real.cos_arccos ht_gt.le ht_lt.le
  have hsin_formula :
      Real.sin r = Real.sqrt (1 - t ^ 2) :=
    Real.sin_arccos t
  have ht_sq : t ^ 2 < 1 := by
    nlinarith [
      mul_pos (by linarith : (0 : ℝ) < 1 - t)
        (by linarith : (0 : ℝ) < 1 + t)]
  have hsin_pos : 0 < Real.sin r := by
    rw [hsin_formula]
    exact Real.sqrt_pos.mpr (by linarith)
  have hpp : ⟪p, p⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hp, one_pow]
  have hpw : ⟪p, w⟫_ℝ = 0 := by
    simp only [w]
    rw [real_inner_smul_right, inner_sub_right,
      real_inner_smul_right, hpp]
    change (Real.sin r)⁻¹ * (t - t * 1) = 0
    ring
  have hxt :
      ‖x - t • p‖ ^ 2 = 1 - t ^ 2 := by
    have hxp_inner : ⟪x, p⟫_ℝ = t := by
      rw [real_inner_comm]
    rw [← real_inner_self_eq_norm_sq, inner_sub_sub_self]
    simp only [real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, hx, hp, hxp_inner]
    rw [show ⟪p, x⟫_ℝ = t from rfl]
    ring
  have hwn : ‖w‖ = 1 := by
    simp only [w]
    rw [norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos hsin_pos]
    have hxn : ‖x - t • p‖ = Real.sin r := by
      rw [hsin_formula, ← hxt]
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    rw [hxn, inv_mul_cancel₀ hsin_pos.ne']
  have hpolar : spherePolar p (r, w) = x := by
    simp only [spherePolar, w]
    rw [smul_smul,
      mul_inv_cancel₀ hsin_pos.ne', one_smul, hcos]
    abel
  exact ⟨hr_mem, hpw, hwn, hpolar⟩

end Geometry
end DifferentialGeometry
