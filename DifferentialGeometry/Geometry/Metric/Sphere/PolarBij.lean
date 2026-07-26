import DifferentialGeometry.Geometry.Metric.Sphere.Polar

/-!
# The polar-coordinate bijection on the round sphere

This file packages the ambient polar decomposition as a bijection between the
open polar cylinder and the unit sphere with its two poles removed.
-/

noncomputable section

open Metric Set
open scoped InnerProductSpace

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The ambient polar inverse is a left inverse on the open polar cylinder. -/
theorem polar_left_inv
    {p : E} (hp : ‖p‖ = 1) :
    Set.LeftInvOn (spherePolarInv p) (spherePolar p)
      (Ioo 0 Real.pi ×ˢ
        {w : E | ⟪p, w⟫_ℝ = 0 ∧ ‖w‖ = 1}) := by
  rintro ⟨r, w⟩ hq
  change r ∈ Ioo 0 Real.pi ∧
    (⟪p, w⟫_ℝ = 0 ∧ ‖w‖ = 1) at hq
  rcases hq with ⟨hr, hpw, -⟩
  have hpp : ⟪p, p⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hp, one_pow]
  have hinner :
      ⟪p, spherePolar p (r, w)⟫_ℝ = Real.cos r := by
    simp only [spherePolar, inner_add_right, real_inner_smul_right,
      hpp, hpw, mul_one, mul_zero, add_zero]
  have harccos :
      Real.arccos ⟪p, spherePolar p (r, w)⟫_ℝ = r := by
    rw [hinner, Real.arccos_cos hr.1.le hr.2.le]
  have hsin : Real.sin r ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hr.1 hr.2).ne'
  apply Prod.ext
  · simp only [spherePolarInv, harccos]
  · simp only [spherePolarInv]
    rw [hinner, Real.arccos_cos hr.1.le hr.2.le]
    change
      (Real.sin r)⁻¹ •
        (Real.cos r • p + Real.sin r • w - Real.cos r • p) = w
    rw [add_sub_cancel_left, smul_smul,
      inv_mul_cancel₀ hsin, one_smul]

/-- Polar coordinates biject the open polar cylinder with the punctured unit
sphere. -/
theorem polar_bijOn
    {p : E} (hp : ‖p‖ = 1) :
    Set.BijOn (spherePolar p)
      (Ioo 0 Real.pi ×ˢ
        {w : E | ⟪p, w⟫_ℝ = 0 ∧ ‖w‖ = 1})
      {x : E | ‖x‖ = 1 ∧ x ≠ p ∧ x ≠ -p} := by
  have hpp : ⟪p, p⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hp, one_pow]
  have hleft := polar_left_inv hp
  refine ⟨?_, hleft.injOn, ?_⟩
  · rintro ⟨r, w⟩ hq
    change r ∈ Ioo 0 Real.pi ∧
      (⟪p, w⟫_ℝ = 0 ∧ ‖w‖ = 1) at hq
    rcases hq with ⟨hr, hpw, hwn⟩
    have hq' :
        (r, w) ∈ Ioo 0 Real.pi ×ˢ
          {w : E | ⟪p, w⟫_ℝ = 0 ∧ ‖w‖ = 1} :=
      ⟨hr, hpw, hwn⟩
    have horth :
        ⟪Real.cos r • p, Real.sin r • w⟫_ℝ = 0 := by
      simp only [real_inner_smul_left, real_inner_smul_right,
        hpw, mul_zero]
    have hnorm_sq :
        ‖spherePolar p (r, w)‖ ^ 2 = 1 := by
      change ‖Real.cos r • p + Real.sin r • w‖ ^ 2 = 1
      rw [norm_add_sq_real]
      simp only [horth, mul_zero, add_zero, norm_smul,
        Real.norm_eq_abs, hp, hwn, mul_one, sq_abs]
      exact Real.cos_sq_add_sin_sq r
    have hnorm : ‖spherePolar p (r, w)‖ = 1 := by
      nlinarith [norm_nonneg (spherePolar p (r, w))]
    refine ⟨hnorm, ?_, ?_⟩
    · intro heq
      have hfst :=
        congrArg Prod.fst (hleft hq')
      rw [heq] at hfst
      simp only [spherePolarInv, hpp,
        Real.arccos_one] at hfst
      exact (ne_of_lt hr.1) hfst
    · intro heq
      have hfst :=
        congrArg Prod.fst (hleft hq')
      rw [heq] at hfst
      simp only [spherePolarInv, inner_neg_right,
        hpp, Real.arccos_neg_one] at hfst
      exact (ne_of_lt hr.2) hfst.symm
  · intro x hx
    have hdec := polar_decomp hp hx.1 hx.2.1 hx.2.2
    dsimp only at hdec
    rcases hdec with ⟨hr, hpw, hwn, hpolar⟩
    refine ⟨spherePolarInv p x, ?_, ?_⟩
    · simpa only [spherePolarInv] using ⟨hr, hpw, hwn⟩
    · simpa only [spherePolarInv] using hpolar

end Geometry
end DifferentialGeometry
