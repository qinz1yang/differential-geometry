import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

noncomputable section

open Set Metric Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions


def bicollarLineHomeomorph {A : Type*} [TopologicalSpace A] (a : ℝ) (ha : 0 < a) :
    A × ℝ ≃ₜ {p : A × ℝ // -a < p.2 ∧ p.2 < a} where
  toFun p := ⟨(p.1, OpenPartialHomeomorph.univBall (0 : ℝ) a p.2), by
    have hp := (OpenPartialHomeomorph.univBall (0 : ℝ) a).map_source
      (by simp : p.2 ∈ (OpenPartialHomeomorph.univBall (0 : ℝ) a).source)
    rw [OpenPartialHomeomorph.univBall_target _ ha, Real.ball_eq_Ioo] at hp
    simpa using hp⟩
  invFun p := (p.1.1, (OpenPartialHomeomorph.univBall (0 : ℝ) a).symm p.1.2)
  left_inv p := Prod.ext rfl ((OpenPartialHomeomorph.univBall (0 : ℝ) a).left_inv (by simp))
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    apply (OpenPartialHomeomorph.univBall (0 : ℝ) a).right_inv
    rw [OpenPartialHomeomorph.univBall_target _ ha, Real.ball_eq_Ioo]
    simpa using p.property
  continuous_toFun := (continuous_fst.prodMk
    ((OpenPartialHomeomorph.continuous_univBall (0 : ℝ) a).comp continuous_snd)).subtype_mk _
  continuous_invFun := (continuous_fst.comp continuous_subtype_val).prodMk
    ((OpenPartialHomeomorph.continuousOn_univBall_symm (0 : ℝ) a).comp_continuous
      (continuous_snd.comp continuous_subtype_val) (by
        intro p
        simpa [Real.ball_eq_Ioo] using p.property))


theorem bicollarLineHomeomorph_center {A : Type*} [TopologicalSpace A]
    (a : ℝ) (ha : 0 < a) (y : A) :
    (bicollarLineHomeomorph a ha (y, 0)).val = (y, 0) := by
  change (y, OpenPartialHomeomorph.univBall (0 : ℝ) a 0) = (y, 0)
  rw [OpenPartialHomeomorph.univBall_apply_zero]

private theorem bicollar_line_formula (a : ℝ) (ha : 0 < a) (z : ℝ) :
    OpenPartialHomeomorph.univBall (0 : ℝ) a z =
      (a * (Real.sqrt (1 + ‖z‖ ^ 2))⁻¹) * z := by
  rw [OpenPartialHomeomorph.univBall, dif_pos ha]
  change a * ((Real.sqrt (1 + ‖z‖ ^ 2))⁻¹ * z) + 0 = _
  simp only [add_zero, mul_assoc]


theorem bicollarLineHomeomorph_negative_iff {A : Type*} [TopologicalSpace A]
    (a : ℝ) (ha : 0 < a) (y : A) (z : ℝ) :
    (bicollarLineHomeomorph a ha (y, z)).val.2 < 0 ↔ z < 0 := by
  change OpenPartialHomeomorph.univBall (0 : ℝ) a z < 0 ↔ z < 0
  rw [bicollar_line_formula a ha z]
  have hpos : 0 < a * (Real.sqrt (1 + ‖z‖ ^ 2))⁻¹ :=
    mul_pos ha (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity)))
  rw [mul_neg_iff]
  simp only [hpos, hpos.not_gt, true_and, false_and, or_false]


theorem bicollarLineHomeomorph_positive_iff {A : Type*} [TopologicalSpace A]
    (a : ℝ) (ha : 0 < a) (y : A) (z : ℝ) :
    0 < (bicollarLineHomeomorph a ha (y, z)).val.2 ↔ 0 < z := by
  change 0 < OpenPartialHomeomorph.univBall (0 : ℝ) a z ↔ 0 < z
  rw [bicollar_line_formula a ha z]
  exact mul_pos_iff_of_pos_left (mul_pos ha (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))))

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
