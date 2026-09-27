import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace OrthonormalBasis

variable {E F ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [AddCommMonoid F] [Module ℝ F] [Fintype ι] [Fintype κ]

theorem sum_bilinear_diag_eq (e : OrthonormalBasis ι ℝ E)
    (f : OrthonormalBasis κ ℝ E) (B : E →ₗ[ℝ] E →ₗ[ℝ] F) :
    (∑ i, B (e i) (e i)) = ∑ j, B (f j) (f j) := by
  classical
  have h_expand (v : E) :
      B v v = ∑ j, ∑ l, (⟪f j, v⟫ * ⟪f l, v⟫) • B (f j) (f l) := by
    conv_lhs => rw [← f.sum_repr' v]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have h_coeff (j l : κ) :
      (∑ i, ⟪f j, e i⟫ * ⟪f l, e i⟫) = if j = l then 1 else 0 := by
    calc
      _ = ∑ i, ⟪f j, e i⟫ * ⟪e i, f l⟫ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [real_inner_comm (f l) (e i)]
      _ = ⟪f j, f l⟫ := e.sum_inner_mul_inner _ _
      _ = _ := orthonormal_iff_ite.mp f.orthonormal j l
  conv_lhs => simp only [h_expand]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, h_coeff]
  simp

end OrthonormalBasis
