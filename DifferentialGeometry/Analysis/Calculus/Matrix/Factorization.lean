import DifferentialGeometry.Analysis.Calculus.ContDiff.OrthonormalBasis
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section

open scoped ContDiff Matrix Matrix.Norms.Elementwise

namespace ContDiffOn

theorem exists_mul_transpose
    {P ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [Fintype ι] [DecidableEq ι]
    {n : ℕ∞ω} {s : Set P} {A : P → Matrix ι ι ℝ}
    (hA : ContDiffOn ℝ n A s) (hpos : ∀ x ∈ s, (A x).PosDef) :
    ∃ S : P → Matrix ι ι ℝ, ContDiffOn ℝ n S s ∧
      ∀ x ∈ s, IsUnit (S x) ∧ S x * (S x)ᵀ = A x := by
  classical
  let e := Pi.basisFun ℝ ι
  let B (x : P) : (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ :=
    ∑ i, ∑ j, A x i j • (ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj j)
  have hB : ContDiffOn ℝ n B s := by
    apply ContDiffOn.sum
    intro i _
    apply ContDiffOn.sum
    intro j _
    exact (contDiffOn_pi.mp (contDiffOn_pi.mp hA i) j).smul contDiffOn_const
  have hBapply (x : P) (v w : ι → ℝ) : B x v w = v ⬝ᵥ (A x *ᵥ w) := by
    simp only [B, sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hsym (x : P) (hx : x ∈ s) (v w : ι → ℝ) : B x v w = B x w v := by
    rw [hBapply, hBapply]
    have hT : (A x)ᵀ = A x := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (hpos x hx).isHermitian.eq
    simpa only [hT] using Matrix.dotProduct_transpose_mulVec (A x) v w
  have hBpos (x : P) (hx : x ∈ s) (v : ι → ℝ) (hv : v ≠ 0) : 0 < B x v v := by
    rw [hBapply]
    simpa only [star_trivial] using (hpos x hx).dotProduct_mulVec_pos hv
  obtain ⟨b, hb, horth⟩ := hB.exists_orthonormal_basis e hsym hBpos
  let S (x : P) : Matrix ι ι ℝ := fun i j => B x (b x j) (e i)
  have horth' (x : P) (hx : x ∈ s) (i j : ι) :
      B x (b x i) (b x j) = if i = j then 1 else 0 := by
    split_ifs with hij
    · subst j
      exact (horth x hx).1 i
    · exact (horth x hx).2 i j hij
  have hrepr (x : P) (hx : x ∈ s) (i j : ι) : S x i j = (b x).repr (e i) j := by
    change B x (b x j) (e i) = _
    conv_lhs => rw [← (b x).sum_repr (e i)]
    simp only [map_sum, map_smul, smul_eq_mul, horth' x hx, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hBbasis (x : P) (i j : ι) : B x (e i) (e j) = A x i j := by
    rw [hBapply]
    simp only [e, Pi.basisFun_apply, Matrix.mulVec_single_one, single_one_dotProduct, Matrix.col_apply]
  refine ⟨S, ?_, ?_⟩
  · apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    exact (hB.clm_apply (hb j)).clm_apply contDiffOn_const
  · intro x hx
    have hS : S x = ((b x).toMatrix e)ᵀ := by
      ext i j
      exact hrepr x hx i j
    have hI : LinearMap.toMatrix₂ (b x) (b x) (B x).toBilinForm = (1 : Matrix ι ι ℝ) := by
      ext i j
      simpa only [LinearMap.toMatrix₂_apply, ContinuousLinearMap.toBilinForm_apply, Matrix.one_apply]
        using horth' x hx i j
    have hM : LinearMap.toMatrix₂ e e (B x).toBilinForm = A x := by
      ext i j
      simpa only [LinearMap.toMatrix₂_apply, ContinuousLinearMap.toBilinForm_apply] using hBbasis x i j
    constructor
    · rw [hS, Matrix.isUnit_transpose]
      let := Module.Basis.invertibleToMatrix (b x) e
      exact isUnit_of_invertible _
    · rw [hS, Matrix.transpose_transpose]
      have h := LinearMap.toMatrix₂_mul_basis_toMatrix (b x) (b x) e e (B x).toBilinForm
      simpa only [hI, hM, Matrix.mul_one] using h

end ContDiffOn
