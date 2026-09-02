import DifferentialGeometry.Bundle.SmoothSubbundle.KernelMotion
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureReactionAlgebra
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorKernel
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Endomorphism
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open scoped BigOperators
open scoped Manifold ContDiff

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

private theorem diagonal_mulVec_apply {q : Fin 3 → Real} {w : Fin 3 → Real} (i : Fin 3) :
    Matrix.mulVec (Matrix.diagonal q) w i = q i * w i := by
  unfold Matrix.mulVec dotProduct Matrix.diagonal
  simp only [Matrix.of_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte]

theorem curvatureOperator_rank_two_reaction_annihilation_impossible
    {A : Matrix (Fin 3) (Fin 3) Real}
    (hA : A.PosSemidef) (hrank : A.rank = 2)
    (hnull : ∀ v : Fin 3 → Real,
      Matrix.mulVec A v = 0 →
        Matrix.mulVec (curvatureOperatorReaction3 A) v = 0) :
    False := by
  have hdim : A.rank +
      Module.finrank Real (Matrix.mulVecLin A).ker = 3 := by
    simpa [Matrix.rank] using (Matrix.mulVecLin A).finrank_range_add_finrank_ker
  have hkerpos : 0 < Module.finrank Real (Matrix.mulVecLin A).ker := by
    omega
  obtain ⟨v, hvne⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hkerpos
  have hvker : Matrix.mulVec A v = 0 := by
    exact LinearMap.mem_ker.mp v.2
  have hvreaction : Matrix.mulVec (curvatureOperatorReaction3 A) v = 0 :=
    hnull v hvker
  have hR : (curvatureOperatorReaction3 A).PosDef :=
    curvatureOperatorReaction3_posDef_of_rank_two hA hrank
  have hvne' : (v : Fin 3 → Real) ≠ 0 := by
    intro h
    apply hvne
    exact Subtype.ext h
  have hpositive : 0 < dotProduct v
      (Matrix.mulVec (curvatureOperatorReaction3 A) v) := by
    simpa [show star (v : Fin 3 → Real) = v from rfl] using
      hR.dotProduct_mulVec_pos hvne'
  rw [hvreaction] at hpositive
  simp at hpositive

theorem curvatureOperator_rank_trichotomy_of_reaction_annihilation
    {A : Matrix (Fin 3) (Fin 3) Real} (hA : A.PosSemidef)
    (hnull : ∀ v : Fin 3 → Real,
      Matrix.mulVec A v = 0 →
        Matrix.mulVec (curvatureOperatorReaction3 A) v = 0) :
    A.rank = 0 ∨ A.rank = 1 ∨ A.rank = 3 := by
  have hle : A.rank ≤ 3 := Matrix.rank_le_height A
  have htwo : A.rank ≠ 2 := by
    intro htwo
    exact curvatureOperator_rank_two_reaction_annihilation_impossible hA htwo hnull
  omega

theorem curvatureOperatorReaction3_preserves_kernel
    {A : Matrix (Fin 3) (Fin 3) Real} {v : Fin 3 → Real}
    (hv : Matrix.mulVec A v = 0) :
    Matrix.mulVec A (Matrix.mulVec (curvatureOperatorReaction3 A) v) = 0 := by
  have hcomm := curvatureOperatorReaction3_commute A
  have hvec := congrArg (fun B : Matrix (Fin 3) (Fin 3) Real => Matrix.mulVec B v) hcomm.eq
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero] at hvec
  exact hvec

theorem curvatureOperatorReaction3_mulVec_eq_zero_of_rank_le_one
    {A : Matrix (Fin 3) (Fin 3) Real} (hA : A.PosSemidef) (hrank : A.rank ≤ 1)
    {v : Fin 3 → Real} (hv : Matrix.mulVec A v = 0) :
    Matrix.mulVec (curvatureOperatorReaction3 A) v = 0 := by
  let hH : A.IsHermitian := hA.isHermitian
  let d : Fin 3 → Real := hH.eigenvalues
  have hcard : Fintype.card {i // d i ≠ 0} ≤ 1 := by
    rw [← hH.rank_eq_card_non_zero_eigs]
    exact hrank
  have hpair {i j : Fin 3} (hij : i ≠ j) : d i * d j = 0 := by
    by_cases hi : d i = 0
    · simp [hi]
    by_cases hj : d j = 0
    · simp [hj]
    have heq : i = j := by
      exact Subtype.ext_iff.mp (Fintype.card_le_one_iff.mp hcard ⟨i, hi⟩ ⟨j, hj⟩)
    exact (hij heq).elim
  let U : Matrix.unitaryGroup (Fin 3) Real := hH.eigenvectorUnitary
  have hU : (U : Matrix (Fin 3) (Fin 3) Real) *
      (U : Matrix (Fin 3) (Fin 3) Real).transpose = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp U.prop)
  have hUinv : (U : Matrix (Fin 3) (Fin 3) Real).transpose *
      (U : Matrix (Fin 3) (Fin 3) Real) = 1 :=
    DifferentialGeometry.Analysis.InnerProductSpace.matrixTransposeMul_orthogonal
      (U : Matrix (Fin 3) (Fin 3) Real) hU
  let D : Matrix (Fin 3) (Fin 3) Real := Matrix.diagonal d
  have hrepr : A = (U : Matrix (Fin 3) (Fin 3) Real) * D *
      (U : Matrix (Fin 3) (Fin 3) Real).transpose := by
    have hs := hH.spectral_theorem
    simpa [U, D, Matrix.star_eq_conjTranspose] using hs
  have hleft : (U : Matrix (Fin 3) (Fin 3) Real).transpose * A =
      D * (U : Matrix (Fin 3) (Fin 3) Real).transpose := by
    rw [hrepr]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc, hUinv]
    simp
  let w : Fin 3 → Real := Matrix.mulVec
    (U : Matrix (Fin 3) (Fin 3) Real).transpose v
  have hvD : Matrix.mulVec D w = 0 := by
    change Matrix.mulVec D
      ((U : Matrix (Fin 3) (Fin 3) Real).transpose.mulVec v) = 0
    rw [Matrix.mulVec_mulVec]
    rw [← hleft]
    rw [← Matrix.mulVec_mulVec, hv]
    simp
  have hDcoord (i : Fin 3) : d i * w i = 0 := by
    have hi := congr_fun hvD i
    rw [diagonal_mulVec_apply] at hi
    simpa [D] using hi
  have hdvec : d = ![d 0, d 1, d 2] := by
    funext i
    fin_cases i <;> rfl
  have hQDx : Matrix.mulVec (curvatureOperatorReaction3 D) w = 0 := by
    rw [show D = Matrix.diagonal ![d 0, d 1, d 2] by
      rw [← congrArg Matrix.diagonal hdvec]]
    rw [curvatureOperatorReaction3_diagonal]
    ext i
    rw [diagonal_mulVec_apply]
    fin_cases i
    · change (d 0 ^ 2 + d 1 * d 2) * w 0 = 0
      by_cases h0 : d 0 = 0
      · rw [h0, hpair (by decide : (1 : Fin 3) ≠ 2)]
        simp
      · rw [hpair (by decide : (1 : Fin 3) ≠ 2), add_zero]
        calc
          d 0 ^ 2 * w 0 = d 0 * (d 0 * w 0) := by ring
          _ = 0 := by rw [hDcoord 0, mul_zero]
    · change (d 1 ^ 2 + d 0 * d 2) * w 1 = 0
      by_cases h1 : d 1 = 0
      · rw [h1, hpair (by decide : (0 : Fin 3) ≠ 2)]
        simp
      · rw [hpair (by decide : (0 : Fin 3) ≠ 2), add_zero]
        calc
          d 1 ^ 2 * w 1 = d 1 * (d 1 * w 1) := by ring
          _ = 0 := by rw [hDcoord 1, mul_zero]
    · change (d 2 ^ 2 + d 0 * d 1) * w 2 = 0
      by_cases h2 : d 2 = 0
      · rw [h2, hpair (by decide : (0 : Fin 3) ≠ 1)]
        simp
      · rw [hpair (by decide : (0 : Fin 3) ≠ 1), add_zero]
        calc
          d 2 ^ 2 * w 2 = d 2 * (d 2 * w 2) := by ring
          _ = 0 := by rw [hDcoord 2, mul_zero]
  have hQrepr : curvatureOperatorReaction3 A =
      (U : Matrix (Fin 3) (Fin 3) Real) * curvatureOperatorReaction3 D *
        (U : Matrix (Fin 3) (Fin 3) Real).transpose := by
    rw [hrepr]
    exact curvatureOperatorReaction3_orthogonal_conj _ _ hU
  rw [hQrepr]
  rw [show (U : Matrix (Fin 3) (Fin 3) Real) * curvatureOperatorReaction3 D *
      (U : Matrix (Fin 3) (Fin 3) Real).transpose =
      (U : Matrix (Fin 3) (Fin 3) Real) *
        (curvatureOperatorReaction3 D *
          (U : Matrix (Fin 3) (Fin 3) Real).transpose) by
    simp only [Matrix.mul_assoc]]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simpa [w] using congrArg (Matrix.mulVec (U : Matrix (Fin 3) (Fin 3) Real)) hQDx

theorem curvatureOperator_rank_zero_iff
    {A : Matrix (Fin 3) (Fin 3) Real} :
    A.rank = 0 ↔ A = 0 := by
  constructor
  · intro h
    have hspan : Submodule.span Real (Set.range A.col) = ⊥ := by
      rw [← Matrix.range_mulVecLin]
      exact Submodule.finrank_eq_zero.mp h
    apply Matrix.ext
    intro i j
    have hc : A.col j ∈ Submodule.span Real (Set.range A.col) :=
      Submodule.subset_span (Set.mem_range_self j)
    have hc0 : A.col j = 0 := by
      have hc' : A.col j ∈ (⊥ : Submodule Real (Fin 3 → Real)) := by
        rw [← hspan]
        exact hc
      simpa using hc'
    have hi := congr_fun hc0 i
    simpa [Matrix.col] using hi
  · intro h
    subst A
    simp [Matrix.rank]

theorem curvatureOperator_rank_three_iff_injective
    {A : Matrix (Fin 3) (Fin 3) Real} :
    A.rank = 3 ↔ Function.Injective (Matrix.mulVecLin A) := by
  constructor
  · intro h
    apply LinearMap.ker_eq_bot.mp
    have hdim : A.rank +
        Module.finrank Real (Matrix.mulVecLin A).ker = 3 := by
      simpa [Matrix.rank] using (Matrix.mulVecLin A).finrank_range_add_finrank_ker
    have hker : Module.finrank Real (Matrix.mulVecLin A).ker = 0 := by omega
    exact Submodule.finrank_eq_zero.mp hker
  · intro h
    have hker : Module.finrank Real (Matrix.mulVecLin A).ker = 0 := by
      rw [Submodule.finrank_eq_zero]
      exact LinearMap.ker_eq_bot.mpr h
    have hdim : A.rank +
        Module.finrank Real (Matrix.mulVecLin A).ker = 3 := by
      simpa [Matrix.rank] using (Matrix.mulVecLin A).finrank_range_add_finrank_ker
    omega

theorem curvatureOperatorReaction3_mulVec_eq_zero_of_rank_ne_two
    {A : Matrix (Fin 3) (Fin 3) Real} (hA : A.PosSemidef) (hrank : A.rank ≠ 2)
    {v : Fin 3 → Real} (hv : Matrix.mulVec A v = 0) :
    Matrix.mulVec (curvatureOperatorReaction3 A) v = 0 := by
  have hle : A.rank ≤ 3 := Matrix.rank_le_height A
  have hcases : A.rank = 0 ∨ A.rank = 1 ∨ A.rank = 3 := by
    omega
  rcases hcases with hzero | hone | hthree
  · have hAzero : A = 0 := curvatureOperator_rank_zero_iff.mp hzero
    rw [hAzero]
    simp [curvatureOperatorReaction3]
  · exact curvatureOperatorReaction3_mulVec_eq_zero_of_rank_le_one hA hone.le hv
  · have hinj : Function.Injective (Matrix.mulVecLin A) :=
      curvatureOperator_rank_three_iff_injective.mp hthree
    have hvzero : v = 0 := by
      apply hinj
      change Matrix.mulVec A v = Matrix.mulVec A 0
      simpa using hv
    rw [hvzero]
    simp

theorem curvatureOperatorReaction3_kernel_annihilation_iff_rank_ne_two
    {A : Matrix (Fin 3) (Fin 3) Real} (hA : A.PosSemidef) :
    (∀ v : Fin 3 → Real,
      Matrix.mulVec A v = 0 →
        Matrix.mulVec (curvatureOperatorReaction3 A) v = 0) ↔
      A.rank ≠ 2 := by
  constructor
  · intro hnull htwo
    exact curvatureOperator_rank_two_reaction_annihilation_impossible hA htwo hnull
  · intro hrank v hv
    exact curvatureOperatorReaction3_mulVec_eq_zero_of_rank_ne_two hA hrank hv

theorem curvatureOperatorReaction3_kernel_annihilation_at_right_endpoint
    {A : Real → Matrix (Fin 3) (Fin 3) Real}
    {K : Submodule Real (Fin 3 → Real)} {a b : Real} (hab : a < b)
    (hA : ContinuousAt A b)
    (hK : ∀ t ∈ Set.Ioo a b, (Matrix.mulVecLin (A t)).ker = K)
    (hfin : Module.finrank Real K =
      Module.finrank Real (Matrix.mulVecLin (A b)).ker)
    (hzero : ∀ t ∈ Set.Ioo a b, ∀ v,
      Matrix.mulVec (A t) v = 0 →
        Matrix.mulVec (curvatureOperatorReaction3 (A t)) v = 0) :
    ∀ v, Matrix.mulVec (A b) v = 0 →
      Matrix.mulVec (curvatureOperatorReaction3 (A b)) v = 0 := by
  let toCLM : Matrix (Fin 3) (Fin 3) Real →L[Real]
      ((Fin 3 → Real) →L[Real] (Fin 3 → Real)) :=
    (((Matrix.toLin' : Matrix (Fin 3) (Fin 3) Real ≃ₗ[Real]
      ((Fin 3 → Real) →ₗ[Real] (Fin 3 → Real))).trans
        LinearMap.toContinuousLinearMap).toLinearMap.toContinuousLinearMap)
  let Aop : Real → (Fin 3 → Real) →L[Real] (Fin 3 → Real) :=
    fun t => toCLM (A t)
  let Bop : Real → (Fin 3 → Real) →L[Real] (Fin 3 → Real) :=
    fun t => toCLM (curvatureOperatorReaction3 (A t))
  have hAop : ContinuousAt Aop b := toCLM.continuous.continuousAt.comp hA
  have hreaction : ContinuousAt (fun t => curvatureOperatorReaction3 (A t)) b := by
    exact (hA.mul hA).add (continuous_id.matrix_adjugate.continuousAt.comp hA)
  have hBop : ContinuousAt Bop b := toCLM.continuous.continuousAt.comp hreaction
  have hKop : ∀ t ∈ Set.Ioo a b, (Aop t).ker = K := by
    intro t ht
    change (Matrix.toLin' (A t)).ker = K
    rw [Matrix.toLin'_apply']
    exact hK t ht
  have hfinop : Module.finrank Real K = Module.finrank Real (Aop b).ker := by
    change Module.finrank Real K = Module.finrank Real (Matrix.toLin' (A b)).ker
    rw [Matrix.toLin'_apply']
    exact hfin
  have hzeroop : ∀ t ∈ Set.Ioo a b, ∀ v, v ∈ (Aop t).ker → Bop t v = 0 := by
    intro t ht v hv
    apply hzero t ht v
    simpa [Aop, toCLM] using LinearMap.mem_ker.mp hv
  intro v hv
  have hvop : v ∈ (Aop b).ker := by
    apply LinearMap.mem_ker.mpr
    simpa [Aop, toCLM] using hv
  have hout := continuousLinearMap_kernel_annihilation_of_constant_on_left
    hab hAop hBop hKop hfinop hzeroop v hvop
  simpa [Bop, toCLM] using hout

theorem curvatureOperator_rank_trichotomy_at_right_endpoint
    {A : Real → Matrix (Fin 3) (Fin 3) Real}
    {K : Submodule Real (Fin 3 → Real)} {a b : Real} (hab : a < b)
    (hA : ContinuousAt A b) (hAb : (A b).PosSemidef)
    (hK : ∀ t ∈ Set.Ioo a b, (Matrix.mulVecLin (A t)).ker = K)
    (hfin : Module.finrank Real K =
      Module.finrank Real (Matrix.mulVecLin (A b)).ker)
    (hzero : ∀ t ∈ Set.Ioo a b, ∀ v,
      Matrix.mulVec (A t) v = 0 →
        Matrix.mulVec (curvatureOperatorReaction3 (A t)) v = 0) :
    (A b).rank = 0 ∨ (A b).rank = 1 ∨ (A b).rank = 3 := by
  apply curvatureOperator_rank_trichotomy_of_reaction_annihilation hAb
  exact curvatureOperatorReaction3_kernel_annihilation_at_right_endpoint
    hab hA hK hfin hzero

private theorem finrank_range_eq_matrix_rank_of_basis
    {V : Type*} [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    (basis : Module.Basis (Fin 3) Real V) (L : V →ₗ[Real] V) :
    Module.finrank Real L.range = Matrix.rank ((LinearMap.toMatrix basis basis) L) := by
  rw [Matrix.rank_eq_finrank_range_toLin ((LinearMap.toMatrix basis basis) L) basis basis]
  rw [Matrix.toLin_toMatrix]

theorem curvatureOperator_finrank_range_trichotomy_of_matrix_representation
    [FiniteDimensional Real E]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (A : DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorSubmodule
      (I := I) (M := M) x)
    (hmatrix : LinearMap.toMatrix
      (curvatureTwoFormBasisAt (I := I) basis)
      (curvatureTwoFormBasisAt (I := I) basis)
      (DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt
        (I := I) g x A).toLinearMap =
        traceNormalizedCurvatureOperatorMatrixAt (I := I) x basis A)
    (hpositive : (traceNormalizedCurvatureOperatorMatrixAt (I := I) x basis A).PosSemidef)
    (hnull : ∀ v : Fin 3 → Real,
      Matrix.mulVec (traceNormalizedCurvatureOperatorMatrixAt (I := I) x basis A) v = 0 →
        Matrix.mulVec
          (curvatureOperatorReaction3
            (traceNormalizedCurvatureOperatorMatrixAt (I := I) x basis A)) v = 0) :
    Module.finrank Real
        (DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt
          (I := I) g x A).range = 0 ∨
      Module.finrank Real
          (DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt
            (I := I) g x A).range = 1 ∨
        Module.finrank Real
            (DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt
              (I := I) g x A).range = 3 := by
  let b := curvatureTwoFormBasisAt (I := I) basis
  let _ : FiniteDimensional Real
      (TangentSpace I x [⋀^Fin 2]→L[Real] Real) :=
    (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2)
      (Module.finBasis Real (TangentSpace I x))).finiteDimensional_of_finite
  let L := (DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt
    (I := I) g x A).toLinearMap
  let R := traceNormalizedCurvatureOperatorMatrixAt (I := I) x basis A
  have htri := curvatureOperator_rank_trichotomy_of_reaction_annihilation
    (A := R) hpositive hnull
  have hL : LinearMap.toMatrix b b L = R := by
    simpa [b, L, R] using hmatrix
  have hrank : Module.finrank Real L.range = R.rank := by
    calc
      Module.finrank Real L.range = Matrix.rank (LinearMap.toMatrix b b L) :=
        finrank_range_eq_matrix_rank_of_basis b L
      _ = R.rank := by rw [hL]
  rcases htri with h0 | h1 | h3
  · exact Or.inl (hrank.trans h0)
  · exact Or.inr (Or.inl (hrank.trans h1))
  · exact Or.inr (Or.inr (hrank.trans h3))

theorem curvatureOperatorImageAt_finrank_trichotomy_of_matrix_representation
    [FiniteDimensional Real E]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (A : DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorSubmodule
      (I := I) (M := M) x)
    (hmatrix : LinearMap.toMatrix
      (curvatureTwoFormBasisAt (I := I) basis)
      (curvatureTwoFormBasisAt (I := I) basis)
      (DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt
        (I := I) g x A).toLinearMap =
        traceNormalizedCurvatureOperatorMatrixAt (I := I) x basis A)
    (hpositive : (traceNormalizedCurvatureOperatorMatrixAt (I := I) x basis A).PosSemidef)
    (hnull : ∀ v : Fin 3 → Real,
      Matrix.mulVec (traceNormalizedCurvatureOperatorMatrixAt (I := I) x basis A) v = 0 →
        Matrix.mulVec
          (curvatureOperatorReaction3
            (traceNormalizedCurvatureOperatorMatrixAt (I := I) x basis A)) v = 0) :
    Module.finrank Real
        (DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt
          (I := I) g x A) = 0 ∨
      Module.finrank Real
          (DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt
            (I := I) g x A) = 1 ∨
        Module.finrank Real
            (DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt
              (I := I) g x A) = 3 := by
  change Module.finrank Real
      (DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt
        (I := I) g x A).range = 0 ∨
    Module.finrank Real
        (DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt
          (I := I) g x A).range = 1 ∨
      Module.finrank Real
          (DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt
            (I := I) g x A).range = 3
  exact curvatureOperator_finrank_range_trichotomy_of_matrix_representation
    (I := I) g x basis A hmatrix hpositive hnull

end DifferentialGeometry.Geometry.Curvature.DimensionThree
