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

noncomputable local instance twoFormFiniteDimensional (x : M)
    [FiniteDimensional Real E] :
    FiniteDimensional Real (TangentSpace I x [⋀^Fin 2]→L[Real] Real) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2)
    (Module.finBasis Real (TangentSpace I x))).finiteDimensional_of_finite

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

private theorem adjugate_eq_zero_of_rank_lt
    {R : Type*} [Field R] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (hrank : A.rank < n) :
    A.adjugate = 0 := by
  ext i j
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  have hminor : (A.submatrix j.succAbove i.succAbove).det = 0 := by
    by_contra hdet
    have heq := Matrix.rank_of_det_ne_zero hdet
    have hle := Matrix.rank_submatrix_le A j.succAbove i.succAbove
    rw [heq, Fintype.card_fin] at hle
    omega
  rw [hminor, mul_zero]
  rfl

theorem curvatureOperatorReaction3_mulVec_eq_zero_of_rank_ne_two
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hrank : A.rank ≠ 2)
    {v : Fin 3 → ℝ} (hv : A.mulVec v = 0) :
    (curvatureOperatorReaction3 A).mulVec v = 0 := by
  have hle : A.rank ≤ 3 := Matrix.rank_le_height A
  by_cases hthree : A.rank = 3
  · have hinj := curvatureOperator_rank_three_iff_injective.mp hthree
    have hvzero : v = 0 := by
      apply hinj
      change A.mulVec v = A.mulVec 0
      simpa using hv
    rw [hvzero, Matrix.mulVec_zero]
  · have hlow : A.rank < 2 := by omega
    have hadj := adjugate_eq_zero_of_rank_lt A hlow
    rw [curvatureOperatorReaction3, hadj, add_zero, ← Matrix.mulVec_mulVec, hv,
      Matrix.mulVec_zero]

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
    exact curvatureOperatorReaction3_mulVec_eq_zero_of_rank_ne_two hrank hv

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

theorem curvatureOperatorEndomorphism_finrank_range_trichotomy
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    [FiniteDimensional Real V]
    (hDim : Module.finrank Real V = 3) (A : V →ₗ[Real] V)
    (hA : A.IsPositive)
    (hnull : ∀ v : V, A v = 0 → curvatureOperatorReactionEndomorphism3 A v = 0) :
    Module.finrank Real A.range = 0 ∨
      Module.finrank Real A.range = 1 ∨
        Module.finrank Real A.range = 3 := by
  let basis : OrthonormalBasis (Fin 3) Real V :=
    hA.isSymmetric.eigenvectorBasis hDim
  let matrix : Matrix (Fin 3) (Fin 3) Real :=
    LinearMap.toMatrix basis.toBasis basis.toBasis A
  have hmatrix_positive : matrix.PosSemidef :=
    (LinearMap.posSemidef_toMatrix_iff basis).mpr hA
  have hmatrix_null : ∀ v : Fin 3 → Real,
      Matrix.mulVec matrix v = 0 →
        Matrix.mulVec (curvatureOperatorReaction3 matrix) v = 0 := by
    intro v hv
    let w : V := basis.repr.symm (WithLp.toLp 2 v)
    have hwrepr : (basis.toBasis.repr w : Fin 3 → Real) = v := by
      ext i
      simp [w]
    have hAwrepr : basis.toBasis.repr (A w) = 0 := by
      have hcoord := LinearMap.toMatrix_mulVec_repr
        basis.toBasis basis.toBasis A w
      rw [hwrepr] at hcoord
      rw [show matrix = LinearMap.toMatrix basis.toBasis basis.toBasis A by rfl] at hv
      simpa using hcoord.symm.trans hv
    have hAw : A w = 0 :=
      basis.toBasis.repr.injective (by simpa using hAwrepr)
    have hreaction := hnull w hAw
    have hcoord := LinearMap.toMatrix_mulVec_repr basis.toBasis basis.toBasis
      (curvatureOperatorReactionEndomorphism3 A) w
    rw [curvatureOperatorReactionEndomorphism3_toMatrix basis.toBasis A, hwrepr] at hcoord
    rw [hreaction] at hcoord
    simpa using hcoord
  have htrichotomy :=
    curvatureOperator_rank_trichotomy_of_reaction_annihilation
      hmatrix_positive hmatrix_null
  have hrank : Module.finrank Real A.range = matrix.rank := by
    calc
      Module.finrank Real A.range = Matrix.rank
          (LinearMap.toMatrix basis.toBasis basis.toBasis A) := by
        rw [Matrix.rank_eq_finrank_range_toLin
          (LinearMap.toMatrix basis.toBasis basis.toBasis A)
          basis.toBasis basis.toBasis]
        rw [Matrix.toLin_toMatrix]
      _ = matrix.rank := by rfl
  rcases htrichotomy with hzero | hone | hthree
  · exact Or.inl (hrank.trans hzero)
  · exact Or.inr (Or.inl (hrank.trans hone))
  · exact Or.inr (Or.inr (hrank.trans hthree))

theorem curvatureOperatorEndomorphism_finrank_range_trichotomy_of_metric
    {V : Type*} [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    (D : DifferentialGeometry.Tensor0SBundle.MetricFiberData V)
    (hDim : Module.finrank Real V = 3) (A : V →ₗ[Real] V)
    (hA_symm : D.IsSymmetric A)
    (hA_nonneg : ∀ v : V, 0 ≤ D.inner (A v) v)
    (hnull : ∀ v : V, A v = 0 → curvatureOperatorReactionEndomorphism3 A v = 0) :
    Module.finrank Real A.range = 0 ∨
      Module.finrank Real A.range = 1 ∨
        Module.finrank Real A.range = 3 := by
  let addV : AddCommGroup V := inferInstance
  let modV : Module Real V := inferInstance
  let : InnerProductSpace.Core Real V := D.toCore
  let : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real V _ addV modV D.toCore
  let : AddCommGroup V := addV
  let : Module Real V := modV
  let : InnerProductSpace Real V :=
    @InnerProductSpace.ofCore Real V _ _ _ D.toCore.toCore
  have hA : A.IsPositive := by
    rw [LinearMap.isPositive_iff]
    constructor
    · intro v w
      rw [DifferentialGeometry.Tensor0SBundle.MetricFiberData.toCore_inner D,
        DifferentialGeometry.Tensor0SBundle.MetricFiberData.toCore_inner D]
      exact hA_symm v w
    · intro v
      rw [DifferentialGeometry.Tensor0SBundle.MetricFiberData.toCore_inner D]
      exact hA_nonneg v
  exact curvatureOperatorEndomorphism_finrank_range_trichotomy hDim A hA hnull

theorem curvatureOperatorEndomorphism_finrank_range_ne_two_of_metric
    {V : Type*} [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    (D : DifferentialGeometry.Tensor0SBundle.MetricFiberData V)
    (hDim : Module.finrank Real V = 3) (A : V →ₗ[Real] V)
    (hA_symm : D.IsSymmetric A)
    (hA_nonneg : ∀ v : V, 0 ≤ D.inner (A v) v)
    (hnull : ∀ v : V, A v = 0 → curvatureOperatorReactionEndomorphism3 A v = 0) :
    Module.finrank Real A.range ≠ 2 := by
  intro htwo
  have htri := curvatureOperatorEndomorphism_finrank_range_trichotomy_of_metric
    D hDim A hA_symm hA_nonneg hnull
  rcases htri with hzero | hone | hthree
  · omega
  · omega
  · omega

theorem curvatureOperatorImageAt_finrank_trichotomy
    [FiniteDimensional Real E]
    (hDim : Module.finrank Real E = 3)
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorSubmodule
      (I := I) (M := M) x)
    (hpositive : ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real,
      0 ≤ (DifferentialGeometry.Geometry.Curvature.twoFormMetricData
        (I := I) g x).inner
          (DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt
            (I := I) g x A a) a)
    (hnull : ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real,
      DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt
          (I := I) g x A a = 0 →
        curvatureOperatorReactionEndomorphism3
            (DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt
              (I := I) g x A).toLinearMap a = 0) :
    Module.finrank Real
        (DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt
          (I := I) g x A) = 0 ∨
      Module.finrank Real
          (DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt
            (I := I) g x A) = 1 ∨
        Module.finrank Real
            (DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt
              (I := I) g x A) = 3 := by
  have hTangentDim : Module.finrank Real (TangentSpace I x) = 3 := by
    exact (show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl).trans hDim
  let tangentBasis : Module.Basis (Fin 3) Real (TangentSpace I x) := by
    have basis := Module.finBasis Real (TangentSpace I x)
    rw [hTangentDim] at basis
    exact basis
  let twoFormBasis := DifferentialGeometry.Geometry.Curvature.curvatureTwoFormBasisAt
    (I := I) tangentBasis
  have hTwoFormDim : Module.finrank Real
      (TangentSpace I x [⋀^Fin 2]→L[Real] Real) = 3 := by
    rw [Module.finrank_eq_card_basis twoFormBasis, Fintype.card_fin]
  change Module.finrank Real
      (DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt
        (I := I) g x A).toLinearMap.range = 0 ∨
    Module.finrank Real
        (DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt
          (I := I) g x A).toLinearMap.range = 1 ∨
      Module.finrank Real
          (DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt
            (I := I) g x A).toLinearMap.range = 3
  exact curvatureOperatorEndomorphism_finrank_range_trichotomy_of_metric
    (DifferentialGeometry.Geometry.Curvature.twoFormMetricData (I := I) g x)
    hTwoFormDim
    (DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt
      (I := I) g x A).toLinearMap
    (DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt_isSymmetric
      (I := I) g x A)
    hpositive hnull

theorem curvatureOperatorImageAt_finrank_ne_two
    [FiniteDimensional Real E]
    (hDim : Module.finrank Real E = 3)
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorSubmodule
      (I := I) (M := M) x)
    (hpositive : ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real,
      0 ≤ (DifferentialGeometry.Geometry.Curvature.twoFormMetricData
        (I := I) g x).inner
          (DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt
            (I := I) g x A a) a)
    (hnull : ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real,
      DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt
          (I := I) g x A a = 0 →
        curvatureOperatorReactionEndomorphism3
            (DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt
              (I := I) g x A).toLinearMap a = 0) :
    Module.finrank Real
        (DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt
          (I := I) g x A) ≠ 2 := by
  intro htwo
  have htri := curvatureOperatorImageAt_finrank_trichotomy
    hDim g x A hpositive hnull
  rcases htri with hzero | hone | hthree
  · omega
  · omega
  · omega

theorem curvatureOperatorImageAt_finrank_trichotomy_of_spatially_constant
    [FiniteDimensional Real E] [Nonempty M]
    (hDim : Module.finrank Real E = 3)
    (g : SmoothRiemannianMetric I M)
    (A : (x : M) ->
      DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorSubmodule
        (I := I) (M := M) x)
    (hpositive : forall x,
      forall a : TangentSpace I x [⋀^Fin 2]→L[Real] Real,
        0 <= (DifferentialGeometry.Geometry.Curvature.twoFormMetricData
          (I := I) g x).inner
            (DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt
              (I := I) g x (A x) a) a)
    (hnull : forall x,
      forall a : TangentSpace I x [⋀^Fin 2]→L[Real] Real,
        DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt
            (I := I) g x (A x) a = 0 ->
          curvatureOperatorReactionEndomorphism3
              (DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt
                (I := I) g x (A x)).toLinearMap a = 0)
    (hrank : forall x y,
      Module.finrank Real
          (DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt
            (I := I) g x (A x)) =
        Module.finrank Real
          (DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt
            (I := I) g y (A y))) :
    (forall x, Module.finrank Real
        (DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt
          (I := I) g x (A x)) = 0) \/
      (forall x, Module.finrank Real
        (DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt
          (I := I) g x (A x)) = 1) \/
      (forall x, Module.finrank Real
        (DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt
          (I := I) g x (A x)) = 3) := by
  let x0 : M := Classical.choice inferInstance
  have htrichotomy := curvatureOperatorImageAt_finrank_trichotomy
    hDim g x0 (A x0) (hpositive x0) (hnull x0)
  rcases htrichotomy with hzero | hone | hthree
  · exact Or.inl (fun x => (hrank x x0).trans hzero)
  · exact Or.inr (Or.inl (fun x => (hrank x x0).trans hone))
  · exact Or.inr (Or.inr (fun x => (hrank x x0).trans hthree))

private theorem finrank_range_eq_matrix_rank_of_basis
    {V : Type*} [AddCommGroup V] [Module Real V]
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

theorem curvatureOperatorReactionEndomorphism3_eq_zero_of_mem_ker_of_finrank_range_ne_two
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (hdim : Module.finrank ℝ V = 3) (A : V →ₗ[ℝ] V)
    (hrank : Module.finrank ℝ A.range ≠ 2) {v : V} (hv : A v = 0) :
    curvatureOperatorReactionEndomorphism3 A v = 0 := by
  let b : Module.Basis (Fin 3) ℝ V := Module.finBasisOfFinrankEq ℝ V hdim
  let B := LinearMap.toMatrix b b A
  have hBrank : B.rank ≠ 2 := by
    rw [Matrix.rank_eq_finrank_range_toLin B b b,
      show Matrix.toLin b b B = A from Matrix.toLin_toMatrix _ _ _]
    exact hrank
  have hBv : B.mulVec (b.repr v) = 0 := by
    rw [LinearMap.toMatrix_mulVec_repr, hv, map_zero, Finsupp.coe_zero]
  have hR := curvatureOperatorReaction3_mulVec_eq_zero_of_rank_ne_two hBrank hBv
  apply b.repr.injective
  have hcoord := LinearMap.toMatrix_mulVec_repr b b
    (curvatureOperatorReactionEndomorphism3 A) v
  rw [curvatureOperatorReactionEndomorphism3_toMatrix] at hcoord
  exact DFunLike.coe_injective (by
    simpa only [map_zero, Finsupp.coe_zero] using hcoord.symm.trans hR)


end DifferentialGeometry.Geometry.Curvature.DimensionThree
