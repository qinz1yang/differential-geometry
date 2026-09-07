import DifferentialGeometry.Geometry.Curvature.DimensionThree.HamiltonIvey.Reaction
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open DifferentialGeometry.Analysis.InnerProductSpace
open scoped BigOperators RealInnerProductSpace

def curvatureOperatorReaction3
    (A : Matrix (Fin 3) (Fin 3) Real) : Matrix (Fin 3) (Fin 3) Real :=
  A * A + A.adjugate

def curvatureOperatorReactionEndomorphism3
    {V : Type*} [AddCommGroup V] [Module Real V]
    [finite : FiniteDimensional Real V]
    (A : V →ₗ[Real] V) : V →ₗ[Real] V :=
  let _ := finite
  (2 : Real) • (A.comp A) - (LinearMap.trace Real V A) • A +
      (((LinearMap.trace Real V A) ^ 2 - LinearMap.trace Real V (A.comp A)) / (2 : Real)) •
        LinearMap.id

theorem curvatureOperatorReactionEndomorphism3_smul
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (r : ℝ) (A : V →ₗ[ℝ] V) :
    curvatureOperatorReactionEndomorphism3 (r • A) =
      r ^ 2 • curvatureOperatorReactionEndomorphism3 A := by
  have hsq : (r • A).comp (r • A) = r ^ 2 • A.comp A := by
    ext v
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, smul_smul, pow_two]
  unfold curvatureOperatorReactionEndomorphism3
  rw [hsq]
  simp only [map_smul, smul_eq_mul, smul_add, smul_sub, smul_smul]
  module

theorem trace_curvatureOperatorReactionEndomorphism3
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (hdim : Module.finrank ℝ V = 3) (A : V →ₗ[ℝ] V) :
    LinearMap.trace ℝ V (curvatureOperatorReactionEndomorphism3 A) =
      ((LinearMap.trace ℝ V A) ^ 2 + LinearMap.trace ℝ V (A.comp A)) / 2 := by
  unfold curvatureOperatorReactionEndomorphism3
  simp only [map_add, map_sub, map_smul, smul_eq_mul, LinearMap.trace_id, hdim,
    Nat.cast_ofNat]
  ring

theorem curvatureOperatorReactionEndomorphism3_smul_id
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (hdim : Module.finrank ℝ V = 3) (r : ℝ) :
    curvatureOperatorReactionEndomorphism3 (r • (LinearMap.id : V →ₗ[ℝ] V)) =
      (2 * r ^ 2) • LinearMap.id := by
  have hsq : (r • (LinearMap.id : V →ₗ[ℝ] V)).comp (r • LinearMap.id) =
      (r * r) • LinearMap.id := by
    ext v
    simp [smul_smul]
  unfold curvatureOperatorReactionEndomorphism3
  rw [hsq]
  simp only [map_smul, LinearMap.trace_id, hdim, Nat.cast_ofNat]
  rw [smul_smul, smul_smul, ← sub_smul, ← add_smul]
  congr 1
  ring


theorem curvatureOperatorReactionEndomorphism3_conj
    {W W' : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    [AddCommGroup W'] [Module ℝ W'] [FiniteDimensional ℝ W']
    (e : W ≃ₗ[ℝ] W') (A : W →ₗ[ℝ] W) :
    curvatureOperatorReactionEndomorphism3 (e.conj A) =
      e.conj (curvatureOperatorReactionEndomorphism3 A) := by
  unfold curvatureOperatorReactionEndomorphism3
  rw [← e.conj_comp, LinearMap.trace_conj', LinearMap.trace_conj']
  simp only [map_add, map_sub, map_smul, e.conj_comp, e.conj_id]


section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem curvatureOperatorReactionEndomorphism3_isSymmetric
    (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric) :
    (curvatureOperatorReactionEndomorphism3 A).IsSymmetric := by
  have hsq : (A.comp A).IsSymmetric := by
    intro x y
    change ⟪A (A x), y⟫ = ⟪x, A (A y)⟫
    rw [hA, hA]
  exact ((hsq.smul (by simp)).sub (hA.smul (by simp))).add
    (LinearMap.IsSymmetric.id.smul (by simp))

def curvatureOperatorReactionSelfAdjoint3 (A : selfAdjoint (E →L[ℝ] E)) :
    selfAdjoint (E →L[ℝ] E) :=
  ⟨(curvatureOperatorReactionEndomorphism3 (A : E →L[ℝ] E).toLinearMap).toContinuousLinearMap,
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (curvatureOperatorReactionEndomorphism3_isSymmetric _
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp A.property))⟩

theorem curvatureOperatorReactionSelfAdjoint3_coe (A : selfAdjoint (E →L[ℝ] E)) :
    (curvatureOperatorReactionSelfAdjoint3 A : E →L[ℝ] E) =
      (curvatureOperatorReactionEndomorphism3 (A : E →L[ℝ] E).toLinearMap).toContinuousLinearMap := rfl

theorem curvatureOperatorReactionSelfAdjoint3_smul
    (r : ℝ) (A : selfAdjoint (E →L[ℝ] E)) :
    curvatureOperatorReactionSelfAdjoint3 (r • A) =
      r ^ 2 • curvatureOperatorReactionSelfAdjoint3 A := by
  apply Subtype.ext
  change (curvatureOperatorReactionEndomorphism3
    (r • (A : E →L[ℝ] E).toLinearMap)).toContinuousLinearMap =
    r ^ 2 • (curvatureOperatorReactionEndomorphism3
      (A : E →L[ℝ] E).toLinearMap).toContinuousLinearMap
  rw [curvatureOperatorReactionEndomorphism3_smul]
  rfl

end

private theorem curvatureOperatorReaction3_eq_trace_polynomial
    (A : Matrix (Fin 3) (Fin 3) Real) :
    curvatureOperatorReaction3 A =
      (2 : Real) • (A * A) - A.trace • A +
        ((A.trace ^ 2 - (A * A).trace) / (2 : Real)) •
          (1 : Matrix (Fin 3) (Fin 3) Real) := by
  unfold curvatureOperatorReaction3
  rw [Matrix.adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem curvatureOperatorReactionEndomorphism3_toMatrix
    {V : Type*} [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    (basis : Module.Basis (Fin 3) Real V) (A : V →ₗ[Real] V) :
    LinearMap.toMatrix basis basis (curvatureOperatorReactionEndomorphism3 A) =
      curvatureOperatorReaction3 (LinearMap.toMatrix basis basis A) := by
  classical
  let B := LinearMap.toMatrix basis basis A
  have htrace : LinearMap.trace Real V A = B.trace :=
    LinearMap.trace_eq_matrix_trace Real basis A
  have htraceSq : LinearMap.trace Real V (A.comp A) = (B * B).trace := by
    rw [LinearMap.trace_eq_matrix_trace Real basis, LinearMap.toMatrix_comp basis basis basis]
  unfold curvatureOperatorReactionEndomorphism3
  simp only [map_add, map_sub, map_smul, LinearMap.toMatrix_id]
  rw [LinearMap.toMatrix_comp basis basis basis, htrace, htraceSq]
  exact (curvatureOperatorReaction3_eq_trace_polynomial B).symm

private lemma diagProduct_erase_curvatureReaction3
    (l1 l2 l3 : Real) (i : Fin 3) :
    (∏ j ∈ (Finset.univ : Finset (Fin 3)).erase i, ![l1, l2, l3] j) =
      (if i = 0 then l2 * l3 else if i = 1 then l1 * l3 else l1 * l2) := by
  fin_cases i
  · change (∏ j ∈ (Finset.univ : Finset (Fin 3)).erase (0 : Fin 3),
      ![l1, l2, l3] j) = l2 * l3
    have hset : (Finset.univ : Finset (Fin 3)).erase (0 : Fin 3) =
        ({1, 2} : Finset (Fin 3)) := by
      ext j
      fin_cases j <;> simp
    rw [hset]
    simp
  · change (∏ j ∈ (Finset.univ : Finset (Fin 3)).erase (1 : Fin 3),
      ![l1, l2, l3] j) = l1 * l3
    have hset : (Finset.univ : Finset (Fin 3)).erase (1 : Fin 3) =
        ({0, 2} : Finset (Fin 3)) := by
      ext j
      fin_cases j <;> simp
    rw [hset]
    simp
  · change (∏ j ∈ (Finset.univ : Finset (Fin 3)).erase (2 : Fin 3),
      ![l1, l2, l3] j) = l1 * l2
    have hset : (Finset.univ : Finset (Fin 3)).erase (2 : Fin 3) =
        ({0, 1} : Finset (Fin 3)) := by
      ext j
      fin_cases j <;> simp
    rw [hset]
    simp

theorem curvatureOperatorReaction3_diagonal (l1 l2 l3 : Real) :
    curvatureOperatorReaction3 (Matrix.diagonal ![l1, l2, l3]) =
      Matrix.diagonal
        ![l1 ^ 2 + l2 * l3, l2 ^ 2 + l1 * l3, l3 ^ 2 + l1 * l2] := by
  unfold curvatureOperatorReaction3
  rw [Matrix.adjugate_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Matrix.mul_apply,
      diagProduct_erase_curvatureReaction3] <;> ring

theorem trace_curvatureOperatorReactionEndomorphism3_eq_eigenvalues
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3) (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric) :
    LinearMap.trace ℝ E (curvatureOperatorReactionEndomorphism3 A) =
      (hA.eigenvalues hdim 0) ^ 2 + (hA.eigenvalues hdim 1) ^ 2 +
      (hA.eigenvalues hdim 2) ^ 2 +
      hA.eigenvalues hdim 0 * hA.eigenvalues hdim 1 +
      hA.eigenvalues hdim 0 * hA.eigenvalues hdim 2 +
      hA.eigenvalues hdim 1 * hA.eigenvalues hdim 2 := by
  let b := (hA.eigenvectorBasis hdim).toBasis
  have hdiag : LinearMap.toMatrix b b A =
      Matrix.diagonal ![hA.eigenvalues hdim 0, hA.eigenvalues hdim 1,
        hA.eigenvalues hdim 2] := by
    rw [hA.toMatrix_eigenvectorBasis hdim]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [LinearMap.trace_eq_matrix_trace ℝ b, curvatureOperatorReactionEndomorphism3_toMatrix,
    hdiag, curvatureOperatorReaction3_diagonal]
  simp only [Matrix.trace, Matrix.diag_diagonal, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

theorem curvatureOperatorReaction3_orthogonal_conj
    (O A : Matrix (Fin 3) (Fin 3) Real) (hO : O * O.transpose = 1) :
    curvatureOperatorReaction3 (O * A * O.transpose) =
      O * curvatureOperatorReaction3 A * O.transpose := by
  unfold curvatureOperatorReaction3
  have hOinv : O.transpose * O = 1 := matrixTransposeMul_orthogonal O hO
  have hsq : (O * A * O.transpose) * (O * A * O.transpose) =
      O * (A * A) * O.transpose := by
    calc
      (O * A * O.transpose) * (O * A * O.transpose) =
          O * A * (O.transpose * O) * A * O.transpose := by
            simp only [Matrix.mul_assoc]
      _ = O * A * A * O.transpose := by
            rw [hOinv]
            simp
      _ = O * (A * A) * O.transpose := by
            simp only [Matrix.mul_assoc]
  have hadj := adjugate_orthogonal_conj O A hO
  rw [hsq, hadj]
  simp only [mul_add, add_mul, Matrix.mul_assoc]

theorem curvatureOperatorReaction3_commute
    (A : Matrix (Fin 3) (Fin 3) Real) :
    Commute A (curvatureOperatorReaction3 A) := by
  change A * curvatureOperatorReaction3 A = curvatureOperatorReaction3 A * A
  unfold curvatureOperatorReaction3
  rw [mul_add, add_mul, Matrix.mul_adjugate, Matrix.adjugate_mul]
  simp [mul_assoc]

theorem curvatureOperatorReaction3_posSemidef
    {A : Matrix (Fin 3) (Fin 3) Real} (hA : A.PosSemidef) :
    (curvatureOperatorReaction3 A).PosSemidef := by
  have hAh : A.IsHermitian := hA.isHermitian
  have hev : ∀ i : Fin 3, 0 ≤ hAh.eigenvalues i := by
    intro i
    exact hA.eigenvalues_nonneg i
  let U : Matrix.unitaryGroup (Fin 3) Real := hAh.eigenvectorUnitary
  let D : Matrix (Fin 3) (Fin 3) Real := Matrix.diagonal (hAh.eigenvalues)
  have hU : (U : Matrix (Fin 3) (Fin 3) Real) *
      (U : Matrix (Fin 3) (Fin 3) Real).transpose = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp U.prop)
  have hA_repr : A = (U : Matrix (Fin 3) (Fin 3) Real) * D *
      (U : Matrix (Fin 3) (Fin 3) Real).transpose := by
    have hspec := hAh.spectral_theorem
    simpa [U, D, Matrix.star_eq_conjTranspose] using hspec
  rw [hA_repr]
  rw [curvatureOperatorReaction3_orthogonal_conj _ _ hU]
  have hR : (curvatureOperatorReaction3 D).PosSemidef := by
    rw [show D = Matrix.diagonal (hAh.eigenvalues) by rfl]
    let d : Fin 3 → Real := hAh.eigenvalues
    have hd : d = ![d 0, d 1, d 2] := by
      funext i
      fin_cases i <;> rfl
    rw [congrArg Matrix.diagonal hd]
    rw [curvatureOperatorReaction3_diagonal]
    apply Matrix.PosSemidef.diagonal
    intro i
    have hdn : ∀ j : Fin 3, 0 ≤ d j := by
      intro j
      simpa [d] using hev j
    fin_cases i
    · exact add_nonneg (sq_nonneg _) (mul_nonneg (hdn 1) (hdn 2))
    · exact add_nonneg (sq_nonneg _) (mul_nonneg (hdn 0) (hdn 2))
    · exact add_nonneg (sq_nonneg _) (mul_nonneg (hdn 0) (hdn 1))
  simpa [Matrix.star_eq_conjTranspose] using
    (Matrix.PosSemidef.mul_mul_conjTranspose_same hR
      (U : Matrix (Fin 3) (Fin 3) Real))

theorem curvatureOperatorReaction3_diagonal_rank_two_null_direction
    (a b : Real) :
    curvatureOperatorReaction3 (Matrix.diagonal ![a, b, 0]) 2 2 = a * b := by
  rw [curvatureOperatorReaction3_diagonal]
  simp [Matrix.diagonal]

theorem curvatureOperatorReaction3_diagonal_rank_two_null_direction_pos
    {a b : Real} (ha : 0 < a) (hb : 0 < b) :
    0 < curvatureOperatorReaction3 (Matrix.diagonal ![a, b, 0]) 2 2 := by
  rw [curvatureOperatorReaction3_diagonal_rank_two_null_direction]
  exact mul_pos ha hb

theorem curvatureOperatorReaction3_diagonal_rank_two_excluded
    {a b : Real} (ha : 0 < a) (hb : 0 < b)
    (hnull : curvatureOperatorReaction3 (Matrix.diagonal ![a, b, 0]) 2 2 = 0) :
    False := by
  have hpos := curvatureOperatorReaction3_diagonal_rank_two_null_direction_pos ha hb
  linarith

theorem curvatureOperatorReaction3_posDef_of_rank_two
    {A : Matrix (Fin 3) (Fin 3) Real} (hA : A.PosSemidef) (hrank : A.rank = 2) :
    (curvatureOperatorReaction3 A).PosDef := by
  let hH : A.IsHermitian := hA.isHermitian
  let d : Fin 3 → Real := hH.eigenvalues
  have hcard : Fintype.card {i // d i ≠ 0} = 2 := by
    rw [← hH.rank_eq_card_non_zero_eigs]
    exact hrank
  have hzero_card : Fintype.card {i // d i = 0} = 1 := by
    have hc := Fintype.card_subtype_compl (fun i : Fin 3 => d i ≠ 0)
    have hc' : Fintype.card {i // ¬ d i ≠ 0} =
        Fintype.card (Fin 3) - Fintype.card {i // d i ≠ 0} := hc
    rw [hcard] at hc'
    norm_num [Fintype.card_fin] at hc'
    simpa [not_ne_iff] using hc'
  obtain ⟨i₀, hi₀zero⟩ := Fintype.card_eq_one_iff.mp hzero_card
  have hi₀ : ∀ j : Fin 3, d j = 0 → j = i₀ := by
    intro j hj
    have heq := congrArg Subtype.val
      (hi₀zero (⟨j, hj⟩ : {i // d i = 0}))
    exact heq
  have hne_of_ne (i : Fin 3) (hi : i ≠ i₀) : d i ≠ 0 := by
    intro hz
    exact hi (hi₀ i hz)
  have hd_nonneg (i : Fin 3) : 0 ≤ d i := by
    exact hA.eigenvalues_nonneg i
  have hdiag_pos :
      0 < d 0 ^ 2 + d 1 * d 2 ∧
      0 < d 1 ^ 2 + d 0 * d 2 ∧
      0 < d 2 ^ 2 + d 0 * d 1 := by
    have hp0 : 0 < d 0 ^ 2 + d 1 * d 2 := by
      by_cases h0 : d 0 = 0
      · have hzero : (0 : Fin 3) = i₀ := hi₀ 0 h0
        have h1 : 0 < d 1 := lt_of_le_of_ne (hd_nonneg 1)
          (Ne.symm (hne_of_ne 1 (by simpa [hzero] using
            (show (1 : Fin 3) ≠ 0 by decide))))
        have h2 : 0 < d 2 := lt_of_le_of_ne (hd_nonneg 2)
          (Ne.symm (hne_of_ne 2 (by simpa [hzero] using
            (show (2 : Fin 3) ≠ 0 by decide))))
        simpa [h0] using (mul_pos h1 h2)
      · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h0)
          (mul_nonneg (hd_nonneg 1) (hd_nonneg 2))
    have hp1 : 0 < d 1 ^ 2 + d 0 * d 2 := by
      by_cases h1 : d 1 = 0
      · have hzero : (1 : Fin 3) = i₀ := hi₀ 1 h1
        have h0 : 0 < d 0 := lt_of_le_of_ne (hd_nonneg 0)
          (Ne.symm (hne_of_ne 0 (by simpa [hzero] using
            (show (0 : Fin 3) ≠ 1 by decide))))
        have h2 : 0 < d 2 := lt_of_le_of_ne (hd_nonneg 2)
          (Ne.symm (hne_of_ne 2 (by simpa [hzero] using
            (show (2 : Fin 3) ≠ 1 by decide))))
        simpa [h1] using (mul_pos h0 h2)
      · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h1)
          (mul_nonneg (hd_nonneg 0) (hd_nonneg 2))
    have hp2 : 0 < d 2 ^ 2 + d 0 * d 1 := by
      by_cases h2 : d 2 = 0
      · have hzero : (2 : Fin 3) = i₀ := hi₀ 2 h2
        have h0 : 0 < d 0 := lt_of_le_of_ne (hd_nonneg 0)
          (Ne.symm (hne_of_ne 0 (by simpa [hzero] using
            (show (0 : Fin 3) ≠ 2 by decide))))
        have h1 : 0 < d 1 := lt_of_le_of_ne (hd_nonneg 1)
          (Ne.symm (hne_of_ne 1 (by simpa [hzero] using
            (show (1 : Fin 3) ≠ 2 by decide))))
        simpa [h2] using (mul_pos h0 h1)
      · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h2)
          (mul_nonneg (hd_nonneg 0) (hd_nonneg 1))
    exact ⟨hp0, hp1, hp2⟩
  have hdvec : d = ![d 0, d 1, d 2] := by
    funext i
    fin_cases i <;> rfl
  let D : Matrix (Fin 3) (Fin 3) Real := Matrix.diagonal d
  have hRD : (curvatureOperatorReaction3 D).PosDef := by
    have hD : D = Matrix.diagonal ![d 0, d 1, d 2] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [hD, curvatureOperatorReaction3_diagonal]
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i
    · exact hdiag_pos.1
    · exact hdiag_pos.2.1
    · exact hdiag_pos.2.2
  let U : Matrix.unitaryGroup (Fin 3) Real := hH.eigenvectorUnitary
  have hU : (U : Matrix (Fin 3) (Fin 3) Real) *
      (U : Matrix (Fin 3) (Fin 3) Real).transpose = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp U.prop)
  have hrepr : A = (U : Matrix (Fin 3) (Fin 3) Real) * D *
      (U : Matrix (Fin 3) (Fin 3) Real).transpose := by
    have hs := hH.spectral_theorem
    simpa [U, D, Matrix.star_eq_conjTranspose] using hs
  have hinj : Function.Injective (fun v : Fin 3 → Real =>
      Matrix.vecMul v (U : Matrix (Fin 3) (Fin 3) Real)) := by
    intro x y hxy
    have hxy' := congrArg (fun z : Fin 3 → Real =>
      Matrix.vecMul z (U : Matrix (Fin 3) (Fin 3) Real).transpose) hxy
    simpa [Matrix.vecMul_vecMul, hU, Matrix.vecMul_one] using hxy'
  rw [hrepr, curvatureOperatorReaction3_orthogonal_conj _ _ hU]
  simpa [Matrix.star_eq_conjTranspose] using
    (Matrix.PosDef.mul_mul_conjTranspose_same hRD hinj)

end DifferentialGeometry.Geometry.Curvature.DimensionThree
