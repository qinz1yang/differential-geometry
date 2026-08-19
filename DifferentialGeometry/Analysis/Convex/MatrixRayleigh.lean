import DifferentialGeometry.Analysis.InnerProductSpace.MatrixEuclidean
import Mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DifferentialGeometry.Analysis.Convex

open DifferentialGeometry.Analysis.InnerProductSpace
open scoped BigOperators Matrix

theorem diagonal_eigenvalues₀_eq_of_antitone
    {n : ℕ} (d : Fin n → Real) (hd : Antitone d) :
    (fun i : Fin n => (Matrix.isHermitian_diagonal d).eigenvalues₀
      (Fin.cast (Fintype.card_fin n).symm i)) = d := by
  let hA : (Matrix.diagonal d).IsHermitian := Matrix.isHermitian_diagonal d
  have hchar : (Matrix.diagonal d).charpoly =
      ∏ i : Fin n, (Polynomial.X - Polynomial.C (d i)) :=
    Matrix.charpoly_diagonal d
  have hsort := hA.sort_roots_charpoly_eq_eigenvalues₀
  rw [hchar] at hsort
  have hprod_ne : (∏ i : Fin n, (Polynomial.X - Polynomial.C (d i))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact Polynomial.X_sub_C_ne_zero (d i)
  have hroots : (∏ i : Fin n, (Polynomial.X - Polynomial.C (d i))).roots =
      (Finset.univ.val.bind fun i : Fin n => (Polynomial.X - Polynomial.C (d i)).roots) := by
    simpa using Polynomial.roots_prod (fun i : Fin n => (Polynomial.X - Polynomial.C (d i)))
      Finset.univ hprod_ne
  rw [hroots] at hsort
  simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Multiset.map_map,
    Function.comp_apply] at hsort
  change ((Finset.univ.val.map d).sort (· ≥ ·)) = List.ofFn hA.eigenvalues₀ at hsort
  have hd_sorted : (Finset.univ.val.map d).sort (· ≥ ·) = List.ofFn d := by
    rw [Fin.univ_val_map]
    change (List.ofFn d).mergeSort ((· ≥ ·) · ·) = List.ofFn d
    exact List.mergeSort_eq_self (r := (· ≥ ·)) (Antitone.sortedGE_ofFn hd).pairwise
  rw [hd_sorted] at hsort
  have hcast := List.ofFn_congr (Fintype.card_fin n) hA.eigenvalues₀
  exact List.ofFn_inj.mp (hcast.symm.trans hsort.symm)

theorem eigenvalues₀_eq_of_charpoly_eq_real
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι Real}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hchar : A.charpoly = B.charpoly) :
    hA.eigenvalues₀ = hB.eigenvalues₀ := by
  have hsA := hA.sort_roots_charpoly_eq_eigenvalues₀
  have hsB := hB.sort_roots_charpoly_eq_eigenvalues₀
  rw [← hchar] at hsB
  exact List.ofFn_inj.mp (hsA.symm.trans hsB)

theorem sum_eigenvalues_eq_sum_eigenvalues₀
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) :
    (∑ i : ι, hA.eigenvalues i) =
      ∑ i : Fin (Fintype.card ι), hA.eigenvalues₀ i := by
  let e : Fin (Fintype.card ι) ≃ ι :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))
  have hsum := Fintype.sum_equiv e.symm
    (f := fun i => hA.eigenvalues₀ (e.symm i))
    (g := fun i => hA.eigenvalues₀ i)
    (by intro i; rfl)
  simpa [e, Matrix.IsHermitian.eigenvalues] using hsum

theorem charpoly_orthogonal_conj
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S O : Matrix ι ι ℝ} (hO : O * O.transpose = 1) :
    (O.transpose * S * O).charpoly = S.charpoly := by
  have hmul := Matrix.charpoly_mul_comm O.transpose (S * O)
  rw [show O.transpose * (S * O) = O.transpose * S * O by simp [Matrix.mul_assoc]] at hmul
  rw [hmul]
  rw [show (S * O) * O.transpose = S * (O * O.transpose) by simp [Matrix.mul_assoc]]
  rw [hO, Matrix.mul_one]

theorem eigenvalues₀_orthogonal_conj
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S O : Matrix ι ι ℝ} (hS : S.IsHermitian)
    (hO : O * O.transpose = 1) :
    (show (O.transpose * S * O).IsHermitian from by
      have hconj : (O.conjTranspose * S * O).IsHermitian :=
        Matrix.isHermitian_conjTranspose_mul_mul O hS
      simpa using hconj).eigenvalues₀ = hS.eigenvalues₀ := by
  exact eigenvalues₀_eq_of_charpoly_eq_real
    (show (O.transpose * S * O).IsHermitian from by
      have hconj : (O.conjTranspose * S * O).IsHermitian :=
        Matrix.isHermitian_conjTranspose_mul_mul O hS
      simpa using hconj) hS (charpoly_orthogonal_conj hO)

theorem euclideanMatrixSymmetrization_matrixToEuclidean_orthogonal_conj_eigenvalues₀
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M O : Matrix ι ι ℝ) (hO : O * O.transpose = 1) :
    (euclideanMatrixSymmetrization_isHermitian (matrixToEuclidean (O.transpose * M * O))).eigenvalues₀ =
      (euclideanMatrixSymmetrization_isHermitian (matrixToEuclidean M)).eigenvalues₀ := by
  exact eigenvalues₀_eq_of_charpoly_eq_real
    (euclideanMatrixSymmetrization_isHermitian (matrixToEuclidean (O.transpose * M * O)))
    (euclideanMatrixSymmetrization_isHermitian (matrixToEuclidean M))
    (by
      rw [euclideanMatrixSymmetrization_matrixToEuclidean_conj]
      exact charpoly_orthogonal_conj hO)

private def matrixQuadraticForm3 (A : Matrix (Fin 3) (Fin 3) Real)
    (x : EuclideanSpace Real (Fin 3)) : Real :=
  ∑ i : Fin 3, x i * (∑ j : Fin 3, A i j * x j)

private theorem matrixQuadraticForm3_eq_inner (A : Matrix (Fin 3) (Fin 3) Real)
    (x : EuclideanSpace Real (Fin 3)) :
    matrixQuadraticForm3 A x = inner Real (A.toEuclideanLin x) x := by
  unfold matrixQuadraticForm3
  have hdot :
      ∑ i : Fin 3, x i * (∑ j : Fin 3, A i j * x j) =
        inner Real (A.toEuclideanLin x) x := by
    simpa [WithLp.ofLp_toLp, dotProduct_comm, dotProduct, Matrix.mulVec] using
      (EuclideanSpace.inner_eq_star_dotProduct (𝕜 := Real)
        (x := WithLp.toLp 2 ((Matrix.toEuclideanLin A) x))
        (y := x)).symm
  exact hdot


private theorem matrixQuadraticForm3_add_smul (a b : ℝ) (A B : Matrix (Fin 3) (Fin 3) Real)
    (x : EuclideanSpace Real (Fin 3)) :
    matrixQuadraticForm3 (a • A + b • B) x =
      a * matrixQuadraticForm3 A x + b * matrixQuadraticForm3 B x := by
  unfold matrixQuadraticForm3
  simp [Finset.mul_sum, Finset.sum_add_distrib, mul_add, add_mul, mul_assoc, mul_left_comm]


private theorem matrix_one_smul_mulVec_shift_dot
    (c : Real) (A : Matrix (Fin 3) (Fin 3) Real) (x : Fin 3 → Real) :
    star x ⬝ᵥ (c • (1 : Matrix (Fin 3) (Fin 3) Real) + A).mulVec x =
      c * (∑ i : Fin 3, x i ^ 2) + star x ⬝ᵥ A.mulVec x := by
  change (∑ i : Fin 3, star x i * (∑ j : Fin 3,
      (c * (1 : Matrix (Fin 3) (Fin 3) Real) i j + A i j) * x j)) =
    c * (∑ i : Fin 3, x i ^ 2) + star x ⬝ᵥ A.mulVec x
  simp only [star_trivial]
  rw [show (∑ i : Fin 3, x i * (∑ j : Fin 3,
      (c * (1 : Matrix (Fin 3) (Fin 3) Real) i j + A i j) * x j)) =
      ∑ i : Fin 3, x i * (∑ j : Fin 3,
        (c * (1 : Matrix (Fin 3) (Fin 3) Real) i j + A i j) * x j) by rfl]
  have hdiag : ∀ i : Fin 3,
      (∑ j : Fin 3, (c * (1 : Matrix (Fin 3) (Fin 3) Real) i j + A i j) * x j) =
        c * x i + ∑ j : Fin 3, A i j * x j := by
    intro i
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    have hone : (∑ j : Fin 3, (c * (1 : Matrix (Fin 3) (Fin 3) Real) i j) * x j) =
        c * x i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        by_cases hij : i = j
        · exact False.elim (hj hij.symm)
        · simp [hij]
      · intro hi
        simp at hi
    rw [hone]
  rw [show (∑ i : Fin 3, x i * (∑ j : Fin 3,
      (c * (1 : Matrix (Fin 3) (Fin 3) Real) i j + A i j) * x j)) =
      ∑ i : Fin 3, x i * (c * x i + ∑ j : Fin 3, A i j * x j) by
    apply Finset.sum_congr rfl
    intro i _
    rw [hdiag i]]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  rw [show (∑ i : Fin 3, x i * (c * x i)) = ∑ i : Fin 3, c * x i ^ 2 by
    apply Finset.sum_congr rfl
    intro i _
    ring]
  rw [show (∑ i : Fin 3, x i * ∑ j : Fin 3, A i j * x j) =
      star x ⬝ᵥ A.mulVec x by
    simp [Matrix.mulVec, dotProduct]]
  rw [← Finset.mul_sum]
  simp only [star_trivial]


private theorem continuous_matrixQuadraticForm3 :
    Continuous (fun p : Matrix (Fin 3) (Fin 3) Real × EuclideanSpace Real (Fin 3) =>
      matrixQuadraticForm3 p.1 p.2) := by
  unfold matrixQuadraticForm3
  fun_prop

noncomputable def minimumRayleighQuotient3 (A : Matrix (Fin 3) (Fin 3) Real) : Real :=
  sInf (matrixQuadraticForm3 A '' Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1)

theorem continuous_minimumRayleighQuotient3 :
    Continuous minimumRayleighQuotient3 := by
  unfold minimumRayleighQuotient3
  refine IsCompact.continuous_sInf (K := Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (isCompact_sphere _ _) ?_
  simpa [Function.uncurry] using continuous_matrixQuadraticForm3

theorem continuous_minimumRayleighQuotient3_comp
    {α : Type*} [TopologicalSpace α]
    {A : α → Matrix (Fin 3) (Fin 3) Real} (hA : Continuous A) :
    Continuous (fun x : α => minimumRayleighQuotient3 (A x)) :=
  continuous_minimumRayleighQuotient3.comp hA

theorem concave_minimumRayleighQuotient3 :
    ConcaveOn ℝ Set.univ minimumRayleighQuotient3 := by
  rw [concaveOn_iff_forall_pos]
  constructor
  · exact convex_univ
  · intro A hA B hB a b ha hb hab
    let SA : Set ℝ := matrixQuadraticForm3 A '' Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1
    let SB : Set ℝ := matrixQuadraticForm3 B '' Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1
    let SC : Set ℝ := matrixQuadraticForm3 (a • A + b • B) '' Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1
    have hSphere : (WithLp.toLp 2 (fun i : Fin 3 => if i = 0 then (1 : ℝ) else 0)) ∈
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 := by
      rw [mem_sphere_zero_iff_norm]
      norm_num [PiLp.norm_eq_of_L2]
    have hSA_nonempty : SA.Nonempty := ⟨matrixQuadraticForm3 A (WithLp.toLp 2 (fun i : Fin 3 => if i = 0 then (1 : ℝ) else 0)), ⟨_, hSphere, rfl⟩⟩
    have hSB_nonempty : SB.Nonempty := ⟨matrixQuadraticForm3 B (WithLp.toLp 2 (fun i : Fin 3 => if i = 0 then (1 : ℝ) else 0)), ⟨_, hSphere, rfl⟩⟩
    have hSC_nonempty : SC.Nonempty := ⟨matrixQuadraticForm3 (a • A + b • B) (WithLp.toLp 2 (fun i : Fin 3 => if i = 0 then (1 : ℝ) else 0)), ⟨_, hSphere, rfl⟩⟩
    have hcontA : ContinuousOn (matrixQuadraticForm3 A) (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) := by
      have hcont : Continuous (fun x : EuclideanSpace Real (Fin 3) => matrixQuadraticForm3 A x) :=
        continuous_matrixQuadraticForm3.comp (continuous_const.prodMk continuous_id)
      exact hcont.continuousOn
    have hcontB : ContinuousOn (matrixQuadraticForm3 B) (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) := by
      have hcont : Continuous (fun x : EuclideanSpace Real (Fin 3) => matrixQuadraticForm3 B x) :=
        continuous_matrixQuadraticForm3.comp (continuous_const.prodMk continuous_id)
      exact hcont.continuousOn
    have hcontC : ContinuousOn (matrixQuadraticForm3 (a • A + b • B)) (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) := by
      have hcont : Continuous (fun x : EuclideanSpace Real (Fin 3) => matrixQuadraticForm3 (a • A + b • B) x) :=
        continuous_matrixQuadraticForm3.comp (continuous_const.prodMk continuous_id)
      exact hcont.continuousOn
    have hSA_bdd : BddBelow SA := by
      dsimp [SA]
      exact (isCompact_sphere (0 : EuclideanSpace Real (Fin 3)) 1).bddBelow_image hcontA
    have hSB_bdd : BddBelow SB := by
      dsimp [SB]
      exact (isCompact_sphere (0 : EuclideanSpace Real (Fin 3)) 1).bddBelow_image hcontB
    have hSC_bdd : BddBelow SC := by
      dsimp [SC]
      exact (isCompact_sphere (0 : EuclideanSpace Real (Fin 3)) 1).bddBelow_image hcontC
    have hlower : a * sInf SA + b * sInf SB ∈ lowerBounds SC := by
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      have hAinf : sInf SA ≤ matrixQuadraticForm3 A x := csInf_le hSA_bdd ⟨x, hx, rfl⟩
      have hBinf : sInf SB ≤ matrixQuadraticForm3 B x := csInf_le hSB_bdd ⟨x, hx, rfl⟩
      have hmulA : a * sInf SA ≤ a * matrixQuadraticForm3 A x :=
        mul_le_mul_of_nonneg_left hAinf ha.le
      have hmulB : b * sInf SB ≤ b * matrixQuadraticForm3 B x :=
        mul_le_mul_of_nonneg_left hBinf hb.le
      have hadd := add_le_add hmulA hmulB
      have hlin := matrixQuadraticForm3_add_smul a b A B x
      simpa [hlin] using hadd
    have hle : a * sInf SA + b * sInf SB ≤ sInf SC := le_csInf hSC_nonempty hlower
    change sInf SC ≥ a * sInf SA + b * sInf SB
    exact hle


theorem convex_negPart_minimumRayleighQuotient3 :
    ConvexOn ℝ Set.univ (fun A : Matrix (Fin 3) (Fin 3) Real =>
      max (-minimumRayleighQuotient3 A) 0) := by
  have hneg : ConvexOn ℝ Set.univ (fun A : Matrix (Fin 3) (Fin 3) Real =>
      -minimumRayleighQuotient3 A) := concave_minimumRayleighQuotient3.neg
  have hzero : ConvexOn ℝ Set.univ (fun _ : Matrix (Fin 3) (Fin 3) Real => (0 : ℝ)) :=
    convexOn_const (0 : ℝ) convex_univ
  change ConvexOn ℝ Set.univ (fun A : Matrix (Fin 3) (Fin 3) Real =>
      (-minimumRayleighQuotient3 A) ⊔ 0)
  exact hneg.sup hzero

private theorem matrixQuadraticForm3_eq_dotProduct
    (A : Matrix (Fin 3) (Fin 3) Real) (x : Fin 3 → Real) :
    matrixQuadraticForm3 A (WithLp.toLp 2 x) = star x ⬝ᵥ A.mulVec x := by
  rw [matrixQuadraticForm3_eq_inner]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [Matrix.mulVec, dotProduct]

private theorem min_eigenvalue_mul_sum_sq_le_matrixQuadraticForm3
    {A : Matrix (Fin 3) (Fin 3) Real} (hA : A.IsHermitian)
    (x : EuclideanSpace Real (Fin 3)) :
    hA.eigenvalues₀ 2 * (∑ i : Fin 3, x i ^ 2) ≤ matrixQuadraticForm3 A x := by
  let T : EuclideanSpace Real (Fin 3) →ₗ[Real] EuclideanSpace Real (Fin 3) :=
    A.toEuclideanLin
  let hT : T.IsSymmetric := by
    dsimp [T]
    exact (Matrix.isHermitian_iff_isSymmetric (A := A)).1 hA
  let hn : Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3 := finrank_euclideanSpace
  let b : OrthonormalBasis (Fin 3) Real (EuclideanSpace Real (Fin 3)) :=
    hT.eigenvectorBasis hn
  have hquad :
      matrixQuadraticForm3 A x = inner Real (T x) x := by
    dsimp [T]
    exact matrixQuadraticForm3_eq_inner A x
  have hdiag :
      inner Real (T x) x =
        ∑ i : Fin 3, hT.eigenvalues hn i * (b.repr x i) ^ 2 := by
    have happly : ∀ i : Fin 3, T (b i : EuclideanSpace Real (Fin 3)) =
        hT.eigenvalues hn i • (b i : EuclideanSpace Real (Fin 3)) :=
      hT.apply_eigenvectorBasis hn
    have hx : x = ∑ i : Fin 3, (b.repr x i) • (b i : EuclideanSpace Real (Fin 3)) :=
      (b.sum_repr x).symm
    conv_lhs => rw [hx]
    rw [map_sum T]
    simp_rw [map_smul T]
    simp_rw [happly]
    simp_rw [smul_smul]
    have hortho : Orthonormal Real (fun i : Fin 3 => (b i : EuclideanSpace Real (Fin 3))) :=
      b.orthonormal
    simpa [mul_assoc, mul_comm, mul_left_comm, pow_two] using
      (hortho.inner_sum (fun i => (b.repr x i) * hT.eigenvalues hn i) (fun i => b.repr x i)
        Finset.univ)
  have hmin : ∀ i : Fin 3, hT.eigenvalues hn 2 ≤ hT.eigenvalues hn i := by
    intro i
    exact (hT.eigenvalues_antitone hn) (show i ≤ (2 : Fin 3) from Nat.le_of_lt_succ i.2)
  have hsum : ∑ i : Fin 3, hT.eigenvalues hn i * (b.repr x i) ^ 2 ≥
      hT.eigenvalues hn 2 * ∑ i : Fin 3, (b.repr x i) ^ 2 := by
    have hle : ∀ i : Fin 3, hT.eigenvalues hn 2 * (b.repr x i) ^ 2 ≤
        hT.eigenvalues hn i * (b.repr x i) ^ 2 := by
      intro i
      exact mul_le_mul_of_nonneg_right (hmin i) (sq_nonneg _)
    calc
      hT.eigenvalues hn 2 * ∑ i : Fin 3, (b.repr x i) ^ 2
          = ∑ i : Fin 3, hT.eigenvalues hn 2 * (b.repr x i) ^ 2 := by
            rw [Finset.mul_sum Finset.univ (fun i => (b.repr x i) ^ 2) (hT.eigenvalues hn 2)]
      _ ≤ ∑ i : Fin 3, hT.eigenvalues hn i * (b.repr x i) ^ 2 :=
            Finset.sum_le_sum (fun i _ => hle i)
  have hnorm : ∑ i : Fin 3, (b.repr x i) ^ 2 = ∑ i : Fin 3, x i ^ 2 := by
    have hrepr : ∀ i : Fin 3, b.repr x i = inner Real (b i : EuclideanSpace Real (Fin 3)) x :=
      b.repr_apply_apply x
    have hparseval :
        ∑ i : Fin 3, inner Real x (b i : EuclideanSpace Real (Fin 3)) *
          inner Real (b i : EuclideanSpace Real (Fin 3)) x = inner Real x x :=
      b.sum_inner_mul_inner x x
    have hparseval' : ∑ i : Fin 3, (b.repr x i) ^ 2 = inner Real x x := by
      rw [← hparseval]
      apply Finset.sum_congr rfl
      intro i _
      rw [hrepr i, real_inner_comm, sq]
    rw [hparseval', real_inner_self_eq_norm_sq]
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (x i)))]
  have hbridge :
      hT.eigenvalues hn 2 * ∑ i : Fin 3, x i ^ 2 ≤ matrixQuadraticForm3 A x := by
    rw [hquad, hdiag]
    rw [hnorm] at hsum
    exact hsum
  have hord : hA.eigenvalues₀ 2 = hT.eigenvalues hn 2 := by
    rfl
  rw [hord]
  exact hbridge

theorem posSemidef_shift_iff_min_eigenvalue
    {A : Matrix (Fin 3) (Fin 3) Real} (hA : A.IsHermitian) (c : Real) :
    (c • (1 : Matrix (Fin 3) (Fin 3) Real) + A).PosSemidef ↔
      0 ≤ c + hA.eigenvalues₀ 2 := by
  constructor
  · intro hP
    let T : EuclideanSpace Real (Fin 3) →ₗ[Real] EuclideanSpace Real (Fin 3) := A.toEuclideanLin
    let hT : T.IsSymmetric := (Matrix.isHermitian_iff_isSymmetric (A := A)).1 hA
    let hn : Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3 := finrank_euclideanSpace
    let b : OrthonormalBasis (Fin 3) Real (EuclideanSpace Real (Fin 3)) := hT.eigenvectorBasis hn
    let bvec : EuclideanSpace Real (Fin 3) := b 2
    let x : Fin 3 → Real := fun i => bvec.ofLp i
    have hnorm : ∑ i : Fin 3, x i ^ 2 = 1 := by
      have hb : ‖bvec‖ = 1 := by dsimp [bvec]; exact b.orthonormal.1 2
      have hsq : ‖bvec‖ ^ 2 = 1 := by rw [hb]; norm_num
      rw [EuclideanSpace.norm_eq] at hsq
      simp only [Real.norm_eq_abs, sq_abs] at hsq
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (x i)))] at hsq
      simpa [x, bvec] using hsq
    have hnonneg := (Matrix.PosSemidef.dotProduct_mulVec_nonneg hP) x
    have hshift := matrix_one_smul_mulVec_shift_dot c A x
    have hAquad : star x ⬝ᵥ A.mulVec x = hT.eigenvalues hn 2 := by
      have heig := hT.apply_eigenvectorBasis hn 2
      have hx : (WithLp.toLp 2 x : EuclideanSpace Real (Fin 3)) = bvec := by
        ext i
        simp [x, bvec]
      calc
        star x ⬝ᵥ A.mulVec x = matrixQuadraticForm3 A (WithLp.toLp 2 x) :=
          (matrixQuadraticForm3_eq_dotProduct A x).symm
        _ = inner Real (T bvec) bvec := by
          rw [hx]
          dsimp [T]
          exact matrixQuadraticForm3_eq_inner A bvec
        _ = hT.eigenvalues hn 2 := by
          rw [real_inner_comm]
          have hnormb : ‖bvec‖ = 1 := by dsimp [bvec]; exact b.orthonormal.1 2
          simpa [hnormb] using (inner_product_apply_eigenvector (T := T) (v := bvec) heig)
    have hminord : hA.eigenvalues₀ 2 = hT.eigenvalues hn 2 := rfl
    rw [hshift, hAquad, ← hminord] at hnonneg
    simpa [hnorm] using hnonneg
  · intro hnonneg
    have hHerm : (c • (1 : Matrix (Fin 3) (Fin 3) Real) + A).IsHermitian := by
      rw [show c • (1 : Matrix (Fin 3) (Fin 3) Real) + A =
          A + c • (1 : Matrix (Fin 3) (Fin 3) Real) by simp [add_comm]]
      have hA' : A.IsHermitian := hA
      have h1 : (c • (1 : Matrix (Fin 3) (Fin 3) Real)).IsHermitian := by
        have hdiag : c • (1 : Matrix (Fin 3) (Fin 3) Real) =
            Matrix.diagonal (fun _ : Fin 3 => c) := by
          ext i j
          simp [Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal]
        rw [hdiag]
        exact Matrix.isHermitian_diagonal (fun _ : Fin 3 => c)
      exact hA'.add h1
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
    intro x
    have hshift := matrix_one_smul_mulVec_shift_dot c A x
    rw [hshift]
    have hlow : hA.eigenvalues₀ 2 * (∑ i : Fin 3, x i ^ 2) ≤ star x ⬝ᵥ A.mulVec x := by
      rw [← matrixQuadraticForm3_eq_dotProduct A x]
      have hquad := min_eigenvalue_mul_sum_sq_le_matrixQuadraticForm3 hA (WithLp.toLp 2 x)
      have hnormeq : ∑ i : Fin 3, x i ^ 2 =
          ∑ i : Fin 3, (WithLp.toLp 2 x : EuclideanSpace Real (Fin 3)) i ^ 2 := rfl
      simpa [hnormeq] using hquad
    have hsumnonneg : 0 ≤ ∑ i : Fin 3, x i ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
    nlinarith [mul_nonneg hnonneg hsumnonneg, hlow]


theorem minimumRayleighQuotient3_eq_min_eigenvalue
    {A : Matrix (Fin 3) (Fin 3) Real} (hA : A.IsHermitian) :
    minimumRayleighQuotient3 A = hA.eigenvalues₀ 2 := by
  let T : EuclideanSpace Real (Fin 3) →ₗ[Real] EuclideanSpace Real (Fin 3) :=
    A.toEuclideanLin
  let hT : T.IsSymmetric := by
    dsimp [T]
    exact (Matrix.isHermitian_iff_isSymmetric (A := A)).1 hA
  let hn : Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3 := finrank_euclideanSpace
  let b : OrthonormalBasis (Fin 3) Real (EuclideanSpace Real (Fin 3)) :=
    hT.eigenvectorBasis hn
  let bvec : EuclideanSpace Real (Fin 3) := b 2
  have hsphere : bvec ∈ Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 := by
    rw [mem_sphere_zero_iff_norm]
    dsimp [bvec]
    exact b.orthonormal.1 2
  have hcont : Continuous (fun x : EuclideanSpace Real (Fin 3) => matrixQuadraticForm3 A x) := by
    simpa using continuous_matrixQuadraticForm3.comp
      ((continuous_const (y := A)).prodMk
        (continuous_id (X := EuclideanSpace Real (Fin 3))))
  have hbdd : BddBelow (matrixQuadraticForm3 A ''
      Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) := by
    exact (isCompact_sphere (0 : EuclideanSpace Real (Fin 3)) 1).bddBelow_image
      hcont.continuousOn
  have heval : matrixQuadraticForm3 A bvec = hT.eigenvalues hn 2 := by
    have hquad : matrixQuadraticForm3 A bvec = inner Real (T bvec) bvec := by
      dsimp [T]
      exact matrixQuadraticForm3_eq_inner A bvec
    rw [hquad, real_inner_comm]
    have heig := hT.apply_eigenvectorBasis hn 2
    have hnorm : ‖bvec‖ = 1 := by
      dsimp [bvec]
      exact b.orthonormal.1 2
    simpa [T, bvec, hnorm] using
      (inner_product_apply_eigenvector (T := T) (v := bvec) heig)
  have hminord : hT.eigenvalues hn 2 = hA.eigenvalues₀ 2 := rfl
  have him : matrixQuadraticForm3 A bvec ∈
      matrixQuadraticForm3 A '' Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 := by
    exact Set.mem_image_of_mem (matrixQuadraticForm3 A) hsphere
  apply le_antisymm
  · unfold minimumRayleighQuotient3
    have hval : hA.eigenvalues₀ 2 = matrixQuadraticForm3 A bvec := by
      exact hminord.symm.trans heval.symm
    exact csInf_le hbdd (hval ▸ him)
  · unfold minimumRayleighQuotient3
    apply le_csInf
    · exact ⟨matrixQuadraticForm3 A bvec, him⟩
    · rintro y ⟨x, hx, rfl⟩
      have hsumsq : ∑ i : Fin 3, x i ^ 2 = 1 := by
        have hnorm : ‖x‖ = 1 := (mem_sphere_zero_iff_norm).mp hx
        have hsqnorm : ‖x‖ ^ 2 = 1 := by
          rw [hnorm]
          norm_num
        have hsum : ∑ i : Fin 3, x i ^ 2 = ‖x‖ ^ 2 := by
          rw [EuclideanSpace.norm_eq]
          simp only [Real.norm_eq_abs, sq_abs]
          rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (x i)))]
        rw [hsum, hsqnorm]
      simpa [hsumsq, hminord] using min_eigenvalue_mul_sum_sq_le_matrixQuadraticForm3 hA x

theorem three_mul_minimumRayleighQuotient3_le_trace
    {A : Matrix (Fin 3) (Fin 3) Real} (hA : A.IsHermitian) :
    3 * minimumRayleighQuotient3 A ≤ A.trace := by
  have hmin : minimumRayleighQuotient3 A = hA.eigenvalues₀ 2 :=
    minimumRayleighQuotient3_eq_min_eigenvalue hA
  rw [hmin]
  have hle : ∀ i : Fin 3, hA.eigenvalues₀ 2 ≤ A i i := by
    intro i
    let e : EuclideanSpace Real (Fin 3) := WithLp.toLp 2 (fun j : Fin 3 => if j = i then (1 : ℝ) else 0)
    have hsum : (∑ j : Fin 3, e j ^ 2) = 1 := by
      dsimp [e]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [hj]
      · intro h; exact absurd (Finset.mem_univ i) h
    have hquad := min_eigenvalue_mul_sum_sq_le_matrixQuadraticForm3 hA e
    have hmain : hA.eigenvalues₀ 2 ≤ matrixQuadraticForm3 A e := by
      simpa [hsum] using hquad
    have hsec : matrixQuadraticForm3 A e = A i i := by
      unfold matrixQuadraticForm3
      dsimp [e]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [hj]
      · intro h; exact absurd (Finset.mem_univ i) h
    simpa [hsec] using hmain
  calc
    3 * hA.eigenvalues₀ 2 = ∑ i : Fin 3, hA.eigenvalues₀ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ A.trace := by
      unfold Matrix.trace
      exact Finset.sum_le_sum (fun i _ => hle i)

theorem neg_three_mul_negPart_minimumRayleighQuotient3_le_trace
    {A : Matrix (Fin 3) (Fin 3) Real} (hA : A.IsHermitian) :
    -3 * max (-minimumRayleighQuotient3 A) 0 ≤ A.trace := by
  have htrace := three_mul_minimumRayleighQuotient3_le_trace hA
  by_cases h : minimumRayleighQuotient3 A < 0
  · have hmax : max (-minimumRayleighQuotient3 A) 0 = -minimumRayleighQuotient3 A :=
      max_eq_left (neg_nonneg.mpr h.le)
    rw [hmax]
    linarith
  · have hmax : max (-minimumRayleighQuotient3 A) 0 = 0 :=
      max_eq_right (neg_nonpos.mpr (not_lt.mp h))
    rw [hmax]
    have hnonneg : 0 ≤ 3 * minimumRayleighQuotient3 A := by nlinarith
    linarith

theorem minimumRayleighQuotient3_zero : minimumRayleighQuotient3 (0 : Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
  unfold minimumRayleighQuotient3
  have hzero : matrixQuadraticForm3 (0 : Matrix (Fin 3) (Fin 3) ℝ) = fun _ => 0 := by
    funext x
    simp [matrixQuadraticForm3]
  simp [hzero]

theorem hermitian_orthogonal_diagonalization
    {A : Matrix (Fin 3) (Fin 3) Real} (hA : A.IsHermitian) :
    ∃ O : Matrix (Fin 3) (Fin 3) Real,
      O * O.transpose = 1 ∧
      O.transpose * A * O = Matrix.diagonal hA.eigenvalues₀ := by
  let T : EuclideanSpace Real (Fin 3) →ₗ[Real] EuclideanSpace Real (Fin 3) := A.toEuclideanLin
  let hT : T.IsSymmetric := by
    dsimp [T]
    exact (Matrix.isHermitian_iff_isSymmetric (A := A)).1 hA
  let hn : Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3 := finrank_euclideanSpace
  let b : OrthonormalBasis (Fin 3) Real (EuclideanSpace Real (Fin 3)) := hT.eigenvectorBasis hn
  let O : Matrix (Fin 3) (Fin 3) Real :=
    (EuclideanSpace.basisFun (Fin 3) Real).toBasis.toMatrix b.toBasis
  refine ⟨O, ?_, ?_⟩
  · have hO_mem : O ∈ Matrix.unitaryGroup (Fin 3) Real := by
      dsimp [O]
      exact (EuclideanSpace.basisFun (Fin 3) Real).toMatrix_orthonormalBasis_mem_unitary b
    have hOO : O * star O = 1 := Matrix.mem_unitaryGroup_iff.mp hO_mem
    simpa [star, Matrix.conjTranspose] using hOO
  · have hO_col : ∀ i : Fin 3, O *ᵥ Pi.single i (1 : Real) = b i := by
      intro i
      ext j
      simp [O, Matrix.mulVec, Module.Basis.toMatrix_apply, EuclideanSpace.basisFun_repr]
    have hOorth : O.transpose * O = 1 := by
      have hO_mem' : O ∈ Matrix.unitaryGroup (Fin 3) Real := by
        dsimp [O]
        exact (EuclideanSpace.basisFun (Fin 3) Real).toMatrix_orthonormalBasis_mem_unitary b
      have hOO' : star O * O = 1 := Matrix.mem_unitaryGroup_iff'.mp hO_mem'
      simpa [star, Matrix.conjTranspose] using hOO'
    have hOinv : ∀ i : Fin 3, O.transpose *ᵥ b i = Pi.single i (1 : Real) := by
      intro i
      calc
        O.transpose *ᵥ b i = O.transpose *ᵥ (O *ᵥ Pi.single i (1 : Real)) := by
          rw [← hO_col i]
        _ = (O.transpose * O) *ᵥ Pi.single i (1 : Real) := by
          rw [Matrix.mulVec_mulVec]
        _ = 1 *ᵥ Pi.single i (1 : Real) := by
          rw [hOorth]
        _ = Pi.single i (1 : Real) := by
          ext j
          simp [Matrix.mulVec, Matrix.one_apply, Pi.single_apply]
    have hAeig : ∀ i : Fin 3, A *ᵥ (b i).ofLp = (hT.eigenvalues hn i) • (b i).ofLp := by
      intro i
      have h := hT.apply_eigenvectorBasis hn i
      have hof : (T (b i)).ofLp = (hT.eigenvalues hn i • b i).ofLp := congrArg WithLp.ofLp h
      have hTval : (T (b i)).ofLp = A *ᵥ (b i).ofLp := by
        simp [T, Matrix.toEuclideanLin, Matrix.toLpLin_apply]
      simp [← hTval, hof, WithLp.ofLp_smul]
    apply Matrix.toEuclideanLin.injective <| (EuclideanSpace.basisFun (Fin 3) Real).toBasis.ext fun i ↦ ?_
    change Matrix.toEuclideanLin (O.transpose * A * O) (EuclideanSpace.basisFun (Fin 3) Real i) =
      Matrix.toEuclideanLin (Matrix.diagonal (hT.eigenvalues hn)) (EuclideanSpace.basisFun (Fin 3) Real i)
    simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      EuclideanSpace.basisFun_apply, PiLp.ofLp_single, ← Matrix.mulVec_mulVec, hO_col,
      ← Matrix.mulVec_mulVec, hAeig,
      Matrix.diagonal_mulVec_single, Matrix.mulVec_smul, hOinv,
      WithLp.toLp_smul, PiLp.toLp_single, mul_one]
    apply PiLp.ext fun j ↦ ?_
    simp only [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

theorem eigenvalues₀_smul_of_nonneg
    {S : Matrix (Fin 3) (Fin 3) ℝ} (hS : S.IsHermitian)
    {c : ℝ} (hc : 0 ≤ c) (hcS : (c • S).IsHermitian) :
    hcS.eigenvalues₀ = c • hS.eigenvalues₀ := by
  classical
  rcases hermitian_orthogonal_diagonalization hS with ⟨O, hO, hdiag⟩
  have hOt : O.transpose * O = 1 := matrixTransposeMul_orthogonal O hO
  let D₀ : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal hS.eigenvalues₀
  have hdiag' : O.transpose * S * O = D₀ := by simpa [D₀] using hdiag
  have hSrep : S = O * D₀ * O.transpose := by
    have h1 : S = (O * O.transpose) * S * (O * O.transpose) := by
      rw [hO]
      simp
    calc
      S = (O * O.transpose) * S * (O * O.transpose) := h1
      _ = O * (O.transpose * S * O) * O.transpose := by
            simp [Matrix.mul_assoc]
      _ = O * D₀ * O.transpose := by
            rw [hdiag']
  have hdiagc : O.transpose * (c • S) * O = Matrix.diagonal (c • hS.eigenvalues₀) := by
    calc
      O.transpose * (c • S) * O
          = O.transpose * (c • (O * D₀ * O.transpose)) * O := by
              rw [show c • S = c • (O * D₀ * O.transpose) from by rw [hSrep]]
      _ = O.transpose * (O * (c • D₀) * O.transpose) * O := by
              rw [← Matrix.smul_mul, ← Matrix.mul_smul]
      _ = c • D₀ := by
            calc
              O.transpose * (O * (c • D₀) * O.transpose) * O
                  = (O.transpose * O) * (c • D₀) * (O.transpose * O) := by
                      simp [Matrix.mul_assoc]
              _ = c • D₀ := by
                      simp [hOt]
      _ = Matrix.diagonal (c • hS.eigenvalues₀) := by
            ext i j
            simp [D₀, Matrix.diagonal, smul_eq_mul]
  have hanti : Antitone (c • hS.eigenvalues₀) := by
    intro i j hij
    change c * hS.eigenvalues₀ j ≤ c * hS.eigenvalues₀ i
    exact mul_le_mul_of_nonneg_left (hS.eigenvalues₀_antitone hij) hc
  have hdiagE : (Matrix.isHermitian_diagonal (c • hS.eigenvalues₀)).eigenvalues₀ =
      c • hS.eigenvalues₀ := by
    funext i
    have h := congrFun (diagonal_eigenvalues₀_eq_of_antitone
      (c • hS.eigenvalues₀) hanti) (Fin.cast (Fintype.card_fin 3) i)
    simpa using h
  have hOcS : (O.transpose * (c • S) * O).IsHermitian := by
    have hconj : (O.conjTranspose * (c • S) * O).IsHermitian :=
      Matrix.isHermitian_conjTranspose_mul_mul O hcS
    simpa using hconj
  have hStep1 : hcS.eigenvalues₀ = hOcS.eigenvalues₀ :=
    (eigenvalues₀_orthogonal_conj (S := c • S) hcS hO).symm
  have hStep2a : hOcS.eigenvalues₀ =
      (Matrix.isHermitian_diagonal (c • hS.eigenvalues₀)).eigenvalues₀ := by
    exact eigenvalues₀_eq_of_charpoly_eq_real hOcS
      (Matrix.isHermitian_diagonal (c • hS.eigenvalues₀)) (by rw [hdiagc])
  exact hStep1.trans (hStep2a.trans hdiagE)

theorem diagonal_eigenvalues_tuple {A : Matrix (Fin 3) (Fin 3) Real} (hA : A.IsHermitian) :
    Matrix.diagonal hA.eigenvalues₀ =
      Matrix.diagonal ![hA.eigenvalues₀ 0, hA.eigenvalues₀ 1, hA.eigenvalues₀ 2] := by
  have hfun : hA.eigenvalues₀ = fun i : Fin 3 =>
      ![hA.eigenvalues₀ 0, hA.eigenvalues₀ 1, hA.eigenvalues₀ 2] i := by
    ext i
    fin_cases i <;> rfl
  rw [hfun]
  rfl

private theorem matrixQuadraticForm3_diagonal
    (d : Fin 3 → Real) (x : EuclideanSpace ℝ (Fin 3)) :
    matrixQuadraticForm3 (Matrix.diagonal d) x = ∑ i : Fin 3, d i * (x i) ^ 2 := by
  unfold matrixQuadraticForm3
  simp only [Matrix.diagonal]
  have hdiag : ∀ i : Fin 3,
      (∑ x_2 : Fin 3, (if i = x_2 then d i else 0) * x.ofLp x_2) =
        d i * x.ofLp i := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro x_2 _ hx2
      rw [if_neg (Ne.symm hx2)]
      simp
    · intro h
      exact absurd (Finset.mem_univ i) h
  calc
    ∑ i : Fin 3, x i * (∑ x_2 : Fin 3, (if i = x_2 then d i else 0) * x.ofLp x_2)
        = ∑ i : Fin 3, x i * (d i * x i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hdiag i]
    _ = ∑ i : Fin 3, d i * (x i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          ring

theorem minimumRayleighQuotient3_diagonal_le
    (d : Fin 3 → Real) (j : Fin 3) :
    minimumRayleighQuotient3 (Matrix.diagonal d) ≤ d j := by
  let e : EuclideanSpace ℝ (Fin 3) :=
    WithLp.toLp 2 (fun i : Fin 3 => if i = j then (1 : ℝ) else 0)
  have hsphere : e ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    rw [mem_sphere_zero_iff_norm]
    dsimp [e]
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [show (∑ i : Fin 3, (if i = j then (1 : ℝ) else 0) ^ 2) = 1 by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hi
        simp [hi]
      · intro h
        exact absurd (Finset.mem_univ j) h]
    norm_num
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin 3) =>
      matrixQuadraticForm3 (Matrix.diagonal d) x) := by
    simpa using continuous_matrixQuadraticForm3.comp
      ((continuous_const (y := Matrix.diagonal d)).prodMk continuous_id)
  have hbdd : BddBelow (matrixQuadraticForm3 (Matrix.diagonal d) ''
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
    exact (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).bddBelow_image
      hcont.continuousOn
  unfold minimumRayleighQuotient3
  have hval : matrixQuadraticForm3 (Matrix.diagonal d) e = d j := by
    rw [matrixQuadraticForm3_diagonal]
    dsimp [e]
    rw [show (∑ i : Fin 3, d i * (if i = j then (1 : ℝ) else 0) ^ 2) = d j by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hi
        simp [hi]
      · intro h
        exact absurd (Finset.mem_univ j) h]
  have him : d j ∈ matrixQuadraticForm3 (Matrix.diagonal d) ''
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    exact hval ▸ Set.mem_image_of_mem (matrixQuadraticForm3 (Matrix.diagonal d)) hsphere
  exact csInf_le hbdd (hval ▸ him)

theorem minimumRayleighQuotient3_diagonal_ge
    (d : Fin 3 → Real) {m : Real}
    (hm : ∀ i : Fin 3, m ≤ d i) :
    m ≤ minimumRayleighQuotient3 (Matrix.diagonal d) := by
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin 3) =>
      matrixQuadraticForm3 (Matrix.diagonal d) x) := by
    simpa using continuous_matrixQuadraticForm3.comp
      ((continuous_const (y := Matrix.diagonal d)).prodMk continuous_id)
  have hbdd : BddBelow (matrixQuadraticForm3 (Matrix.diagonal d) ''
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
    exact (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).bddBelow_image
      hcont.continuousOn
  have hne : (matrixQuadraticForm3 (Matrix.diagonal d) ''
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).Nonempty := by
    have hsphere0 : (WithLp.toLp 2 (fun i : Fin 3 => if i = 0 then (1 : ℝ) else 0)) ∈
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
      rw [mem_sphere_zero_iff_norm]
      rw [EuclideanSpace.norm_eq]
      simp only [Real.norm_eq_abs, sq_abs]
      rw [show (∑ i : Fin 3, (if i = 0 then (1 : ℝ) else 0) ^ 2) = 1 by
        rw [Finset.sum_eq_single 0]
        · simp
        · intro i _ hi
          simp [hi]
        · intro h
          exact absurd (Finset.mem_univ (0 : Fin 3)) h]
      norm_num
    exact ⟨matrixQuadraticForm3 (Matrix.diagonal d)
      (WithLp.toLp 2 (fun i : Fin 3 => if i = 0 then (1 : ℝ) else 0)),
      ⟨_, hsphere0, rfl⟩⟩
  unfold minimumRayleighQuotient3
  apply le_csInf hne
  rintro y ⟨x, hx, rfl⟩
  rw [matrixQuadraticForm3_diagonal]
  have hsumsq : (∑ i : Fin 3, (x i) ^ 2) = 1 := by
    have hnorm : ‖x‖ = 1 := (mem_sphere_zero_iff_norm).mp hx
    have hsq : (∑ i : Fin 3, (x i) ^ 2) = ‖x‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq]
      simp only [Real.norm_eq_abs, sq_abs]
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (x i)))]
    rw [hsq, hnorm]
    norm_num
  calc
    m = m * (∑ i : Fin 3, (x i) ^ 2) := by rw [hsumsq, mul_one]
    _ = ∑ i : Fin 3, m * (x i) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ ∑ i : Fin 3, d i * (x i) ^ 2 := by
          exact Finset.sum_le_sum (fun i _ =>
            mul_le_mul_of_nonneg_right (hm i) (sq_nonneg (x i)))

theorem minimumRayleighQuotient3_diagonal_eq_last
    (l1 l2 l3 : ℝ) (h21 : l2 ≤ l1) (h32 : l3 ≤ l2) :
    minimumRayleighQuotient3 (Matrix.diagonal ![l1, l2, l3]) = l3 := by
  have hge : ∀ i : Fin 3, l3 ≤ ![l1, l2, l3] i := by
    intro i
    fin_cases i <;> simp <;> linarith
  have hle : minimumRayleighQuotient3 (Matrix.diagonal ![l1, l2, l3]) ≤ l3 := by
    simpa using (minimumRayleighQuotient3_diagonal_le ![l1, l2, l3] (2 : Fin 3))
  have hge' : l3 ≤ minimumRayleighQuotient3 (Matrix.diagonal ![l1, l2, l3]) :=
    minimumRayleighQuotient3_diagonal_ge ![l1, l2, l3] hge
  exact le_antisymm hle hge'

theorem inner_diag_le_eigen_bound
    {ν : Fin 3 → ℝ} (hν : Antitone ν)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.IsHermitian) :
    inner ℝ (matrixToEuclidean (Matrix.diagonal ν)) (matrixToEuclidean A) ≤
      ν 0 * A.trace + (2 * ν 0 - ν 1 - ν 2) * max (-hA.eigenvalues₀ 2) 0 := by
  rcases hermitian_orthogonal_diagonalization hA with ⟨O, hOorth, hdiag⟩
  have hOorth2 : O.transpose * O = 1 := matrixTransposeMul_orthogonal O hOorth
  let a : Fin 3 → ℝ := hA.eigenvalues₀
  let d : Matrix (Fin 3) (Fin 3) ℝ := O.transpose * Matrix.diagonal ν * O
  let X : ℝ := max (-a 2) 0
  have hdiag_expand : ∀ i : Fin 3, d i i = ∑ j : Fin 3, ν j * (O j i) ^ 2 := by
    intro i
    dsimp [d]
    simp only [Matrix.diagonal, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, sq]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  have hd_le : ∀ i : Fin 3, d i i ≤ ν 0 := by
    intro i
    calc
      d i i = ∑ j : Fin 3, ν j * (O j i) ^ 2 := hdiag_expand i
      _ ≤ ν 0 * (∑ j : Fin 3, (O j i) ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_le_sum
            intro j hj
            exact mul_le_mul_of_nonneg_right (hν (Fin.zero_le j)) (sq_nonneg (O j i))
      _ = ν 0 := by
            rw [sum_sq_column_eq_one O hOorth2 i]
            simp
  have hd_sum : (∑ i : Fin 3, d i i) = ∑ i : Fin 3, ν i := by
    calc
      (∑ i : Fin 3, d i i) = ∑ i : Fin 3, ∑ j : Fin 3, ν j * (O j i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hdiag_expand i
      _ = ∑ j : Fin 3, ν j * (∑ i : Fin 3, (O j i) ^ 2) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mul_sum]
      _ = ∑ i : Fin 3, ν i := by
            apply Finset.sum_congr rfl
            intro j hj
            have hw : (∑ i : Fin 3, (O j i) ^ 2) = 1 := by
              have hOO : (O * O.transpose) j j = 1 := by
                have h1 := congrFun (congrFun hOorth j) j
                simpa [Matrix.one_apply] using h1
              have hmain : (O * O.transpose) j j = ∑ i : Fin 3, (O j i) ^ 2 := by
                simp [Matrix.mul_apply, Matrix.transpose_apply, sq]
              rw [hmain] at hOO
              exact hOO
            rw [hw]
            ring
  have ha_ge : ∀ i : Fin 3, 0 ≤ a i + X := by
    intro i
    have hi_le : i ≤ (2 : Fin 3) := by fin_cases i <;> decide
    have ha2 : a 2 ≤ a i := hA.eigenvalues₀_antitone hi_le
    have hX : 0 ≤ a 2 + X := by
      dsimp [X]
      have hle : -a 2 ≤ max (-a 2) 0 := le_max_left _ _
      linarith
    nlinarith
  have htrace : A.trace = ∑ i : Fin 3, a i := by
    rw [Matrix.IsHermitian.trace_eq_sum_eigenvalues hA]
    simpa [a] using sum_eigenvalues_eq_sum_eigenvalues₀ A hA
  have hsum : inner ℝ (matrixToEuclidean (Matrix.diagonal ν)) (matrixToEuclidean A) ≤
      ν 0 * (∑ i : Fin 3, (a i + X)) - X * (∑ i : Fin 3, ν i) := by
    have hconj := inner_matrixToEuclidean_orthogonal_conj (Matrix.diagonal ν) A O hOorth
    rw [hconj, hdiag]
    rw [inner_matrixToEuclidean]
    have hmain : (∑ ij : Fin 3 × Fin 3, d ij.1 ij.2 * (Matrix.diagonal a) ij.1 ij.2) ≤
        ν 0 * (∑ i : Fin 3, (a i + X)) - X * (∑ i : Fin 3, ν i) := by
      calc
        (∑ ij : Fin 3 × Fin 3, d ij.1 ij.2 * (Matrix.diagonal a) ij.1 ij.2)
            = (∑ i : Fin 3, d i i * a i) := by
              rw [Fintype.sum_prod_type]
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.sum_eq_single i]
              · simp [Matrix.diagonal]
              · intro j _ hj
                simp [Matrix.diagonal, Ne.symm hj]
              · intro h
                exact absurd (Finset.mem_univ i) h
        _ = (∑ i : Fin 3, d i i * (a i + X)) - X * (∑ i : Fin 3, d i i) := by
              calc
                (∑ i : Fin 3, d i i * a i)
                    = ∑ i : Fin 3, (d i i * (a i + X) - d i i * X) := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      ring
                _ = (∑ i : Fin 3, d i i * (a i + X)) - X * (∑ i : Fin 3, d i i) := by
                      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
                      apply Finset.sum_congr rfl
                      intro i hi
                      ring_nf
        _ ≤ ν 0 * (∑ i : Fin 3, (a i + X)) - X * (∑ i : Fin 3, ν i) := by
              have h1 : (∑ i : Fin 3, d i i * (a i + X)) ≤
                  ν 0 * (∑ i : Fin 3, (a i + X)) := by
                rw [Finset.mul_sum]
                apply Finset.sum_le_sum
                intro i hi
                exact mul_le_mul_of_nonneg_right (hd_le i) (ha_ge i)
              rw [hd_sum]
              linarith
    simpa [d, a, hmain]
  have hX0 : 0 ≤ X := le_max_right _ _
  have hcalc : ν 0 * (∑ i : Fin 3, (a i + X)) - X * (∑ i : Fin 3, ν i) =
      ν 0 * A.trace + (2 * ν 0 - ν 1 - ν 2) * X := by
    rw [htrace]
    simp [Finset.sum_add_distrib, Fin.sum_univ_three]
    ring
  simpa [X, a, hcalc] using hsum

theorem inner_diag_diag (ν l : Fin 3 → ℝ) :
    inner ℝ (matrixToEuclidean (Matrix.diagonal ν)) (matrixToEuclidean (Matrix.diagonal l)) =
      ∑ i : Fin 3, ν i * l i := by
  rw [inner_matrixToEuclidean]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · simp [matrixToEuclidean, Matrix.diagonal]
  · intro j _ hj
    simp [Matrix.diagonal, Ne.symm hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem euclideanMatrixSymmetrization_diag_eigenvalues₀ (ν : Fin 3 → ℝ) (hν : Antitone ν) :
    (euclideanMatrixSymmetrization_isHermitian
      (matrixToEuclidean (Matrix.diagonal ν))).eigenvalues₀ = ν := by
  have hsymm : euclideanMatrixSymmetrization
      (matrixToEuclidean (Matrix.diagonal ν)) = Matrix.diagonal ν := by
    ext i j
    dsimp [euclideanMatrixSymmetrization, euclideanToMatrix]
    by_cases h : i = j
    · simp [h, matrixToEuclidean, Matrix.diagonal]
      ring
    · simp [h, matrixToEuclidean, Matrix.diagonal, Ne.symm h]
  have hchar : (euclideanMatrixSymmetrization
      (matrixToEuclidean (Matrix.diagonal ν))).charpoly =
      (Matrix.diagonal ν).charpoly := by
    rw [hsymm]
  have heig' : (euclideanMatrixSymmetrization_isHermitian
      (matrixToEuclidean (Matrix.diagonal ν))).eigenvalues₀ =
      (Matrix.isHermitian_diagonal ν).eigenvalues₀ :=
    eigenvalues₀_eq_of_charpoly_eq_real
      (euclideanMatrixSymmetrization_isHermitian (matrixToEuclidean (Matrix.diagonal ν)))
      (Matrix.isHermitian_diagonal ν) hchar
  have heig : (Matrix.isHermitian_diagonal ν).eigenvalues₀ = ν :=
    diagonal_eigenvalues₀_eq_of_antitone ν hν
  exact heig'.trans heig

end DifferentialGeometry.Analysis.Convex
