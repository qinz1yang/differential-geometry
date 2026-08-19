import Mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DifferentialGeometry.Analysis.Convex

open scoped BigOperators Matrix

def sectionalRayleigh3 (A : Matrix (Fin 3) (Fin 3) Real)
    (x : EuclideanSpace Real (Fin 3)) : Real :=
  ∑ i : Fin 3, x i * (∑ j : Fin 3, A i j * x j)

theorem sectionalRayleigh3_eq_inner (A : Matrix (Fin 3) (Fin 3) Real)
    (x : EuclideanSpace Real (Fin 3)) :
    sectionalRayleigh3 A x = inner Real (A.toEuclideanLin x) x := by
  unfold sectionalRayleigh3
  have hdot :
      ∑ i : Fin 3, x i * (∑ j : Fin 3, A i j * x j) =
        inner Real (A.toEuclideanLin x) x := by
    simpa [WithLp.ofLp_toLp, dotProduct_comm, dotProduct, Matrix.mulVec] using
      (EuclideanSpace.inner_eq_star_dotProduct (𝕜 := Real)
        (x := WithLp.toLp 2 ((Matrix.toEuclideanLin A) x))
        (y := x)).symm
  exact hdot


theorem sectionalRayleigh3_add_smul (a b : ℝ) (A B : Matrix (Fin 3) (Fin 3) Real)
    (x : EuclideanSpace Real (Fin 3)) :
    sectionalRayleigh3 (a • A + b • B) x =
      a * sectionalRayleigh3 A x + b * sectionalRayleigh3 B x := by
  unfold sectionalRayleigh3
  simp [Finset.mul_sum, Finset.sum_add_distrib, mul_add, add_mul, mul_assoc, mul_left_comm]


theorem matrix_one_smul_mulVec_shift_dot
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


theorem continuous_sectionalRayleigh3 :
    Continuous (fun p : Matrix (Fin 3) (Fin 3) Real × EuclideanSpace Real (Fin 3) =>
      sectionalRayleigh3 p.1 p.2) := by
  unfold sectionalRayleigh3
  fun_prop

noncomputable def sectionalRayleighMin3 (A : Matrix (Fin 3) (Fin 3) Real) : Real :=
  sInf (sectionalRayleigh3 A '' Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1)

theorem continuous_sectionalRayleighMin3 :
    Continuous sectionalRayleighMin3 := by
  unfold sectionalRayleighMin3
  refine IsCompact.continuous_sInf (K := Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (isCompact_sphere _ _) ?_
  simpa [Function.uncurry] using continuous_sectionalRayleigh3

theorem continuous_sectionalRayleighMin3_comp
    {α : Type*} [TopologicalSpace α]
    {A : α → Matrix (Fin 3) (Fin 3) Real} (hA : Continuous A) :
    Continuous (fun x : α => sectionalRayleighMin3 (A x)) :=
  continuous_sectionalRayleighMin3.comp hA

theorem concave_sectionalRayleighMin3 :
    ConcaveOn ℝ Set.univ sectionalRayleighMin3 := by
  rw [concaveOn_iff_forall_pos]
  constructor
  · exact convex_univ
  · intro A hA B hB a b ha hb hab
    let SA : Set ℝ := sectionalRayleigh3 A '' Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1
    let SB : Set ℝ := sectionalRayleigh3 B '' Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1
    let SC : Set ℝ := sectionalRayleigh3 (a • A + b • B) '' Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1
    have hSphere : (WithLp.toLp 2 (fun i : Fin 3 => if i = 0 then (1 : ℝ) else 0)) ∈
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 := by
      rw [mem_sphere_zero_iff_norm]
      norm_num [PiLp.norm_eq_of_L2]
    have hSA_nonempty : SA.Nonempty := ⟨sectionalRayleigh3 A (WithLp.toLp 2 (fun i : Fin 3 => if i = 0 then (1 : ℝ) else 0)), ⟨_, hSphere, rfl⟩⟩
    have hSB_nonempty : SB.Nonempty := ⟨sectionalRayleigh3 B (WithLp.toLp 2 (fun i : Fin 3 => if i = 0 then (1 : ℝ) else 0)), ⟨_, hSphere, rfl⟩⟩
    have hSC_nonempty : SC.Nonempty := ⟨sectionalRayleigh3 (a • A + b • B) (WithLp.toLp 2 (fun i : Fin 3 => if i = 0 then (1 : ℝ) else 0)), ⟨_, hSphere, rfl⟩⟩
    have hcontA : ContinuousOn (sectionalRayleigh3 A) (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) := by
      have hcont : Continuous (fun x : EuclideanSpace Real (Fin 3) => sectionalRayleigh3 A x) :=
        continuous_sectionalRayleigh3.comp (continuous_const.prodMk continuous_id)
      exact hcont.continuousOn
    have hcontB : ContinuousOn (sectionalRayleigh3 B) (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) := by
      have hcont : Continuous (fun x : EuclideanSpace Real (Fin 3) => sectionalRayleigh3 B x) :=
        continuous_sectionalRayleigh3.comp (continuous_const.prodMk continuous_id)
      exact hcont.continuousOn
    have hcontC : ContinuousOn (sectionalRayleigh3 (a • A + b • B)) (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) := by
      have hcont : Continuous (fun x : EuclideanSpace Real (Fin 3) => sectionalRayleigh3 (a • A + b • B) x) :=
        continuous_sectionalRayleigh3.comp (continuous_const.prodMk continuous_id)
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
      have hAinf : sInf SA ≤ sectionalRayleigh3 A x := csInf_le hSA_bdd ⟨x, hx, rfl⟩
      have hBinf : sInf SB ≤ sectionalRayleigh3 B x := csInf_le hSB_bdd ⟨x, hx, rfl⟩
      have hmulA : a * sInf SA ≤ a * sectionalRayleigh3 A x :=
        mul_le_mul_of_nonneg_left hAinf ha.le
      have hmulB : b * sInf SB ≤ b * sectionalRayleigh3 B x :=
        mul_le_mul_of_nonneg_left hBinf hb.le
      have hadd := add_le_add hmulA hmulB
      have hlin := sectionalRayleigh3_add_smul a b A B x
      simpa [hlin] using hadd
    have hle : a * sInf SA + b * sInf SB ≤ sInf SC := le_csInf hSC_nonempty hlower
    change sInf SC ≥ a * sInf SA + b * sInf SB
    exact hle


theorem convex_sectionalRayleighPinchHeight3 :
    ConvexOn ℝ Set.univ (fun A : Matrix (Fin 3) (Fin 3) Real =>
      max (-sectionalRayleighMin3 A) 0) := by
  have hneg : ConvexOn ℝ Set.univ (fun A : Matrix (Fin 3) (Fin 3) Real =>
      -sectionalRayleighMin3 A) := concave_sectionalRayleighMin3.neg
  have hzero : ConvexOn ℝ Set.univ (fun _ : Matrix (Fin 3) (Fin 3) Real => (0 : ℝ)) :=
    convexOn_const (0 : ℝ) convex_univ
  change ConvexOn ℝ Set.univ (fun A : Matrix (Fin 3) (Fin 3) Real =>
      (-sectionalRayleighMin3 A) ⊔ 0)
  exact hneg.sup hzero

theorem sectionalRayleigh3_eq_dotProduct
    (A : Matrix (Fin 3) (Fin 3) Real) (x : Fin 3 → Real) :
    sectionalRayleigh3 A (WithLp.toLp 2 x) = star x ⬝ᵥ A.mulVec x := by
  rw [sectionalRayleigh3_eq_inner]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [Matrix.mulVec, dotProduct]

theorem sectionalRayleigh3_min_eigenvalue_le
    {A : Matrix (Fin 3) (Fin 3) Real} (hA : A.IsHermitian)
    (x : EuclideanSpace Real (Fin 3)) :
    hA.eigenvalues₀ 2 * (∑ i : Fin 3, x i ^ 2) ≤ sectionalRayleigh3 A x := by
  let T : EuclideanSpace Real (Fin 3) →ₗ[Real] EuclideanSpace Real (Fin 3) :=
    A.toEuclideanLin
  let hT : T.IsSymmetric := by
    dsimp [T]
    exact (Matrix.isHermitian_iff_isSymmetric (A := A)).1 hA
  let hn : Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3 := finrank_euclideanSpace
  let b : OrthonormalBasis (Fin 3) Real (EuclideanSpace Real (Fin 3)) :=
    hT.eigenvectorBasis hn
  have hquad :
      sectionalRayleigh3 A x = inner Real (T x) x := by
    dsimp [T]
    exact sectionalRayleigh3_eq_inner A x
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
      hT.eigenvalues hn 2 * ∑ i : Fin 3, x i ^ 2 ≤ sectionalRayleigh3 A x := by
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
        star x ⬝ᵥ A.mulVec x = sectionalRayleigh3 A (WithLp.toLp 2 x) :=
          (sectionalRayleigh3_eq_dotProduct A x).symm
        _ = inner Real (T bvec) bvec := by
          rw [hx]
          dsimp [T]
          exact sectionalRayleigh3_eq_inner A bvec
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
      rw [← sectionalRayleigh3_eq_dotProduct A x]
      have hquad := sectionalRayleigh3_min_eigenvalue_le hA (WithLp.toLp 2 x)
      have hnormeq : ∑ i : Fin 3, x i ^ 2 =
          ∑ i : Fin 3, (WithLp.toLp 2 x : EuclideanSpace Real (Fin 3)) i ^ 2 := rfl
      simpa [hnormeq] using hquad
    have hsumnonneg : 0 ≤ ∑ i : Fin 3, x i ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
    nlinarith [mul_nonneg hnonneg hsumnonneg, hlow]


theorem sectionalRayleighMin3_eq_eigenvalue_min
    {A : Matrix (Fin 3) (Fin 3) Real} (hA : A.IsHermitian) :
    sectionalRayleighMin3 A = hA.eigenvalues₀ 2 := by
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
  have hcont : Continuous (fun x : EuclideanSpace Real (Fin 3) => sectionalRayleigh3 A x) := by
    simpa using continuous_sectionalRayleigh3.comp
      ((continuous_const (y := A)).prodMk
        (continuous_id (X := EuclideanSpace Real (Fin 3))))
  have hbdd : BddBelow (sectionalRayleigh3 A ''
      Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) := by
    exact (isCompact_sphere (0 : EuclideanSpace Real (Fin 3)) 1).bddBelow_image
      hcont.continuousOn
  have heval : sectionalRayleigh3 A bvec = hT.eigenvalues hn 2 := by
    have hquad : sectionalRayleigh3 A bvec = inner Real (T bvec) bvec := by
      dsimp [T]
      exact sectionalRayleigh3_eq_inner A bvec
    rw [hquad, real_inner_comm]
    have heig := hT.apply_eigenvectorBasis hn 2
    have hnorm : ‖bvec‖ = 1 := by
      dsimp [bvec]
      exact b.orthonormal.1 2
    simpa [T, bvec, hnorm] using
      (inner_product_apply_eigenvector (T := T) (v := bvec) heig)
  have hminord : hT.eigenvalues hn 2 = hA.eigenvalues₀ 2 := rfl
  have him : sectionalRayleigh3 A bvec ∈
      sectionalRayleigh3 A '' Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 := by
    exact Set.mem_image_of_mem (sectionalRayleigh3 A) hsphere
  apply le_antisymm
  · unfold sectionalRayleighMin3
    have hval : hA.eigenvalues₀ 2 = sectionalRayleigh3 A bvec := by
      exact hminord.symm.trans heval.symm
    exact csInf_le hbdd (hval ▸ him)
  · unfold sectionalRayleighMin3
    apply le_csInf
    · exact ⟨sectionalRayleigh3 A bvec, him⟩
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
      simpa [hsumsq, hminord] using sectionalRayleigh3_min_eigenvalue_le hA x

theorem trace_ge_three_mul_sectionalRayleighMin
    {A : Matrix (Fin 3) (Fin 3) Real} (hA : A.IsHermitian) :
    3 * sectionalRayleighMin3 A ≤ A.trace := by
  have hmin : sectionalRayleighMin3 A = hA.eigenvalues₀ 2 :=
    sectionalRayleighMin3_eq_eigenvalue_min hA
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
    have hquad := sectionalRayleigh3_min_eigenvalue_le hA e
    have hmain : hA.eigenvalues₀ 2 ≤ sectionalRayleigh3 A e := by
      simpa [hsum] using hquad
    have hsec : sectionalRayleigh3 A e = A i i := by
      unfold sectionalRayleigh3
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

theorem neg_three_mul_sectionalRayleighPinch_le_trace
    {A : Matrix (Fin 3) (Fin 3) Real} (hA : A.IsHermitian) :
    -3 * max (-sectionalRayleighMin3 A) 0 ≤ A.trace := by
  have htrace := trace_ge_three_mul_sectionalRayleighMin hA
  by_cases h : sectionalRayleighMin3 A < 0
  · have hmax : max (-sectionalRayleighMin3 A) 0 = -sectionalRayleighMin3 A :=
      max_eq_left (neg_nonneg.mpr h.le)
    rw [hmax]
    linarith
  · have hmax : max (-sectionalRayleighMin3 A) 0 = 0 :=
      max_eq_right (neg_nonpos.mpr (not_lt.mp h))
    rw [hmax]
    have hnonneg : 0 ≤ 3 * sectionalRayleighMin3 A := by nlinarith
    linarith

theorem sectionalRayleighMin3_zero : sectionalRayleighMin3 (0 : Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
  unfold sectionalRayleighMin3
  have hzero : sectionalRayleigh3 (0 : Matrix (Fin 3) (Fin 3) ℝ) = fun _ => 0 := by
    funext x
    simp [sectionalRayleigh3]
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

theorem diagonal_eigenvalues_tuple {A : Matrix (Fin 3) (Fin 3) Real} (hA : A.IsHermitian) :
    Matrix.diagonal hA.eigenvalues₀ =
      Matrix.diagonal ![hA.eigenvalues₀ 0, hA.eigenvalues₀ 1, hA.eigenvalues₀ 2] := by
  have hfun : hA.eigenvalues₀ = fun i : Fin 3 =>
      ![hA.eigenvalues₀ 0, hA.eigenvalues₀ 1, hA.eigenvalues₀ 2] i := by
    ext i
    fin_cases i <;> rfl
  rw [hfun]
  rfl

end DifferentialGeometry.Analysis.Convex
