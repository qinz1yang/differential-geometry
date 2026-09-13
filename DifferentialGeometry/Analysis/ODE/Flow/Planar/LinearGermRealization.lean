import DifferentialGeometry.Analysis.ODE.Flow.Planar.CompactLinearGerm
import DifferentialGeometry.Analysis.ODE.Flow.Planar.IdentityTangentGerm
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

noncomputable section
open Set Metric Filter Topology
open scoped ContDiff Manifold Matrix

namespace DifferentialGeometry.Analysis

variable {n : ℕ}

def planeFlipM (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun k => if k = i ∨ k = j then (-1 : ℝ) else 1)

theorem planeFlipM_eq_one_sub_two_smul_planeProjM {i j : Fin n} (hij : i ≠ j) :
    planeFlipM i j = 1 - (2 : ℝ) • planeProjM i j := by
  ext a b
  simp only [planeFlipM, Matrix.diagonal_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    planeProjM, Matrix.add_apply, Matrix.single_apply]
  split_ifs <;> simp_all <;> norm_num <;> aesop

theorem realizesGerm_matEnd_planeFlipM {i j : Fin n} (hij : i ≠ j) :
    RealizesGerm (fun x => matEnd (planeFlipM i j) x) (Metric.closedBall 0 2) := by
  refine RealizesGerm.congr ?_ (realizesGerm_matEnd_planeFlip hij)
  funext x
  rw [planeFlipM_eq_one_sub_two_smul_planeProjM hij, matEnd_sub, matEnd_one, matEnd_smul]
  simp only [sub_apply, add_apply, one_apply_eq_self, two_smul]

def signPairs {α : Type*} : List α → List (α × α)
  | [] => []
  | [_] => []
  | a :: b :: l => (a, b) :: signPairs l

theorem signPairs_prod_planeFlipM : ∀ (l : List (Fin n)), l.Nodup → Even l.length →
    ((signPairs l).map (fun p : Fin n × Fin n => planeFlipM p.1 p.2)).prod
      = Matrix.diagonal (fun k => if k ∈ l then (-1 : ℝ) else 1)
  | [], _, _ => by simp [signPairs]
  | [_], _, hev => by
      exfalso
      exact Nat.not_even_one hev
  | a :: b :: t, hnd, hev => by
      have hnd' : t.Nodup := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2
      have hndb : (b :: t).Nodup := (List.nodup_cons.mp hnd).2
      have ha : a ∉ t := fun h => (List.nodup_cons.mp hnd).1 (List.mem_cons_of_mem b h)
      have hb : b ∉ t := (List.nodup_cons.mp hndb).1
      have hab : a ≠ b := fun h => (List.nodup_cons.mp hnd).1 (by simp [h])
      have hev' : Even t.length := by
        obtain ⟨k, hk⟩ := hev
        exact ⟨k - 1, by simp only [List.length_cons] at hk; omega⟩
      rw [signPairs, List.map_cons, List.prod_cons,
        signPairs_prod_planeFlipM t hnd' hev', planeFlipM, Matrix.diagonal_mul_diagonal]
      congr 1
      funext k
      by_cases h1 : k = a <;> by_cases h2 : k = b <;> by_cases h3 : k ∈ t <;>
        simp_all [List.mem_cons]

theorem signPairs_fst_ne_snd {α : Type*} : ∀ (l : List α), l.Nodup → ∀ p ∈ signPairs l, p.1 ≠ p.2
  | [], _, _, hp => by simp [signPairs] at hp
  | [_], _, _, hp => by simp [signPairs] at hp
  | a :: b :: t, hnd, p, hp => by
      have hndb : (b :: t).Nodup := (List.nodup_cons.mp hnd).2
      have hab : a ≠ b := fun h => (List.nodup_cons.mp hnd).1 (by simp [h])
      simp only [signPairs, List.mem_cons] at hp
      rcases hp with hp | hp
      · rw [hp]; exact hab
      · exact signPairs_fst_ne_snd t (List.nodup_cons.mp hndb).2 p hp

theorem abs_mul_ite_neg (x : ℝ) : |x| * (if x < 0 then (-1 : ℝ) else 1) = x := by
  by_cases h : x < 0
  · rw [if_pos h, abs_of_neg h]
    ring
  · rw [if_neg h, abs_of_nonneg (le_of_not_gt h), mul_one]

theorem even_card_of_prod_neg_pos {α : Type*} (s : Finset α) (D : α → ℝ)
    (h : 0 < ∏ i ∈ s, D i) (hs : ∀ i ∈ s, D i < 0) : Even s.card := by
  have hg : ∀ i ∈ s, 0 < -D i := fun i hi => neg_pos.mpr (hs i hi)
  have hG : 0 < ∏ i ∈ s, -D i := Finset.prod_pos hg
  have hsplit : ∏ i ∈ s, D i = (-1 : ℝ) ^ s.card * ∏ i ∈ s, -D i := by
    simpa using Finset.prod_neg (s := s) (fun i => -D i)
  rcases Nat.even_or_odd s.card with he | ho
  · exact he
  · exfalso
    rw [hsplit, ho.neg_one_pow] at h
    nlinarith

theorem realizesGerm_matEnd_of_det_pos (M : Matrix (Fin n) (Fin n) ℝ) (hM : 0 < M.det) :
    RealizesGerm (fun x => matEnd M x) (Metric.closedBall 0 2) := by
  obtain ⟨L, L', D, hdec⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M
  have hdet : M.det = ∏ i, D i := by
    rw [hdec, Matrix.det_mul, Matrix.det_mul, Matrix.TransvectionStruct.det_toMatrix_prod,
      Matrix.TransvectionStruct.det_toMatrix_prod, Matrix.det_diagonal, mul_one, one_mul]
  have hprod : 0 < ∏ i, D i := by rw [← hdet]; exact hM
  have hne : ∀ i, D i ≠ 0 := by
    intro i hi
    have hz : ∏ j, D j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [hz] at hprod
    exact lt_irrefl 0 hprod
  let neg : Finset (Fin n) := Finset.univ.filter (fun i => D i < 0)
  have hcompl : (∏ i ∈ neg, D i) * ∏ i ∈ negᶜ, D i = ∏ i, D i :=
    Finset.prod_mul_prod_compl neg D
  have hpos : 0 < ∏ i ∈ negᶜ, D i := by
    refine Finset.prod_pos fun i hi => ?_
    have hi' : ¬ D i < 0 := fun hlt =>
      (Finset.mem_compl.mp hi) (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hlt⟩)
    exact lt_of_le_of_ne (le_of_not_gt hi') (Ne.symm (hne i))
  have hnegpos : 0 < ∏ i ∈ neg, D i := by nlinarith [hcompl, hpos]
  have hnegeven : Even neg.card :=
    even_card_of_prod_neg_pos neg D hnegpos fun i hi => (Finset.mem_filter.mp hi).2
  have hnegEven : Even neg.toList.length := by
    rw [Finset.length_toList]; exact hnegeven
  let lA : List (Matrix (Fin n) (Fin n) ℝ) := L.map Matrix.TransvectionStruct.toMatrix
  let B : List (Matrix (Fin n) (Fin n) ℝ) :=
    (List.finRange n).map (fun i => coordScaleM i (|D i|))
  let C : List (Matrix (Fin n) (Fin n) ℝ) :=
    (signPairs neg.toList).map (fun p => planeFlipM p.1 p.2)
  let lD : List (Matrix (Fin n) (Fin n) ℝ) := L'.map Matrix.TransvectionStruct.toMatrix
  let l : List (Matrix (Fin n) (Fin n) ℝ) := ((lA ++ B) ++ C) ++ lD
  have hB : B.prod = Matrix.diagonal (fun i => |D i|) := prod_coordScaleM_finRange (fun i => |D i|)
  have hC : C.prod = Matrix.diagonal (fun k => if D k < 0 then (-1 : ℝ) else 1) := by
    have h1 := signPairs_prod_planeFlipM neg.toList (Finset.nodup_toList neg) hnegEven
    have h2 : (fun k : Fin n => if k ∈ neg.toList then (-1 : ℝ) else 1)
        = fun k => if D k < 0 then (-1 : ℝ) else 1 := by
      funext k
      simp only [neg, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← h2]
    exact h1
  have hdiag : Matrix.diagonal (fun i => |D i|) *
      Matrix.diagonal (fun k => if D k < 0 then (-1 : ℝ) else 1) = Matrix.diagonal D := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    exact abs_mul_ite_neg (D k)
  have hl : l.prod = ((L.map Matrix.TransvectionStruct.toMatrix).prod *
      Matrix.diagonal (fun i => |D i|)) * Matrix.diagonal (fun k => if D k < 0 then (-1 : ℝ) else 1) *
        (L'.map Matrix.TransvectionStruct.toMatrix).prod := by
    simp only [l, lA, lD, List.prod_append, hB, hC]
  have hlp : l.prod = M := by
    rw [hl, Matrix.mul_assoc (L.map Matrix.TransvectionStruct.toMatrix).prod
        (Matrix.diagonal (fun i => |D i|))
        (Matrix.diagonal (fun k => if D k < 0 then (-1 : ℝ) else 1)), hdiag, ← hdec]
  have hmem : ∀ m ∈ l, RealizesGerm (fun x => matEnd m x) (Metric.closedBall 0 2) := by
    intro m hm
    have hm' := hm
    simp only [l, List.mem_append] at hm'
    rcases hm' with ((hmA | hmB) | hmC) | hmD
    · obtain ⟨t, -, rfl⟩ := List.mem_map.mp hmA
      exact realizesGerm_matEnd_transvection t.hij t.c
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hmB
      exact realizesGerm_matEnd_coordScale i (|D i|) (abs_pos.mpr (hne i))
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hmC
      exact realizesGerm_matEnd_planeFlipM
        (signPairs_fst_ne_snd neg.toList (Finset.nodup_toList neg) p hp)
    · obtain ⟨t, -, rfl⟩ := List.mem_map.mp hmD
      exact realizesGerm_matEnd_transvection t.hij t.c
  refine RealizesGerm.congr ?_ (realizesGerm_matEnd_prod l (isCompact_closedBall _ _) hmem)
  funext x
  rw [hlp]

theorem matEnd_eq_toEuclideanCLM (M : Matrix (Fin n) (Fin n) ℝ) :
    matEnd M = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [matEnd_apply]
  exact (Matrix.toEuclideanCLM_toLp M (WithLp.ofLp x)).symm

theorem det_toEuclideanCLM_symm (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm A).det = A.det := by
  rw [ContinuousLinearMap.det]
  have h : (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm A
      = LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin n) ℝ) A.toLinearMap := rfl
  rw [h, LinearMap.toMatrixOrthonormal_apply]
  exact LinearMap.det_toMatrix _ _

theorem exists_realizesGerm_of_identity_tangent {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {f : E → E} {U : Set E}
    (hU : IsOpen U) (h0U : (0 : E) ∈ U) (hf : ContDiffOn ℝ ∞ f U) (hf0 : f 0 = 0)
    (hdf0 : HasFDerivAt f (1 : E →L[ℝ] E) 0) :
    ∃ K : Set E, K ⊆ U ∧ RealizesGerm f K := by
  obtain ⟨D, hD, hDi, hD0, hDg, -, K, hK, hKU, hfix⟩ :=
    exists_compact_isotopy_realizing_identity_tangent_germ hU h0U hf hf0 hdf0
  exact ⟨K, hKU, hf0, hK, D, hD, hDi, hD0, hDg, hfix⟩

theorem exists_realizesGerm_of_contDiffOn_det_pos {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (h0U : (0 : EuclideanSpace ℝ (Fin n)) ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (hf0 : f 0 = 0)
    (hdet : 0 < (fderiv ℝ f 0).det) :
    ∃ K : Set (EuclideanSpace ℝ (Fin n)), K ⊆ U ∧
      RealizesGerm f (Metric.closedBall 0 2 ∪ K) := by
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := fderiv ℝ f 0
  have hA : A = fderiv ℝ f 0 := rfl
  let M : Matrix (Fin n) (Fin n) ℝ := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm A
  have hMA : matEnd M = A := by
    rw [matEnd_eq_toEuclideanCLM]
    exact StarAlgEquiv.apply_symm_apply _ A
  have hdetA : 0 < A.det := by rw [hA]; exact hdet
  have hMdet : 0 < M.det := by
    have h : M.det = A.det := det_toEuclideanCLM_symm A
    rw [h]
    exact hdetA
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr (ne_of_gt hMdet)
  have hMinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hunit
  have hMinv' : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hunit
  have hmul : matEnd M * matEnd M⁻¹ = 1 := by rw [← matEnd_mul, hMinv, matEnd_one]
  have hfix : ∀ x, matEnd M (matEnd M⁻¹ (f x)) = f x := by
    intro x
    rw [← mul_apply_eq_comp, hmul, one_apply_eq_self]
  let r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => matEnd M⁻¹ (f x)
  have hr : ContDiffOn ℝ ∞ r U := (matEnd M⁻¹).contDiff.comp_contDiffOn hf
  have hr0 : r 0 = 0 := by simp only [r, hf0, map_zero]
  have hrd : HasFDerivAt r (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) 0 := by
    have hfAt : HasFDerivAt f A 0 := by
      have hd : DifferentiableAt ℝ f 0 := (hf.contDiffAt (hU.mem_nhds h0U)).differentiableAt (by simp)
      have := hd.hasFDerivAt
      rw [← hA] at this
      exact this
    have hcomp : HasFDerivAt r ((matEnd M⁻¹).comp A) 0 :=
      (ContinuousLinearMap.hasFDerivAt (matEnd M⁻¹)).comp 0 hfAt
    have hderiv : ((matEnd M⁻¹).comp A) = 1 := by
      refine ContinuousLinearMap.ext fun x => ?_
      rw [ContinuousLinearMap.comp_apply, ← hMA, ← mul_apply_eq_comp, ← matEnd_mul, hMinv',
        matEnd_one, one_apply_eq_self]
    rw [← hderiv]
    exact hcomp
  obtain ⟨K, hKU, hK⟩ := exists_realizesGerm_of_identity_tangent hU h0U hr hr0 hrd
  refine ⟨K, hKU, RealizesGerm.congr ?_ ((realizesGerm_matEnd_of_det_pos M hMdet).comp hK)⟩
  funext x
  exact hfix x

theorem realizesGerm_scale {n : ℕ} (s : ℝ) (hs : 0 < s) :
    RealizesGerm (fun x : EuclideanSpace ℝ (Fin n) => s • x) (Metric.closedBall 0 2) := by
  refine RealizesGerm.congr ?_ (realizesGerm_matEnd_diagonal_pos (fun _ : Fin n => s) (fun _ => hs))
  funext x
  rw [matEnd_apply]
  have h : (Matrix.diagonal (fun _ : Fin n => s)) *ᵥ WithLp.ofLp x
      = (s • WithLp.ofLp x : Fin n → ℝ) := by
    funext i
    rw [Matrix.mulVec_diagonal]
    rfl
  rw [h]
  apply WithLp.ofLp_injective
  rfl

end DifferentialGeometry.Analysis
