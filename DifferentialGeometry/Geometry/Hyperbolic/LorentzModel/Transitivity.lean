/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.Defs

open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.HyperbolicTransitive

open DifferentialGeometry.Hyperbolic
open DifferentialGeometry.Hyperbolic.HUpper
open DifferentialGeometry.HyperbolicAction
open DifferentialGeometry.HyperbolicFaithful
open DifferentialGeometry.HyperbolicBoundary
open Matrix

variable {n : ℕ}

noncomputable def partialSd (x : HUpper n) (k : ℕ) : ℝ :=
  ∑ j ∈ (Finset.univ.filter fun j : Fin n => (j : ℕ) < k), (x.val (Sum.inl j)) ^ 2

theorem partialSd_succ (x : HUpper n) {k : ℕ} (hk : k < n) :
    partialSd x (k + 1) = partialSd x k + (x.val (Sum.inl ⟨k, hk⟩)) ^ 2 := by
  have hset : (Finset.univ.filter fun j : Fin n => (j : ℕ) < k + 1)
      = insert ⟨k, hk⟩ (Finset.univ.filter fun j : Fin n => (j : ℕ) < k) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · intro hj
      rcases hj with h | h
      · rw [h]
        exact Nat.lt_succ_self k
      · omega
  unfold partialSd
  rw [hset, Finset.sum_insert (by simp)]
  exact add_comm _ _

theorem partialSd_zero (x : HUpper n) : partialSd x 0 = 0 := by
  unfold partialSd
  rw [Finset.filter_eq_empty_iff.mpr (fun j _ => Nat.not_lt_zero _), Finset.sum_empty]

theorem partialSd_self (x : HUpper n) : partialSd x n = sdot x.val x.val := by
  unfold partialSd
  rw [Finset.filter_true_of_mem (fun j _ => j.isLt)]
  show (∑ j : Fin n, (x.val (Sum.inl j)) ^ 2) = sdot x.val x.val
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_two]

theorem boostMat_mulVec_apply (k : Fin n) (c s : ℝ) (v : LorVec n) (a : Fin n ⊕ Fin 1) :
    (DifferentialGeometry.ProjectiveOrthogonalGroup.Center.boostMat k c s *ᵥ v) a
      = (Sum.elim (fun j => if j = k then c else 1) (fun _ => c) a) * v a
        + s * ((if a = Sum.inl k then v (Sum.inr 0) else 0)
            + (if a = Sum.inr 0 then v (Sum.inl k) else 0)) := by
  rw [DifferentialGeometry.ProjectiveOrthogonalGroup.Center.boostMat, Matrix.add_mulVec, Pi.add_apply, Matrix.smul_mulVec, Pi.smul_apply,
    DifferentialGeometry.ProjectiveOrthogonalGroup.Center.boostD, Matrix.mulVec_diagonal, DifferentialGeometry.ProjectiveOrthogonalGroup.Center.boostS, Matrix.add_mulVec, Pi.add_apply,
    Matrix.single_mulVec, Matrix.single_mulVec, Function.update_apply, Function.update_apply]
  simp only [Pi.zero_apply, one_mul, smul_eq_mul]

theorem boostMat_mulVec_inl_ne (k : Fin n) (c s : ℝ) (v : LorVec n) {j : Fin n}
    (hj : j ≠ k) :
    (DifferentialGeometry.ProjectiveOrthogonalGroup.Center.boostMat k c s *ᵥ v) (Sum.inl j) = v (Sum.inl j) := by
  rw [boostMat_mulVec_apply]
  simp [Sum.elim_inl, hj]

theorem boostMat_mulVec_inl_self (k : Fin n) (c s : ℝ) (v : LorVec n) :
    (DifferentialGeometry.ProjectiveOrthogonalGroup.Center.boostMat k c s *ᵥ v) (Sum.inl k)
      = c * v (Sum.inl k) + s * v (Sum.inr 0) := by
  rw [boostMat_mulVec_apply]
  simp [Sum.elim_inl]

theorem boostMat_mulVec_inr (k : Fin n) (c s : ℝ) (v : LorVec n) :
    (DifferentialGeometry.ProjectiveOrthogonalGroup.Center.boostMat k c s *ᵥ v) (Sum.inr 0)
      = s * v (Sum.inl k) + c * v (Sum.inr 0) := by
  rw [boostMat_mulVec_apply]
  simp [Sum.elim_inr]
  ring

theorem exists_unitary_partial (x : HUpper n) (k : ℕ) :
    k ≤ n →
    ∃ A : LorGrp n, ∃ T : ℝ,
      (∀ j : Fin n, (j : ℕ) < k → (matOf A *ᵥ eTime) (Sum.inl j) = x.val (Sum.inl j))
      ∧ (∀ j : Fin n, k ≤ (j : ℕ) → (matOf A *ᵥ eTime) (Sum.inl j) = 0)
      ∧ ((matOf A *ᵥ eTime) (Sum.inr 0) = T)
      ∧ 1 ≤ T
      ∧ T ^ 2 = 1 + partialSd x k := by
  induction k with
  | zero =>
    intro _
    refine ⟨1, 1, ?_, ?_, ?_, le_rfl, ?_⟩
    · intro j hj
      exact absurd hj (Nat.not_lt_zero _)
    · intro j _
      rw [matOf_one, Matrix.one_mulVec]
      exact eTime_apply_inl j
    · rw [matOf_one, Matrix.one_mulVec]
      exact eTime_apply_inr
    · rw [partialSd_zero]
      norm_num
  | succ k ih =>
    intro hk
    have hk' : k ≤ n := Nat.le_of_succ_le hk
    obtain ⟨A, T, hlt, hge, htime, hT1, hT2⟩ := ih hk'
    set kk : Fin n := ⟨k, Nat.lt_of_succ_le hk⟩ with hkk
    have hkkval : (kk : ℕ) = k := rfl
    set xk : ℝ := x.val (Sum.inl kk) with hxk
    set v : LorVec n := matOf A *ᵥ eTime with hvdef
    set T' : ℝ := Real.sqrt (T ^ 2 + xk ^ 2) with hT'def
    set s : ℝ := xk / T with hsdef
    set c : ℝ := T' / T with hcdef
    have hTpos : 0 < T := zero_lt_one.trans_le hT1
    have hT'2 : T' ^ 2 = T ^ 2 + xk ^ 2 := Real.sq_sqrt (by positivity)
    have hcs : c * c - s * s = 1 := by
      rw [hcdef, hsdef]
      have h1 : (T' / T) * (T' / T) - (xk / T) * (xk / T) = (T' ^ 2 - xk ^ 2) / (T ^ 2) := by
        field_simp
      rw [h1, hT'2]
      have h2 : T ^ 2 + xk ^ 2 - xk ^ 2 = T ^ 2 := by ring
      rw [h2]
      exact div_self (pow_ne_zero 2 (ne_of_gt hTpos))
    set B : LorGrp n := ⟨DifferentialGeometry.ProjectiveOrthogonalGroup.Center.boostMatM kk c s, DifferentialGeometry.ProjectiveOrthogonalGroup.Center.boostMat_mem kk hcs⟩ with hBdef
    have hmatB : matOf B = DifferentialGeometry.ProjectiveOrthogonalGroup.Center.boostMat kk c s := rfl
    have hstep : matOf (B * A) *ᵥ eTime = DifferentialGeometry.ProjectiveOrthogonalGroup.Center.boostMat kk c s *ᵥ v := by
      rw [hvdef, matOf_mul, hmatB, ← Matrix.mulVec_mulVec]
    refine ⟨B * A, T', ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjk | hjk
      · have hne : j ≠ kk := by
          intro h
          rw [h] at hjk
          exact Nat.lt_irrefl _ (hkk ▸ hjk)
        rw [hstep, boostMat_mulVec_inl_ne kk c s v hne]
        exact hlt j hjk
      · have hjeq : j = kk := Fin.ext hjk
        subst hjeq
        rw [hstep, boostMat_mulVec_inl_self, hge kk (Nat.le_refl k), htime,
          mul_zero, zero_add, hsdef]
        exact div_mul_cancel₀ xk (ne_of_gt hTpos)
    · intro j hj
      have hne : j ≠ kk := by
        intro h
        rw [h, hkkval] at hj
        exact absurd hj (Nat.not_succ_le_self k)
      rw [hstep, boostMat_mulVec_inl_ne kk c s v hne]
      exact hge j (Nat.le_of_succ_le hj)
    · rw [hstep, boostMat_mulVec_inr, hge kk (Nat.le_refl k), htime,
        mul_zero, zero_add, hcdef]
      exact div_mul_cancel₀ T' (ne_of_gt hTpos)
    · rw [hT'def]
      calc (1 : ℝ) = Real.sqrt (1 ^ 2) := (Real.sqrt_sq zero_le_one).symm
        _ ≤ Real.sqrt (T ^ 2 + xk ^ 2) := Real.sqrt_le_sqrt (by nlinarith [hT1])
    · rw [hT'2, hT2, partialSd_succ x (Nat.lt_of_succ_le hk)]
      ring

theorem exists_lorGrp_basepoint (x : HUpper n) :
    ∃ A : LorGrp n, matOf A *ᵥ eTime = x.val := by
  obtain ⟨A, T, hlt, _hge, htime, hT1, hT2⟩ := exists_unitary_partial x n le_rfl
  rw [partialSd_self] at hT2
  have htx2 : tc x.val ^ 2 = 1 + sdot x.val x.val := tc_sq x
  have hTeq : T = tc x.val := by
    have h1 : T ^ 2 = tc x.val ^ 2 := by rw [hT2, htx2]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
    · exact h
    · have hT0 : (0 : ℝ) ≤ T := zero_le_one.trans hT1
      have hf : 0 < tc x.val := x.future
      linarith
  refine ⟨A, ?_⟩
  funext a
  rcases a with j | k
  · exact hlt j j.isLt
  · have hk0 : k = 0 := Subsingleton.elim k 0
    subst hk0
    rw [htime]
    exact hTeq

theorem exists_po_smul_basepoint (hn : 1 ≤ n) (x : HUpper n) :
    ∃ g : PO n 1, (poMulAction hn).smul g basepointH = x := by
  obtain ⟨A, hval⟩ := exists_lorGrp_basepoint x
  refine ⟨QuotientGroup.mk' (Subgroup.center ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ))) A, ?_⟩
  have h1 : (poMulAction hn).smul
        (QuotientGroup.mk' (Subgroup.center ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ))) A)
        basepointH = A • basepointH :=
    po_smul_mk hn A basepointH
  rw [h1]
  apply HUpper.ext
  rw [smul_val]
  change upperize (matOf A *ᵥ eTime) = x.val
  rw [hval]
  show upperize x.val = x.val
  unfold upperize
  rw [ite_eq_left x.future]

theorem exists_po_smul_eq (hn : 1 ≤ n) (x y : HUpper n) :
    ∃ g : PO n 1, (poMulAction hn).smul g x = y := by
  obtain ⟨gx, hgx⟩ := exists_po_smul_basepoint hn x
  obtain ⟨gy, hgy⟩ := exists_po_smul_basepoint hn y
  let := poMulAction hn
  have hgx' : gx • basepointH = x := hgx
  have hgy' : gy • basepointH = y := hgy
  have hinv : gx⁻¹ • x = basepointH := by
    rw [← hgx', smul_smul, inv_mul_cancel, one_smul]
  refine ⟨gy * gx⁻¹, ?_⟩
  change (gy * gx⁻¹) • x = y
  rw [mul_smul, hinv]
  exact hgy'

end DifferentialGeometry.HyperbolicTransitive
