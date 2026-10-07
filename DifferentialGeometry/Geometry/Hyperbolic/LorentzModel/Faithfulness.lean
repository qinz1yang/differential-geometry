/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Action

open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.HyperbolicFaithful

open DifferentialGeometry.Hyperbolic
open DifferentialGeometry.HyperbolicAction
open Matrix

variable {n : ℕ}

noncomputable def eTime : LorVec n := Pi.single (Sum.inr 0) 1

noncomputable def eBoost (i : Fin n) : LorVec n :=
  Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr 0) (Real.sqrt 2)

theorem eTime_apply_inl (j : Fin n) : eTime (Sum.inl j) = (0 : ℝ) := by
  simp [eTime]

theorem eTime_apply_inr : (eTime : LorVec n) (Sum.inr 0) = 1 := by
  simp [eTime]

theorem sdot_eTime : sdot (eTime : LorVec n) eTime = 0 := by
  simp [sdot, eTime_apply_inl]

theorem lorB_eTime : lorB (eTime : LorVec n) eTime = -1 := by
  simp [lorB, sdot_eTime, tc, eTime_apply_inr]

theorem eBoost_apply_inl (i j : Fin n) :
    (eBoost i : LorVec n) (Sum.inl j) = (if j = i then 1 else 0 : ℝ) := by
  simp [eBoost, Pi.add_apply, Pi.single_apply, Sum.inl.injEq]

theorem eBoost_apply_inr (i : Fin n) : (eBoost i : LorVec n) (Sum.inr 0) = Real.sqrt 2 := by
  simp [eBoost, Pi.add_apply]

theorem sdot_eBoost (i : Fin n) : sdot (eBoost i : LorVec n) (eBoost i) = 1 := by
  simp only [sdot, eBoost_apply_inl]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

theorem lorB_eBoost (i : Fin n) : lorB (eBoost i : LorVec n) (eBoost i) = -1 := by
  have h2 : (Real.sqrt 2 : ℝ) * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  change sdot (eBoost i) (eBoost i) - tc (eBoost i) * tc (eBoost i) = -1
  rw [sdot_eBoost i, show tc (eBoost i) = Real.sqrt 2 from eBoost_apply_inr i, h2]
  norm_num

noncomputable def basepointH : HUpper n where
  val := eTime
  is_unit := lorB_eTime
  future := by rw [tc, eTime_apply_inr]; norm_num

noncomputable def boostH (i : Fin n) : HUpper n where
  val := eBoost i
  is_unit := lorB_eBoost i
  future := by rw [tc, eBoost_apply_inr i]; positivity

theorem eBoost_sub_smul_eTime (i : Fin n) :
    (eBoost i : LorVec n) - Real.sqrt 2 • eTime = Pi.single (Sum.inl i) 1 := by
  funext a
  rcases a with a | a
  · rw [Pi.sub_apply, Pi.smul_apply, eBoost_apply_inl, eTime_apply_inl, smul_eq_mul,
      mul_zero, sub_zero]
    simp [Pi.single_apply, Sum.inl.injEq, eq_comm]
  · have ha : a = 0 := Subsingleton.elim a 0
    subst ha
    rw [Pi.sub_apply, Pi.smul_apply, eBoost_apply_inr, eTime_apply_inr, smul_eq_mul, mul_one]
    simp []

theorem eq_smul_one_of_forall_hyperboloid_eigen {B : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ}
    (hB : ∀ x y : LorVec n, lorB (B *ᵥ x) (B *ᵥ y) = lorB x y)
    (heig : ∀ x : HUpper n, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ B *ᵥ x.val = σ • x.val) :
    ∃ ε : ℝ, B = ε • 1 := by
  obtain ⟨ε, hε, hε0⟩ := heig basepointH
  have hconst : ∀ x : HUpper n, B *ᵥ x.val = ε • x.val := by
    intro x
    obtain ⟨σ, hσ, hσx⟩ := heig x
    have hpr : lorB (B *ᵥ x.val) (B *ᵥ basepointH.val) = lorB x.val basepointH.val := hB _ _
    rw [hσx, hε0, lorB_smul_left, lorB_smul_right] at hpr
    have hne : lorB x.val basepointH.val ≠ 0 := by
      have h1 := HUpper.one_le_neg_lorB x basepointH
      have hle : lorB x.val basepointH.val ≤ -1 := by linarith [h1]
      linarith
    have hse : σ * ε = 1 := by
      have h0 : (σ * ε - 1) * lorB x.val basepointH.val = 0 := by linarith [hpr]
      rcases mul_eq_zero.mp h0 with h' | h'
      · linarith
      · exact absurd h' hne
    have hσ_eq : σ = ε := by
      rcases hσ with hσ1 | hσ1 <;> rcases hε with hε1 | hε1
      · rw [hσ1, hε1]
      · rw [hσ1, hε1] at hse; norm_num at hse
      · rw [hσ1, hε1] at hse; norm_num at hse
      · rw [hσ1, hε1]
    rw [hσx, hσ_eq]
  refine ⟨ε, ?_⟩
  apply Matrix.ext_of_mulVec_single
  intro a
  have hRHS : (ε • (1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)) *ᵥ Pi.single a 1
      = ε • Pi.single a 1 := by
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hRHS]
  rcases a with a | a
  · rw [← eBoost_sub_smul_eTime a, Matrix.mulVec_sub, Matrix.mulVec_smul,
      show B *ᵥ eBoost a = ε • eBoost a from hconst (boostH a),
      show B *ᵥ eTime = ε • eTime from hconst basepointH]
    module
  · have ha : a = 0 := Subsingleton.elim a 0
    subst ha
    change B *ᵥ Pi.single (Sum.inr 0) 1 = ε • Pi.single (Sum.inr 0) 1
    rw [show Pi.single (Sum.inr 0) 1 = (eTime : LorVec n) from rfl,
      show B *ᵥ eTime = ε • eTime from hconst basepointH]

theorem exists_sign_smul_of_actH_eq {A : LorGrp n} {x : HUpper n}
    (h : actH A x = x) : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ matOf A *ᵥ x.val = σ • x.val := by
  have hval : upperize (matOf A *ᵥ x.val) = x.val := congrArg HUpper.val h
  unfold upperize at hval
  by_cases hc : 0 < tc (matOf A *ᵥ x.val)
  · rw [ite_eq_left hc] at hval
    exact ⟨1, Or.inl rfl, by rw [hval, one_smul]⟩
  · rw [ite_eq_right hc] at hval
    refine ⟨-1, Or.inr rfl, ?_⟩
    have hv : matOf A *ᵥ x.val = - x.val := by
      calc matOf A *ᵥ x.val = -(-(matOf A *ᵥ x.val)) := (neg_neg _).symm
        _ = - x.val := by rw [hval]
    rw [hv, neg_one_smul]

theorem po_smul_eq_one (hn : 1 ≤ n) {g : PO n 1}
    (h : ∀ x : HUpper n, (poMulAction hn).smul g x = x) : g = 1 := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ))) g
  have hA : ∀ x : HUpper n, actH A x = x := by
    intro x
    have hx := h x
    change actH A x = x
    exact hx
  have heig : ∀ x : HUpper n, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ matOf A *ᵥ x.val = σ • x.val :=
    fun x => exists_sign_smul_of_actH_eq (hA x)
  have hB : ∀ u v : LorVec n, lorB (matOf A *ᵥ u) (matOf A *ᵥ v) = lorB u v :=
    fun u v => lorB_matOf_mulVec A u v
  obtain ⟨ε, hεA⟩ := eq_smul_one_of_forall_hyperboloid_eigen hB heig
  have hε2 : ε ^ 2 = 1 := by
    have h1 := hB eTime eTime
    rw [hεA, Matrix.smul_mulVec, Matrix.one_mulVec, lorB_smul_left, lorB_smul_right,
      lorB_eTime] at h1
    have : ε * ε = 1 := by nlinarith [h1]
    rw [pow_two]; exact this
  have hAval : (A : MatrixSum (Fin n) (Fin 1) ℝ) = 1 ∨ (A : MatrixSum (Fin n) (Fin 1) ℝ) = -1 := by
    rcases sq_eq_one_iff.mp hε2 with hε1 | hε1
    · left
      have hm : matOf A = (1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) := by
        rw [hεA, hε1, one_smul]
      exact hm
    · right
      have hm : matOf A = (-1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) := by
        rw [hεA, hε1, neg_one_smul]
      exact hm
  have hAcent : A ∈ Subgroup.center ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ)) := by
    rcases hAval with h1 | h1
    · have hA1 : A = 1 := Subtype.ext h1
      rw [hA1]; exact Subgroup.one_mem _
    · have hAneg : A = ⟨-1, DifferentialGeometry.ProjectiveOrthogonalGroup.Center.neg_one_mem_unitary⟩ := Subtype.ext h1
      rw [hAneg]; exact DifferentialGeometry.ProjectiveOrthogonalGroup.Center.neg_one_mem_center (n := n)
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hAcent

end DifferentialGeometry.HyperbolicFaithful
