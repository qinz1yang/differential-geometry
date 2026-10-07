/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Faithfulness
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit

open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.HyperbolicBoundary

open DifferentialGeometry.Hyperbolic
open DifferentialGeometry.HyperbolicAction
open DifferentialGeometry.HyperbolicFaithful
open Matrix

variable {n : ℕ}

theorem eq_zero_of_lorB_self_eq_zero {w : LorVec n} (h : lorB w w = 0) (ht : tc w = 0) :
    w = 0 := by
  have hsdot : sdot w w = 0 := by
    have h0 := h
    simp only [lorB, ht, mul_zero, sub_zero] at h0
    exact h0
  funext a
  rcases a with a | a
  · exact HUpper.inl_eq_zero_of_sdot_self_eq_zero hsdot a
  · have : a = 0 := Subsingleton.elim a 0
    subst this
    exact ht

noncomputable def boundaryRep (w : LorVec n) : LorVec n := (tc w)⁻¹ • w

theorem tc_boundaryRep {w : LorVec n} (hw : tc w ≠ 0) : tc (boundaryRep w) = 1 := by
  change (tc w)⁻¹ * tc w = 1
  exact inv_mul_cancel₀ hw

theorem lorB_boundaryRep_self {w : LorVec n} (h : lorB w w = 0) :
    lorB (boundaryRep w) (boundaryRep w) = 0 := by
  change lorB ((tc w)⁻¹ • w) ((tc w)⁻¹ • w) = 0
  rw [lorB_smul_left, lorB_smul_right, h, mul_zero, mul_zero]

theorem boundaryRep_neg (w : LorVec n) : boundaryRep (-w) = boundaryRep w := by
  change (tc (-w))⁻¹ • (-w) = (tc w)⁻¹ • w
  rw [tc_neg, inv_neg, neg_smul, smul_neg, neg_neg]

theorem inv_mul_mul_smul_eq {c x : ℝ} (d : ℝ) (hc : c ≠ 0) :
    (c * d)⁻¹ * (c * x) = d⁻¹ * x := by
  field_simp

theorem boundaryRep_smul {w : LorVec n} (c : ℝ) (hc : c ≠ 0) :
    boundaryRep (c • w) = boundaryRep w := by
  funext a
  have htc : tc (c • w) = c * tc w := tc_smul c w
  change (tc (c • w))⁻¹ * ((c • w) a) = (tc w)⁻¹ * (w a)
  rw [htc, Pi.smul_apply, smul_eq_mul]
  exact inv_mul_mul_smul_eq (tc w) hc

@[ext]
structure BoundaryH (n : ℕ) where
  val : LorVec n
  is_null : lorB val val = 0
  tc_eq : tc val = 1

theorem tc_matOf_mulVec_ne_zero_of_null (g : LorGrp n) {w : LorVec n}
    (hnull : lorB w w = 0) (htc : tc w ≠ 0) : tc (matOf g *ᵥ w) ≠ 0 := by
  intro htc0
  have hnull' : lorB (matOf g *ᵥ w) (matOf g *ᵥ w) = 0 := by
    rw [lorB_matOf_mulVec]; exact hnull
  have hzero : matOf g *ᵥ w = 0 := eq_zero_of_lorB_self_eq_zero hnull' htc0
  have h1 : lorB (matOf g *ᵥ w) (matOf g *ᵥ (eTime : LorVec n)) = lorB w eTime :=
    lorB_matOf_mulVec g w eTime
  rw [hzero] at h1
  have hleft : lorB (0 : LorVec n) (matOf g *ᵥ (eTime : LorVec n)) = 0 := by
    simp [lorB, sdot, tc]
  rw [hleft] at h1
  have hright : lorB w (eTime : LorVec n) = - tc w := by
    have hsdot : sdot w (eTime : LorVec n) = 0 := by
      simp [sdot, eTime]
    have htce : tc (eTime : LorVec n) = 1 := eTime_apply_inr
    change sdot w eTime - tc w * tc eTime = - tc w
    rw [hsdot, htce]; ring
  rw [hright] at h1
  have : tc w = 0 := by linarith [h1]
  exact htc this

theorem tc_matOf_mulVec_ne_zero (g : LorGrp n) (v : BoundaryH n) :
    tc (matOf g *ᵥ v.val) ≠ 0 :=
  tc_matOf_mulVec_ne_zero_of_null g v.is_null (by rw [v.tc_eq]; norm_num)

noncomputable def actB (g : LorGrp n) (v : BoundaryH n) : BoundaryH n where
  val := boundaryRep (matOf g *ᵥ v.val)
  is_null := by
    apply lorB_boundaryRep_self
    rw [lorB_matOf_mulVec]
    exact v.is_null
  tc_eq := tc_boundaryRep (tc_matOf_mulVec_ne_zero g v)

noncomputable instance : MulAction (LorGrp n) (BoundaryH n) where
  smul g v := actB g v
  one_smul v := by
    apply BoundaryH.ext
    change boundaryRep (matOf (1 : LorGrp n) *ᵥ v.val) = v.val
    rw [matOf_one, Matrix.one_mulVec]
    change (tc v.val)⁻¹ • v.val = v.val
    rw [v.tc_eq, inv_one, one_smul]
  mul_smul g h v := by
    apply BoundaryH.ext
    change boundaryRep (matOf (g * h) *ᵥ v.val)
        = boundaryRep (matOf g *ᵥ boundaryRep (matOf h *ᵥ v.val))
    rw [matOf_mul, ← Matrix.mulVec_mulVec]
    set w := matOf h *ᵥ v.val with hwdef
    have htcw : tc w ≠ 0 := tc_matOf_mulVec_ne_zero_of_null h v.is_null (by rw [v.tc_eq]; norm_num)
    have htcgw : tc (matOf g *ᵥ w) ≠ 0 := tc_matOf_mulVec_ne_zero_of_null g
      (by rw [hwdef, lorB_matOf_mulVec]; exact v.is_null) htcw
    change boundaryRep (matOf g *ᵥ w) = boundaryRep (matOf g *ᵥ boundaryRep w)
    rw [show boundaryRep w = (tc w)⁻¹ • w from rfl, Matrix.mulVec_smul,
      boundaryRep_smul _ (inv_ne_zero htcw)]

section QuotientDescent

theorem boundary_smul_eq_self_of_mem_center (hn : 1 ≤ n) (z : LorGrp n)
    (hz : z ∈ Subgroup.center (LorGrp n)) (v : BoundaryH n) : z • v = v := by
  rcases DifferentialGeometry.ProjectiveOrthogonalGroup.Center.center_coe_eq hn hz with h1 | h1
  · have hz1 : z = 1 := Subtype.ext h1
    rw [hz1]
    exact one_smul _ v
  · apply BoundaryH.ext
    change boundaryRep (matOf z *ᵥ v.val) = v.val
    have hm : matOf z = (-1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) := h1
    have hmv : matOf z *ᵥ v.val = -v.val := by
      rw [hm]
      calc ((-1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) *ᵥ v.val)
          = -(1 *ᵥ v.val) := Matrix.neg_mulVec _ _
        _ = -v.val := by rw [Matrix.one_mulVec]
    rw [hmv, boundaryRep_neg]
    change (tc v.val)⁻¹ • v.val = v.val
    rw [v.tc_eq, inv_one, one_smul]

noncomputable def poBoundaryPermHom (hn : 1 ≤ n) : PO n 1 →* Equiv.Perm (BoundaryH n) :=
  QuotientGroup.lift (Subgroup.center ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ)))
    (MulAction.toPermHom ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ)) (BoundaryH n)) (by
    intro z hz
    rw [MonoidHom.mem_ker]
    apply Equiv.Perm.ext
    intro v
    exact boundary_smul_eq_self_of_mem_center hn z hz v)

@[instance_reducible]
noncomputable def poBoundaryMulAction (hn : 1 ≤ n) : MulAction (PO n 1) (BoundaryH n) where
  smul g v := poBoundaryPermHom hn g v
  one_smul v := by
    change poBoundaryPermHom hn 1 v = v
    rw [map_one]
    rfl
  mul_smul g h v := by
    change poBoundaryPermHom hn (g * h) v = poBoundaryPermHom hn g (poBoundaryPermHom hn h v)
    rw [map_mul]
    rfl

theorem po_boundary_smul_mk (hn : 1 ≤ n) (A : LorGrp n) (v : BoundaryH n) :
    letI := poBoundaryMulAction hn
    (QuotientGroup.mk' (Subgroup.center ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ))) A : PO n 1) • v
      = A • v := by
  let := poBoundaryMulAction hn
  change poBoundaryPermHom hn (QuotientGroup.mk' _ A) v = A • v
  rfl

end QuotientDescent

section BoundaryFaithfulness

theorem eigen_of_boundary_fixed {A : LorGrp n} {v : BoundaryH n} (h : A • v = v) :
    matOf A *ᵥ v.val = tc (matOf A *ᵥ v.val) • v.val := by
  have h1 : boundaryRep (matOf A *ᵥ v.val) = v.val := congrArg BoundaryH.val h
  set w := matOf A *ᵥ v.val with hw
  have htc : tc w ≠ 0 := tc_matOf_mulVec_ne_zero A v
  calc w = tc w • ((tc w)⁻¹ • w) := by rw [smul_smul, mul_inv_cancel₀ htc, one_smul]
    _ = tc w • boundaryRep w := rfl
    _ = tc w • v.val := by rw [h1]

noncomputable def nullUp (i : Fin n) : LorVec n := Pi.single (Sum.inl i) 1 + eTime

noncomputable def nullDown (i : Fin n) : LorVec n := -Pi.single (Sum.inl i) 1 + eTime

theorem nullUp_inl_self (i : Fin n) : (nullUp i) (Sum.inl i) = 1 := by
  change (Pi.single (Sum.inl i) 1 + eTime : LorVec n) (Sum.inl i) = 1
  rw [Pi.add_apply, eTime_apply_inl, add_zero, Pi.single_eq_same]

theorem nullUp_inl_of_ne {i k : Fin n} (h : k ≠ i) : (nullUp i) (Sum.inl k) = 0 := by
  change (Pi.single (Sum.inl i) 1 + eTime : LorVec n) (Sum.inl k) = 0
  rw [Pi.add_apply, eTime_apply_inl, add_zero, Pi.single_apply]
  rw [ite_eq_right (by rwa [Sum.inl.injEq])]

theorem nullDown_inl_self (i : Fin n) : (nullDown i) (Sum.inl i) = -1 := by
  change (-Pi.single (Sum.inl i) 1 + eTime : LorVec n) (Sum.inl i) = -1
  rw [Pi.add_apply, Pi.neg_apply, eTime_apply_inl, add_zero, Pi.single_eq_same]

theorem nullDown_inl_of_ne {i k : Fin n} (h : k ≠ i) : (nullDown i) (Sum.inl k) = 0 := by
  change (-Pi.single (Sum.inl i) 1 + eTime : LorVec n) (Sum.inl k) = 0
  rw [Pi.add_apply, Pi.neg_apply, eTime_apply_inl, add_zero, Pi.single_apply]
  rw [ite_eq_right (by rwa [Sum.inl.injEq]), neg_zero]

theorem nullUp_inr (i : Fin n) : (nullUp i) (Sum.inr 0) = 1 := by
  change (Pi.single (Sum.inl i) 1 + eTime : LorVec n) (Sum.inr 0) = 1
  rw [Pi.add_apply, eTime_apply_inr, Pi.single_apply, ite_eq_right Sum.inr_ne_inl, zero_add]

theorem nullDown_inr (i : Fin n) : (nullDown i) (Sum.inr 0) = 1 := by
  change (-Pi.single (Sum.inl i) 1 + eTime : LorVec n) (Sum.inr 0) = 1
  rw [Pi.add_apply, Pi.neg_apply, eTime_apply_inr, Pi.single_apply, ite_eq_right Sum.inr_ne_inl,
    neg_zero, zero_add]

theorem tc_single (i : Fin n) : tc (Pi.single (Sum.inl i) 1 : LorVec n) = 0 := by
  change (Pi.single (Sum.inl i) 1 : LorVec n) (Sum.inr 0) = 0
  rw [Pi.single_apply, ite_eq_right Sum.inr_ne_inl]

theorem tc_eTime : tc (eTime : LorVec n) = 1 := eTime_apply_inr

theorem tc_nullUp (i : Fin n) : tc (nullUp i : LorVec n) = 1 := nullUp_inr i

theorem tc_nullDown (i : Fin n) : tc (nullDown i : LorVec n) = 1 := nullDown_inr i

theorem sdot_single_self (i : Fin n) :
    sdot (Pi.single (Sum.inl i) 1 : LorVec n) (Pi.single (Sum.inl i) 1 : LorVec n) = 1 := by
  change (∑ j : Fin n, (Pi.single (Sum.inl i) 1 : LorVec n) (Sum.inl j)
      * (Pi.single (Sum.inl i) 1 : LorVec n) (Sum.inl j)) = 1
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, mul_one]
  · intro j _ hji
    have h' : ¬ (Sum.inl j : Fin n ⊕ Fin 1) = Sum.inl i := by
      rw [Sum.inl.injEq]
      exact hji
    rw [Pi.single_apply, ite_eq_right h', mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem sdot_single_eTime (i : Fin n) :
    sdot (Pi.single (Sum.inl i) 1 : LorVec n) (eTime : LorVec n) = 0 := by
  change (∑ j : Fin n, (Pi.single (Sum.inl i) 1 : LorVec n) (Sum.inl j)
      * (eTime : LorVec n) (Sum.inl j)) = 0
  apply Finset.sum_eq_zero
  intro j _
  rw [eTime_apply_inl, mul_zero]

theorem sdot_eTime_single (i : Fin n) :
    sdot (eTime : LorVec n) (Pi.single (Sum.inl i) 1 : LorVec n) = 0 := by
  rw [sdot_comm]
  exact sdot_single_eTime i

theorem lorB_single_self (i : Fin n) :
    lorB (Pi.single (Sum.inl i) 1 : LorVec n) (Pi.single (Sum.inl i) 1 : LorVec n) = 1 := by
  simp only [lorB, sdot_single_self, tc_single, mul_zero, sub_zero]

theorem lorB_single_eTime (i : Fin n) :
    lorB (Pi.single (Sum.inl i) 1 : LorVec n) (eTime : LorVec n) = 0 := by
  simp only [lorB, sdot_single_eTime, tc_single, tc_eTime, zero_mul, sub_zero]

theorem lorB_eTime_single (i : Fin n) :
    lorB (eTime : LorVec n) (Pi.single (Sum.inl i) 1 : LorVec n) = 0 := by
  rw [lorB_comm]
  exact lorB_single_eTime i

theorem lorB_nullUp (i : Fin n) : lorB (nullUp i) (nullUp i) = 0 := by
  change lorB (Pi.single (Sum.inl i) 1 + eTime) (Pi.single (Sum.inl i) 1 + eTime) = 0
  rw [lorB_add_left, lorB_add_right, lorB_add_right, lorB_single_self, lorB_single_eTime,
    lorB_eTime_single, lorB_eTime]
  norm_num

theorem lorB_nullDown (i : Fin n) : lorB (nullDown i) (nullDown i) = 0 := by
  have h1 : lorB (nullDown i) (nullDown i) =
      lorB (Pi.single (Sum.inl i) 1 : LorVec n) (Pi.single (Sum.inl i) 1 : LorVec n)
        + lorB (eTime : LorVec n) eTime := by
    change lorB (-Pi.single (Sum.inl i) 1 + eTime) (-Pi.single (Sum.inl i) 1 + eTime) = _
    rw [lorB_add_left, lorB_add_right, lorB_add_right, lorB_neg_left, lorB_neg_right, neg_neg,
      lorB_neg_left, lorB_single_eTime, neg_zero, lorB_neg_right, lorB_eTime_single, neg_zero]
    ring
  rw [h1, lorB_single_self, lorB_eTime]
  norm_num

noncomputable def nullUpB (i : Fin n) : BoundaryH n := ⟨nullUp i, lorB_nullUp i, tc_nullUp i⟩

noncomputable def nullDownB (i : Fin n) : BoundaryH n :=
  ⟨nullDown i, lorB_nullDown i, tc_nullDown i⟩

theorem nullUp_add_nullDown (i : Fin n) : nullUp i + nullDown i = (2 : ℝ) • eTime := by
  change (Pi.single (Sum.inl i) 1 + eTime) + (-Pi.single (Sum.inl i) 1 + eTime)
    = (2 : ℝ) • eTime
  rw [two_smul]
  abel

theorem nullUp_sub_nullDown (i : Fin n) :
    nullUp i - nullDown i = (2 : ℝ) • Pi.single (Sum.inl i) 1 := by
  change (Pi.single (Sum.inl i) 1 + eTime) - (-Pi.single (Sum.inl i) 1 + eTime)
    = (2 : ℝ) • Pi.single (Sum.inl i) 1
  rw [two_smul]
  abel

theorem matOf_eq_smul_one_of_boundary_trivial (hn : 2 ≤ n) {A : LorGrp n}
    (h : ∀ v : BoundaryH n, A • v = v) :
    ∃ ε : ℝ, matOf A = ε • (1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) := by
  classical
  obtain ⟨i₀, i₁, h01⟩ : ∃ i₀ i₁ : Fin n, i₀ ≠ i₁ :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.mk.injEq]⟩
  have eigUp : ∀ i : Fin n, matOf A *ᵥ nullUp i = tc (matOf A *ᵥ nullUp i) • nullUp i :=
    fun i => eigen_of_boundary_fixed (h (nullUpB i))
  have eigDn : ∀ i : Fin n, matOf A *ᵥ nullDown i = tc (matOf A *ᵥ nullDown i) • nullDown i :=
    fun i => eigen_of_boundary_fixed (h (nullDownB i))
  have htwo : ∀ i : Fin n, (2 : ℝ) • (matOf A *ᵥ eTime)
      = tc (matOf A *ᵥ nullUp i) • nullUp i + tc (matOf A *ᵥ nullDown i) • nullDown i := by
    intro i
    calc (2 : ℝ) • (matOf A *ᵥ eTime) = matOf A *ᵥ ((2 : ℝ) • eTime) :=
        (Matrix.mulVec_smul _ _ _).symm
      _ = matOf A *ᵥ (nullUp i + nullDown i) := by rw [nullUp_add_nullDown]
      _ = matOf A *ᵥ nullUp i + matOf A *ᵥ nullDown i := Matrix.mulVec_add _ _ _
      _ = tc (matOf A *ᵥ nullUp i) • nullUp i + tc (matOf A *ᵥ nullDown i) • nullDown i := by
        conv_lhs => rw [eigUp i, eigDn i]
  have hzero : ∀ k : Fin n, (matOf A *ᵥ eTime) (Sum.inl k) = 0 := by
    intro k
    rcases eq_or_ne k i₀ with hk | hk
    · have hk1 : k ≠ i₁ := fun h => h01 (hk.symm.trans h)
      have hc := congrFun (htwo i₁) (Sum.inl k)
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, nullUp_inl_of_ne hk1,
        nullDown_inl_of_ne hk1, mul_zero, add_zero] at hc
      linarith
    · have hc := congrFun (htwo i₀) (Sum.inl k)
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, nullUp_inl_of_ne hk,
        nullDown_inl_of_ne hk, mul_zero, add_zero] at hc
      linarith
  have htime : matOf A *ᵥ eTime = tc (matOf A *ᵥ eTime) • eTime := by
    funext a
    rcases a with k | k
    · rw [hzero k]
      show (0 : ℝ) = (tc (matOf A *ᵥ eTime) • eTime) (Sum.inl k)
      rw [Pi.smul_apply, eTime_apply_inl, smul_eq_mul, mul_zero]
    · have hk0 : k = 0 := Subsingleton.elim k 0
      subst hk0
      change (matOf A *ᵥ eTime) (Sum.inr 0) = (tc (matOf A *ᵥ eTime) • eTime) (Sum.inr 0)
      rw [Pi.smul_apply, eTime_apply_inr, smul_eq_mul, mul_one]
      rfl
  have hlmu : ∀ i : Fin n, tc (matOf A *ᵥ nullUp i) = tc (matOf A *ᵥ nullDown i) := by
    intro i
    have hc := congrFun (htwo i) (Sum.inl i)
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, nullUp_inl_self,
      nullDown_inl_self] at hc
    rw [hzero i] at hc
    linarith
  have hlc : ∀ i : Fin n, tc (matOf A *ᵥ nullUp i) = tc (matOf A *ᵥ eTime) := by
    intro i
    have hc := congrFun (htwo i) (Sum.inr 0)
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, nullUp_inr, nullDown_inr,
      mul_one] at hc
    have htc : (matOf A *ᵥ eTime) (Sum.inr 0) = tc (matOf A *ᵥ eTime) := rfl
    rw [htc] at hc
    have hμ := hlmu i
    linarith
  have hUp : ∀ i : Fin n, matOf A *ᵥ nullUp i = tc (matOf A *ᵥ eTime) • nullUp i := by
    intro i
    rw [← hlc i]
    exact eigUp i
  have hDn : ∀ i : Fin n, matOf A *ᵥ nullDown i = tc (matOf A *ᵥ eTime) • nullDown i := by
    intro i
    rw [← hlc i, hlmu i]
    exact eigDn i
  have hsingle : ∀ i : Fin n,
      matOf A *ᵥ Pi.single (Sum.inl i) 1 = tc (matOf A *ᵥ eTime) • Pi.single (Sum.inl i) 1 := by
    intro i
    have key : matOf A *ᵥ ((2 : ℝ) • Pi.single (Sum.inl i) 1)
        = tc (matOf A *ᵥ eTime) • ((2 : ℝ) • Pi.single (Sum.inl i) 1) := by
      rw [← nullUp_sub_nullDown, Matrix.mulVec_sub, hUp i, hDn i, smul_sub]
    rw [Matrix.mulVec_smul, smul_comm] at key
    have h2 : (2 : ℝ) • (matOf A *ᵥ Pi.single (Sum.inl i) 1
        - tc (matOf A *ᵥ eTime) • Pi.single (Sum.inl i) 1) = 0 := by
      rw [smul_sub, key, sub_self]
    rcases smul_eq_zero.mp h2 with h0 | h0
    · norm_num at h0
    · exact sub_eq_zero.mp h0
  refine ⟨tc (matOf A *ᵥ eTime), ?_⟩
  apply Matrix.ext_of_mulVec_single
  intro a
  change matOf A *ᵥ Pi.single a 1
    = (tc (matOf A *ᵥ eTime) • (1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)) *ᵥ Pi.single a 1
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rcases a with i | k
  · exact hsingle i
  · have hk0 : k = 0 := Subsingleton.elim k 0
    subst hk0
    change matOf A *ᵥ Pi.single (Sum.inr 0) 1 = tc (matOf A *ᵥ eTime) • Pi.single (Sum.inr 0) 1
    rw [show (Pi.single (Sum.inr 0) 1 : LorVec n) = eTime from rfl]
    exact htime

theorem po_boundary_smul_eq_one (hn : 2 ≤ n) {g : PO n 1}
    (h : ∀ ξ : BoundaryH n, (poBoundaryMulAction (by omega : 1 ≤ n)).smul g ξ = ξ) :
    g = 1 := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ))) g
  have hA : ∀ ξ : BoundaryH n, A • ξ = ξ := by
    intro ξ
    have hx := h ξ
    change A • ξ = ξ
    exact hx
  obtain ⟨ε, hεA⟩ := matOf_eq_smul_one_of_boundary_trivial hn hA
  have hB : ∀ u v : LorVec n, lorB (matOf A *ᵥ u) (matOf A *ᵥ v) = lorB u v :=
    fun u v => lorB_matOf_mulVec A u v
  have hε2 : ε ^ 2 = 1 := by
    have h1 := hB eTime eTime
    rw [hεA, Matrix.smul_mulVec, Matrix.one_mulVec, lorB_smul_left, lorB_smul_right,
      lorB_eTime] at h1
    have hε : ε * ε = 1 := by nlinarith [h1]
    rw [pow_two]
    exact hε
  have hAval : (A : MatrixSum (Fin n) (Fin 1) ℝ) = 1 ∨
      (A : MatrixSum (Fin n) (Fin 1) ℝ) = -1 := by
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
      rw [hA1]
      exact Subgroup.one_mem _
    · have hAneg : A = ⟨-1, DifferentialGeometry.ProjectiveOrthogonalGroup.Center.neg_one_mem_unitary⟩ := Subtype.ext h1
      rw [hAneg]
      exact DifferentialGeometry.ProjectiveOrthogonalGroup.Center.neg_one_mem_center (n := n)
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hAcent

theorem eq_of_po_boundary_smul_eq (hn : 2 ≤ n) {a b : PO n 1}
    (h : ∀ ξ : BoundaryH n, (poBoundaryMulAction (by omega : 1 ≤ n)).smul a ξ
      = (poBoundaryMulAction (by omega : 1 ≤ n)).smul b ξ) : a = b := by
  have h1 : (1 : ℕ) ≤ n := by omega
  let := poBoundaryMulAction h1
  have key : ∀ ξ : BoundaryH n, (b⁻¹ * a) • ξ = ξ := by
    intro ξ
    rw [mul_smul]
    have hξ : a • ξ = b • ξ := h ξ
    rw [hξ, ← mul_smul, inv_mul_cancel, one_smul]
  have hba : b⁻¹ * a = 1 := po_boundary_smul_eq_one hn key
  exact (inv_mul_eq_one.mp hba).symm

end BoundaryFaithfulness

end DifferentialGeometry.HyperbolicBoundary
