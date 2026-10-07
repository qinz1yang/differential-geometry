/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import Mathlib.GroupTheory.Nilpotent

noncomputable section

open Set
open scoped commutatorElement

namespace DifferentialGeometry.NilpotentCenter

variable {G : Type*} [Group G]

theorem inv_mul_mem_center_of_commutators_eq (S : Set G)
    (hS : Subgroup.closure S = ⊤) {a b : G}
    (h : ∀ s ∈ S, ⁅a, s⁆ = ⁅b, s⁆) :
    b⁻¹ * a ∈ Subgroup.center G := by
  have hc : b⁻¹ * a ∈ Subgroup.centralizer S := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro s hs
    have he := h s hs
    simp only [commutatorElement_def, mul_right_cancel_iff] at he
    have he' := congrArg (fun x : G => b⁻¹ * x * a) he
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using he'.symm
  rwa [← Subgroup.centralizer_closure S, hS, Subgroup.coe_top,
    Subgroup.centralizer_univ] at hc

theorem finite_upperCentralSeries_succ (S : Set G)
    (hgen : Subgroup.closure S = ⊤) (hS : S.Finite)
    [Finite (Subgroup.center G)] (k : ℕ)
    [Finite (Subgroup.upperCentralSeries G k)] :
    Finite (Subgroup.upperCentralSeries G (k + 1)) := by
  classical
  let : Finite S := hS
  let A := Subgroup.upperCentralSeries G (k + 1)
  let B := Subgroup.upperCentralSeries G k
  let q : A → (S → B) := fun a s =>
    ⟨⁅(a : G), (s : G)⁆, Subgroup.mem_upperCentralSeries_succ_iff.mp a.property s⟩
  have hfin : (Set.univ : Set A).Finite := by
    apply Set.Finite.of_finite_fibers q (Set.toFinite _)
    rintro p ⟨b, _, hqb⟩
    let j : (Set.univ ∩ q ⁻¹' {p} : Set A) → Subgroup.center G := fun a =>
      ⟨(b : G)⁻¹ * (a : A),
        inv_mul_mem_center_of_commutators_eq S hgen (fun s hs => by
          have he : q (a : A) = q b := a.property.2.trans hqb.symm
          exact congrArg Subtype.val (congrFun he ⟨s, hs⟩))⟩
    exact Finite.of_injective j (by
      intro a a' he
      apply Subtype.ext
      apply Subtype.ext
      exact mul_left_cancel (congrArg Subtype.val he))
  exact Set.finite_univ_iff.mp hfin

theorem finite_of_finite_center [Group.FG G] [Group.IsNilpotent G]
    [Finite (Subgroup.center G)] : Finite G := by
  obtain ⟨S, hgen, hS⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  have hfinite : ∀ k : ℕ, Finite (Subgroup.upperCentralSeries G k) := by
    intro k
    induction k with
    | zero => exact inferInstanceAs (Finite (⊥ : Subgroup G))
    | succ k ih =>
      let := ih
      exact finite_upperCentralSeries_succ S hgen hS k
  obtain ⟨k, hk⟩ := Group.IsNilpotent.nilpotent (G := G)
  let : Finite (⊤ : Subgroup G) := hk ▸ hfinite k
  exact Finite.of_equiv (⊤ : Subgroup G) Subgroup.topEquiv.toEquiv

theorem infinite_center [Group.FG G] [Group.IsNilpotent G] [Infinite G] :
    Infinite (Subgroup.center G) := by
  apply not_finite_iff_infinite.mp
  intro h
  let := h
  let : Finite G := finite_of_finite_center
  exact _root_.not_finite G

end DifferentialGeometry.NilpotentCenter
