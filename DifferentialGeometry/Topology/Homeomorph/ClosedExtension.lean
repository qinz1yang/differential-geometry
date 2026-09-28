/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Bounded

open Set Topology

namespace Homeomorph

variable {X : Type*} [TopologicalSpace X] {P : Set X}

private noncomputable def extendByIdMap (e : P ≃ₜ P) : X → X := by
  classical
  exact fun x => if hx : x ∈ P then (e ⟨x, hx⟩ : X) else x

private theorem extendByIdMap_of_mem (e : P ≃ₜ P) {x : X} (hx : x ∈ P) :
    extendByIdMap e x = (e ⟨x, hx⟩ : X) := by
  simp only [extendByIdMap, dite_eq_left hx]

private theorem extendByIdMap_of_notMem (e : P ≃ₜ P) {x : X} (hx : x ∉ P) :
    extendByIdMap e x = x := by
  simp only [extendByIdMap, dite_eq_right hx]

private theorem continuous_extendByIdMap (e : P ≃ₜ P) (hP : IsClosed P)
    (hfix : ∀ x : P, (x : X) ∈ frontier P → e x = x) : Continuous (extendByIdMap e) := by
  have hcontP : ContinuousOn (extendByIdMap e) P := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (fun x : P => extendByIdMap e x) = (fun x : P => (e x : X)) :=
      funext fun x => extendByIdMap_of_mem e x.2
    change Continuous (fun x : P => extendByIdMap e x)
    rw [heq]
    exact continuous_subtype_val.comp e.continuous
  have hcontC : ContinuousOn (extendByIdMap e) (closure Pᶜ) := by
    apply continuousOn_id.congr
    intro x hx
    by_cases hxP : x ∈ P
    · rw [extendByIdMap_of_mem e hxP]
      exact congrArg Subtype.val (hfix ⟨x, hxP⟩
        (by rw [frontier_eq_closure_inter_closure]; exact ⟨subset_closure hxP, hx⟩))
    · exact extendByIdMap_of_notMem e hxP
  have hcover : P ∪ closure Pᶜ = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ P
    · exact Or.inl hx
    · exact Or.inr (subset_closure hx)
  have h := hcontP.union_of_isClosed hcontC hP isClosed_closure
  rwa [hcover, continuousOn_univ] at h

private theorem leftInverse_extendByIdMap (e : P ≃ₜ P) :
    Function.LeftInverse (extendByIdMap e.symm) (extendByIdMap e) := by
  intro x
  by_cases hx : x ∈ P
  · rw [extendByIdMap_of_mem e hx, extendByIdMap_of_mem e.symm (e ⟨x, hx⟩).2]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)
  · rw [extendByIdMap_of_notMem e hx, extendByIdMap_of_notMem e.symm hx]

noncomputable def extendById (e : P ≃ₜ P) (hP : IsClosed P)
    (hfix : ∀ x : P, (x : X) ∈ frontier P → e x = x) : X ≃ₜ X where
  toFun := extendByIdMap e
  invFun := extendByIdMap e.symm
  left_inv := leftInverse_extendByIdMap e
  right_inv := leftInverse_extendByIdMap e.symm
  continuous_toFun := continuous_extendByIdMap e hP hfix
  continuous_invFun := continuous_extendByIdMap e.symm hP (fun x hx => by
    apply e.injective
    rw [e.apply_symm_apply, hfix x hx])

theorem extendById_apply_of_mem (e : P ≃ₜ P) (hP : IsClosed P)
    (hfix : ∀ x : P, (x : X) ∈ frontier P → e x = x) {x : X} (hx : x ∈ P) :
    e.extendById hP hfix x = (e ⟨x, hx⟩ : X) := extendByIdMap_of_mem e hx

theorem extendById_apply_of_notMem (e : P ≃ₜ P) (hP : IsClosed P)
    (hfix : ∀ x : P, (x : X) ∈ frontier P → e x = x) {x : X} (hx : x ∉ P) :
    e.extendById hP hfix x = x := extendByIdMap_of_notMem e hx

theorem extendById_eqOn_compl_interior (e : P ≃ₜ P) (hP : IsClosed P)
    (hfix : ∀ x : P, (x : X) ∈ frontier P → e x = x) :
    EqOn (e.extendById hP hfix) id (interior P)ᶜ := by
  intro x hx
  by_cases hxP : x ∈ P
  · rw [e.extendById_apply_of_mem hP hfix hxP]
    exact congrArg Subtype.val (hfix ⟨x, hxP⟩ ⟨subset_closure hxP, hx⟩)
  · exact e.extendById_apply_of_notMem hP hfix hxP

theorem extendById_image_self (e : P ≃ₜ P) (hP : IsClosed P)
    (hfix : ∀ x : P, (x : X) ∈ frontier P → e x = x) :
    e.extendById hP hfix '' P = P := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    rw [e.extendById_apply_of_mem hP hfix hx]
    exact (e ⟨x, hx⟩).2
  · intro y hy
    refine ⟨(e.symm ⟨y, hy⟩ : X), (e.symm ⟨y, hy⟩).2, ?_⟩
    rw [e.extendById_apply_of_mem hP hfix (e.symm ⟨y, hy⟩).2]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)

end Homeomorph

namespace Homeomorph

variable {X : Type*} [PseudoMetricSpace X] {P : Set X}

theorem dist_extendById_le_diam (e : P ≃ₜ P) (hP : IsClosed P)
    (hfix : ∀ x : P, (x : X) ∈ frontier P → e x = x) (hbounded : Bornology.IsBounded P)
    (x : X) : dist (e.extendById hP hfix x) x ≤ Metric.diam P := by
  by_cases hx : x ∈ P
  · rw [e.extendById_apply_of_mem hP hfix hx]
    exact Metric.dist_le_diam_of_mem hbounded (e ⟨x, hx⟩).2 hx
  · rw [e.extendById_apply_of_notMem hP hfix hx, dist_self]
    exact Metric.diam_nonneg

theorem dist_extendById_lt (e : P ≃ₜ P) (hP : IsClosed P)
    (hfix : ∀ x : P, (x : X) ∈ frontier P → e x = x) (hbounded : Bornology.IsBounded P)
    {ε : X → ℝ} (hε : ∀ x, 0 < ε x) (hdiam : ∀ x ∈ P, Metric.diam P < ε x) (x : X) :
    dist (e.extendById hP hfix x) x < ε x := by
  by_cases hx : x ∈ P
  · exact (e.dist_extendById_le_diam hP hfix hbounded x).trans_lt (hdiam x hx)
  · rw [e.extendById_apply_of_notMem hP hfix hx, dist_self]
    exact hε x

end Homeomorph
