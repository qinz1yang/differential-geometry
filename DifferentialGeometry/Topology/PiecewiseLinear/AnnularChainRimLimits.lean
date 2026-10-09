/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Separation.Basic

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem subset_closure_iUnion_of_tail_retractions
    {X : Type*} [TopologicalSpace X] [T1Space X] {R V : Set X}
    (hV : IsOpen V) (hRV : R ⊆ V) (r : C(V, R))
    (hr : ∀ x : R, r (Set.inclusion hRV x) = x)
    (F : ℤ → Set X) (hF : ∀ i, F i ⊆ V)
    (honto : ∀ i, Function.Surjective (fun x : F i => r (Set.inclusion (hF i) x)))
    (htail : ∀ U : Set X, IsOpen U → R ⊆ U → ∃ m : ℤ, ∀ i, m ≤ i → F i ⊆ U) :
    R ⊆ closure (⋃ i, F i) := by
  intro x hx
  rw [mem_closure_iff]
  intro O hO hxO
  let Q : Set V := r ⁻¹' {⟨x, hx⟩}ᶜ ∪ Subtype.val ⁻¹' O
  have hQ : IsOpen Q :=
    (isOpen_compl_singleton.preimage r.continuous).union (hO.preimage continuous_subtype_val)
  let U : Set X := Subtype.val '' Q
  have hU : IsOpen U := hV.isOpenMap_subtype_val Q hQ
  have hRU : R ⊆ U := by
    intro y hy
    refine ⟨⟨y, hRV hy⟩, ?_, rfl⟩
    by_cases hxy : y = x
    · exact Or.inr (hxy ▸ hxO)
    · left
      change r (Set.inclusion hRV ⟨y, hy⟩) ≠ ⟨x, hx⟩
      rw [hr]
      exact fun h => hxy (congrArg Subtype.val h)
  obtain ⟨m, hm⟩ := htail U hU hRU
  obtain ⟨y, hy⟩ := honto m ⟨x, hx⟩
  obtain ⟨z, hz, hzy⟩ := hm m le_rfl y.property
  have hzval : z = Set.inclusion (hF m) y := Subtype.ext hzy
  have hyO : (y : X) ∈ O := by
    rcases hz with hz | hz
    · change r z ≠ ⟨x, hx⟩ at hz
      exact False.elim (hz (hzval ▸ hy))
    · exact hzy ▸ hz
  exact ⟨y, hyO, mem_iUnion.mpr ⟨m, y.property⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
