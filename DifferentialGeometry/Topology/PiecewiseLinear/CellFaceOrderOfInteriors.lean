/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CellFaceRecognition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {Λ X : Type*} {step : Λ → Λ → Prop} {dim : Λ → ℕ} {tc tcBd : Λ → Set X}

theorem subset_iff_reflTransGen_of_disjoint_interiors
    (hdim : ∀ m l, step m l → dim m < dim l)
    (hstep : ∀ m l, step m l → tc m ⊆ tcBd l)
    (hbd : ∀ l, tcBd l ⊆ ⋃ m, ⋃ (_ : step m l), tc m)
    (hsub : ∀ l, tcBd l ⊆ tc l)
    (hne : ∀ l, (tc l \ tcBd l).Nonempty)
    (hmeet : ∀ k k', k ≠ k' → tc k ∩ tc k' ⊆ tcBd k ∪ tcBd k') {m l : Λ} :
    tc m ⊆ tc l ↔ Relation.ReflTransGen step m l := by
  constructor
  · intro hml
    obtain ⟨y, hym, hynm⟩ := hne m
    obtain ⟨k, hkl, hyk, hynk⟩ :=
      exists_reflTransGen_mem_sdiff_boundary hdim hbd l (hml hym)
    have hkm : k = m := by
      by_contra hkm
      rcases hmeet k m hkm ⟨hyk, hym⟩ with h | h
      · exact hynk h
      · exact hynm h
    exact hkm ▸ hkl
  · exact subset_of_reflTransGen_of_step hstep hsub

theorem boundary_inter_and_strict_of_disjoint_interiors
    (hdim : ∀ m l, step m l → dim m < dim l)
    (hstep : ∀ m l, step m l → tc m ⊆ tcBd l)
    (hbd : ∀ l, tcBd l ⊆ ⋃ m, ⋃ (_ : step m l), tc m)
    (hsub : ∀ l, tcBd l ⊆ tc l)
    (hne : ∀ l, (tc l \ tcBd l).Nonempty)
    (hmeet : ∀ k k', k ≠ k' → tc k ∩ tc k' ⊆ tcBd k ∪ tcBd k') :
    (∀ l, tcBd l = ⋃ m ∈ {m | tc m ⊆ tc l} \ {l}, tc m) ∧
      (∀ l m, tc l ∩ tc m = ⋃ k ∈ {k | tc k ⊆ tc l} ∩ {k | tc k ⊆ tc m}, tc k) ∧
      ∀ l m, tc m ⊆ tc l → m = l ∨ dim m < dim l := by
  have hF : ∀ l m, m ∈ {m | tc m ⊆ tc l} ↔ Relation.ReflTransGen step m l :=
    fun _ _ => subset_iff_reflTransGen_of_disjoint_interiors hdim hstep hbd hsub hne hmeet
  obtain ⟨hb, hi⟩ := boundary_eq_and_inter_eq_of_step hF hdim hstep hbd hsub hmeet
  exact ⟨hb, hi, fun l m hml =>
    eq_or_dim_lt_of_reflTransGen hdim ((hF l m).mp hml)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
