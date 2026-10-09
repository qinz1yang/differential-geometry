/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.Connected.Clopen

open Set

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X]

theorem IsPreconnected.subset_or_disjoint_of_disjoint_relativeBoundary
    {Y T D : Set X} (hY : IsPreconnected Y) (hYT : Y ⊆ T) (hD : IsClosed D)
    (hYB : Disjoint Y (D ∩ closure (T \ D))) : Y ⊆ D ∨ Disjoint D Y := by
  have hcover : Y ⊆ D ∪ closure (T \ D) := fun x hx => by
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · exact Or.inr (subset_closure ⟨hYT hx, hxD⟩)
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hY D (closure (T \ D))
      hD isClosed_closure hcover hYB.inter_eq with h | h
  · exact Or.inl h
  · exact Or.inr (disjoint_left.mpr fun x hxD hxY =>
      disjoint_left.mp hYB hxY ⟨hxD, h hxY⟩)

theorem subset_or_disjoint_of_pairwiseDisjoint_boundary
    {ι : Type*} {F : ι → Set X} {T D : Set X}
    (hF : ∀ i, IsPreconnected (F i)) (hFT : ∀ i, F i ⊆ T)
    (hdis : Pairwise fun i j => Disjoint (F i) (F j)) (hD : IsClosed D)
    (i₀ : ι) (hboundary : D ∩ closure (T \ D) = F i₀) :
    ∀ i, i ≠ i₀ → F i ⊆ D ∨ Disjoint D (F i) := by
  intro i hi
  exact IsPreconnected.subset_or_disjoint_of_disjoint_relativeBoundary (hF i) (hFT i) hD
    (hboundary.symm ▸ hdis hi)

end DifferentialGeometry.Topology
