/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SphereComplement
import DifferentialGeometry.Topology.Connected.Separation

/-!
# PL spheres separating nested sets
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLSphere.exists_isPLBall_between_of_separates
    {B C₁ C₂ : Set (EuclideanSpace ℝ (Fin 3))} (hB : IsPLSphere 2 B)
    (hC₁ : IsClosed C₁) (hC₂ : IsCompact C₂) (hconn₁ : IsConnected C₁)
    (hconn₂ : IsPreconnected C₂ᶜ) (hBX : B ⊆ interior (closure (C₂ \ C₁)))
    (hsep : Separates B (frontier C₁) (frontier C₂)) :
    ∃ D, IsPLBall 3 D ∧ frontier D = B ∧ C₁ ⊆ interior D ∧ D ⊆ interior C₂ := by
  have hBC₂ : B ⊆ interior C₂ :=
    hBX.trans (interior_mono (closure_minimal sdiff_subset hC₂.isClosed))
  have hBC₁ : B ⊆ C₁ᶜ := by
    intro x hx hx₁
    have hni : x ∉ interior C₁ := by
      have h := closure_mono (sdiff_subset_compl C₂ C₁)
        (interior_subset (hBX hx))
      simpa only [closure_compl, mem_compl_iff] using h
    exact hsep.left_subset_compl
      (by rw [hC₁.frontier_eq]; exact ⟨hx₁, hni⟩) hx
  obtain ⟨D, hD, hfront, hbounded, hunion, hdisjoint, -, hDconn, -⟩ :=
    hB.exists_isPLBall_complement_components
  have hDclosed : IsClosed D := hD.isPolyhedron.isCompact.isClosed
  have hunbounded : ¬ Bornology.IsBounded (univ : Set (EuclideanSpace ℝ (Fin 3))) :=
    NormedSpace.unbounded_univ ℝ _
  have hC₂unbounded : ¬ Bornology.IsBounded C₂ᶜ := by
    intro h
    exact hunbounded (by simpa using hC₂.isBounded.union h)
  have hC₂B : C₂ᶜ ⊆ Bᶜ := fun _ hx hBmem => hx (interior_subset (hBC₂ hBmem))
  have hC₂D : C₂ᶜ ⊆ Dᶜ := by
    rcases hconn₂.subset_or_subset isOpen_interior hDclosed.isOpen_compl hdisjoint
      (hC₂B.trans hunion.subset) with h | h
    · exact (hC₂unbounded (hbounded.subset (h.trans interior_subset))).elim
    · exact h
  have hDC₂ : D ⊆ interior C₂ := by
    have hsub : D ⊆ C₂ := compl_subset_compl.mp hC₂D
    intro x hx
    by_cases hi : x ∈ interior D
    · exact interior_mono hsub hi
    · apply hBC₂
      rw [← hfront, hDclosed.frontier_eq]
      exact ⟨hx, hi⟩
  have hC₁B : C₁ ⊆ Bᶜ := fun _ hx hxB => hBC₁ hxB hx
  refine ⟨D, hD, hfront, ?_, hDC₂⟩
  rcases hconn₁.isPreconnected.subset_or_subset isOpen_interior hDclosed.isOpen_compl
    hdisjoint (hC₁B.trans hunion.subset) with h | h
  · exact h
  · have hne₁ : (frontier C₁).Nonempty := nonempty_frontier_iff.mpr
      ⟨hconn₁.nonempty, fun heq => by
        obtain ⟨z, hz⟩ := hB.isConnected.nonempty
        exact hBC₁ hz (heq.symm ▸ mem_univ z)⟩
    have hne₂ : (frontier C₂).Nonempty := nonempty_frontier_iff.mpr
      ⟨hB.isConnected.nonempty.mono (hBC₂.trans interior_subset),
        fun heq => hunbounded (heq ▸ hC₂.isBounded)⟩
    obtain ⟨x, hx⟩ := hne₁
    obtain ⟨y, hy⟩ := hne₂
    have hxD : x ∈ Dᶜ := h (hC₁.frontier_subset hx)
    have hyD : y ∈ Dᶜ := fun hyD => hy.2 (hDC₂ hyD)
    have hDB : Dᶜ ⊆ Bᶜ := subset_union_right.trans hunion.symm.subset
    exact (hsep.not_mem_connectedComponentIn hx hy
      (hDconn.isPreconnected.subset_connectedComponentIn hxD hDB hyD)).elim

end DifferentialGeometry.Topology.PiecewiseLinear
