/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallPairHalfSpaceChart
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellPairExtension
import DifferentialGeometry.Topology.PiecewiseLinear.CompactEmbeddingApproximation
import DifferentialGeometry.Topology.Manifold.EmbeddingLocalHomeomorph

open Set
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]
  [HasGroupoid M (plGroupoid 3)]

theorem exists_halfspace_chart_of_cell_pair
    {C₁ B₁ C₂ B₂ D J : Set M}
    (h₁ : IsPLCellOn 3 C₁ B₁) (h₂ : IsPLCellOn 3 C₂ B₂)
    (hD : IsPLCellOn 2 D J) (hmeet : C₁ ∩ C₂ = D)
    (hD₁ : D ⊆ B₁) (hD₂ : D ⊆ B₂) :
    ∃ e : OpenPartialHomeomorph M (Plane × ℝ),
      D \ J ⊆ e.source ∧ e.source ⊆ interior (C₁ ∪ C₂) ∧
      (∀ x ∈ e.source, x ∈ C₁ ↔ 0 ≤ (e x).2) ∧
      (∀ x ∈ e.source, x ∈ C₂ ↔ (e x).2 ≤ 0) ∧
      ∀ x ∈ e.source, x ∈ D ↔ (e x).2 = 0 := by
  obtain ⟨P, Q, hP, hQ, -, hI, hIP, hIQ, F, hF, hFP, hFQ, hFD⟩ :=
    exists_isPLHomeomorphInto_ball_pair_of_cell_pair h₁ h₂ hD hmeet hD₁ hD₂
  obtain ⟨r, hr⟩ := id hI
  have hIK : P ∩ Q ⊆ P ∪ Q := inter_subset_left.trans subset_union_left
  have hFI : IsPLHomeomorphInto 3 F (P ∩ Q) :=
    IsPLOn.isPLHomeomorphInto (hF.isPLOn.mono_of_isPolyhedron hI.isPolyhedron hIK)
      hI.isPolyhedron.isCompact (hF.injOn.mono hIK)
  have hFJ : F '' (r '' stdSimplexBoundary 2) = J := by
    have himage := (isPLCellOn_id_of_isPLBall hr).image hFI
    rw [hFD] at himage
    exact himage.boundary_eq hD
  obtain ⟨c, hcD, hcsub, hcP, hcQ, -⟩ :=
    exists_halfspace_chart_of_ball_pair hP hQ hr rfl hIP hIQ
  obtain ⟨H, hHs, hHt, hH⟩ := exists_openPartialHomeomorph_of_continuousOn_injOn
    (E := E3) isOpen_interior (hF.continuousOn.mono interior_subset)
      (hF.injOn.mono interior_subset)
  have hHt' : H.target = interior (C₁ ∪ C₂) := by
    rw [hHt, hF.image_interior, image_union, hFP, hFQ]
  let e := H.symm ≫ₕ c
  have hsource : D \ J ⊆ e.source := by
    intro x hx
    obtain ⟨p, hp, hpx⟩ := hFD.symm.subset hx.1
    have hpJ : p ∉ r '' stdSimplexBoundary 2 := by
      intro hpJ
      have hxJ : F p ∈ J := hFJ ▸ mem_image_of_mem F hpJ
      exact hx.2 (hpx ▸ hxJ)
    have hpc : p ∈ c.source := hcD ⟨hp, hpJ⟩
    have hpH : p ∈ H.source := hHs ▸ hcsub hpc
    have hHx : H p = x := (hH p).trans hpx
    have hxHt : x ∈ H.target := hHx ▸ H.map_source hpH
    have hsymm : H.symm x = p := by rw [← hHx, H.left_inv hpH]
    exact ⟨hxHt, by change H.symm x ∈ c.source; rw [hsymm]; exact hpc⟩
  have hmem {T : Set E3} (hT : T ⊆ P ∪ Q) (y : M) (hy : y ∈ H.target) :
      y ∈ F '' T ↔ H.symm y ∈ T := by
    have hp : H.symm y ∈ P ∪ Q := interior_subset (hHs ▸ H.map_target hy)
    have hFy : F (H.symm y) = y := (hH _).symm.trans (H.right_inv hy)
    constructor
    · rintro ⟨p, hpT, hpy⟩
      have hpeq : p = H.symm y := hF.injOn (hT hpT) hp (hpy.trans hFy.symm)
      exact hpeq ▸ hpT
    · intro hpT
      exact ⟨H.symm y, hpT, hFy⟩
  have hside₁ (x : M) (hx : x ∈ e.source) : x ∈ C₁ ↔ 0 ≤ (e x).2 := by
    rw [← hFP, hmem subset_union_left x hx.1]
    exact hcP (H.symm x) hx.2
  have hside₂ (x : M) (hx : x ∈ e.source) : x ∈ C₂ ↔ (e x).2 ≤ 0 := by
    rw [← hFQ, hmem subset_union_right x hx.1]
    exact hcQ (H.symm x) hx.2
  refine ⟨e, hsource, fun _ hx => hHt' ▸ hx.1, hside₁, hside₂, ?_⟩
  intro x hx
  rw [← hmeet, mem_inter_iff, hside₁ x hx, hside₂ x hx]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
