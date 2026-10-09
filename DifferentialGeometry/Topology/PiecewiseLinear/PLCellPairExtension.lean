/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellDiskExtension
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellPairMap
import DifferentialGeometry.Topology.PiecewiseLinear.BallGluing
import DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphIntoMonoOfIsPLCellOn

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Pasting

variable {n : ℕ} {M N : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]

theorem exists_isPLHomeomorphInto_union_of_closed_pieces
    {P Q : Set M} {P' Q' : Set N} {f g : M → N}
    (hP : IsClosed P) (hQ : IsClosed Q) (hP' : IsClosed P') (hQ' : IsClosed Q')
    (hf : IsPLHomeomorphInto n f P) (hfim : f '' P = P')
    (hg : IsPLHomeomorphInto n g Q) (hgim : g '' Q = Q')
    (hfg : EqOn f g (P ∩ Q)) (hmeet : f '' (P ∩ Q) = P' ∩ Q') :
    ∃ F : M → N, IsPLHomeomorphInto n F (P ∪ Q) ∧
      EqOn F f P ∧ EqOn F g Q ∧ F '' (P ∪ Q) = P' ∪ Q' := by
  obtain ⟨F, hF, hFf, hFg, hFim⟩ :=
    exists_isPLHomeomorphInto_union_of_locallyFinite_pieces
      (S := fun _ : Unit => Q) (T := fun _ : Unit => Q')
      (f := fun _ : Unit => g) hP hP' (fun _ => hQ) (fun _ => hQ') hf hfim
      (fun _ => hg) (fun _ => hgim) (fun _ => hfg) (fun _ => hmeet)
      (fun _ _ _ _ => rfl) (fun _ _ => by simpa only [inter_self] using hgim)
      (fun _ _ => ⟨univ, Filter.univ_mem, Set.toFinite _⟩)
      (fun _ _ => ⟨univ, Filter.univ_mem, Set.toFinite _⟩)
  exact ⟨F, by simpa only [iUnion_const] using hF, hFf, hFg (),
    by simpa only [iUnion_const] using hFim⟩

end Pasting

variable {M₁ M₂ : Type*} [TopologicalSpace M₁] [T2Space M₁] [ChartedSpace E3 M₁]
  [TopologicalSpace M₂] [T2Space M₂] [ChartedSpace E3 M₂]

theorem exists_isPLHomeomorphInto_cell_pair_of_disk_map
    {P PB Q QB D J : Set M₁} {P' PB' Q' QB' : Set M₂}
    (hP : IsPLCellOn 3 P PB) (hQ : IsPLCellOn 3 Q QB)
    (hP' : IsPLCellOn 3 P' PB') (hQ' : IsPLCellOn 3 Q' QB')
    (hD : IsPLCellOn 2 D J) (hPQ : P ∩ Q = D)
    (hDP : D ⊆ PB) (hDQ : D ⊆ QB)
    {g : M₁ → M₂} (hg : IsPLHomeomorphInto 3 g D)
    (himage : g '' D = P' ∩ Q')
    (hDP' : P' ∩ Q' ⊆ PB') (hDQ' : P' ∩ Q' ⊆ QB') :
    ∃ F : M₁ → M₂, IsPLHomeomorphInto 3 F (P ∪ Q) ∧
      F '' P = P' ∧ F '' Q = Q' ∧ EqOn F g D := by
  obtain ⟨f₁, hf₁, hf₁im, hf₁g⟩ := exists_isPLHomeomorphInto_extension_of_boundary_disk
    hP hP' hD hDP hg (himage ▸ hDP')
  obtain ⟨f₂, hf₂, hf₂im, hf₂g⟩ := exists_isPLHomeomorphInto_extension_of_boundary_disk
    hQ hQ' hD hDQ hg (himage ▸ hDQ')
  have hfg : EqOn f₁ f₂ (P ∩ Q) := hPQ ▸ hf₁g.trans hf₂g.symm
  have hmeet : f₁ '' (P ∩ Q) = P' ∩ Q' := by rw [hPQ, hf₁g.image_eq, himage]
  obtain ⟨F, hF, hF₁, hF₂, -⟩ := exists_isPLHomeomorphInto_union_of_closed_pieces
    hP.isCompact.isClosed hQ.isCompact.isClosed hP'.isCompact.isClosed hQ'.isCompact.isClosed
    hf₁ hf₁im hf₂ hf₂im hfg hmeet
  exact ⟨F, hF, hF₁.image_eq.trans hf₁im, hF₂.image_eq.trans hf₂im,
    (hF₁.mono (hDP.trans hP.boundary_subset)).trans hf₁g⟩

omit [TopologicalSpace M₂] [T2Space M₂] [ChartedSpace E3 M₂] in
theorem exists_isPLHomeomorphInto_ball_pair_of_cell_pair
    {C₁ B₁ C₂ B₂ D J : Set M₁}
    (h₁ : IsPLCellOn 3 C₁ B₁) (h₂ : IsPLCellOn 3 C₂ B₂)
    (hD : IsPLCellOn 2 D J) (hmeet : C₁ ∩ C₂ = D)
    (hD₁ : D ⊆ B₁) (hD₂ : D ⊆ B₂) :
    ∃ P Q : Set E3, IsPLBall 3 P ∧ IsPLBall 3 Q ∧ IsPLBall 3 (P ∪ Q) ∧
      IsPLBall 2 (P ∩ Q) ∧ P ∩ Q ⊆ frontier P ∧ P ∩ Q ⊆ frontier Q ∧
      ∃ F : E3 → M₁, IsPLHomeomorphInto 3 F (P ∪ Q) ∧
        F '' P = C₁ ∧ F '' Q = C₂ ∧ F '' (P ∩ Q) = D := by
  obtain ⟨P, Q, hP, hQ, hPQ, hI, hIP, hIQ⟩ := exists_isPLBall_pair_with_disk_inter
  obtain ⟨r, hr⟩ := hP
  obtain ⟨s, hs⟩ := hQ
  obtain ⟨t, ht⟩ := hI
  have hPc := isPLCellOn_id_of_isPLBall hr
  have hQc := isPLCellOn_id_of_isPLBall hs
  have hIc := isPLCellOn_id_of_isPLBall ht
  have hIP' : P ∩ Q ⊆ r '' stdSimplexBoundary 3 := by
    rw [IsPLHomeomorphOn.image_stdSimplexBoundary (n := 2) hr]
    exact hIP
  have hIQ' : P ∩ Q ⊆ s '' stdSimplexBoundary 3 := by
    rw [IsPLHomeomorphOn.image_stdSimplexBoundary (n := 2) hs]
    exact hIQ
  obtain ⟨g, hg, hgim, -⟩ := exists_isPLHomeomorphInto_cells hIc hD
  obtain ⟨F, hF, hFP, hFQ, hFg⟩ := exists_isPLHomeomorphInto_cell_pair_of_disk_map
    hPc hQc h₁ h₂ hIc rfl hIP' hIQ' hg (hgim.trans hmeet.symm)
    (hmeet ▸ hD₁) (hmeet ▸ hD₂)
  exact ⟨P, Q, ⟨r, hr⟩, ⟨s, hs⟩, hPQ, ⟨t, ht⟩, hIP, hIQ, F, hF, hFP, hFQ,
    hFg.image_eq.trans hgim⟩

universe u

theorem exists_isPLHomeomorphInto_cell_pair_extension
    {N₁ N₂ : Type u} [TopologicalSpace N₁] [T2Space N₁] [ChartedSpace E3 N₁]
    [MetricSpace N₂] [ChartedSpace E3 N₂]
    {P PB Q QB D J : Set N₁} {P' PB' Q' QB' : Set N₂}
    (hP : IsPLCellOn 3 P PB) (hQ : IsPLCellOn 3 Q QB)
    (hP' : IsPLCellOn 3 P' PB') (hQ' : IsPLCellOn 3 Q' QB')
    (hD : IsPLCellOn 2 D J) (hPQ : P ∩ Q = D) (hDQ : D ⊆ QB)
    {f : N₁ → N₂} (hf : IsPLHomeomorphInto 3 f P) (hfim : f '' P = P')
    (himage : f '' D = P' ∩ Q') (hDQ' : P' ∩ Q' ⊆ QB') :
    ∃ F : N₁ → N₂, IsPLHomeomorphInto 3 F (P ∪ Q) ∧
      EqOn F f P ∧ F '' P = P' ∧ F '' Q = Q' := by
  have hDP : D ⊆ P := hPQ ▸ inter_subset_left
  have hfD := hf.mono_of_isPLCellOn hD hDP
  obtain ⟨g, hg, hgim, hgf⟩ := exists_isPLHomeomorphInto_extension_of_boundary_disk
    hQ hQ' hD hDQ hfD (himage ▸ hDQ')
  have hfg : EqOn f g (P ∩ Q) := hPQ ▸ hgf.symm
  have hmeet : f '' (P ∩ Q) = P' ∩ Q' := by rw [hPQ, himage]
  obtain ⟨F, hF, hFf, hFg, -⟩ := exists_isPLHomeomorphInto_union_of_closed_pieces
    hP.isCompact.isClosed hQ.isCompact.isClosed hP'.isCompact.isClosed hQ'.isCompact.isClosed
    hf hfim hg hgim hfg hmeet
  exact ⟨F, hF, hFf, hFf.image_eq.trans hfim, hFg.image_eq.trans hgim⟩
omit [TopologicalSpace M₂] [T2Space M₂] [ChartedSpace E3 M₂] in
theorem isPLCellOn_union_of_inter_eq_disk
    {C₁ B₁ C₂ B₂ D J : Set M₁}
    (h₁ : IsPLCellOn 3 C₁ B₁) (h₂ : IsPLCellOn 3 C₂ B₂)
    (hD : IsPLCellOn 2 D J) (hmeet : C₁ ∩ C₂ = D)
    (hD₁ : D ⊆ B₁) (hD₂ : D ⊆ B₂) :
    IsPLCellOn 3 (C₁ ∪ C₂) (frontier (C₁ ∪ C₂)) := by
  obtain ⟨P, Q, -, -, hPQ, -, -, -, F, hF, hFP, hFQ, -⟩ :=
    exists_isPLHomeomorphInto_ball_pair_of_cell_pair h₁ h₂ hD hmeet hD₁ hD₂
  obtain ⟨r, hr⟩ := hPQ
  have hc := (isPLCellOn_id_of_isPLBall hr).image hF
  rw [image_union, hFP, hFQ] at hc
  exact hc.boundary_eq_frontier ▸ hc
end DifferentialGeometry.Topology.PiecewiseLinear
