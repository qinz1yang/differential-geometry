/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellPairExtension
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphIntoInverse

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M N : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]
  [MetricSpace N] [ChartedSpace E3 N]

theorem exists_comparison_map_of_cell_pair
    {P PB Q QB D J : Set M} {P' PB' Q' QB' D' : Set N}
    (hP : IsPLCellOn 3 P PB) (hQ : IsPLCellOn 3 Q QB)
    (hP' : IsPLCellOn 3 P' PB') (hQ' : IsPLCellOn 3 Q' QB')
    (hD : IsPLCellOn 2 D J) (hPQ : P ∩ Q = D) (hP'Q' : P' ∩ Q' = D')
    (hDP : D ⊆ PB) (hDQ : D ⊆ QB) (hDP' : D' ⊆ PB') (hDQ' : D' ⊆ QB')
    {f g : M → N} (hf : IsPLHomeomorphInto 3 f P) (hfim : f '' P = P')
    (hg : IsPLHomeomorphInto 3 g Q) (hgim : g '' Q = Q')
    (hfD : f '' D = D') (hgD : g '' D = D') :
    ∃ (T₁ T₂ : M → N) (K : N → N),
      IsPLHomeomorphInto 3 T₁ (P ∪ Q) ∧ IsPLHomeomorphInto 3 T₂ (P ∪ Q) ∧
      T₁ '' P = P' ∧ T₁ '' Q = Q' ∧ T₂ '' P = P' ∧ T₂ '' Q = Q' ∧
      EqOn T₁ f P ∧ EqOn T₂ g Q ∧
      IsPLHomeomorphInto 3 K (P' ∪ Q') ∧ K '' (P' ∪ Q') = P' ∪ Q' ∧
      K '' P' = P' ∧ K '' Q' = Q' ∧
      (∀ x ∈ P ∪ Q, K (T₂ x) = T₁ x) ∧ EqOn (K ∘ g) f D := by
  have : Nonempty M := ⟨hP.nonempty.choose⟩
  obtain ⟨T₁, hT₁, hT₁f, hT₁P, hT₁Q⟩ :=
    exists_isPLHomeomorphInto_cell_pair_extension hP hQ hP' hQ' hD hPQ hDQ hf hfim
      (hfD.trans hP'Q'.symm) (by rw [hP'Q']; exact hDQ')
  obtain ⟨T₂, hT₂, hT₂g, hT₂Q, hT₂P⟩ :=
    exists_isPLHomeomorphInto_cell_pair_extension hQ hP hQ' hP' hD
      (by rw [inter_comm]; exact hPQ) hDP hg hgim
      (by rw [inter_comm, hP'Q']; exact hgD) (by rw [inter_comm, hP'Q']; exact hDP')
  rw [union_comm Q P] at hT₂
  have hT₁im : T₁ '' (P ∪ Q) = P' ∪ Q' := by rw [image_union, hT₁P, hT₁Q]
  have hT₂im : T₂ '' (P ∪ Q) = P' ∪ Q' := by rw [image_union, hT₂P, hT₂Q]
  let I := Function.invFunOn T₂ (P ∪ Q)
  have hI : IsPLHomeomorphInto 3 I (P' ∪ Q') := hT₂im ▸ hT₂.invFunOn
  have hIbij : BijOn I (P' ∪ Q') (P ∪ Q) := by
    rw [← hT₂im]
    exact hT₂.injOn.bijOn_image.invOn_invFunOn.symm.bijOn
      hT₂.injOn.bijOn_image.surjOn.mapsTo_invFunOn hT₂.injOn.bijOn_image.mapsTo
  let K := T₁ ∘ I
  have hK : IsPLHomeomorphInto 3 K (P' ∪ Q') :=
    hI.comp_of_image_eq (by rw [hIbij.image_eq]; exact hT₁)
  have hKim : K '' (P' ∪ Q') = P' ∪ Q' := by
    rw [image_comp, hIbij.image_eq, hT₁im]
  have hIP : I '' P' = P := by
    rw [← hT₂P, ← image_comp]
    have hEq : EqOn (I ∘ T₂) id P := fun x hx =>
      hT₂.injOn.leftInvOn_invFunOn (Or.inl hx)
    exact hEq.image_eq.trans (image_id P)
  have hIQ : I '' Q' = Q := by
    rw [← hT₂Q, ← image_comp]
    have hEq : EqOn (I ∘ T₂) id Q := fun x hx =>
      hT₂.injOn.leftInvOn_invFunOn (Or.inr hx)
    exact hEq.image_eq.trans (image_id Q)
  have hKP : K '' P' = P' := by rw [image_comp, hIP, hT₁P]
  have hKQ : K '' Q' = Q' := by rw [image_comp, hIQ, hT₁Q]
  have hKT (x : M) (hx : x ∈ P ∪ Q) : K (T₂ x) = T₁ x := by
    change T₁ (Function.invFunOn T₂ (P ∪ Q) (T₂ x)) = T₁ x
    rw [hT₂.injOn.leftInvOn_invFunOn hx]
  refine ⟨T₁, T₂, K, hT₁, hT₂, hT₁P, hT₁Q, hT₂P, hT₂Q,
    hT₁f, hT₂g, hK, hKim, hKP, hKQ, hKT, ?_⟩
  intro x hx
  have hxP := hDP.trans hP.boundary_subset hx
  have hxQ := hDQ.trans hQ.boundary_subset hx
  have hEq := hKT x (Or.inl hxP)
  rw [hT₂g hxQ, hT₁f hxP] at hEq
  exact hEq

end DifferentialGeometry.Topology.PiecewiseLinear
