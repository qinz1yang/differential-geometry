/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldWithBoundary
import DifferentialGeometry.Topology.Attachment.Basic

/-! PL cell attachments with exact boundary traces and relative adjunction maps. -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open Classical in
def IsPLCellAttachment (n : ℕ) (P B : Set F) (L : Geometry.SimplicialComplex ℝ E)
    (C N : Set E) : Prop :=
  IsPLBall n P ∧ B ⊆ P ∧
    ∃ g : F → E, IsPLHomeomorphOn g P C ∧ IsPLHomeomorphOn g B (C ∩ L.space) ∧
      let A : Set P := {z | z.val ∈ B}
      ∃ φ : A → L.space, IsClosedEmbedding φ ∧
        (∀ z, (φ z : E) = g z.val.val) ∧
        (∀ z, (φ z : E) ∈ (boundaryComplex n L).space) ∧
        ∃ e : AdjunctionSpace (Subtype.val : A → P) φ ≃ₜ N,
          (∀ x, (e (adjunctionLower φ x) : E) = x) ∧
          ∀ z, (e (adjunctionCell Subtype.val φ z) : E) = g z.val

theorem IsPLCellAttachment.nonempty {n : ℕ} {P B : Set F}
    {L : Geometry.SimplicialComplex ℝ E} {C N : Set E}
    (h : IsPLCellAttachment n P B L C N) : C.Nonempty := by
  obtain ⟨hP, _, g, hg, _⟩ := h
  obtain ⟨x, hx⟩ := hP.nonempty
  exact ⟨g x, hg.bijOn.mapsTo hx⟩

theorem IsPLCellAttachment.cell_subset {n : ℕ} {P B : Set F}
    {L : Geometry.SimplicialComplex ℝ E} {C N : Set E}
    (h : IsPLCellAttachment n P B L C N) : C ⊆ N := by
  obtain ⟨_, _, g, hg, _, φ, _, _, _, e, _, he⟩ := h
  intro x hx
  obtain ⟨z, hz, rfl⟩ := hg.bijOn.surjOn hx
  exact he ⟨z, hz⟩ ▸ (e (adjunctionCell Subtype.val φ ⟨z, hz⟩)).property

theorem IsPLCellAttachment.lower_subset {n : ℕ} {P B : Set F}
    {L : Geometry.SimplicialComplex ℝ E} {C N : Set E}
    (h : IsPLCellAttachment n P B L C N) : L.space ⊆ N := by
  obtain ⟨_, _, _, _, _, φ, _, _, _, e, he, _⟩ := h
  intro x hx
  have hxe : (e (adjunctionLower φ ⟨x, hx⟩) : E) = x := he ⟨x, hx⟩
  exact hxe ▸ (e (adjunctionLower φ ⟨x, hx⟩)).property

open Classical in
def IsPLThreeHandleAttachment (k : Fin 4) (L : Geometry.SimplicialComplex ℝ E)
    (C N : Set E) : Prop :=
  match k.val with
  | 0 => IsPLCellAttachment 3 (stdSimplex ℝ (Fin 4)) ∅ L C N
  | 1 => IsPLCellAttachment 3 (stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1)
      (stdSimplex ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)) L C N
  | 2 => IsPLCellAttachment 3 (stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1)
      (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) L C N
  | _ => IsPLCellAttachment 3 (stdSimplex ℝ (Fin 4)) (stdSimplexBoundary 3) L C N

end DifferentialGeometry.Topology.PiecewiseLinear
