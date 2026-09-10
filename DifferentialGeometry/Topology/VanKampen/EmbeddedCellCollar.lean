/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.Handle.Manifold
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.LocalAtTarget
import DifferentialGeometry.Topology.LocallyPathConnected
import DifferentialGeometry.Topology.VanKampen.EmbeddedCell

set_option autoImplicit false

open Filter Set Topology
open scoped Manifold ContDiff

noncomputable section

universe u

namespace Poincare.Topology.ThreeManifold

open DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Handle

structure TwoSidedCellCollar {M : Type u} [TopologicalSpace M]
    (c : ClosedCell 3 → M) where

  toFun : CellBoundary 3 × ℝ → M

  isOpenEmbedding_toFun : IsOpenEmbedding toFun

  zero_eq : ∀ b, toFun (b, 0) = c (cellBoundaryInclusion 3 b)

  mem_complement_iff : ∀ p,
    toFun p ∈ embeddedCellComplement c ↔ 0 ≤ p.2

namespace TwoSidedCellCollar

variable {M : Type u} [TopologicalSpace M] {c : ClosedCell 3 → M}


def complementMap (h : TwoSidedCellCollar c) :
    h.toFun ⁻¹' embeddedCellComplement c → embeddedCellComplement c :=
  (embeddedCellComplement c).restrictPreimage h.toFun


theorem isOpenEmbedding_complementMap (h : TwoSidedCellCollar c) :
    IsOpenEmbedding h.complementMap :=
  h.isOpenEmbedding_toFun.restrictPreimage (embeddedCellComplement c)


theorem preimage_complement (h : TwoSidedCellCollar c) :
    h.toFun ⁻¹' embeddedCellComplement c =
      (Set.univ : Set (CellBoundary 3)) ×ˢ Set.Ici (0 : ℝ) := by
  ext p
  simp only [mem_preimage, mem_prod, mem_univ, true_and, mem_Ici]
  exact h.mem_complement_iff p


theorem locallyPathConnectedSpace_complementPreimage (h : TwoSidedCellCollar c) :
    LocallyPathConnectedSpace (h.toFun ⁻¹' embeddedCellComplement c) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) (CellBoundary 3) :=
    cellBoundaryChartedSpace 3
  let _ : LocallyPathConnectedSpace (CellBoundary 3) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) (CellBoundary 3)
  let _ : LocallyPathConnectedSpace (Set.Ici (0 : ℝ)) :=
    (convex_Ici (0 : ℝ)).locallyPathConnectedSpace
  let e : (h.toFun ⁻¹' embeddedCellComplement c) ≃ₜ
      CellBoundary 3 × Set.Ici (0 : ℝ) :=
    (Homeomorph.setCongr h.preimage_complement).trans
      ((Homeomorph.Set.prod Set.univ (Set.Ici (0 : ℝ))).trans
        ((Homeomorph.Set.univ (CellBoundary 3)).prodCongr
          (Homeomorph.refl (Set.Ici (0 : ℝ)))))
  exact e.isOpenEmbedding.locallyPathConnectedSpace


theorem locallyPathConnectedSpace_range_complementMap (h : TwoSidedCellCollar c) :
    LocallyPathConnectedSpace (Set.range h.complementMap) := by
  let _ : LocallyPathConnectedSpace (h.toFun ⁻¹' embeddedCellComplement c) :=
    h.locallyPathConnectedSpace_complementPreimage
  let e : (h.toFun ⁻¹' embeddedCellComplement c) ≃ₜ Set.range h.complementMap :=
    (Homeomorph.Set.univ _).symm.trans
      ((h.isOpenEmbedding_complementMap.toIsEmbedding.homeomorphImage Set.univ).trans
        (Homeomorph.setCongr (by simp)))
  exact e.symm.isOpenEmbedding.locallyPathConnectedSpace

end TwoSidedCellCollar


def embeddedCellExterior {M : Type u} (c : ClosedCell 3 → M) :
    Set (embeddedCellComplement c) :=
  Subtype.val ⁻¹' (Set.range c)ᶜ

def embeddedCellExteriorHomeomorph {M : Type u} [TopologicalSpace M]
    (c : ClosedCell 3 → M) :
    embeddedCellExterior c ≃ₜ ((Set.range c)ᶜ : Set M) where
  toFun q := ⟨q.1.1, q.2⟩
  invFun q := ⟨⟨q.1, by
    intro hq
    exact q.2 ⟨Classical.choose hq, Classical.choose_spec hq |>.2⟩⟩, q.2⟩
  left_inv q := rfl
  right_inv q := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _


theorem isOpen_embeddedCellExterior {M : Type u} [TopologicalSpace M] [T2Space M]
    (c : ClosedCell 3 → M) (hcont : Continuous c) :
    IsOpen (embeddedCellExterior c) := by
  apply continuous_subtype_val.isOpen_preimage
  exact (isCompact_range hcont).isClosed.isOpen_compl


theorem locallyPathConnectedSpace_embeddedCellExterior
    {M : Type u} [TopologicalSpace M] [T2Space M] [LocallyPathConnectedSpace M]
    (c : ClosedCell 3 → M) (hcont : Continuous c) :
    LocallyPathConnectedSpace (embeddedCellExterior c) := by
  let _ : LocallyPathConnectedSpace ((Set.range c)ᶜ : Set M) :=
    (isCompact_range hcont).isClosed.isOpen_compl.locallyPathConnectedSpace
  exact (embeddedCellExteriorHomeomorph c).isOpenEmbedding.locallyPathConnectedSpace


theorem locallyPathConnectedSpace_embeddedCellComplement_of_twoSidedCellCollar
    {M : Type u} [TopologicalSpace M] [T2Space M] [LocallyPathConnectedSpace M]
    (c : ClosedCell 3 → M) (hcont : Continuous c)
    (hcollar : TwoSidedCellCollar c) :
    LocallyPathConnectedSpace (embeddedCellComplement c) := by
  let U : Bool → Set (embeddedCellComplement c)
    | false => embeddedCellExterior c
    | true => Set.range hcollar.complementMap
  apply Poincare.Topology.locallyPathConnectedSpace_of_openCover U
  · intro i
    cases i with
    | false => exact isOpen_embeddedCellExterior c hcont
    | true => exact hcollar.isOpenEmbedding_complementMap.isOpen_range
  · intro q
    by_cases hq : (q : M) ∈ Set.range c
    · rcases hq with ⟨d, hd⟩
      have hdK : c d ∈ embeddedCellComplement c := by
        rw [hd]
        exact q.2
      rcases cellBoundary_of_image_mem_embeddedCellComplement c d hdK with ⟨b, hb⟩
      refine ⟨true, ?_⟩
      change q ∈ Set.range hcollar.complementMap
      let p : CellBoundary 3 × ℝ := (b, 0)
      have hpK : hcollar.toFun p ∈ embeddedCellComplement c :=
        (hcollar.mem_complement_iff p).mpr (by simp [p])
      refine ⟨⟨p, hpK⟩, Subtype.ext ?_⟩
      change hcollar.toFun (b, 0) = (q : M)
      rw [hcollar.zero_eq, hb, hd]
    · exact ⟨false, hq⟩
  · intro i
    cases i with
    | false => exact locallyPathConnectedSpace_embeddedCellExterior c hcont
    | true => exact hcollar.locallyPathConnectedSpace_range_complementMap

theorem pathConnectedSpace_embeddedCellComplement_of_smoothEmbedding_of_twoSidedCellCollar
    {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (c : ClosedCell 3 → M) (hc : Function.Injective c) (hcont : Continuous c)
    (hsmooth : Manifold.IsSmoothEmbedding
      𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (embeddedCellInteriorMap c))
    (hcollar : TwoSidedCellCollar c) :
    PathConnectedSpace (embeddedCellComplement c) := by
  let _ : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let _ : LocallyPathConnectedSpace (embeddedCellComplement c) :=
    locallyPathConnectedSpace_embeddedCellComplement_of_twoSidedCellCollar
      c hcont hcollar
  exact pathConnectedSpace_embeddedCellComplement c hc hcont
    (isOpen_embeddedCellInteriorImage_of_isSmoothEmbedding c hsmooth)

noncomputable def fundamentalGroupEmbeddedCellComplementEquivOfSmoothEmbeddingOfCollar
    {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (c : ClosedCell 3 → M) (hc : Function.Injective c) (hcont : Continuous c)
    (hsmooth : Manifold.IsSmoothEmbedding
      𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (embeddedCellInteriorMap c))
    (hcollar : TwoSidedCellCollar c) (x : embeddedCellComplement c) :
    FundamentalGroup (embeddedCellComplement c) x ≃* FundamentalGroup M (x : M) := by
  let _ : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let _ : LocallyPathConnectedSpace (embeddedCellComplement c) :=
    locallyPathConnectedSpace_embeddedCellComplement_of_twoSidedCellCollar
      c hcont hcollar
  exact fundamentalGroupEmbeddedCellComplementEquivOfSmoothEmbedding c hc hcont hsmooth x


theorem fundamentalGroupEmbeddedCellComplementEquivOfSmoothEmbeddingOfCollar_toMonoidHom
    {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (c : ClosedCell 3 → M) (hc : Function.Injective c) (hcont : Continuous c)
    (hsmooth : Manifold.IsSmoothEmbedding
      𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (embeddedCellInteriorMap c))
    (hcollar : TwoSidedCellCollar c) (x : embeddedCellComplement c) :
    (↑(fundamentalGroupEmbeddedCellComplementEquivOfSmoothEmbeddingOfCollar
        c hc hcont hsmooth hcollar x) :
      FundamentalGroup (embeddedCellComplement c) x →* FundamentalGroup M (x : M)) =
      FundamentalGroup.map (embeddedCellComplementInclusion c) x := by
  rfl

end Poincare.Topology.ThreeManifold
