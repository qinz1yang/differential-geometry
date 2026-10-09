/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLModelCellRestriction
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBallVocabulary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe v

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type v} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {tgtV tgtVBd : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {tgtE tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
  {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}

theorem exists_section34Compression_of_pl_model
    {u : E3 → M₂} {P : Set E3} (hu : IsPLHomeomorphInto 3 u P)
    (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦')
    {D J : Set E3} (hD : IsPLCellOn 2 D J) (hDP : D ⊆ P)
    (hDV : D ⊆ u ⁻¹' tgtVBd w) (hJF : J ⊆ u ⁻¹' fblBd s)
    (hDF : D ∩ u ⁻¹' fblBd s = J)
    (hDE : ∀ e : Section34EdgeIndex 𝒦 𝒦', Disjoint D (u ⁻¹' tgtE e))
    (hclean : ∀ t : Section34SimplexIndex 𝒦 3, t ≠ s →
      Disjoint (D \ J) (u ⁻¹' fbl t)) :
    Section34Compression 𝒦 𝒦' tgtVBd tgtE fbl fblBd s := by
  refine ⟨w, u '' D, u '' J, hD.image (hu.mono_of_model_cell hD hDP),
    image_subset_iff.mpr hDV, image_subset_iff.mpr hJF, ?_, ?_, ?_⟩
  · rw [← image_inter_preimage, hDF]
  · intro e
    exact disjoint_image_left.mpr (hDE e)
  · intro t hts
    apply Set.disjoint_left.mpr
    rintro _ ⟨⟨x, hxD, rfl⟩, hxJ⟩ hxF
    exact Set.disjoint_left.mp (hclean t hts)
      ⟨hxD, fun hx => hxJ ⟨x, hx, rfl⟩⟩ hxF

theorem exists_section34BigonSlide_of_pl_model
    {u : E3 → M₂} {P : Set E3} (hu : IsPLHomeomorphInto 3 u P)
    (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦')
    (e : Section34EdgeIndex 𝒦 𝒦') {B B' Bb D J : Set E3}
    (hB : IsPLCellOn 1 B Bb) (hBP : B ⊆ P)
    (hBF : B ⊆ u ⁻¹' fblBd s) (hBV : B ⊆ u ⁻¹' tgtVBd w)
    (hBbE : Bb ⊆ u ⁻¹' tgtEBd e)
    (hBE : B ∩ u ⁻¹' (⋃ d : Section34EdgeIndex 𝒦 𝒦', tgtE d) = Bb)
    (hB' : IsPLCellOn 1 B' Bb) (hB'P : B' ⊆ P) (hB'E : B' ⊆ u ⁻¹' tgtEBd e)
    (hBB' : B ∩ B' = Bb) (hD : IsPLCellOn 2 D J) (hDP : D ⊆ P)
    (hDN : D ⊆ u ⁻¹' (tgtVBd w ∩ frontier (⋃ v : Section34VertexIndex 𝒦 𝒦', tgtV v)))
    (hJ : J = B ∪ B')
    (hclean : ∀ t : Section34SimplexIndex 𝒦 3, Disjoint (D \ J) (u ⁻¹' fblBd t)) :
    Section34BigonSlide 𝒦 𝒦' tgtV tgtVBd tgtE tgtEBd fblBd s := by
  refine ⟨w, e, u '' B, u '' B', u '' Bb, u '' D, u '' J,
    hB.image (hu.mono_of_model_cell hB hBP), image_subset_iff.mpr hBF,
    image_subset_iff.mpr hBV, image_subset_iff.mpr hBbE, ?_,
    hB'.image (hu.mono_of_model_cell hB' hB'P), image_subset_iff.mpr hB'E, ?_,
    hD.image (hu.mono_of_model_cell hD hDP), image_subset_iff.mpr hDN, ?_, ?_⟩
  · rw [← image_inter_preimage, hBE]
  · apply Subset.antisymm
    · rintro _ ⟨⟨x, hx, rfl⟩, y, hy, hyx⟩
      have heq : y = x := hu.injOn (hB'P hy) (hBP hx) hyx
      subst y
      exact ⟨x, hBB'.subset ⟨hx, hy⟩, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      have h := hBB'.symm.subset hx
      exact ⟨⟨x, h.1, rfl⟩, ⟨x, h.2, rfl⟩⟩
  · rw [hJ, image_union]
  · intro t
    apply Set.disjoint_left.mpr
    rintro _ ⟨⟨x, hxD, rfl⟩, hxJ⟩ hxF
    exact Set.disjoint_left.mp (hclean t)
      ⟨hxD, fun hx => hxJ ⟨x, hx, rfl⟩⟩ hxF

end DifferentialGeometry.Topology.PiecewiseLinear
