/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedBoundaryCollar
import Mathlib.Topology.Order.Compact

open Set Filter Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_open_bicollar_restriction {X : Type*} [TopologicalSpace X]
    {S W : Set X} (hS : IsCompact S) (ρ : S × Icc (-1 : ℝ) 1 ≃ₜ W)
    (hW : W ∈ 𝓝ˢ S)
    (hzero : ∀ x : S, (ρ (x, ⟨0, by norm_num⟩) : X) = x) :
    ∃ (ε : ℝ) (_ : 0 < ε) (hε1 : ε ≤ 1),
      IsOpenEmbedding (fun p : S × Ioo (-ε) ε =>
        (ρ (p.1, ⟨p.2, (neg_le_neg hε1).trans p.2.property.1.le,
          p.2.property.2.le.trans hε1⟩) : X)) := by
  let _ : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let f : S × Icc (-1 : ℝ) 1 → X := fun p => ρ p
  have hf : IsEmbedding f := IsEmbedding.subtypeVal.comp ρ.isEmbedding
  have hrange : range f = W := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact (ρ p).property
    · intro hx
      obtain ⟨p, hp⟩ := ρ.surjective ⟨x, hx⟩
      exact ⟨p, congrArg Subtype.val hp⟩
  let t₀ : Icc (-1 : ℝ) 1 := ⟨0, by norm_num⟩
  let G := f ⁻¹' interior W
  have hG : G ∈ (𝓝ˢ (univ : Set S)) ×ˢ 𝓝 t₀ := by
    apply isCompact_univ.mem_nhdsSet_prod_of_forall
    intro s _
    rw [← nhds_prod_eq]
    apply (isOpen_interior.preimage hf.continuous).mem_nhds
    change f (s, t₀) ∈ interior W
    rw [show f (s, t₀) = (s : X) from hzero s]
    exact subset_interior_iff_mem_nhdsSet.mpr hW s.property
  obtain ⟨A, hA, V, hV, hAV⟩ := mem_prod_iff.mp hG
  have hV' : V ∈ comap (Subtype.val : Icc (-1 : ℝ) 1 → ℝ) (𝓝 0) := by
    rw [show 𝓝 t₀ = comap (Subtype.val : Icc (-1 : ℝ) 1 → ℝ) (𝓝 0) from
      nhds_subtype_eq_comap] at hV
    exact hV
  obtain ⟨B, hB, hBV⟩ := mem_comap.mp hV'
  obtain ⟨δ, hδ, hδB⟩ := Metric.mem_nhds_iff.mp hB
  let ε := min 1 δ
  have hε : 0 < ε := lt_min zero_lt_one hδ
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεδ : ε ≤ δ := min_le_right _ _
  have hinterval : Ioo (-ε) ε ⊆ Icc (-1 : ℝ) 1 := fun t ht =>
    ⟨(neg_le_neg hε1).trans ht.1.le, ht.2.le.trans hε1⟩
  let j : Ioo (-ε) ε → Icc (-1 : ℝ) 1 := Set.inclusion hinterval
  have hj : IsOpenEmbedding j :=
    IsOpenEmbedding.inclusion hinterval (isOpen_Ioo.preimage continuous_subtype_val)
  let k : S × Ioo (-ε) ε → S × Icc (-1 : ℝ) 1 := Prod.map id j
  have hk : IsOpenEmbedding k := IsOpenEmbedding.id.prodMap hj
  have hkin (p : S × Ioo (-ε) ε) : f (k p) ∈ interior W := by
    apply hAV
    refine ⟨subset_of_mem_nhdsSet hA (mem_univ _), hBV (hδB ?_)⟩
    change dist (p.2 : ℝ) 0 < δ
    rw [Real.dist_eq, sub_zero, abs_lt]
    exact ⟨(neg_le_neg hεδ).trans_lt p.2.property.1, p.2.property.2.trans_le hεδ⟩
  have hopen : IsOpen (range (f ∘ k)) := by
    obtain ⟨O, hO, hOr⟩ := hf.isInducing.image_eq_isOpen_inter_range hk.isOpen_range
    have hsub : O ∩ range f ⊆ interior W := by
      rw [← hOr]
      rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
      exact hkin p
    have heq : O ∩ range f = O ∩ interior W := by
      rw [hrange] at hsub ⊢
      exact Subset.antisymm (fun _ hx => ⟨hx.1, hsub hx⟩)
        (inter_subset_inter_right _ interior_subset)
    rw [range_comp, hOr, heq]
    exact hO.inter isOpen_interior
  exact ⟨ε, hε, hε1, ⟨hf.comp hk.isEmbedding, hopen⟩⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_open_bicollar_glued₂_space_in_double
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (p : K.space) :
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K hK)
    let ι := simplicialMap K (glueEmbed₂ (boundaryComplex 3 K) id)
    let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
    ∀ U : Set (double 3 K).space, U ∈ 𝓝ˢ (frontier C) →
      ∃ (T : PLPiece 3 (double 3 K).space (frontier C)) (W : Set (double 3 K).space)
        (B : PLPieceIn ((EuclideanSpace ℝ (Fin T.ambientDim)) × ℝ) 3 (double 3 K).space W)
        (ε : ℝ), 0 < ε ∧ ε ≤ 1 ∧ W ⊆ U ∧
        IsCombinatorialManifold 2 T.piece.complex ∧
        B.complex.space = T.piece.complex.space ×ˢ Icc (-1 : ℝ) 1 ∧
        IsOpenEmbedding (fun z : T.piece.complex.space × Ioo (-ε) ε => B.map (z.1, z.2)) ∧
        (∀ x : T.piece.complex.space, B.map (x, 0) = T.piece.map x) ∧
        ∀ (x : T.piece.complex.space) (t : ℝ), t ∈ Icc (-1 : ℝ) 1 →
          (B.map (x, t) ∈ frontier C ↔ t = 0) := by
  classical
  let _ := combinatorialChartedSpace (double 3 K)
    (isCombinatorialManifold_double_succ_succ K hK)
  let ι := simplicialMap K (glueEmbed₂ (boundaryComplex 3 K) id)
  let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
  change ∀ U : Set (double 3 K).space, U ∈ 𝓝ˢ (frontier C) → _
  intro U hU
  obtain ⟨-, hBd, -, hcollar⟩ := exists_bicollar_glued₂_space_in_double K hK p
  obtain ⟨T, W, B, ρ, hWU, hW, hB, hρ, hcenter⟩ := hcollar U hU
  obtain ⟨ε, hε, hε1, hopen⟩ := exists_open_bicollar_restriction hBd.isCompact ρ hW hcenter
  let σ : (frontier C) × Ioo (-ε) ε → (double 3 K).space := fun z =>
    ρ (z.1, ⟨z.2, (neg_le_neg hε1).trans z.2.property.1.le,
      z.2.property.2.le.trans hε1⟩)
  have hσ : IsOpenEmbedding σ := hopen
  let d := T.piece.homeomorph.prodCongr (Homeomorph.refl (Ioo (-ε) ε))
  have hfun : σ ∘ d = (fun z : T.piece.complex.space × Ioo (-ε) ε => B.map (z.1, z.2)) := by
    funext z
    exact hρ z.1 ⟨z.2, (neg_le_neg hε1).trans z.2.property.1.le,
      z.2.property.2.le.trans hε1⟩
  have hBcenter (x : T.piece.complex.space) : B.map (x, 0) = T.piece.map x :=
    (hρ x ⟨0, by norm_num⟩).symm.trans (hcenter ⟨T.piece.map x, T.piece.bijOn.mapsTo x.property⟩)
  refine ⟨T, W, B, ε, hε, hε1, hWU,
    hBd.isCombinatorialManifold_of_piece T, hB, ?_, hBcenter, ?_⟩
  · have h := hσ.comp d.isOpenEmbedding
    rwa [hfun] at h
  · intro x t ht
    constructor
    · intro hx
      obtain ⟨u, hu, heq⟩ := T.piece.bijOn.surjOn hx
      have hxt : ((x : EuclideanSpace ℝ (Fin T.ambientDim)), t) ∈ B.complex.space := by
        rw [hB]
        exact ⟨x.property, ht⟩
      have hu0 : (u, (0 : ℝ)) ∈ B.complex.space := by
        rw [hB]
        exact ⟨hu, by norm_num⟩
      have h := B.bijOn.injOn hxt hu0 (heq.symm.trans (hBcenter ⟨u, hu⟩).symm)
      exact congrArg Prod.snd h
    · rintro rfl
      rw [hBcenter]
      exact T.piece.bijOn.mapsTo x.property

end DifferentialGeometry.Topology.PiecewiseLinear
