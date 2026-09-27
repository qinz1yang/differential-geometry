/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import
  DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceTwistedSingularSet
import DifferentialGeometry.Topology.PiecewiseLinear.NormalCrossingTransport

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private noncomputable def crossingCoordinates : halfTurnQuotient → (ℝ × ℝ) × ℝ :=
  twistedTubeLift.symm ∘ spliceEmbedding.symm ∘ halfTurnSlabChart 0

private noncomputable def normalizedStripMap : (ℝ × ℝ) → (ℝ × ℝ) × ℝ :=
  crossingCoordinates ∘ twistedStripMap

private def stripSheet (l u : ℝ) : Set (ℝ × ℝ) := Icc l u ×ˢ Icc (0 : ℝ) 1

private theorem crossingCoordinates_tube {p : (ℝ × ℝ) × ℝ} (hp : p ∈ spliceCylinder) :
    crossingCoordinates (twistedTubeChart p) = p := by
  have hsq := mem_spliceSquare.mp hp.1
  have hb : (twistedTubeLift p).1.1 ∈ Ioo (0 - 1 / 4) (0 + 1 / 4) := by
    change 0 - 1 / 4 < (p.1.1 - p.1.2) / 16 ∧
      (p.1.1 - p.1.2) / 16 < 0 + 1 / 4
    constructor <;> linarith [hsq.1.1, hsq.1.2, hsq.2.1, hsq.2.2]
  change twistedTubeLift.symm (spliceEmbedding.symm
    (halfTurnSlabChart 0 (halfTurnProjection (twistedTubeLift p)))) = p
  rw [halfTurnSlabChart_apply hb, ContinuousLinearEquiv.symm_apply_apply,
    Homeomorph.symm_apply_apply]

private theorem first_sheet_tube {p : ℝ × ℝ} (hp : p ∈ stripSheet (-1 / 16) (1 / 16)) :
    ((16 * p.1, 0), p.2) ∈ spliceCylinder ∧
      twistedTubeChart ((16 * p.1, 0), p.2) = twistedStripMap p := by
  refine ⟨⟨mem_spliceSquare.mpr ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
    by norm_num, by norm_num⟩, hp.2⟩, ?_⟩
  rw [twistedTubeChart_horizontal]
  congr 1
  ext <;> dsimp; ring

private theorem second_sheet_tube {p : ℝ × ℝ} (hp : p ∈ stripSheet (15 / 16) (17 / 16)) :
    ((0, 16 * (1 - p.1)), 1 - p.2) ∈ spliceCylinder ∧
      twistedTubeChart ((0, 16 * (1 - p.1)), 1 - p.2) = twistedStripMap p := by
  refine ⟨⟨mem_spliceSquare.mpr ⟨⟨by norm_num, by norm_num⟩,
    by linarith [hp.1.2], by linarith [hp.1.1]⟩,
      ⟨by linarith [hp.2.2], by linarith [hp.2.1]⟩⟩, ?_⟩
  rw [twistedTubeChart_vertical]
  congr 1
  ext <;> dsimp <;> ring

private theorem normalizedStripMap_first {p : ℝ × ℝ}
    (hp : p ∈ stripSheet (-1 / 16) (1 / 16)) :
    normalizedStripMap p = ((16 * p.1, 0), p.2) := by
  obtain ⟨hc, hv⟩ := first_sheet_tube hp
  change crossingCoordinates (twistedStripMap p) = _
  rw [← hv]
  exact crossingCoordinates_tube hc

private theorem normalizedStripMap_second {p : ℝ × ℝ}
    (hp : p ∈ stripSheet (15 / 16) (17 / 16)) :
    normalizedStripMap p = ((0, 16 * (1 - p.1)), 1 - p.2) := by
  obtain ⟨hc, hv⟩ := second_sheet_tube hp
  change crossingCoordinates (twistedStripMap p) = _
  rw [← hv]
  exact crossingCoordinates_tube hc

private theorem first_sheet_plhomeomorph :
    IsPLHomeomorphOn normalizedStripMap (stripSheet (-1 / 16) (1 / 16))
      (normalizedStripMap '' stripSheet (-1 / 16) (1 / 16)) := by
  let A : (ℝ × ℝ) →ᵃ[ℝ] ((ℝ × ℝ) × ℝ) :=
    (((16 : ℝ) • (LinearMap.fst ℝ ℝ ℝ).toAffineMap).prod
      (AffineMap.const ℝ _ 0)).prod (LinearMap.snd ℝ ℝ ℝ).toAffineMap
  have hpoly : IsPolyhedron (stripSheet (-1 / 16) (1 / 16)) :=
    (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron
  have hpa := (isPiecewiseAffineOn_of_affine A isOpen_univ).mono_of_isPolyhedron
    hpoly (subset_univ _)
  refine isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hpoly
    (hpa.congr fun p hp => normalizedStripMap_first hp) (InjOn.bijOn_image ?_)
  intro p hp q hq heq
  rw [normalizedStripMap_first hp, normalizedStripMap_first hq] at heq
  have hx := congrArg (fun z : (ℝ × ℝ) × ℝ => z.1.1) heq
  have ht := congrArg Prod.snd heq
  exact Prod.ext (by dsimp at hx; linarith) ht

private theorem second_sheet_plhomeomorph :
    IsPLHomeomorphOn normalizedStripMap (stripSheet (15 / 16) (17 / 16))
      (normalizedStripMap '' stripSheet (15 / 16) (17 / 16)) := by
  let A : (ℝ × ℝ) →ᵃ[ℝ] ((ℝ × ℝ) × ℝ) :=
    ((AffineMap.const ℝ _ 0).prod
      ((16 : ℝ) • (AffineMap.const ℝ _ 1 - (LinearMap.fst ℝ ℝ ℝ).toAffineMap))).prod
        (AffineMap.const ℝ _ 1 - (LinearMap.snd ℝ ℝ ℝ).toAffineMap)
  have hpoly : IsPolyhedron (stripSheet (15 / 16) (17 / 16)) :=
    (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron
  have hpa := (isPiecewiseAffineOn_of_affine A isOpen_univ).mono_of_isPolyhedron
    hpoly (subset_univ _)
  refine isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hpoly
    (hpa.congr fun p hp => normalizedStripMap_second hp) (InjOn.bijOn_image ?_)
  intro p hp q hq heq
  rw [normalizedStripMap_second hp, normalizedStripMap_second hq] at heq
  have hx := congrArg (fun z : (ℝ × ℝ) × ℝ => z.1.2) heq
  have ht := congrArg Prod.snd heq
  exact Prod.ext (by dsimp at hx; linarith) (by dsimp at ht; linarith)

private theorem first_sheet_image :
    normalizedStripMap '' stripSheet (-1 / 16) (1 / 16) =
      (Icc (-1 : ℝ) 1 ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1 := by
  ext ⟨⟨x, y⟩, t⟩
  constructor
  · rintro ⟨p, hp, heq⟩
    rw [normalizedStripMap_first hp] at heq
    cases heq
    exact ⟨⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, rfl⟩, hp.2⟩
  · rintro ⟨⟨hx, rfl⟩, ht⟩
    have hs : (x / 16, t) ∈ stripSheet (-1 / 16) (1 / 16) :=
      ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, ht⟩
    refine ⟨(x / 16, t), hs, ?_⟩
    rw [normalizedStripMap_first hs]
    congr 2
    ring

private theorem second_sheet_image :
    normalizedStripMap '' stripSheet (15 / 16) (17 / 16) =
      ({0} ×ˢ Icc (-1 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1 := by
  ext ⟨⟨x, y⟩, t⟩
  constructor
  · rintro ⟨p, hp, heq⟩
    rw [normalizedStripMap_second hp] at heq
    cases heq
    exact ⟨⟨rfl, ⟨by linarith [hp.1.2], by linarith [hp.1.1]⟩⟩,
      ⟨by linarith [hp.2.2], by linarith [hp.2.1]⟩⟩
  · rintro ⟨⟨rfl, hy⟩, ht⟩
    have hs : (1 - y / 16, 1 - t) ∈ stripSheet (15 / 16) (17 / 16) :=
      ⟨⟨by linarith [hy.2], by linarith [hy.1]⟩,
        ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩
    refine ⟨(1 - y / 16, 1 - t), hs, ?_⟩
    rw [normalizedStripMap_second hs]
    ext <;> dsimp <;> ring

private def sourceInChart : Set (ℝ × ℝ) :=
  twistedSourceRect ∩ twistedStripMap ⁻¹' (halfTurnSlabChart 0).source

private theorem stripSheet_nhds {l u s t : ℝ} (hl : l < s) (hu : s < u) :
    stripSheet l u ∈ 𝓝[twistedSourceRect] (s, t) := by
  have hO : {p : ℝ × ℝ | p.1 ∈ Ioo l u} ∈ 𝓝 (s, t) :=
    (isOpen_Ioo.preimage continuous_fst).mem_nhds ⟨hl, hu⟩
  filter_upwards [mem_nhdsWithin_of_mem_nhds hO, self_mem_nhdsWithin] with p hp hpP
  exact ⟨⟨hp.1.le, hp.2.le⟩, hpP.2⟩

private theorem first_sheet_subset : stripSheet (-1 / 16) (1 / 16) ⊆ sourceInChart := by
  intro p hp
  obtain ⟨hc, hv⟩ := first_sheet_tube hp
  exact ⟨⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, hp.2⟩,
    by simpa only [mem_preimage, ← hv] using twistedTubeChart_mapsTo_slab hc⟩

private theorem second_sheet_subset : stripSheet (15 / 16) (17 / 16) ⊆ sourceInChart := by
  intro p hp
  obtain ⟨hc, hv⟩ := second_sheet_tube hp
  exact ⟨⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, hp.2⟩,
    by simpa only [mem_preimage, ← hv] using twistedTubeChart_mapsTo_slab hc⟩

private theorem tube_crossingCoordinates {q : halfTurnQuotient}
    (hq : q ∈ (halfTurnSlabChart 0).source) :
    twistedTubeChart (crossingCoordinates q) = q := by
  change halfTurnProjection (twistedTubeLift (twistedTubeLift.symm
    (spliceEmbedding.symm (halfTurnSlabChart 0 q)))) = q
  rw [Homeomorph.apply_symm_apply]
  exact (halfTurnSlabChart 0).left_inv hq

private theorem normalizedStripMap_fiber_cover {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ᶠ z in 𝓝 (((0 : ℝ), (0 : ℝ)), t),
      sourceInChart ∩ normalizedStripMap ⁻¹' {z} ⊆
        stripSheet (-1 / 16) (1 / 16) ∪ stripSheet (15 / 16) (17 / 16) := by
  have ha : (0, t) ∈ twistedSourceRect := ⟨⟨by norm_num, by norm_num⟩, ht⟩
  have hb : (1, 1 - t) ∈ twistedSourceRect :=
    ⟨⟨by norm_num, by norm_num⟩, ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩
  have hab : ((0 : ℝ), t) ≠ (1, 1 - t) := by
    intro h
    have := congrArg Prod.fst h
    norm_num at this
  have hfiber := fiber_eq_pair_of_encard_le_two twistedStripMap twistedSourceRect ha hb hab
    rfl (twistedStripMap_seam t).symm (twistedStripMap_fiber_le_two _)
  have hA : stripSheet (-1 / 16) (1 / 16) ∈ 𝓝[twistedSourceRect] (0, t) :=
    stripSheet_nhds (by norm_num) (by norm_num)
  have hB : stripSheet (15 / 16) (17 / 16) ∈ 𝓝[twistedSourceRect] (1, 1 - t) :=
    stripSheet_nhds (by norm_num) (by norm_num)
  have hc := eventually_preimage_subset_union_of_fiber_eq_pair twistedStripMap
    isPLBall_twistedSourceRect.isPolyhedron.isCompact continuous_twistedStripMap.continuousOn
    hfiber hA hB
  have htend : Filter.Tendsto twistedTubeChart (𝓝 ((0, 0), t))
      (𝓝 (twistedStripMap (0, t))) := by
    rw [← twistedTubeChart_core]
    exact continuous_twistedTubeChart.continuousAt
  filter_upwards [htend.eventually hc] with z hz p hp
  apply hz ⟨hp.1.1, ?_⟩
  exact (tube_crossingCoordinates hp.1.2).symm.trans (congrArg twistedTubeChart hp.2)

private theorem normalizedStripMap_crossing {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasPLNormalDoubleCrossingAt normalizedStripMap sourceInChart
      {q : (ℝ × ℝ) × ℝ | q.2 = 0 ∨ q.2 = 1} ((0, 0), t) := by
  have ha : (0, t) ∈ stripSheet (-1 / 16) (1 / 16) :=
    ⟨⟨by norm_num, by norm_num⟩, ht⟩
  have hb : (1, 1 - t) ∈ stripSheet (15 / 16) (17 / 16) :=
    ⟨⟨by norm_num, by norm_num⟩, ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩
  have hfa : normalizedStripMap (0, t) = ((0, 0), t) := by
    rw [normalizedStripMap_first ha]; norm_num
  have hfb : normalizedStripMap (1, 1 - t) = ((0, 0), t) := by
    rw [normalizedStripMap_second hb]; congr 1 <;> simp
  have hdis : Disjoint (stripSheet (-1 / 16) (1 / 16))
      (stripSheet (15 / 16) (17 / 16)) := by
    apply disjoint_left.mpr
    intro p hp hq
    linarith [hp.1.2, hq.1.1]
  have hA : stripSheet (-1 / 16) (1 / 16) ∈ 𝓝[sourceInChart] (0, t) :=
    (nhdsWithin_mono _ inter_subset_left) (stripSheet_nhds (by norm_num) (by norm_num))
  have hB : stripSheet (15 / 16) (17 / 16) ∈ 𝓝[sourceInChart] (1, 1 - t) :=
    (nhdsWithin_mono _ inter_subset_left) (stripSheet_nhds (by norm_num) (by norm_num))
  have hc := normalizedStripMap_fiber_cover ht
  by_cases ht0 : t = 0
  · subst t
    refine Or.inl ⟨Or.inl rfl, {q | 0 ≤ q.2},
      (0, 0), (1, 1 - 0), stripSheet (-1 / 16) (1 / 16),
      stripSheet (15 / 16) (17 / 16), ha, hb, hfa, hfb,
      first_sheet_subset, second_sheet_subset, hdis, hA, hB,
      first_sheet_plhomeomorph, second_sheet_plhomeomorph, ?_, hc⟩
    rw [first_sheet_image, second_sheet_image]
    exact hasPLBoundaryCrossingAt_coordinate_rectangles_zero (by norm_num) (by norm_num)
  by_cases ht1 : t = 1
  · subst t
    refine Or.inl ⟨Or.inr rfl, {q | q.2 ≤ 1},
      (0, 1), (1, 1 - 1), stripSheet (-1 / 16) (1 / 16),
      stripSheet (15 / 16) (17 / 16), ha, hb, hfa, hfb,
      first_sheet_subset, second_sheet_subset, hdis, hA, hB,
      first_sheet_plhomeomorph, second_sheet_plhomeomorph, ?_, hc⟩
    rw [first_sheet_image, second_sheet_image]
    exact hasPLBoundaryCrossingAt_coordinate_rectangles_one (by norm_num) (by norm_num)
  refine Or.inr ⟨fun h => h.elim ht0 ht1,
    (0, t), (1, 1 - t), stripSheet (-1 / 16) (1 / 16),
    stripSheet (15 / 16) (17 / 16), ha, hb, hfa, hfb,
    first_sheet_subset, second_sheet_subset, hdis, hA, hB,
    first_sheet_plhomeomorph, second_sheet_plhomeomorph, ?_, hc⟩
  rw [first_sheet_image, second_sheet_image]
  exact hasPLCrossingAt_coordinate_rectangles (by norm_num) (by norm_num)
    (lt_of_le_of_ne ht.1 (Ne.symm ht0)) (lt_of_le_of_ne ht.2 ht1)

private theorem twistedStripMap_chart_crossing {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasPLNormalDoubleCrossingAt (halfTurnSlabChart 0 ∘ twistedStripMap) sourceInChart
      (halfTurnSlabChart 0 '' ((halfTurnSlabChart 0).source ∩ frontier twistedStripSide))
      (halfTurnSlabChart 0 (twistedStripMap (0, t))) := by
  have hn := (normalizedStripMap_crossing ht).postcomp_openPartialHomeomorph
    twistedTubeLift.toOpenPartialHomeomorph isPLHomeomorphOn_twistedTubeLift.isPiecewiseAffineOn
    (fun _ _ => mem_univ _) (mem_univ _)
  have hm := hn.postcomp_continuousLinearEquiv spliceEmbedding
  change HasPLNormalDoubleCrossingAt (spliceEmbedding ∘ (twistedTubeLift ∘ normalizedStripMap))
    sourceInChart (spliceEmbedding '' (twistedTubeLift ''
      (univ ∩ {q : (ℝ × ℝ) × ℝ | q.2 = 0 ∨ q.2 = 1})))
        (spliceEmbedding (twistedTubeLift ((0, 0), t))) at hm
  have hfunc : spliceEmbedding ∘ (twistedTubeLift ∘ normalizedStripMap) =
      halfTurnSlabChart 0 ∘ twistedStripMap := by
    funext p
    simp only [Function.comp_apply, normalizedStripMap, crossingCoordinates,
      Homeomorph.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  have hp : ((0, 0), t) ∈ spliceCylinder :=
    ⟨mem_spliceSquare.mpr (by norm_num), ht⟩
  have hy := twistedTubeChart_mapsTo_slab hp
  rw [twistedTubeChart_core] at hy
  have hpoint : spliceEmbedding (twistedTubeLift ((0, 0), t)) =
      halfTurnSlabChart 0 (twistedStripMap (0, t)) := by
    have hc := crossingCoordinates_tube hp
    rw [twistedTubeChart_core] at hc
    have h := congrArg (fun z => spliceEmbedding (twistedTubeLift z)) hc
    simpa only [crossingCoordinates, Function.comp_apply, Homeomorph.apply_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply] using h.symm
  rw [hfunc, hpoint] at hm
  have hleft : halfTurnSlabChart 0 (twistedStripMap (0, t)) ∈
      spliceEmbedding '' (twistedTubeLift ''
        (univ ∩ {q : (ℝ × ℝ) × ℝ | q.2 = 0 ∨ q.2 = 1})) ↔ t = 0 ∨ t = 1 := by
    rw [← hpoint, spliceEmbedding.injective.mem_set_image,
      twistedTubeLift.injective.mem_set_image]
    simp only [mem_inter_iff, mem_univ, true_and, mem_ofPred_eq]
  have hright := (mem_image_source_inter_iff (halfTurnSlabChart 0)
    (frontier twistedStripSide) hy).trans (twistedStripMap_core_mem_frontier_iff ht)
  exact hm.congr_boundary (hleft.trans hright.symm)

theorem twistedStripCell_exists_normal_crossing_chart {y : halfTurnQuotient}
    (hy : y ∈ doublePointSet (⇑twistedStripCell) twistedStripCell.domain) :
    ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) halfTurnQuotient, y ∈ e.source ∧
      HasPLNormalDoubleCrossingAt (e ∘ ⇑twistedStripCell)
        (twistedStripCell.domain ∩ ⇑twistedStripCell ⁻¹' e.source)
        (e '' (e.source ∩ frontier twistedStripSide)) (e y) := by
  rw [twistedStripCell_doublePointSet] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  have hc := twistedStripMap_chart_crossing ht
  let Q := twistedStripCell.domain ∩ ⇑twistedStripCell ⁻¹' (halfTurnSlabChart 0).source
  have hbij : BijOn (⇑seamWitnessPlane.symm) Q sourceInChart := by
    refine ⟨fun p hp => ⟨mem_image_seamWitnessPlane.mp hp.1, hp.2⟩,
      seamWitnessPlane.symm.injective.injOn, ?_⟩
    intro p hp
    refine ⟨seamWitnessPlane p, ⟨mem_image_of_mem _ hp.1, ?_⟩,
      ContinuousLinearEquiv.symm_apply_apply _ _⟩
    change twistedStripMap (seamWitnessPlane.symm (seamWitnessPlane p)) ∈
      (halfTurnSlabChart 0).source
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hp.2
  have hn := hc.precomp_bijOn_of_isPLHomeomorphOn
    (isPLHomeomorphOn_seamWitnessPlaneSymm isPLBall_twistedSourceRect.isPolyhedron)
    hbij inter_subset_left inter_subset_left (fun _ hx hp => ⟨hx, hp.2⟩)
  have hsource : twistedStripMap (0, t) ∈ (halfTurnSlabChart 0).source :=
    (first_sheet_subset ⟨⟨by norm_num, by norm_num⟩, ht⟩).2
  exact exists_crossing_chart_mem_atlas hn twistedStripCell.continuousOn
    (halfTurnSlabChart_mem_maximalAtlas 0) hsource

theorem twistedStripCell_nonempty_normalSingularCellData {B : Set halfTurnQuotient}
    (hB : Set.range twistedStripCell.boundary ⊆ B) :
    Nonempty (NormalSingularCellData twistedStripCell (frontier twistedStripSide) B) := by
  obtain ⟨T⟩ := twistedStripCell_nonempty_normalSingularSetTriangulation
  exact ⟨{
    locallyInjective := twistedStripCell_locallyInjective
    fiber_le_two := twistedStripCell_fiber_le_two
    boundary_image_subset := hB
    image_inter_boundary := twistedStripCell_image_inter_frontier_side
    singularSet := T
    crossing := fun _ hy => twistedStripCell_exists_normal_crossing_chart hy }⟩

end DifferentialGeometry.Topology.PiecewiseLinear
