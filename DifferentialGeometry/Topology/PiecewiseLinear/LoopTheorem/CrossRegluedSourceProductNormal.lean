/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceProduct
import DifferentialGeometry.Topology.PiecewiseLinear.BallPairArc
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldDisjointUnion
import DifferentialGeometry.Topology.PiecewiseLinear.SingularCrossingPrecomp

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private def productX : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ :=
  (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ)

private def productY : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ :=
  (LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ)

private theorem coordinate_planes :
    Module.finrank ℝ (LinearMap.ker productY) = 2 ∧
      Module.finrank ℝ (LinearMap.ker productX) = 2 ∧
        Module.finrank ℝ (LinearMap.ker productY ⊓ LinearMap.ker productX :
          Submodule ℝ ((ℝ × ℝ) × ℝ)) = 1 ∧
          LinearMap.ker productY ⊔ LinearMap.ker productX = ⊤ := by
  have hx : productX ≠ 0 := by
    intro h
    have hh := congrArg (fun f => f (((1 : ℝ), (0 : ℝ)), (0 : ℝ))) h
    norm_num [productX] at hh
  have hy : productY ≠ 0 := by
    intro h
    have hh := congrArg (fun f => f (((0 : ℝ), (1 : ℝ)), (0 : ℝ))) h
    norm_num [productY] at hh
  have hdim : Module.finrank ℝ ((ℝ × ℝ) × ℝ) = 3 := by simp
  have hxker : Module.finrank ℝ (LinearMap.ker productX) = 2 := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hx
    rw [hdim] at h
    omega
  have hyker : Module.finrank ℝ (LinearMap.ker productY) = 2 := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hy
    rw [hdim] at h
    omega
  have hsup : LinearMap.ker productY ⊔ LinearMap.ker productX = ⊤ := by
    apply top_unique
    rintro ⟨⟨x, y⟩, t⟩ _
    have h1 : ((x, 0), t) ∈ LinearMap.ker productY := by rfl
    have h2 : ((0, y), (0 : ℝ)) ∈ LinearMap.ker productX := by rfl
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using
      Submodule.add_mem (LinearMap.ker productY ⊔ LinearMap.ker productX)
        (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)
  refine ⟨hyker, hxker, ?_, hsup⟩
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.ker productY) (LinearMap.ker productX)
  rw [hsup, finrank_top, hdim, hyker, hxker] at h
  omega

private def horizontalRectangle (b : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  (Icc (-1 : ℝ) 1 ×ˢ {b}) ×ˢ Icc (0 : ℝ) 1

private def verticalRectangle (l u : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  ({0} ×ˢ Icc l u) ×ˢ Icc (0 : ℝ) 1

private theorem coordinate_rectangles_germ {l b u : ℝ} (hl : l < b) (hu : b < u) (t : ℝ) :
    ∀ᶠ q in 𝓝 (((0 : ℝ), b), t),
      (q ∈ horizontalRectangle b ↔ q.1.2 = b ∧ q.2 ∈ Icc (0 : ℝ) 1) ∧
        (q ∈ verticalRectangle l u ↔ q.1.1 = 0 ∧ q.2 ∈ Icc (0 : ℝ) 1) := by
  have hO : IsOpen ((Ioo (-1 : ℝ) 1 ×ˢ Ioo l u) ×ˢ (univ : Set ℝ)) :=
    (isOpen_Ioo.prod isOpen_Ioo).prod isOpen_univ
  have hp : (((0 : ℝ), b), t) ∈ (Ioo (-1 : ℝ) 1 ×ˢ Ioo l u) ×ˢ (univ : Set ℝ) :=
    ⟨⟨⟨by norm_num, by norm_num⟩, hl, hu⟩, mem_univ _⟩
  filter_upwards [hO.mem_nhds hp] with q hq
  constructor
  · constructor
    · intro h
      exact ⟨h.1.2, h.2⟩
    · rintro ⟨hy, ht⟩
      exact ⟨⟨⟨hq.1.1.1.le, hq.1.1.2.le⟩, hy⟩, ht⟩
  · constructor
    · intro h
      exact ⟨h.1.1, h.2⟩
    · rintro ⟨hx, ht⟩
      exact ⟨⟨hx, ⟨hq.1.2.1.le, hq.1.2.2.le⟩⟩, ht⟩

private theorem coordinate_rectangles_crossing {l b u t : ℝ}
    (hl : l < b) (hu : b < u) (ht0 : 0 < t) (ht1 : t < 1) :
    HasPLCrossingAt (horizontalRectangle b) (verticalRectangle l u) ((0, b), t) := by
  obtain ⟨hP, hQ, hI, hsup⟩ := coordinate_planes
  have hh : IsPLHomeomorphOn (fun q : (ℝ × ℝ) × ℝ => q - ((0, b), t)) univ univ := by
    simpa only [sub_eq_add_neg] using isPLHomeomorphOn_add_const (-((0, b), t))
  refine ⟨univ, univ, (fun q => q - ((0, b), t)),
    LinearMap.ker productY, LinearMap.ker productX, 0, 0,
    isOpen_univ, isOpen_univ, mem_univ _, hh, sub_self _, hP, hQ, hI, hsup,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, ?_⟩
  have hheight : ∀ᶠ q : (ℝ × ℝ) × ℝ in 𝓝 ((0, b), t), q.2 ∈ Ioo (0 : ℝ) 1 :=
    (isOpen_Ioo.preimage continuous_snd).mem_nhds ⟨ht0, ht1⟩
  filter_upwards [coordinate_rectangles_germ hl hu t, hheight] with q hq ht
  have ht' : q.2 ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  simpa only [LinearMap.mem_ker, productX, productY, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, Prod.fst_sub, Prod.snd_sub,
    sub_zero, sub_eq_zero, LinearMap.zero_apply, le_refl, and_true, ht'] using hq

private theorem coordinate_rectangles_boundary_zero {l b u : ℝ} (hl : l < b) (hu : b < u) :
    HasPLBoundaryCrossingAt {q : (ℝ × ℝ) × ℝ | 0 ≤ q.2}
      (horizontalRectangle b) (verticalRectangle l u) ((0, b), 0) := by
  obtain ⟨hP, hQ, hI, hsup⟩ := coordinate_planes
  have hh : IsPLHomeomorphOn (fun q : (ℝ × ℝ) × ℝ => q - ((0, b), 0)) univ univ := by
    simpa only [sub_eq_add_neg] using isPLHomeomorphOn_add_const (-((0, b), (0 : ℝ)))
  refine ⟨univ, univ, (fun q => q - ((0, b), 0)),
    LinearMap.ker productY, LinearMap.ker productX, LinearMap.snd ℝ (ℝ × ℝ) ℝ,
    isOpen_univ, isOpen_univ, mem_univ _, hh, sub_self _, hP, hQ, hI, hsup,
    ⟨((0, 0), 1), ⟨rfl, rfl⟩, rfl⟩, ?_⟩
  have hheight : ∀ᶠ q : (ℝ × ℝ) × ℝ in 𝓝 ((0, b), 0), q.2 < 1 :=
    (isOpen_Iio.preimage continuous_snd).mem_nhds (by norm_num)
  filter_upwards [coordinate_rectangles_germ hl hu 0, hheight] with q hq ht
  have hIcc : q.2 ∈ Icc (0 : ℝ) 1 ↔ 0 ≤ q.2 := and_iff_left ht.le
  refine ⟨?_, ?_, ?_⟩
  · simp only [LinearMap.snd_apply, Prod.snd_sub, sub_zero]
  · simpa only [LinearMap.mem_ker, productY, LinearMap.comp_apply, LinearMap.snd_apply,
      LinearMap.fst_apply, Prod.fst_sub, Prod.snd_sub, sub_zero, sub_eq_zero, hIcc] using hq.1
  · simpa only [LinearMap.mem_ker, productX, LinearMap.comp_apply, LinearMap.snd_apply,
      LinearMap.fst_apply, Prod.fst_sub, Prod.snd_sub, sub_zero, hIcc] using hq.2

private theorem coordinate_rectangles_boundary_one {l b u : ℝ} (hl : l < b) (hu : b < u) :
    HasPLBoundaryCrossingAt {q : (ℝ × ℝ) × ℝ | q.2 ≤ 1}
      (horizontalRectangle b) (verticalRectangle l u) ((0, b), 1) := by
  obtain ⟨hP, hQ, hI, hsup⟩ := coordinate_planes
  have hh : IsPLHomeomorphOn (fun q : (ℝ × ℝ) × ℝ => q - ((0, b), 1)) univ univ := by
    simpa only [sub_eq_add_neg] using isPLHomeomorphOn_add_const (-((0, b), (1 : ℝ)))
  refine ⟨univ, univ, (fun q => q - ((0, b), 1)),
    LinearMap.ker productY, LinearMap.ker productX, -(LinearMap.snd ℝ (ℝ × ℝ) ℝ),
    isOpen_univ, isOpen_univ, mem_univ _, hh, sub_self _, hP, hQ, hI, hsup,
    ⟨((0, 0), -1), ⟨rfl, rfl⟩, by norm_num⟩, ?_⟩
  have hheight : ∀ᶠ q : (ℝ × ℝ) × ℝ in 𝓝 ((0, b), 1), 0 < q.2 :=
    (isOpen_Ioi.preimage continuous_snd).mem_nhds (by norm_num)
  filter_upwards [coordinate_rectangles_germ hl hu 1, hheight] with q hq ht
  have hIcc : q.2 ∈ Icc (0 : ℝ) 1 ↔ 0 ≤ -(q.2 - 1) := by
    constructor
    · intro h
      linarith [h.2]
    · intro h
      exact ⟨ht.le, by linarith⟩
  refine ⟨?_, ?_, ?_⟩
  · change q.2 ≤ 1 ↔ 0 ≤ -(q.2 - 1)
    constructor <;> intro h <;> linarith
  · simpa only [LinearMap.mem_ker, productY, LinearMap.comp_apply, LinearMap.snd_apply,
      LinearMap.fst_apply, Prod.fst_sub, Prod.snd_sub, LinearMap.neg_apply,
      sub_zero, sub_eq_zero, hIcc] using hq.1
  · simpa only [LinearMap.mem_ker, productX, LinearMap.comp_apply, LinearMap.snd_apply,
      LinearMap.fst_apply, Prod.fst_sub, Prod.snd_sub, LinearMap.neg_apply,
      sub_zero, hIcc] using hq.2

private def sourceSheet (l u : ℝ) : Set (ℝ × ℝ) := Icc l u ×ˢ Icc (0 : ℝ) 1

private theorem sourceSheet_subset {l u : ℝ} (hl : 0 ≤ l) (hu : u ≤ 5) :
    sourceSheet l u ⊆ seamSourceRect := by
  intro p hp
  exact ⟨⟨hl.trans hp.1.1, hp.1.2.trans hu⟩, hp.2⟩

private theorem sourceSheet_nhds {l u s t : ℝ} (hl : l < s) (hu : s < u) :
    sourceSheet l u ∈ 𝓝[seamSourceRect] (s, t) := by
  have hO : {p : ℝ × ℝ | p.1 ∈ Ioo l u} ∈ 𝓝 (s, t) :=
    (isOpen_Ioo.preimage continuous_fst).mem_nhds ⟨hl, hu⟩
  filter_upwards [mem_nhdsWithin_of_mem_nhds hO, self_mem_nhdsWithin] with p hp hpP
  exact ⟨⟨hp.1.le, hp.2.le⟩, hpP.2⟩

private theorem sourceSheet_plhomeomorph {l u : ℝ} (hl : 0 ≤ l) (hu : u ≤ 5)
    (hcore : u < 7 / 2 ∨ 3 / 2 < l) (hcurl : u < 47 / 10 ∨ 62 / 15 < l) :
    IsPLHomeomorphOn crossingProductMap (sourceSheet l u)
      (crossingProductMap '' sourceSheet l u) := by
  have hpoly : IsPolyhedron (sourceSheet l u) :=
    (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron
  apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hpoly
    (isPiecewiseAffineOn_crossingProductMap.mono_of_isPolyhedron hpoly (subset_univ _))
  apply InjOn.bijOn_image
  intro p hp q hq h
  obtain ⟨ht, hs⟩ := (crossingProductMap_eq_iff
    (sourceSheet_subset hl hu hp).1 (sourceSheet_subset hl hu hq).1).mp h
  apply Prod.ext _ ht
  rcases hs with hs | ⟨hp', hq'⟩ | ⟨hp', hq'⟩ | ⟨hp', hq'⟩ | ⟨hp', hq'⟩
  · exact hs
  all_goals
    rcases hcore with hc | hc <;> rcases hcurl with hd | hd <;>
      linarith [hp.1.1, hp.1.2, hq.1.1, hq.1.2]

private theorem image_core_horizontal :
    crossingProductMap '' sourceSheet 1 2 = horizontalRectangle 0 := by
  ext ⟨⟨x, y⟩, t⟩
  constructor
  · rintro ⟨p, hp, heq⟩
    rw [crossingProductMap_of_mem_core_horizontal hp.1] at heq
    cases heq
    exact ⟨⟨⟨by linarith [hp.1.2], by linarith [hp.1.1]⟩, rfl⟩, hp.2⟩
  · rintro ⟨⟨hx, rfl⟩, ht⟩
    have hs : (3 - x) / 2 ∈ Icc (1 : ℝ) 2 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    refine ⟨((3 - x) / 2, t), ⟨hs, ht⟩, ?_⟩
    rw [crossingProductMap_of_mem_core_horizontal hs]
    dsimp
    congr 2
    ring

private theorem image_core_vertical :
    crossingProductMap '' sourceSheet 3 4 = verticalRectangle (-1) 1 := by
  ext ⟨⟨x, y⟩, t⟩
  constructor
  · rintro ⟨p, hp, heq⟩
    rw [crossingProductMap_of_mem_core_vertical hp.1] at heq
    cases heq
    exact ⟨⟨rfl, ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩⟩, hp.2⟩
  · rintro ⟨⟨rfl, hy⟩, ht⟩
    have hs : (y + 7) / 2 ∈ Icc (3 : ℝ) 4 := ⟨by linarith [hy.1], by linarith [hy.2]⟩
    refine ⟨((y + 7) / 2, t), ⟨hs, ht⟩, ?_⟩
    rw [crossingProductMap_of_mem_core_vertical hs]
    dsimp
    congr 2
    ring

private theorem image_curl_horizontal :
    crossingProductMap '' sourceSheet (23 / 5) (24 / 5) = horizontalRectangle 3 := by
  ext ⟨⟨x, y⟩, t⟩
  constructor
  · rintro ⟨p, hp, heq⟩
    rw [crossingProductMap_of_mem_curl_horizontal hp.1] at heq
    cases heq
    exact ⟨⟨⟨by linarith [hp.1.2], by linarith [hp.1.1]⟩, rfl⟩, hp.2⟩
  · rintro ⟨⟨hx, rfl⟩, ht⟩
    have hs : (47 - x) / 10 ∈ Icc (23 / 5 : ℝ) (24 / 5) :=
      ⟨by linarith [hx.2], by linarith [hx.1]⟩
    refine ⟨((47 - x) / 10, t), ⟨hs, ht⟩, ?_⟩
    rw [crossingProductMap_of_mem_curl_horizontal hs]
    dsimp
    congr 2
    ring

private theorem image_curl_vertical :
    crossingProductMap '' sourceSheet 4 (21 / 5) = verticalRectangle 1 4 := by
  ext ⟨⟨x, y⟩, t⟩
  constructor
  · rintro ⟨p, hp, heq⟩
    rw [crossingProductMap_of_mem_curl_vertical hp.1] at heq
    cases heq
    exact ⟨⟨rfl, ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩⟩, hp.2⟩
  · rintro ⟨⟨rfl, hy⟩, ht⟩
    have hs : (y + 59) / 15 ∈ Icc (4 : ℝ) (21 / 5) :=
      ⟨by linarith [hy.1], by linarith [hy.2]⟩
    refine ⟨((y + 59) / 15, t), ⟨hs, ht⟩, ?_⟩
    rw [crossingProductMap_of_mem_curl_vertical hs]
    dsimp
    congr 2
    ring

private theorem coordinate_mem_frontier_box {b t : ℝ} (hb0 : -3 < b) (hb1 : b < 5)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ((0, b), t) ∈ frontier crossingProductBox ↔ t = 0 ∨ t = 1 := by
  rw [isHPolytope_crossingProductBox.isPolyhedron.isClosed.frontier_eq]
  have hmem : ((0, b), t) ∈ crossingProductBox :=
    ⟨⟨⟨by norm_num, by norm_num⟩, ⟨hb0.le, hb1.le⟩⟩, ht⟩
  rw [mem_sdiff, and_iff_right hmem, crossingProductBox,
    interior_prod_eq, interior_prod_eq, interior_Icc, interior_Icc, interior_Icc]
  simp only [mem_prod, mem_Ioo]
  constructor
  · intro h
    by_cases ht0 : t = 0
    · exact Or.inl ht0
    by_cases ht1 : t = 1
    · exact Or.inr ht1
    exact (h ⟨⟨⟨by norm_num, by norm_num⟩, hb0, hb1⟩,
      lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩).elim
  · rintro (rfl | rfl) h <;> linarith [h.2.1, h.2.2]

private theorem normal_crossing_of_sheets {l b u t : ℝ} (hl : l < b) (hu : b < u)
    (hb0 : -3 < b) (hb1 : b < 5) (ht : t ∈ Icc (0 : ℝ) 1)
    {a d : ℝ × ℝ} {A B : Set (ℝ × ℝ)} (ha : a ∈ A) (hd : d ∈ B)
    (hfa : crossingProductMap a = ((0, b), t))
    (hfd : crossingProductMap d = ((0, b), t))
    (hA : A ⊆ seamSourceRect) (hB : B ⊆ seamSourceRect) (hAB : Disjoint A B)
    (hAn : A ∈ 𝓝[seamSourceRect] a) (hBn : B ∈ 𝓝[seamSourceRect] d)
    (hAe : IsPLHomeomorphOn crossingProductMap A (crossingProductMap '' A))
    (hBe : IsPLHomeomorphOn crossingProductMap B (crossingProductMap '' B))
    (hAi : crossingProductMap '' A = horizontalRectangle b)
    (hBi : crossingProductMap '' B = verticalRectangle l u) :
    HasPLNormalDoubleCrossingAt crossingProductMap seamSourceRect
      (frontier crossingProductBox) ((0, b), t) := by
  have had : a ≠ d := fun h => Set.disjoint_left.mp hAB ha (h ▸ hd)
  have hfiber := fiber_eq_pair_of_encard_le_two crossingProductMap seamSourceRect
    (hA ha) (hB hd) had hfa hfd (crossingProductMap_fiber_le_two _)
  have hcover := eventually_preimage_subset_union_of_fiber_eq_pair crossingProductMap
    isPolyhedron_seamSourceRect.isCompact
    (isPiecewiseAffineOn_crossingProductMap.continuousOn.mono (subset_univ _)) hfiber hAn hBn
  have hbd := coordinate_mem_frontier_box hb0 hb1 ht
  by_cases ht0 : t = 0
  · subst t
    refine Or.inl ⟨hbd.mpr (Or.inl rfl), {q | 0 ≤ q.2},
      a, d, A, B, ha, hd, hfa, hfd, hA, hB, hAB, hAn, hBn, hAe, hBe, ?_, hcover⟩
    rw [hAi, hBi]
    exact coordinate_rectangles_boundary_zero hl hu
  by_cases ht1 : t = 1
  · subst t
    refine Or.inl ⟨hbd.mpr (Or.inr rfl), {q | q.2 ≤ 1},
      a, d, A, B, ha, hd, hfa, hfd, hA, hB, hAB, hAn, hBn, hAe, hBe, ?_, hcover⟩
    rw [hAi, hBi]
    exact coordinate_rectangles_boundary_one hl hu
  refine Or.inr ⟨fun h => (hbd.mp h).elim ht0 ht1,
    a, d, A, B, ha, hd, hfa, hfd, hA, hB, hAB, hAn, hBn, hAe, hBe, ?_, hcover⟩
  rw [hAi, hBi]
  exact coordinate_rectangles_crossing hl hu
    (lt_of_le_of_ne ht.1 (Ne.symm ht0)) (lt_of_le_of_ne ht.2 ht1)

theorem crossingProductMap_hasPLNormalDoubleCrossingAt {y : (ℝ × ℝ) × ℝ}
    (hy : y ∈ doublePointSet crossingProductMap seamSourceRect) :
    HasPLNormalDoubleCrossingAt crossingProductMap seamSourceRect
      (frontier crossingProductBox) y := by
  rw [crossingProductMap_doublePointSet] at hy
  rcases y with ⟨⟨x, b⟩, t⟩
  rcases hy with ⟨h | h, ht⟩
  · have hxy : (x, b) = ((0 : ℝ), (0 : ℝ)) := h
    cases hxy
    apply normal_crossing_of_sheets (l := -1) (u := 1) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ht (a := (3 / 2, t)) (d := (7 / 2, t))
      (A := sourceSheet 1 2) (B := sourceSheet 3 4)
    · exact ⟨⟨by norm_num, by norm_num⟩, ht⟩
    · exact ⟨⟨by norm_num, by norm_num⟩, ht⟩
    · exact crossingProductMap_core_first t
    · exact crossingProductMap_core_second t
    · exact sourceSheet_subset (by norm_num) (by norm_num)
    · exact sourceSheet_subset (by norm_num) (by norm_num)
    · exact Set.disjoint_left.mpr fun p hp hq => by linarith [hp.1.2, hq.1.1]
    · exact sourceSheet_nhds (by norm_num) (by norm_num)
    · exact sourceSheet_nhds (by norm_num) (by norm_num)
    · exact sourceSheet_plhomeomorph (by norm_num) (by norm_num)
        (Or.inl (by norm_num)) (Or.inl (by norm_num))
    · exact sourceSheet_plhomeomorph (by norm_num) (by norm_num)
        (Or.inr (by norm_num)) (Or.inl (by norm_num))
    · exact image_core_horizontal
    · exact image_core_vertical
  · have hxy : (x, b) = ((0 : ℝ), (3 : ℝ)) := h
    cases hxy
    apply normal_crossing_of_sheets (l := 1) (u := 4) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ht (a := (47 / 10, t)) (d := (62 / 15, t))
      (A := sourceSheet (23 / 5) (24 / 5)) (B := sourceSheet 4 (21 / 5))
    · exact ⟨⟨by norm_num, by norm_num⟩, ht⟩
    · exact ⟨⟨by norm_num, by norm_num⟩, ht⟩
    · exact crossingProductMap_curl_second t
    · exact crossingProductMap_curl_first t
    · exact sourceSheet_subset (by norm_num) (by norm_num)
    · exact sourceSheet_subset (by norm_num) (by norm_num)
    · exact Set.disjoint_left.mpr fun p hp hq => by linarith [hp.1.1, hq.1.2]
    · exact sourceSheet_nhds (by norm_num) (by norm_num)
    · exact sourceSheet_nhds (by norm_num) (by norm_num)
    · exact sourceSheet_plhomeomorph (by norm_num) (by norm_num)
        (Or.inr (by norm_num)) (Or.inr (by norm_num))
    · exact sourceSheet_plhomeomorph (by norm_num) (by norm_num)
        (Or.inr (by norm_num)) (Or.inl (by norm_num))
    · exact image_curl_horizontal
    · exact image_curl_vertical

section Transport

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem plhomeomorph_postcomp_linearEquiv {f : E → F} {P : Set E} {Q : Set F}
    (hf : IsPLHomeomorphOn f P Q) (e : F ≃L[ℝ] V) :
    IsPLHomeomorphOn (e ∘ f) P (e '' Q) := by
  have hbij : BijOn (e ∘ f) P (e '' Q) := e.injective.injOn.bijOn_image.comp hf.bijOn
  refine ⟨hbij, hf.isPiecewiseAffineOn.affine_comp e.toLinearMap.toAffineMap, ?_⟩
  have hinv := hf.isPiecewiseAffineOn_invFunOn.comp
    (isPiecewiseAffineOn_of_affine e.symm.toLinearMap.toAffineMap isOpen_univ)
  change IsPiecewiseAffineOn (Function.invFunOn f P ∘ e.symm)
    (univ ∩ e.symm ⁻¹' Q) at hinv
  rw [univ_inter, ← e.image_eq_preimage_symm Q] at hinv
  refine hinv.congr fun y hy => ?_
  have hyQ : e.symm y ∈ Q := by rwa [e.image_eq_preimage_symm Q] at hy
  apply hbij.injOn (hbij.surjOn.mapsTo_invFunOn hy)
    (hf.bijOn.surjOn.mapsTo_invFunOn hyQ)
  rw [hbij.invOn_invFunOn.2 hy]
  dsimp only [Function.comp_apply]
  rw [hf.bijOn.invOn_invFunOn.2 hyQ, e.apply_symm_apply]

private theorem plhomeomorph_linearEquiv (e : E ≃L[ℝ] F) {P : Set E} (hP : IsOpen P) :
    IsPLHomeomorphOn (⇑e) P (e '' P) := by
  refine ⟨e.injective.injOn.bijOn_image,
    isPiecewiseAffineOn_of_affine e.toLinearMap.toAffineMap hP, ?_⟩
  apply (isPiecewiseAffineOn_of_affine e.symm.toLinearMap.toAffineMap
    (e.toHomeomorph.isOpenMap P hP)).congr
  rintro y ⟨x, hx, rfl⟩
  change Function.invFunOn (⇑e) P (e x) = e.symm (e x)
  rw [e.injective.injOn.leftInvOn_invFunOn hx, e.symm_apply_apply]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem mem_map_linearEquiv (e : E ≃L[ℝ] F) {P : Submodule ℝ E} {v : E} :
    e v ∈ P.map e.toLinearMap ↔ v ∈ P := by
  constructor
  · rintro ⟨w, hw, heq⟩
    exact e.injective heq ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

private theorem crossing_image_linearEquiv {A B : Set E} {x : E}
    (hAB : HasPLCrossingAt A B x) (e : E ≃L[ℝ] F) :
    HasPLCrossingAt (e '' A) (e '' B) (e x) := by
  obtain ⟨U, W, h, P, Q, α, β, hU, hW, hxU, hh, hhx, hP, hQ, hI, hsup,
    hα, hβ, hzero, hlocal⟩ := hAB
  have hU' : IsOpen (e '' U) := e.toHomeomorph.isOpenMap U hU
  have hinv : IsPLHomeomorphOn (⇑e.symm) (e '' U) U := by
    simpa only [e.symm_image_image] using plhomeomorph_linearEquiv e.symm hU'
  have hcomp := plhomeomorph_postcomp_linearEquiv (hinv.trans hh) e
  refine ⟨e '' U, e '' W, e ∘ h ∘ e.symm, P.map e.toLinearMap, Q.map e.toLinearMap,
    α.comp e.symm.toLinearMap, β.comp e.symm.toLinearMap,
    hU', e.toHomeomorph.isOpenMap W hW, ⟨x, hxU, rfl⟩, hcomp, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · simp only [Function.comp_apply, e.symm_apply_apply, hhx, map_zero]
  · exact (e.toLinearEquiv.finrank_map_eq P).trans hP
  · exact (e.toLinearEquiv.finrank_map_eq Q).trans hQ
  · rw [← Submodule.map_inf _ e.injective, e.toLinearEquiv.finrank_map_eq]
    exact hI
  · rw [← Submodule.map_sup, hsup, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr e.surjective
  · rcases hα with rfl | ⟨u, hu, hαu⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨e u, ⟨⟨u, hu.1, rfl⟩, ⟨u, hu.2, rfl⟩⟩,
        by simpa using hαu⟩
  · rcases hβ with rfl | ⟨u, hu, hβu⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨e u, ⟨⟨u, hu.1, rfl⟩, ⟨u, hu.2, rfl⟩⟩,
        by simpa using hβu⟩
  · rcases hzero with hα | hβ
    · exact Or.inl (by rw [hα]; rfl)
    · exact Or.inr (by rw [hβ]; rfl)
  · have htend : Filter.Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      simpa only [ContinuousAt, e.symm_apply_apply] using
        e.symm.continuous.continuousAt (x := e x)
    filter_upwards [htend.eventually hlocal] with y hy
    change (y ∈ e '' A ↔ e (h (e.symm y)) ∈ P.map e.toLinearMap ∧
        0 ≤ α (e.symm (e (h (e.symm y))))) ∧
      (y ∈ e '' B ↔ e (h (e.symm y)) ∈ Q.map e.toLinearMap ∧
        0 ≤ β (e.symm (e (h (e.symm y)))))
    simpa only [e.image_eq_preimage_symm, mem_preimage, Function.comp_apply,
      mem_map_linearEquiv, e.symm_apply_apply] using hy

private theorem boundary_crossing_image_linearEquiv {M A B : Set E} {x : E}
    (hAB : HasPLBoundaryCrossingAt M A B x) (e : E ≃L[ℝ] F) :
    HasPLBoundaryCrossingAt (e '' M) (e '' A) (e '' B) (e x) := by
  obtain ⟨U, W, h, P, Q, ℓ, hU, hW, hxU, hh, hhx, hP, hQ, hI, hsup,
    ⟨u, hu, hℓu⟩, hlocal⟩ := hAB
  have hU' : IsOpen (e '' U) := e.toHomeomorph.isOpenMap U hU
  have hinv : IsPLHomeomorphOn (⇑e.symm) (e '' U) U := by
    simpa only [e.symm_image_image] using plhomeomorph_linearEquiv e.symm hU'
  have hcomp := plhomeomorph_postcomp_linearEquiv (hinv.trans hh) e
  refine ⟨e '' U, e '' W, e ∘ h ∘ e.symm, P.map e.toLinearMap, Q.map e.toLinearMap,
    ℓ.comp e.symm.toLinearMap,
    hU', e.toHomeomorph.isOpenMap W hW, ⟨x, hxU, rfl⟩, hcomp, ?_, ?_, ?_, ?_, ?_,
    ⟨e u, ⟨⟨u, hu.1, rfl⟩, ⟨u, hu.2, rfl⟩⟩, by simpa using hℓu⟩, ?_⟩
  · simp only [Function.comp_apply, e.symm_apply_apply, hhx, map_zero]
  · exact (e.toLinearEquiv.finrank_map_eq P).trans hP
  · exact (e.toLinearEquiv.finrank_map_eq Q).trans hQ
  · rw [← Submodule.map_inf _ e.injective, e.toLinearEquiv.finrank_map_eq]
    exact hI
  · rw [← Submodule.map_sup, hsup, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr e.surjective
  · have htend : Filter.Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      simpa only [ContinuousAt, e.symm_apply_apply] using
        e.symm.continuous.continuousAt (x := e x)
    filter_upwards [htend.eventually hlocal] with y hy
    change (y ∈ e '' M ↔ 0 ≤ ℓ (e.symm (e (h (e.symm y))))) ∧
      (y ∈ e '' A ↔ e (h (e.symm y)) ∈ P.map e.toLinearMap ∧
        0 ≤ ℓ (e.symm (e (h (e.symm y))))) ∧
      (y ∈ e '' B ↔ e (h (e.symm y)) ∈ Q.map e.toLinearMap ∧
        0 ≤ ℓ (e.symm (e (h (e.symm y)))))
    simpa only [e.image_eq_preimage_symm, mem_preimage, Function.comp_apply,
      mem_map_linearEquiv, e.symm_apply_apply] using hy

omit [FiniteDimensional ℝ E] in
private theorem normal_double_crossing_postcomp_linearEquiv {f : E → F} {P : Set E}
    {B : Set F} {y : F} (hD : HasPLNormalDoubleCrossingAt f P B y) (e : F ≃L[ℝ] V) :
    HasPLNormalDoubleCrossingAt (e ∘ f) P (e '' B) (e y) := by
  have htend : Filter.Tendsto e.symm (𝓝 (e y)) (𝓝 y) := by
    simpa only [ContinuousAt, e.symm_apply_apply] using
      e.symm.continuous.continuousAt (x := e y)
  rcases hD with ⟨hyB, M, a, b, A, C, ha, hb, hfa, hfb, hAP, hCP, hdis,
    hA, hC, hfA, hfC, hcross, hcover⟩ |
    ⟨hyB, a, b, A, C, ha, hb, hfa, hfb, hAP, hCP, hdis, hA, hC, hfA, hfC, hcross, hcover⟩
  · refine Or.inl ⟨⟨y, hyB, rfl⟩, e '' M,
      a, b, A, C, ha, hb, congrArg e hfa, congrArg e hfb, hAP, hCP, hdis, hA, hC,
      ?_, ?_, ?_, ?_⟩
    · simpa only [image_comp] using plhomeomorph_postcomp_linearEquiv hfA e
    · simpa only [image_comp] using plhomeomorph_postcomp_linearEquiv hfC e
    · simpa only [image_comp] using boundary_crossing_image_linearEquiv hcross e
    · filter_upwards [htend.eventually hcover] with z hz
      rintro p ⟨hp, hpz⟩
      apply hz ⟨hp, ?_⟩
      exact e.injective (hpz.trans (e.apply_symm_apply z).symm)
  · refine Or.inr ⟨?_,
      a, b, A, C, ha, hb, congrArg e hfa, congrArg e hfb, hAP, hCP, hdis, hA, hC,
      ?_, ?_, ?_, ?_⟩
    · rintro ⟨z, hz, hzy⟩
      exact hyB (e.injective hzy ▸ hz)
    · simpa only [image_comp] using plhomeomorph_postcomp_linearEquiv hfA e
    · simpa only [image_comp] using plhomeomorph_postcomp_linearEquiv hfC e
    · simpa only [image_comp] using crossing_image_linearEquiv hcross e
    · filter_upwards [htend.eventually hcover] with z hz
      rintro p ⟨hp, hpz⟩
      apply hz ⟨hp, ?_⟩
      exact e.injective (hpz.trans (e.apply_symm_apply z).symm)

end Transport

theorem crossingProductCell_hasPLNormalDoubleCrossingAt {y : EuclideanSpace ℝ (Fin 3)}
    (hy : y ∈ doublePointSet (⇑crossingProductCell) crossingProductCell.domain) :
    HasPLNormalDoubleCrossingAt (⇑crossingProductCell) crossingProductCell.domain
      (frontier crossingProductSide) y := by
  rw [crossingProductCell_doublePointSet] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hzD : z ∈ doublePointSet crossingProductMap seamSourceRect := by
    rwa [crossingProductMap_doublePointSet]
  have hn := normal_double_crossing_postcomp_linearEquiv
    (crossingProductMap_hasPLNormalDoubleCrossingAt hzD) spliceEmbedding
  have hfront : spliceEmbedding '' frontier crossingProductBox =
      frontier crossingProductSide := spliceEmbedding.toHomeomorph.image_frontier _
  rw [hfront] at hn
  exact hn.precomp_isPLHomeomorphOn
    (isPLHomeomorphOn_seamWitnessPlaneSymm isPolyhedron_seamSourceRect)

private theorem vertical_segment (b : ℝ) :
    segment ℝ (((0 : ℝ), b), (0 : ℝ)) ((0, b), 1) =
      {((0 : ℝ), b)} ×ˢ Icc (0 : ℝ) 1 := by
  rw [segment_eq_image_lineMap]
  ext ⟨⟨x, y⟩, t⟩
  constructor
  · rintro ⟨r, hr, heq⟩
    have hline : AffineMap.lineMap (((0 : ℝ), b), (0 : ℝ)) ((0, b), 1) r =
        ((0, b), r) := by
      simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    rw [hline] at heq
    cases heq
    exact ⟨rfl, hr⟩
  · rintro ⟨hxy, ht⟩
    change (x, y) = (0, b) at hxy
    cases hxy
    refine ⟨t, ht, ?_⟩
    simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]

open Classical in
private theorem exists_vertical_complex (b : ℝ) :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      K.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 1 K ∧
        K.space = spliceEmbedding '' ({((0 : ℝ), b)} ×ˢ Icc (0 : ℝ) 1) ∧
          (boundaryComplex 1 K).space =
            {spliceEmbedding ((0, b), 0), spliceEmbedding ((0, b), 1)} := by
  classical
  let a := spliceEmbedding (((0 : ℝ), b), (0 : ℝ))
  let d := spliceEmbedding (((0 : ℝ), b), (1 : ℝ))
  have had : a ≠ d := by
    intro h
    have hh := congrArg Prod.snd (spliceEmbedding.injective h)
    norm_num at hh
  let K := simplexComplex ({a, d} : Finset (EuclideanSpace ℝ (Fin 3)))
    (affineIndependent_coe_pair had)
  have hfin : K.faces.Finite := simplexComplex_faces_finite _ _
  let _ : Finite K.faces := hfin.to_subtype
  have hspace : K.space = segment ℝ a d := by
    rw [simplexComplex_space _ _ (by simp), Finset.coe_pair, convexHull_pair]
  have hball : IsPLBall 1 K.space := hspace ▸ isPLBall_segment had
  refine ⟨K, hfin, hball.isCombinatorialManifoldWithBoundary, ?_, ?_⟩
  · rw [hspace]
    change segment ℝ (spliceEmbedding ((0, b), 0)) (spliceEmbedding ((0, b), 1)) = _
    have himage := image_segment ℝ spliceEmbedding.toLinearMap.toAffineMap ((0, b), 0) ((0, b), 1)
    change spliceEmbedding '' segment ℝ ((0, b), 0) ((0, b), 1) = _ at himage
    rw [vertical_segment] at himage
    exact himage.symm
  · change (boundaryComplex 1 (simplexComplex _ (affineIndependent_coe_pair had))).space = _
    rw [boundaryComplex_simplexComplex (n := 0) (affineIndependent_coe_pair had)
      (Finset.card_pair had), simplexBoundary_pair_space had]

open Classical in
theorem crossingProductCell_exists_singular_complex :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      K.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 1 K ∧
        K.space = doublePointSet (⇑crossingProductCell) crossingProductCell.domain ∧
          (boundaryComplex 1 K).space =
            doublePointSet (⇑crossingProductCell) crossingProductCell.domain ∩
              frontier crossingProductSide := by
  classical
  obtain ⟨K, hKfin, hKman, hKspace, hKbd⟩ := exists_vertical_complex 0
  obtain ⟨L, hLfin, hLman, hLspace, hLbd⟩ := exists_vertical_complex 3
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  have hdis : Disjoint K.space L.space := by
    rw [hKspace, hLspace]
    apply Set.disjoint_left.mpr
    rintro z ⟨p, hp, hpz⟩ ⟨q, hq, hqz⟩
    have hpq := spliceEmbedding.injective (hpz.trans hqz.symm)
    have hx : ((0 : ℝ), (0 : ℝ)) = ((0 : ℝ), (3 : ℝ)) :=
      hp.1.symm.trans ((congrArg Prod.fst hpq).trans hq.1)
    norm_num at hx
  obtain ⟨R, hRfin, hRman, hRspace, hRbd⟩ :=
    hKman.exists_space_disjoint_union K L hLman hdis
  have hRbd' : (boundaryComplex 1 R).space =
      (boundaryComplex 1 K).space ∪ (boundaryComplex 1 L).space := by
    convert hRbd using 1 <;> congr 5 <;> exact Subsingleton.elim _ _
  have hdouble : R.space = doublePointSet (⇑crossingProductCell) crossingProductCell.domain := by
    rw [hRspace, hKspace, hLspace, crossingProductCell_doublePointSet, union_prod, image_union]
  refine ⟨R, hRfin, hRman, hdouble, ?_⟩
  rw [hRbd', hKbd, hLbd, crossingProductCell_doublePointSet]
  have hfront : frontier crossingProductSide =
      spliceEmbedding '' frontier crossingProductBox :=
    (spliceEmbedding.toHomeomorph.image_frontier _).symm
  rw [hfront, ← Set.image_inter spliceEmbedding.injective]
  have hbd : (({((0 : ℝ), (0 : ℝ))} ∪ {((0 : ℝ), (3 : ℝ))}) ×ˢ Icc (0 : ℝ) 1) ∩
      frontier crossingProductBox =
        {(((0 : ℝ), (0 : ℝ)), (0 : ℝ)), ((0, 0), 1)} ∪ {((0, 3), 0), ((0, 3), 1)} := by
    ext ⟨⟨x, y⟩, t⟩
    constructor
    · rintro ⟨⟨h | h, ht⟩, hfront⟩
      · change (x, y) = (0, 0) at h
        cases h
        rcases (coordinate_mem_frontier_box (by norm_num) (by norm_num) ht).mp hfront with
          rfl | rfl <;> simp
      · change (x, y) = (0, 3) at h
        cases h
        rcases (coordinate_mem_frontier_box (by norm_num) (by norm_num) ht).mp hfront with
          rfl | rfl <;> simp
    · rintro ((h | h) | (h | h)) <;> cases h
      all_goals
        refine ⟨by norm_num, ?_⟩
        apply (coordinate_mem_frontier_box (by norm_num) (by norm_num) (by norm_num)).mpr
        simp
  rw [hbd, image_union, image_pair, image_pair]

theorem crossingProductCell_nonempty_normalSingularSetTriangulation :
    Nonempty (NormalSingularSetTriangulation crossingProductCell
      (frontier crossingProductSide)) := by
  classical
  obtain ⟨K, hKfin, hKman, hKspace, hKbd⟩ := crossingProductCell_exists_singular_complex
  let _ : Finite K.faces := hKfin.to_subtype
  have hid := (isPolyhedron_space K).isPLHomeomorphOn_id
  let T : PLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 (EuclideanSpace ℝ (Fin 3)) K.space := {
    complex := K
    finite_faces := hKfin
    map := id
    bijOn := bijOn_id _
    continuousOn := continuous_id.continuousOn
    isPiecewiseAffineOn_chart := by
      intro e he
      have heq : e = OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 3)) := by
        simpa using he
      subst e
      simpa using hid.isPiecewiseAffineOn
    isPiecewiseAffineOn_chart_symm := by
      intro e he
      have heq : e = OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 3)) := by
        simpa using he
      subst e
      simpa using hid.isPiecewiseAffineOn_invFunOn }
  exact ⟨{
    carrier := K.space
    piece := ⟨3, T⟩
    complex := K
    finite_faces := hKfin
    faces_subset := subset_rfl
    isManifoldWithBoundary := hKman
    map_space := by simpa [T] using hKspace
    map_boundary := by simpa [T] using hKbd }⟩

theorem crossingProductCell_nonempty_normalSingularCellData
    {B : Set (EuclideanSpace ℝ (Fin 3))}
    (hB : Set.range crossingProductCell.boundary ⊆ B) :
    Nonempty (NormalSingularCellData crossingProductCell (frontier crossingProductSide) B) := by
  obtain ⟨T⟩ := crossingProductCell_nonempty_normalSingularSetTriangulation
  refine ⟨{
    locallyInjective := crossingProductCell_locallyInjective
    fiber_le_two := crossingProductCell_fiber_le_two
    boundary_image_subset := hB
    image_inter_boundary := crossingProductCell_image_inter_frontier_side
    singularSet := T
    crossing := ?_ }⟩
  intro y hy
  refine ⟨OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 3)), by simp, mem_univ _, ?_⟩
  simpa using crossingProductCell_hasPLNormalDoubleCrossingAt hy

theorem hasPLCrossingAt_coordinate_rectangles {l b u t : ℝ}
    (hl : l < b) (hu : b < u) (ht0 : 0 < t) (ht1 : t < 1) :
    HasPLCrossingAt ((Icc (-1 : ℝ) 1 ×ˢ {b}) ×ˢ Icc (0 : ℝ) 1)
      (({0} ×ˢ Icc l u) ×ˢ Icc (0 : ℝ) 1) ((0, b), t) :=
  coordinate_rectangles_crossing hl hu ht0 ht1

theorem hasPLBoundaryCrossingAt_coordinate_rectangles_zero {l b u : ℝ}
    (hl : l < b) (hu : b < u) :
    HasPLBoundaryCrossingAt {q : (ℝ × ℝ) × ℝ | 0 ≤ q.2}
      ((Icc (-1 : ℝ) 1 ×ˢ {b}) ×ˢ Icc (0 : ℝ) 1)
      (({0} ×ˢ Icc l u) ×ˢ Icc (0 : ℝ) 1) ((0, b), 0) :=
  coordinate_rectangles_boundary_zero hl hu

theorem hasPLBoundaryCrossingAt_coordinate_rectangles_one {l b u : ℝ}
    (hl : l < b) (hu : b < u) :
    HasPLBoundaryCrossingAt {q : (ℝ × ℝ) × ℝ | q.2 ≤ 1}
      ((Icc (-1 : ℝ) 1 ×ˢ {b}) ×ˢ Icc (0 : ℝ) 1)
      (({0} ×ˢ Icc l u) ×ˢ Icc (0 : ℝ) 1) ((0, b), 1) :=
  coordinate_rectangles_boundary_one hl hu

open Classical in
theorem exists_simplicialComplex_vertical_interval (b : ℝ) :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      K.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 1 K ∧
        K.space = spliceEmbedding '' ({((0 : ℝ), b)} ×ˢ Icc (0 : ℝ) 1) ∧
          (boundaryComplex 1 K).space =
            {spliceEmbedding ((0, b), 0), spliceEmbedding ((0, b), 1)} :=
  exists_vertical_complex b

theorem HasPLNormalDoubleCrossingAt.postcomp_continuousLinearEquiv
    {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {f : E → F} {P : Set E} {B : Set F} {y : F}
    (hD : HasPLNormalDoubleCrossingAt f P B y) (e : F ≃L[ℝ] V) :
    HasPLNormalDoubleCrossingAt (e ∘ f) P (e '' B) (e y) :=
  normal_double_crossing_postcomp_linearEquiv hD e

end DifferentialGeometry.Topology.PiecewiseLinear
