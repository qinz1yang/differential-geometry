/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceTwistedChart

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def twistedTubeLift : ((ℝ × ℝ) × ℝ) ≃ₜ ((ℝ × ℝ) × ℝ) where
  toFun p := (((p.1.1 - p.1.2) / 16, -1 / 2 + (p.1.1 + p.1.2) / 16), p.2)
  invFun p := ((8 * (p.1.1 + p.1.2 + 1 / 2), 8 * (p.1.2 + 1 / 2 - p.1.1)), p.2)
  left_inv p := by ext <;> dsimp <;> ring
  right_inv p := by ext <;> dsimp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

noncomputable def twistedTubeChart : ((ℝ × ℝ) × ℝ) → halfTurnQuotient :=
  halfTurnProjection ∘ twistedTubeLift

theorem continuous_twistedTubeChart : Continuous twistedTubeChart :=
  continuous_halfTurnProjection.comp twistedTubeLift.continuous

private theorem twistedTubeLift_bounds {p : (ℝ × ℝ) × ℝ} (hp : p ∈ spliceCylinder) :
    -1 / 4 < (twistedTubeLift p).1.1 ∧ (twistedTubeLift p).1.1 < 1 / 4 ∧
      -3 / 4 < (twistedTubeLift p).1.2 ∧ (twistedTubeLift p).1.2 < 3 / 4 := by
  have h := mem_spliceSquare.mp hp.1
  dsimp [twistedTubeLift]
  constructor
  · linarith [h.1.1, h.2.2]
  constructor
  · linarith [h.1.2, h.2.1]
  constructor
  · linarith [h.1.1, h.2.1]
  · linarith [h.1.2, h.2.2]

theorem twistedTubeChart_injOn : InjOn twistedTubeChart spliceCylinder := by
  intro p hp q hq hpq
  apply twistedTubeLift.injective
  apply halfTurnProjection_injOn_slab 0
  · have h := twistedTubeLift_bounds hp
    simpa only [mem_ofPred_eq, mem_Ioo, zero_sub, zero_add, neg_div] using And.intro h.1 h.2.1
  · have h := twistedTubeLift_bounds hq
    simpa only [mem_ofPred_eq, mem_Ioo, zero_sub, zero_add, neg_div] using And.intro h.1 h.2.1
  · exact hpq

theorem twistedTubeChart_mapsTo_slab :
    MapsTo twistedTubeChart spliceCylinder (halfTurnSlabChart 0).source := by
  intro p hp
  apply (halfTurnSlabChart_side (a := 0) (p := twistedTubeLift p) ?_).1
  have h := twistedTubeLift_bounds hp
  simpa only [mem_Ioo, zero_sub, zero_add, neg_div] using And.intro h.1 h.2.1

theorem twistedTubeChart_core (t : ℝ) :
    twistedTubeChart ((0, 0), t) = twistedStripMap (0, t) := by
  change halfTurnProjection (((0 - 0) / 16, -1 / 2 + (0 + 0) / 16), t) =
    halfTurnProjection ((0, 0 - 1 / 2), t)
  congr 2; norm_num

theorem twistedTubeChart_horizontal (u t : ℝ) :
    twistedTubeChart ((u, 0), t) = twistedStripMap (u / 16, t) := by
  apply congrArg halfTurnProjection
  ext <;> dsimp [twistedTubeLift] <;> ring

theorem twistedTubeChart_vertical (v t : ℝ) :
    twistedTubeChart ((0, v), t) = twistedStripMap (1 - v / 16, 1 - t) := by
  apply halfTurnProjection_eq_iff.mpr
  refine ⟨1, ?_⟩
  ext <;> simp [halfTurnTranslation, twistedTubeLift] <;> ring

private theorem mem_crossingFigure_iff {p : (ℝ × ℝ) × ℝ} :
    p ∈ crossingFigure ↔ p ∈ spliceCylinder ∧ (p.1.1 = 0 ∨ p.1.2 = 0) := by
  change ((p.1 ∈ spliceSquare ∧ p.1.1 = 0) ∨
    (p.1 ∈ spliceSquare ∧ p.1.2 = 0)) ∧ p.2 ∈ Icc (0 : ℝ) 1 ↔
      (p.1 ∈ spliceSquare ∧ p.2 ∈ Icc (0 : ℝ) 1) ∧ (p.1.1 = 0 ∨ p.1.2 = 0)
  tauto

theorem twistedTubeChart_mem_image_iff {p : (ℝ × ℝ) × ℝ} (hp : p ∈ spliceCylinder) :
    twistedTubeChart p ∈ ⇑twistedStripCell '' twistedStripCell.domain ↔
      p ∈ crossingFigure := by
  rw [mem_crossingFigure_iff, and_iff_right hp]
  constructor
  · rintro ⟨z, hz, hzv⟩
    let s := seamWitnessPlane.symm z
    have hs : s ∈ twistedSourceRect := mem_image_seamWitnessPlane.mp hz
    obtain ⟨n, hn⟩ := halfTurnProjection_eq_iff.mp hzv
    have hx := congrArg (fun w : (ℝ × ℝ) × ℝ => w.1.1) hn
    have hy := congrArg (fun w : (ℝ × ℝ) × ℝ => w.1.2) hn
    change (p.1.1 - p.1.2) / 16 = s.1 + (n : ℝ) at hx
    change -1 / 2 + (p.1.1 + p.1.2) / 16 = (-1 : ℝ) ^ n * (s.1 - 1 / 2) at hy
    have hb := twistedTubeLift_bounds hp
    change -1 / 4 < (p.1.1 - p.1.2) / 16 ∧
      (p.1.1 - p.1.2) / 16 < 1 / 4 ∧ _ at hb
    have hnlo : (-2 : ℤ) < n := by
      have h : (-2 : ℝ) < n := by linarith [hb.1, hs.1.2]
      exact_mod_cast h
    have hnhi : n < 1 := by
      have h : (n : ℝ) < 1 := by linarith [hb.2.1, hs.1.1]
      exact_mod_cast h
    interval_cases n
    · norm_num at hx hy
      exact Or.inl (by linarith)
    · norm_num at hx hy
      exact Or.inr (by linarith)
  · intro haxis
    have hsq := mem_spliceSquare.mp hp.1
    rcases haxis with hu | hv
    · refine ⟨seamWitnessPlane (1 - p.1.2 / 16, 1 - p.2),
        mem_image_of_mem _ ⟨⟨by linarith [hsq.2.2], by linarith [hsq.2.1]⟩,
          ⟨by linarith [hp.2.2], by linarith [hp.2.1]⟩⟩, ?_⟩
      change twistedStripMap (seamWitnessPlane.symm
        (seamWitnessPlane (1 - p.1.2 / 16, 1 - p.2))) = _
      rw [ContinuousLinearEquiv.symm_apply_apply]
      have heq : p = ((0, p.1.2), p.2) := Prod.ext (Prod.ext hu rfl) rfl
      exact (twistedTubeChart_vertical p.1.2 p.2).symm.trans
        (congrArg twistedTubeChart heq).symm
    · refine ⟨seamWitnessPlane (p.1.1 / 16, p.2),
        mem_image_of_mem _ ⟨⟨by linarith [hsq.1.1], by linarith [hsq.1.2]⟩, hp.2⟩, ?_⟩
      change twistedStripMap (seamWitnessPlane.symm
        (seamWitnessPlane (p.1.1 / 16, p.2))) = _
      rw [ContinuousLinearEquiv.symm_apply_apply]
      have heq : p = ((p.1.1, 0), p.2) := Prod.ext (Prod.ext rfl hv) rfl
      exact (twistedTubeChart_horizontal p.1.1 p.2).symm.trans
        (congrArg twistedTubeChart heq).symm

theorem twistedTubeChart_image_crossingFigure :
    twistedTubeChart '' crossingFigure =
      ⇑twistedStripCell '' twistedStripCell.domain ∩ twistedTubeChart '' spliceCylinder := by
  apply Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    have hcyl := (mem_crossingFigure_iff.mp hp).1
    exact ⟨(twistedTubeChart_mem_image_iff hcyl).mpr hp, mem_image_of_mem _ hcyl⟩
  · rintro y ⟨hD, p, hp, rfl⟩
    exact mem_image_of_mem _ ((twistedTubeChart_mem_image_iff hp).mp hD)

theorem twistedTubeChart_image_core :
    twistedTubeChart '' spliceCore =
      doublePointSet (⇑twistedStripCell) twistedStripCell.domain := by
  rw [twistedStripCell_doublePointSet]
  apply Subset.antisymm
  · rintro _ ⟨⟨⟨u, v⟩, t⟩, ⟨hxy, ht⟩, rfl⟩
    change (u, v) = (0, 0) at hxy
    cases hxy
    exact ⟨t, ht, (twistedTubeChart_core t).symm⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact ⟨((0, 0), t), ⟨rfl, ht⟩, twistedTubeChart_core t⟩

theorem crossSeamTubeCore_twistedStripCell :
    CrossSeamTubeCore twistedTubeChart
      (⇑twistedStripCell '' twistedStripCell.domain)
      (doublePointSet (⇑twistedStripCell) twistedStripCell.domain)
      (doublePointSet (⇑twistedStripCell) twistedStripCell.domain)
      (halfTurnSlabChart 0).source where
  isOpen_tube := (halfTurnSlabChart 0).open_source
  continuousOn_chart := continuous_twistedTubeChart.continuousOn
  injOn_chart := twistedTubeChart_injOn
  image_subset_tube := (mapsTo_iff_image_subset.mp twistedTubeChart_mapsTo_slab)
  image_spliceCore := twistedTubeChart_image_core
  image_crossingFigure := twistedTubeChart_image_crossingFigure
  double_inter_tube := by
    apply inter_eq_left.mpr
    rw [← twistedTubeChart_image_core]
    exact (image_subset_iff.mpr fun _ hp =>
      twistedTubeChart_mapsTo_slab (spliceCore_subset_spliceCylinder hp))

theorem twistedTubeChart_side : twistedTubeChart '' spliceCylinder ⊆ twistedStripSide := by
  rintro _ ⟨p, hp, rfl⟩
  have hb := twistedTubeLift_bounds hp
  exact ⟨twistedTubeLift p, ⟨⟨mem_univ _, hb.2.2.1.le, hb.2.2.2.le⟩, hp.2⟩, rfl⟩

private theorem twistedTubeChart_mem_boundary_iff {p : (ℝ × ℝ) × ℝ}
    (hp : p ∈ spliceCylinder) :
    twistedTubeChart p ∈ frontier twistedStripSide ↔ p.2 = 0 ∨ p.2 = 1 := by
  change twistedTubeLift p ∈ halfTurnProjection ⁻¹' frontier twistedStripSide ↔ _
  rw [halfTurnProjection_preimage_frontier_twistedStripSide,
    isClosed_twistedSideLift.frontier_eq]
  have hb := twistedTubeLift_bounds hp
  have hmem : twistedTubeLift p ∈ twistedSideLift :=
    ⟨⟨mem_univ _, hb.2.2.1.le, hb.2.2.2.le⟩, hp.2⟩
  rw [mem_sdiff, and_iff_right hmem]
  simp only [twistedSideLift, interior_prod_eq, interior_univ, interior_Icc,
    mem_prod, mem_univ, true_and]
  change ¬ ((-3 / 4 < (twistedTubeLift p).1.2 ∧
    (twistedTubeLift p).1.2 < 3 / 4) ∧ (0 < p.2 ∧ p.2 < 1)) ↔ _
  rw [and_iff_right (And.intro hb.2.2.1 hb.2.2.2)]
  constructor
  · intro ht
    by_cases h0 : p.2 = 0
    · exact Or.inl h0
    · exact Or.inr (by
        have h0' : 0 < p.2 := lt_of_le_of_ne hp.2.1 (fun h => h0 h.symm)
        by_contra h1
        exact ht ⟨h0', lt_of_le_of_ne hp.2.2 h1⟩)
  · rintro (h0 | h1) ⟨ht0, ht1⟩ <;> linarith

theorem twistedTubeChart_boundary :
    twistedTubeChart '' spliceCylinder ∩ frontier twistedStripSide =
      twistedTubeChart '' spliceEndDisks := by
  apply Subset.antisymm
  · rintro y ⟨⟨p, hp, rfl⟩, hb⟩
    exact ⟨p, ⟨hp.1, (twistedTubeChart_mem_boundary_iff hp).mp hb⟩, rfl⟩
  · rintro y ⟨p, hp, rfl⟩
    have hcyl := spliceEndDisks_subset_spliceCylinder hp
    exact ⟨mem_image_of_mem _ hcyl, (twistedTubeChart_mem_boundary_iff hcyl).mpr hp.2⟩

theorem twistedStripMap_cap_not_mem_tube :
    twistedStripMap (-1 / 4, 1 / 2) ∉ twistedTubeChart '' spliceCylinder := by
  rintro ⟨p, hp, heq⟩
  obtain ⟨n, hn⟩ := halfTurnProjection_eq_iff.mp heq.symm
  have hx := congrArg (fun z : (ℝ × ℝ) × ℝ => z.1.1) hn
  change (twistedTubeLift p).1.1 = -1 / 4 + (n : ℝ) at hx
  have hb := twistedTubeLift_bounds hp
  have hlo : (0 : ℤ) < n := by
    have h : (0 : ℝ) < n := by linarith [hb.1]
    exact_mod_cast h
  have hhi : n < 1 := by
    have h : (n : ℝ) < 1 := by linarith [hb.2.1]
    exact_mod_cast h
  omega

theorem twistedTubeChart_crossingFigure_ssubset_image :
    twistedTubeChart '' crossingFigure ⊂ ⇑twistedStripCell '' twistedStripCell.domain := by
  refine ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · rw [twistedTubeChart_image_crossingFigure]
    exact inter_subset_left
  · intro heq
    have hmem : twistedStripMap (-1 / 4, 1 / 2) ∈
        ⇑twistedStripCell '' twistedStripCell.domain := by
      refine ⟨seamWitnessPlane (-1 / 4, 1 / 2),
        mem_image_of_mem _ (by norm_num [twistedSourceRect]), ?_⟩
      change twistedStripMap (seamWitnessPlane.symm (seamWitnessPlane (-1 / 4, 1 / 2))) = _
      rw [ContinuousLinearEquiv.symm_apply_apply]
    rw [← heq, twistedTubeChart_image_crossingFigure] at hmem
    exact twistedStripMap_cap_not_mem_tube hmem.2

end DifferentialGeometry.Topology.PiecewiseLinear
