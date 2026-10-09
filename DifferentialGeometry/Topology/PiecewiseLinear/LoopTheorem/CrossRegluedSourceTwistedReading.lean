/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import
  DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceTwistedCandidate

import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceTwistedSide

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private def bandPos : Set (ℝ × ℝ) := Icc (15 / 16 : ℝ) (17 / 16) ×ˢ Icc (0 : ℝ) 1

private def bandNeg : Set (ℝ × ℝ) := Icc (-1 / 16 : ℝ) (1 / 16) ×ˢ Icc (0 : ℝ) 1

private noncomputable def bandAffinePos : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) :=
  ((8 : ℝ) • (LinearMap.fst ℝ ℝ ℝ).toAffineMap - AffineMap.const ℝ _ (13 / 2)).prod
    (AffineMap.const ℝ _ 1 - (LinearMap.snd ℝ ℝ ℝ).toAffineMap)

private noncomputable def bandAffineNeg : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) :=
  ((8 : ℝ) • (LinearMap.fst ℝ ℝ ℝ).toAffineMap + AffineMap.const ℝ _ (7 / 2)).prod
    (LinearMap.snd ℝ ℝ ℝ).toAffineMap

private theorem isPLHomeomorphOn_bandAffinePos :
    IsPLHomeomorphOn (⇑bandAffinePos) bandPos seamRectPos := by
  have hpoly : IsPolyhedron bandPos := (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron
  apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hpoly
    ((isPiecewiseAffineOn_of_affine bandAffinePos isOpen_univ).mono_of_isPolyhedron
      hpoly (subset_univ _))
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, t⟩ ⟨hs, ht⟩
    change (8 * s - 13 / 2 ∈ Icc (1 : ℝ) 2) ∧ (1 - t ∈ Icc (0 : ℝ) 1)
    exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩,
      ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩
  · intro p _ q _ heq
    have hs := congrArg Prod.fst heq
    have ht := congrArg Prod.snd heq
    change 8 * p.1 - 13 / 2 = 8 * q.1 - 13 / 2 at hs
    change 1 - p.2 = 1 - q.2 at ht
    exact Prod.ext (by linarith) (by linarith)
  · rintro ⟨s, t⟩ ⟨hs, ht⟩
    refine ⟨((s + 13 / 2) / 8, 1 - t),
      ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩,
        ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩, ?_⟩
    ext <;> dsimp [bandAffinePos] <;> ring

private theorem isPLHomeomorphOn_bandAffineNeg :
    IsPLHomeomorphOn (⇑bandAffineNeg) bandNeg seamRectNeg := by
  have hpoly : IsPolyhedron bandNeg := (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron
  apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hpoly
    ((isPiecewiseAffineOn_of_affine bandAffineNeg isOpen_univ).mono_of_isPolyhedron
      hpoly (subset_univ _))
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, t⟩ ⟨hs, ht⟩
    change (8 * s + 7 / 2 ∈ Icc (3 : ℝ) 4) ∧ (t ∈ Icc (0 : ℝ) 1)
    exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, ht⟩
  · intro p _ q _ heq
    have hs := congrArg Prod.fst heq
    have ht := congrArg Prod.snd heq
    change 8 * p.1 + 7 / 2 = 8 * q.1 + 7 / 2 at hs
    change p.2 = q.2 at ht
    exact Prod.ext (by linarith) ht
  · rintro ⟨s, t⟩ ⟨hs, ht⟩
    refine ⟨((s - 7 / 2) / 8, t),
      ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, ht⟩, ?_⟩
    (ext <;> dsimp [bandAffineNeg]); ring

private noncomputable def sheetPos : (ℝ × ℝ) → (ℝ × ℝ) × ℝ :=
  seamSheetPos ∘ ⇑bandAffinePos

private noncomputable def sheetNeg : (ℝ × ℝ) → (ℝ × ℝ) × ℝ :=
  seamSheetNeg ∘ ⇑bandAffineNeg

private theorem sheetPos_apply (p : ℝ × ℝ) :
    sheetPos p = ((max (16 * (1 - p.1)) 0, min (16 * (1 - p.1)) 0), 1 - p.2) := by
  have h : 3 - 2 * (8 * p.1 - 13 / 2) = 16 * (1 - p.1) := by ring
  change ((max (3 - 2 * (8 * p.1 - 13 / 2)) 0,
    min (3 - 2 * (8 * p.1 - 13 / 2)) 0), 1 - p.2) = _
  rw [h]

private theorem sheetNeg_apply (p : ℝ × ℝ) :
    sheetNeg p = ((min (16 * p.1) 0, max (16 * p.1) 0), p.2) := by
  have h : 2 * (8 * p.1 + 7 / 2) - 7 = 16 * p.1 := by ring
  change ((min (2 * (8 * p.1 + 7 / 2) - 7) 0,
    max (2 * (8 * p.1 + 7 / 2) - 7) 0), p.2) = _
  rw [h]

private theorem map_eq_pos {p : ℝ × ℝ} (hp : p ∈ bandPos) :
    crossRegluedTwistedMap p = twistedTubeChart (sheetPos p) := by
  rw [sheetPos_apply]
  rcases le_or_gt p.1 1 with h | h
  · rw [max_eq_left (by linarith : 0 ≤ 16 * (1 - p.1)),
      min_eq_right (by linarith : 0 ≤ 16 * (1 - p.1)), twistedTubeChart_horizontal,
      crossRegluedTwistedMap_middle ⟨by linarith [hp.1.1], h⟩]
    congr 1
    (ext <;> dsimp); ring
  · rw [max_eq_right (by linarith : 16 * (1 - p.1) ≤ 0),
      min_eq_left (by linarith : 16 * (1 - p.1) ≤ 0), twistedTubeChart_vertical,
      crossRegluedTwistedMap_right h.le]
    congr 1
    ext <;> dsimp <;> ring

private theorem map_eq_neg {p : ℝ × ℝ} (hp : p ∈ bandNeg) :
    crossRegluedTwistedMap p = twistedTubeChart (sheetNeg p) := by
  rw [sheetNeg_apply]
  rcases le_or_gt p.1 0 with h | h
  · rw [min_eq_left (by linarith : 16 * p.1 ≤ 0),
      max_eq_right (by linarith : 16 * p.1 ≤ 0), twistedTubeChart_horizontal,
      crossRegluedTwistedMap_left h]
    congr 1
    (ext <;> dsimp); ring
  · rw [min_eq_right (by linarith : 0 ≤ 16 * p.1),
      max_eq_left (by linarith : 0 ≤ 16 * p.1), twistedTubeChart_vertical,
      crossRegluedTwistedMap_middle ⟨h.le, by linarith [hp.1.2]⟩]
    congr 1
    (ext <;> dsimp); ring

private theorem original_mem_tube {p : ℝ × ℝ} (hp : p ∈ twistedSourceRect) :
    twistedStripMap p ∈ twistedTubeChart '' spliceCylinder ↔ p ∈ bandPos ∪ bandNeg := by
  constructor
  · rintro ⟨q, hq, heq⟩
    obtain ⟨n, hn⟩ := halfTurnProjection_eq_iff.mp heq.symm
    have hx := congrArg (fun w : (ℝ × ℝ) × ℝ => w.1.1) hn
    have hy := congrArg (fun w : (ℝ × ℝ) × ℝ => w.1.2) hn
    change (q.1.1 - q.1.2) / 16 = p.1 + (n : ℝ) at hx
    change -1 / 2 + (q.1.1 + q.1.2) / 16 = (-1 : ℝ) ^ n * (p.1 - 1 / 2) at hy
    have hsq := mem_spliceSquare.mp hq.1
    have hnlo : (-2 : ℤ) < n := by
      have h : (-2 : ℝ) < n := by linarith [hsq.1.1, hsq.2.2, hp.1.2]
      exact_mod_cast h
    have hnhi : n < 1 := by
      have h : (n : ℝ) < 1 := by linarith [hsq.1.2, hsq.2.1, hp.1.1]
      exact_mod_cast h
    interval_cases n
    · norm_num at hx hy
      exact Or.inl ⟨⟨by linarith [hsq.2.2], by linarith [hsq.2.1]⟩, hp.2⟩
    · norm_num at hx hy
      exact Or.inr ⟨⟨by linarith [hsq.1.1], by linarith [hsq.1.2]⟩, hp.2⟩
  · rintro (hp' | hp')
    · refine ⟨((0, 16 * (1 - p.1)), 1 - p.2), ⟨?_, ?_⟩, ?_⟩
      · exact mem_spliceSquare.mpr ⟨by norm_num,
          ⟨by linarith [hp'.1.2], by linarith [hp'.1.1]⟩⟩
      · exact ⟨by linarith [hp'.2.2], by linarith [hp'.2.1]⟩
      · rw [twistedTubeChart_vertical]
        congr 1
        ext <;> dsimp <;> ring
    · refine ⟨((16 * p.1, 0), p.2), ⟨?_, hp'.2⟩, ?_⟩
      · exact mem_spliceSquare.mpr
          ⟨⟨by linarith [hp'.1.1], by linarith [hp'.1.2]⟩, by norm_num⟩
      · rw [twistedTubeChart_horizontal]
        congr 1
        (ext <;> dsimp); ring

private theorem reglued_mem_tube {p : ℝ × ℝ} (hp : p ∈ twistedSourceRect) :
    crossRegluedTwistedMap p ∈ twistedTubeChart '' spliceCylinder ↔ p ∈ bandPos ∪ bandNeg := by
  rcases le_or_gt p.1 0 with h0 | h0
  · rw [crossRegluedTwistedMap_left h0]
    exact original_mem_tube hp
  rcases le_or_gt 1 p.1 with h1 | h1
  · rw [crossRegluedTwistedMap_right h1]
    exact original_mem_tube hp
  have href : (1 - p.1, 1 - p.2) ∈ twistedSourceRect :=
    ⟨⟨by linarith, by linarith⟩, ⟨by linarith [hp.2.2], by linarith [hp.2.1]⟩⟩
  rw [crossRegluedTwistedMap_middle ⟨h0.le, h1.le⟩, original_mem_tube href]
  constructor
  · rintro (⟨hs, _⟩ | ⟨hs, _⟩)
    · exact Or.inr ⟨⟨by linarith [hs.2], by linarith [hs.1]⟩, hp.2⟩
    · exact Or.inl ⟨⟨by linarith [hs.2], by linarith [hs.1]⟩, hp.2⟩
  · rintro (⟨hs, _⟩ | ⟨hs, _⟩)
    · exact Or.inr ⟨⟨by linarith [hs.2], by linarith [hs.1]⟩, href.2⟩
    · exact Or.inl ⟨⟨by linarith [hs.2], by linarith [hs.1]⟩, href.2⟩

private theorem band_subset : bandPos ∪ bandNeg ⊆ twistedSourceRect := by
  rintro p (⟨hs, ht⟩ | ⟨hs, ht⟩) <;>
    exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, ht⟩

private noncomputable def coord (x : EuclideanSpace ℝ (Fin 2)) :
    Bool × ((ℝ × ℝ) × ℝ) :=
  if (1 / 2 : ℝ) ≤ (seamWitnessPlane.symm x).1 then
    (true, sheetPos (seamWitnessPlane.symm x))
  else (false, sheetNeg (seamWitnessPlane.symm x))

private theorem coord_pos {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ seamWitnessPlane '' bandPos) :
    coord x = (true, sheetPos (seamWitnessPlane.symm x)) := by
  have h := mem_image_seamWitnessPlane.mp hx
  exact ite_eq_left (by linarith [h.1.1])

private theorem coord_neg {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ seamWitnessPlane '' bandNeg) :
    coord x = (false, sheetNeg (seamWitnessPlane.symm x)) := by
  have h := mem_image_seamWitnessPlane.mp hx
  exact ite_eq_right (by linarith [h.1.2])

private def faceRect : Set (ℝ × ℝ) :=
  (Icc (-1 / 4 : ℝ) (-1 / 16) ×ˢ Icc (0 : ℝ) 1) ∪
    (Icc (1 / 16 : ℝ) (15 / 16) ×ˢ Icc (0 : ℝ) 1) ∪
      (Icc (17 / 16 : ℝ) (5 / 4) ×ˢ Icc (0 : ℝ) 1)

private theorem band_union : bandPos ∪ bandNeg ∪ faceRect = twistedSourceRect := by
  apply Subset.antisymm
  · rintro p (h | ((⟨hs, ht⟩ | ⟨hs, ht⟩) | ⟨hs, ht⟩))
    · exact band_subset h
    all_goals exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, ht⟩
  · rintro p ⟨hs, ht⟩
    rcases le_or_gt p.1 (-1 / 16) with h1 | h1
    · exact Or.inr (Or.inl (Or.inl ⟨⟨hs.1, h1⟩, ht⟩))
    rcases le_or_gt p.1 (1 / 16) with h2 | h2
    · exact Or.inl (Or.inr ⟨⟨h1.le, h2⟩, ht⟩)
    rcases le_or_gt p.1 (15 / 16) with h3 | h3
    · exact Or.inr (Or.inl (Or.inr ⟨⟨h2.le, h3⟩, ht⟩))
    rcases le_or_gt p.1 (17 / 16) with h4 | h4
    · exact Or.inl (Or.inl ⟨⟨h3.le, h4⟩, ht⟩)
    · exact Or.inr (Or.inr ⟨⟨h4.le, hs.2⟩, ht⟩)

private theorem band_boundary_iff {x : EuclideanSpace ℝ (Fin 2)}
    (hx : seamWitnessPlane.symm x ∈ bandPos ∪ bandNeg) :
    x ∈ frontier crossRegluedTwistedCell.domain ↔
      (seamWitnessPlane.symm x).2 = 0 ∨ (seamWitnessPlane.symm x).2 = 1 := by
  have hp := band_subset hx
  have hbounds : -1 / 4 < (seamWitnessPlane.symm x).1 ∧
      (seamWitnessPlane.symm x).1 < 5 / 4 := by
    rcases hx with hx | hx <;> exact ⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩
  change x ∈ frontier (seamWitnessPlane '' (Icc (-1 / 4 : ℝ) (5 / 4) ×ˢ Icc (0 : ℝ) 1)) ↔ _
  rw [mem_frontier_seamWitnessPlane_image_Icc_prod (by norm_num)]
  constructor
  · rintro (⟨_, ht⟩ | ⟨hs, _⟩)
    · exact ht
    · rcases hs with hs | hs <;> linarith [hbounds.1, hbounds.2]
  · intro ht
    exact Or.inl ⟨hp.1, ht⟩

noncomputable def crossRegluedTwistedReading :
    PLCrossSeamReading twistedTubeChart crossRegluedTwistedCell where
  coord := coord
  sourcePos := seamWitnessPlane '' bandPos
  sourceNeg := seamWitnessPlane '' bandNeg
  face := seamWitnessPlane '' faceRect
  isPLHomeomorphOn_pos :=
    ((isPLHomeomorphOn_seamWitnessPlaneSymm
      (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron).trans
        (isPLHomeomorphOn_bandAffinePos.trans isPLHomeomorphOn_seamSheetPos)).congr
          fun x hx => by rw [coord_pos hx]; rfl
  isPLHomeomorphOn_neg :=
    ((isPLHomeomorphOn_seamWitnessPlaneSymm
      (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron).trans
        (isPLHomeomorphOn_bandAffineNeg.trans isPLHomeomorphOn_seamSheetNeg)).congr
          fun x hx => by rw [coord_neg hx]; rfl
  coord_fst_pos := fun _ hx => by rw [coord_pos hx]
  coord_fst_neg := fun _ hx => by rw [coord_neg hx]
  source_eq := by
    ext x
    change (x ∈ seamWitnessPlane '' bandPos ∨ x ∈ seamWitnessPlane '' bandNeg) ↔
      x ∈ seamWitnessPlane '' twistedSourceRect ∧
        crossRegluedTwistedMap (seamWitnessPlane.symm x) ∈ twistedTubeChart '' spliceCylinder
    simp only [mem_image_seamWitnessPlane]
    constructor
    · intro h
      exact ⟨band_subset h, (reglued_mem_tube (band_subset h)).mpr h⟩
    · rintro ⟨h, ht⟩
      exact (reglued_mem_tube h).mp ht
  isPolyhedron_face := isPolyhedron_image_seamWitnessPlane
    (((isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron.union
      (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron).union
        (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron)
  union_eq := by rw [← image_union, ← image_union, band_union]; rfl
  reglued_eq := by
    rintro x (hx | hx)
    · change crossRegluedTwistedMap (seamWitnessPlane.symm x) =
        twistedTubeChart (crossSeamInclude (coord x))
      rw [coord_pos hx]
      exact map_eq_pos (mem_image_seamWitnessPlane.mp hx)
    · change crossRegluedTwistedMap (seamWitnessPlane.symm x) =
        twistedTubeChart (crossSeamInclude (coord x))
      rw [coord_neg hx]
      exact map_eq_neg (mem_image_seamWitnessPlane.mp hx)
  overlap_lateral := by
    rintro x ⟨hx | hx, hf⟩
    · have hp := mem_image_seamWitnessPlane.mp hx
      have hface := mem_image_seamWitnessPlane.mp hf
      rw [coord_pos hx]
      refine ⟨?_, ⟨by change 0 ≤ 1 - (seamWitnessPlane.symm x).2; linarith [hp.2.2],
        by change 1 - (seamWitnessPlane.symm x).2 ≤ 1; linarith [hp.2.1]⟩⟩
      change seamBentPos (8 * (seamWitnessPlane.symm x).1 - 13 / 2) ∈ _
      rcases hface with (⟨hs, _⟩ | ⟨hs, _⟩) | ⟨hs, _⟩
      · linarith [hp.1.1, hs.2]
      · have h : 8 * (seamWitnessPlane.symm x).1 - 13 / 2 = 1 :=
          by linarith [hp.1.1, hs.2]
        rw [h]
        exact seamBentPos_one_mem
      · have h : 8 * (seamWitnessPlane.symm x).1 - 13 / 2 = 2 :=
          by linarith [hp.1.2, hs.1]
        rw [h]
        exact seamBentPos_two_mem
    · have hp := mem_image_seamWitnessPlane.mp hx
      have hface := mem_image_seamWitnessPlane.mp hf
      rw [coord_neg hx]
      refine ⟨?_, hp.2⟩
      change seamBentNeg (8 * (seamWitnessPlane.symm x).1 + 7 / 2) ∈ _
      rcases hface with (⟨hs, _⟩ | ⟨hs, _⟩) | ⟨hs, _⟩
      · have h : 8 * (seamWitnessPlane.symm x).1 + 7 / 2 = 3 :=
          by linarith [hp.1.1, hs.2]
        rw [h]
        exact seamBentNeg_three_mem
      · have h : 8 * (seamWitnessPlane.symm x).1 + 7 / 2 = 4 :=
          by linarith [hp.1.2, hs.1]
        rw [h]
        exact seamBentNeg_four_mem
      · linarith [hp.1.2, hs.1]
  boundary_iff_end := by
    rintro x (hx | hx)
    · rw [coord_pos hx, band_boundary_iff (Or.inl (mem_image_seamWitnessPlane.mp hx))]
      change (seamWitnessPlane.symm x).2 = 0 ∨ (seamWitnessPlane.symm x).2 = 1 ↔
        1 - (seamWitnessPlane.symm x).2 = 0 ∨ 1 - (seamWitnessPlane.symm x).2 = 1
      constructor
      · rintro (h | h)
        · exact Or.inr (by linarith)
        · exact Or.inl (by linarith)
      · rintro (h | h)
        · exact Or.inr (by linarith)
        · exact Or.inl (by linarith)
    · rw [coord_neg hx]
      exact band_boundary_iff (Or.inr (mem_image_seamWitnessPlane.mp hx))

theorem crossRegluedTwistedReading_tubeSource_ssubset :
    crossRegluedTwistedReading.tubeSource ⊂ crossRegluedTwistedCell.domain :=
  crossRegluedTwistedReading.source_ssubset_domain

theorem twistedStripCell_exists_crossReading {B : Set halfTurnQuotient}
    (hD : NormalSingularCellData twistedStripCell (frontier twistedStripSide) B) :
    ∃ (c : hD.singularSet.Branch)
      (T : CrossSeamTubeData hD c (halfTurnSlabChart 0).source)
      (R : PLCrossSeamReading T.chart crossRegluedTwistedCell)
      (C : PLSeamTubeChart halfTurnQuotient T.chart),
      hD.singularSet.complexity = 1 ∧ hD.singularSet.IsBoundaryBranch c ∧
      T.chart = twistedTubeChart ∧ hD.IsCrossRegluedCell c crossRegluedTwistedCell ∧
      IsPLBoundarySide twistedStripCell twistedStripSide (frontier twistedStripSide) ∧
      T.chart '' spliceCylinder ⊆ twistedStripSide ∧
      T.chart '' spliceCylinder ∩ frontier twistedStripSide = T.chart '' spliceEndDisks ∧
      R.tubeSource ⊂ crossRegluedTwistedCell.domain ∧
      doublePointSet (R.resolvedCell C) R.tubeSource = ∅ := by
  obtain ⟨c, T, hn, hb, hc, hT, ⟨C⟩, hside, hbd, -⟩ := twistedStripCell_exists_branchTube hD
  have hR : Nonempty (PLCrossSeamReading T.chart crossRegluedTwistedCell) := by
    rw [hT]
    exact ⟨crossRegluedTwistedReading⟩
  obtain ⟨R⟩ := hR
  exact ⟨c, T, R, C, hn, hb, hT, crossRegluedTwistedCell_isCrossRegluedCell hD hc,
    isPLBoundarySide_twistedStripCell, hside, hbd, R.source_ssubset_domain,
    R.doublePointSet_resolvedCell C⟩

end DifferentialGeometry.Topology.PiecewiseLinear
