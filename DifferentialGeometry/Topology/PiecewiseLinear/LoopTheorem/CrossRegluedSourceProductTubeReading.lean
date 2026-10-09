/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceProductTube

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private noncomputable def bandParameter (r c s : ℝ) : ℝ := (s - c) / r + c

private def narrowBand (r c : ℝ) : Set (ℝ × ℝ) :=
  Icc (c - r / 2) (c + r / 2) ×ˢ Icc (0 : ℝ) 1

private noncomputable def bandMap (r c : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (bandParameter r c p.1, p.2)

private theorem bandParameter_mul {r : ℝ} (hr : r ≠ 0) (c s : ℝ) :
    r * (bandParameter r c s - c) = s - c := by
  dsimp [bandParameter]
  field_simp
  ring

private theorem bandParameter_lower {r : ℝ} (hr : r ≠ 0) (c : ℝ) :
    bandParameter r c (c - r / 2) = c - 1 / 2 := by
  dsimp [bandParameter]
  field_simp
  ring

private theorem bandParameter_upper {r : ℝ} (hr : r ≠ 0) (c : ℝ) :
    bandParameter r c (c + r / 2) = c + 1 / 2 := by
  dsimp [bandParameter]
  field_simp
  ring

private theorem bandParameter_mem {r : ℝ} (hr : 0 < r) {c s : ℝ} :
    bandParameter r c s ∈ Icc (c - 1 / 2) (c + 1 / 2) ↔
      s ∈ Icc (c - r / 2) (c + r / 2) := by
  have heq := bandParameter_mul hr.ne' c s
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith

private theorem bijOn_bandMap {r : ℝ} (hr : 0 < r) (c : ℝ) :
    BijOn (bandMap r c) (narrowBand r c)
      (Icc (c - 1 / 2) (c + 1 / 2) ×ˢ Icc (0 : ℝ) 1) := by
  refine ⟨fun p hp => ⟨(bandParameter_mem hr).mpr hp.1, hp.2⟩, ?_, ?_⟩
  · intro p _ q _ hpq
    have h1 := congrArg Prod.fst hpq
    have h2 := congrArg Prod.snd hpq
    change p.2 = q.2 at h2
    apply Prod.ext ?_ h2
    have hp := bandParameter_mul hr.ne' c p.1
    have hq := bandParameter_mul hr.ne' c q.1
    change bandParameter r c p.1 = bandParameter r c q.1 at h1
    rw [h1] at hp
    linarith
  · rintro ⟨s, t⟩ ⟨hs, ht⟩
    have heq : bandParameter r c (c + r * (s - c)) = s := by
      dsimp [bandParameter]
      field_simp
      ring
    refine ⟨(c + r * (s - c), t), ⟨?_, ht⟩, ?_⟩
    · apply (bandParameter_mem hr).mp
      rwa [heq]
    · exact Prod.ext heq rfl

private theorem isPiecewiseAffineOn_bandMap (r c : ℝ) :
    IsPiecewiseAffineOn (bandMap r c) univ := by
  have h1 : IsPiecewiseAffineOn (bandParameter r c) univ :=
    (isPiecewiseAffineOn_of_affine (seamLine r⁻¹ (c - r⁻¹ * c)) isOpen_univ).congr
      fun s _ => by dsimp [bandParameter, seamLine]; ring
  have h2 : IsPiecewiseAffineOn (id : ℝ → ℝ) univ :=
    isPiecewiseAffineOn_of_affine (AffineMap.id ℝ ℝ) isOpen_univ
  have h := h1.prodMap h2
  rw [univ_prod_univ] at h
  exact h.congr fun _ _ => rfl

private theorem isPLHomeomorphOn_bandMap {r : ℝ} (hr : 0 < r) (c : ℝ) :
    IsPLHomeomorphOn (bandMap r c) (narrowBand r c)
      (Icc (c - 1 / 2) (c + 1 / 2) ×ˢ Icc (0 : ℝ) 1) := by
  have hpoly : IsPolyhedron (narrowBand r c) :=
    isHPolytope_Icc.isPolyhedron.prod isHPolytope_Icc.isPolyhedron
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hpoly
    ((isPiecewiseAffineOn_bandMap r c).mono_of_isPolyhedron hpoly (subset_univ _))
    (bijOn_bandMap hr c)

private noncomputable def narrowSheetPos (r : ℝ) : (ℝ × ℝ) → (ℝ × ℝ) × ℝ :=
  seamSheetPos ∘ bandMap r (3 / 2)

private noncomputable def narrowSheetNeg (r : ℝ) : (ℝ × ℝ) → (ℝ × ℝ) × ℝ :=
  seamSheetNeg ∘ bandMap r (7 / 2)

private theorem isPLHomeomorphOn_narrowSheetPos {r : ℝ} (hr : 0 < r) :
    IsPLHomeomorphOn (narrowSheetPos r) (narrowBand r (3 / 2)) bentSheetPos := by
  have h := isPLHomeomorphOn_bandMap hr (3 / 2)
  norm_num only [show (3 / 2 - 1 / 2 : ℝ) = 1 by norm_num,
    show (3 / 2 + 1 / 2 : ℝ) = 2 by norm_num] at h
  exact h.trans isPLHomeomorphOn_seamSheetPos

private theorem isPLHomeomorphOn_narrowSheetNeg {r : ℝ} (hr : 0 < r) :
    IsPLHomeomorphOn (narrowSheetNeg r) (narrowBand r (7 / 2)) bentSheetNeg := by
  have h := isPLHomeomorphOn_bandMap hr (7 / 2)
  norm_num only [show (7 / 2 - 1 / 2 : ℝ) = 3 by norm_num,
    show (7 / 2 + 1 / 2 : ℝ) = 4 by norm_num] at h
  exact h.trans isPLHomeomorphOn_seamSheetNeg

private theorem scale_narrowSheetPos {r : ℝ} (hr : 0 < r) (p : ℝ × ℝ) :
    crossingProductTubeScale r hr.ne' (narrowSheetPos r p) = seamSheetPos p := by
  have heq : r * (3 - 2 * bandParameter r (3 / 2) p.1) = 3 - 2 * p.1 := by
    have h := bandParameter_mul hr.ne' (3 / 2) p.1
    nlinarith
  change ((r * max (3 - 2 * bandParameter r (3 / 2) p.1) 0,
    r * min (3 - 2 * bandParameter r (3 / 2) p.1) 0), p.2) = _
  rw [mul_max_of_nonneg _ _ hr.le, mul_min_of_nonneg _ _ hr.le, heq, mul_zero]
  rfl

private theorem scale_narrowSheetNeg {r : ℝ} (hr : 0 < r) (p : ℝ × ℝ) :
    crossingProductTubeScale r hr.ne' (narrowSheetNeg r p) = seamSheetNeg p := by
  have heq : r * (2 * bandParameter r (7 / 2) p.1 - 7) = 2 * p.1 - 7 := by
    have h := bandParameter_mul hr.ne' (7 / 2) p.1
    nlinarith
  change ((r * min (2 * bandParameter r (7 / 2) p.1 - 7) 0,
    r * max (2 * bandParameter r (7 / 2) p.1 - 7) 0), p.2) = _
  rw [mul_min_of_nonneg _ _ hr.le, mul_max_of_nonneg _ _ hr.le, heq, mul_zero]
  rfl

private theorem narrowBand_subset_pos {r : ℝ} (hr1 : r ≤ 1) :
    narrowBand r (3 / 2) ⊆ seamRectPos := by
  rintro p ⟨⟨h1, h2⟩, ht⟩
  exact ⟨⟨by linarith, by linarith⟩, ht⟩

private theorem narrowBand_subset_neg {r : ℝ} (hr1 : r ≤ 1) :
    narrowBand r (7 / 2) ⊆ seamRectNeg := by
  rintro p ⟨⟨h1, h2⟩, ht⟩
  exact ⟨⟨by linarith, by linarith⟩, ht⟩

private theorem narrowSheetPos_mem_cylinder {r : ℝ} (hr : 0 < r) {p : ℝ × ℝ} :
    narrowSheetPos r p ∈ spliceCylinder ↔ p ∈ narrowBand r (3 / 2) := by
  constructor
  · rintro ⟨hsq, ht⟩
    rcases mem_spliceSquare.mp hsq with ⟨⟨_, hx⟩, ⟨hy, _⟩⟩
    change max (3 - 2 * bandParameter r (3 / 2) p.1) 0 ≤ 1 at hx
    change -1 ≤ min (3 - 2 * bandParameter r (3 / 2) p.1) 0 at hy
    have hx' := (le_max_left (3 - 2 * bandParameter r (3 / 2) p.1) 0).trans hx
    have hy' := hy.trans (min_le_left (3 - 2 * bandParameter r (3 / 2) p.1) 0)
    refine ⟨(bandParameter_mem hr).mp ?_, ht⟩
    constructor <;> linarith
  · intro hp
    have h := (isPLHomeomorphOn_narrowSheetPos hr).bijOn.mapsTo hp
    exact ⟨bentArcPos_subset_spliceSquare h.1, h.2⟩

private theorem narrowSheetNeg_mem_cylinder {r : ℝ} (hr : 0 < r) {p : ℝ × ℝ} :
    narrowSheetNeg r p ∈ spliceCylinder ↔ p ∈ narrowBand r (7 / 2) := by
  constructor
  · rintro ⟨hsq, ht⟩
    rcases mem_spliceSquare.mp hsq with ⟨⟨hx, _⟩, ⟨_, hy⟩⟩
    change -1 ≤ min (2 * bandParameter r (7 / 2) p.1 - 7) 0 at hx
    change max (2 * bandParameter r (7 / 2) p.1 - 7) 0 ≤ 1 at hy
    have hx' := hx.trans (min_le_left (2 * bandParameter r (7 / 2) p.1 - 7) 0)
    have hy' := (le_max_left (2 * bandParameter r (7 / 2) p.1 - 7) 0).trans hy
    refine ⟨(bandParameter_mem hr).mp ?_, ht⟩
    constructor <;> linarith
  · intro hp
    have h := (isPLHomeomorphOn_narrowSheetNeg hr).bijOn.mapsTo hp
    exact ⟨bentArcNeg_subset_spliceSquare h.1, h.2⟩

private noncomputable def narrowCoord (r : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    Bool × ((ℝ × ℝ) × ℝ) :=
  if (seamWitnessPlane.symm x).1 ≤ 5 / 2 then
    (true, narrowSheetPos r (seamWitnessPlane.symm x))
  else (false, narrowSheetNeg r (seamWitnessPlane.symm x))

private theorem narrowCoord_of_mem_pos {r : ℝ} (hr1 : r ≤ 1)
    {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ seamWitnessPlane '' narrowBand r (3 / 2)) :
    narrowCoord r x = (true, narrowSheetPos r (seamWitnessPlane.symm x)) := by
  have h := narrowBand_subset_pos hr1 (mem_image_seamWitnessPlane.mp hx)
  exact ite_eq_left (by linarith [h.1.2])

private theorem narrowCoord_of_mem_neg {r : ℝ} (hr1 : r ≤ 1)
    {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ seamWitnessPlane '' narrowBand r (7 / 2)) :
    narrowCoord r x = (false, narrowSheetNeg r (seamWitnessPlane.symm x)) := by
  have h := narrowBand_subset_neg hr1 (mem_image_seamWitnessPlane.mp hx)
  exact ite_eq_right (by linarith [h.1.1])

private theorem product_reglued_eq_pos {r : ℝ} (hr : 0 < r)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ seamWitnessReading.sourcePos) :
    crossRegluedProductCell x =
      crossingProductTubeChart r hr.ne' (narrowSheetPos r (seamWitnessPlane.symm x)) := by
  have h := mem_image_seamWitnessPlane.mp hx
  change spliceEmbedding (crossRegluedProductMap (seamWitnessPlane.symm x)) =
    spliceEmbedding (crossingProductTubeScale r hr.ne' _)
  rw [scale_narrowSheetPos hr, crossRegluedProductMap_eq_seamModelMap (by linarith [h.1.2]),
    seamModelMap_eq_seamSheetPos h.1.1 h.1.2]

private theorem product_reglued_eq_neg {r : ℝ} (hr : 0 < r)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ seamWitnessReading.sourceNeg) :
    crossRegluedProductCell x =
      crossingProductTubeChart r hr.ne' (narrowSheetNeg r (seamWitnessPlane.symm x)) := by
  have h := mem_image_seamWitnessPlane.mp hx
  change spliceEmbedding (crossRegluedProductMap (seamWitnessPlane.symm x)) =
    spliceEmbedding (crossingProductTubeScale r hr.ne' _)
  rw [scale_narrowSheetNeg hr, crossRegluedProductMap_eq_seamModelMap h.1.2,
    seamModelMap_eq_seamSheetNeg h.1.1 h.1.2]

private theorem narrow_source_eq {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (seamWitnessPlane '' narrowBand r (3 / 2)) ∪
      (seamWitnessPlane '' narrowBand r (7 / 2)) =
        crossRegluedProductCell.domain ∩ crossRegluedProductCell ⁻¹'
          (crossingProductTubeChart r hr.ne' '' spliceCylinder) := by
  apply Subset.antisymm
  · rintro x (hx | hx)
    · have hp := mem_image_seamWitnessPlane.mp hx
      have hold : x ∈ seamWitnessReading.sourcePos :=
        image_mono (narrowBand_subset_pos hr1) hx
      exact ⟨crossRegluedProductReading.source_subset_domain (Or.inl hold),
        narrowSheetPos r (seamWitnessPlane.symm x),
        (narrowSheetPos_mem_cylinder hr).mpr hp, (product_reglued_eq_pos hr hold).symm⟩
    · have hp := mem_image_seamWitnessPlane.mp hx
      have hold : x ∈ seamWitnessReading.sourceNeg :=
        image_mono (narrowBand_subset_neg hr1) hx
      exact ⟨crossRegluedProductReading.source_subset_domain (Or.inr hold),
        narrowSheetNeg r (seamWitnessPlane.symm x),
        (narrowSheetNeg_mem_cylinder hr).mpr hp, (product_reglued_eq_neg hr hold).symm⟩
  · rintro x ⟨hxd, q, hq, hqx⟩
    have hold : x ∈ crossRegluedProductReading.tubeSource := by
      rw [crossRegluedProductReading.tubeSource_eq]
      refine ⟨hxd, crossingProductTubeScale r hr.ne' q,
        crossingProductTubeScale_mapsTo_cylinder hr hr1 hq, hqx⟩
    rcases hold with hpos | hneg
    · have heq := (crossingProductTubeChart r hr.ne').injective
        ((product_reglued_eq_pos hr hpos).symm.trans hqx.symm)
      apply Or.inl
      apply mem_image_seamWitnessPlane.mpr
      apply (narrowSheetPos_mem_cylinder hr).mp
      exact heq.symm ▸ hq
    · have heq := (crossingProductTubeChart r hr.ne').injective
        ((product_reglued_eq_neg hr hneg).symm.trans hqx.symm)
      apply Or.inr
      apply mem_image_seamWitnessPlane.mpr
      apply (narrowSheetNeg_mem_cylinder hr).mp
      exact heq.symm ▸ hq

private def narrowFace (r : ℝ) : Set (ℝ × ℝ) :=
  ((Icc 0 (3 / 2 - r / 2) ×ˢ Icc (0 : ℝ) 1) ∪
    (Icc (3 / 2 + r / 2) (7 / 2 - r / 2) ×ˢ Icc (0 : ℝ) 1)) ∪
      (Icc (7 / 2 + r / 2) 5 ×ˢ Icc (0 : ℝ) 1)

private theorem isPolyhedron_narrowFace (r : ℝ) : IsPolyhedron (narrowFace r) :=
  ((isHPolytope_Icc.isPolyhedron.prod isHPolytope_Icc.isPolyhedron).union
    (isHPolytope_Icc.isPolyhedron.prod isHPolytope_Icc.isPolyhedron)).union
      (isHPolytope_Icc.isPolyhedron.prod isHPolytope_Icc.isPolyhedron)

private theorem narrow_union {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    narrowBand r (3 / 2) ∪ narrowBand r (7 / 2) ∪ narrowFace r = seamSourceRect := by
  apply Subset.antisymm
  · rintro p ((⟨⟨h1, h2⟩, ht⟩ | ⟨⟨h1, h2⟩, ht⟩) |
      ((⟨⟨h1, h2⟩, ht⟩ | ⟨⟨h1, h2⟩, ht⟩) | ⟨⟨h1, h2⟩, ht⟩)) <;>
      exact ⟨⟨by linarith, by linarith⟩, ht⟩
  · rintro p ⟨⟨hp0, hp5⟩, ht⟩
    rcases le_or_gt p.1 (3 / 2 - r / 2) with h1 | h1
    · exact Or.inr (Or.inl (Or.inl ⟨⟨hp0, h1⟩, ht⟩))
    rcases le_or_gt p.1 (3 / 2 + r / 2) with h2 | h2
    · exact Or.inl (Or.inl ⟨⟨h1.le, h2⟩, ht⟩)
    rcases le_or_gt p.1 (7 / 2 - r / 2) with h3 | h3
    · exact Or.inr (Or.inl (Or.inr ⟨⟨h2.le, h3⟩, ht⟩))
    rcases le_or_gt p.1 (7 / 2 + r / 2) with h4 | h4
    · exact Or.inl (Or.inr ⟨⟨h3.le, h4⟩, ht⟩)
    · exact Or.inr (Or.inr ⟨⟨h4.le, hp5⟩, ht⟩)

noncomputable def crossRegluedProductTubeReading {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    PLCrossSeamReading (crossingProductTubeChart r hr.ne') crossRegluedProductCell where
  coord := narrowCoord r
  sourcePos := seamWitnessPlane '' narrowBand r (3 / 2)
  sourceNeg := seamWitnessPlane '' narrowBand r (7 / 2)
  face := seamWitnessPlane '' narrowFace r
  isPLHomeomorphOn_pos :=
    ((isPLHomeomorphOn_seamWitnessPlaneSymm
      (isHPolytope_Icc.isPolyhedron.prod isHPolytope_Icc.isPolyhedron)).trans
        (isPLHomeomorphOn_narrowSheetPos hr)).congr fun x hx => by
          rw [narrowCoord_of_mem_pos hr1 hx]
          rfl
  isPLHomeomorphOn_neg :=
    ((isPLHomeomorphOn_seamWitnessPlaneSymm
      (isHPolytope_Icc.isPolyhedron.prod isHPolytope_Icc.isPolyhedron)).trans
        (isPLHomeomorphOn_narrowSheetNeg hr)).congr fun x hx => by
          rw [narrowCoord_of_mem_neg hr1 hx]
          rfl
  coord_fst_pos := fun _ hx => by rw [narrowCoord_of_mem_pos hr1 hx]
  coord_fst_neg := fun _ hx => by rw [narrowCoord_of_mem_neg hr1 hx]
  source_eq := narrow_source_eq hr hr1
  isPolyhedron_face := isPolyhedron_image_seamWitnessPlane (isPolyhedron_narrowFace r)
  union_eq := by
    rw [← image_union, ← image_union, narrow_union hr hr1]
    rfl
  reglued_eq := by
    rintro x (hx | hx)
    · have hold : x ∈ seamWitnessReading.sourcePos :=
        image_mono (narrowBand_subset_pos hr1) hx
      change crossRegluedProductCell x =
        crossingProductTubeChart r hr.ne' (crossSeamInclude (narrowCoord r x))
      rw [narrowCoord_of_mem_pos hr1 hx]
      exact product_reglued_eq_pos hr hold
    · have hold : x ∈ seamWitnessReading.sourceNeg :=
        image_mono (narrowBand_subset_neg hr1) hx
      change crossRegluedProductCell x =
        crossingProductTubeChart r hr.ne' (crossSeamInclude (narrowCoord r x))
      rw [narrowCoord_of_mem_neg hr1 hx]
      exact product_reglued_eq_neg hr hold
  overlap_lateral := by
    rintro x ⟨hx | hx, hf⟩
    · have hp := mem_image_seamWitnessPlane.mp hx
      have hface := mem_image_seamWitnessPlane.mp hf
      rw [narrowCoord_of_mem_pos hr1 hx]
      refine ⟨?_, hp.2⟩
      change seamBentPos (bandParameter r (3 / 2) (seamWitnessPlane.symm x).1) ∈ _
      rcases hface with (⟨⟨_, hb⟩, _⟩ | ⟨⟨hb, _⟩, _⟩) | ⟨⟨hb, _⟩, _⟩
      · rw [le_antisymm hb hp.1.1, bandParameter_lower hr.ne']
        convert seamBentPos_one_mem using 1
        norm_num
      · rw [le_antisymm hp.1.2 hb, bandParameter_upper hr.ne']
        convert seamBentPos_two_mem using 1
        norm_num
      · linarith [hp.1.2]
    · have hp := mem_image_seamWitnessPlane.mp hx
      have hface := mem_image_seamWitnessPlane.mp hf
      rw [narrowCoord_of_mem_neg hr1 hx]
      refine ⟨?_, hp.2⟩
      change seamBentNeg (bandParameter r (7 / 2) (seamWitnessPlane.symm x).1) ∈ _
      rcases hface with (⟨⟨_, hb⟩, _⟩ | ⟨⟨_, hb⟩, _⟩) | ⟨⟨hb, _⟩, _⟩
      · linarith [hp.1.1]
      · rw [le_antisymm hb hp.1.1, bandParameter_lower hr.ne']
        convert seamBentNeg_three_mem using 1
        norm_num
      · rw [le_antisymm hp.1.2 hb, bandParameter_upper hr.ne']
        convert seamBentNeg_four_mem using 1
        norm_num
  boundary_iff_end := by
    rintro x (hx | hx)
    · have hold : x ∈ seamWitnessReading.sourcePos :=
        image_mono (narrowBand_subset_pos hr1) hx
      have h := crossRegluedProductReading.boundary_iff_end x (Or.inl hold)
      change x ∈ frontier crossRegluedProductCell.domain ↔
        (seamWitnessCoord x).2.2 = 0 ∨ (seamWitnessCoord x).2.2 = 1 at h
      rw [seamWitnessCoord_of_mem_pos hold] at h
      rw [narrowCoord_of_mem_pos hr1 hx]
      exact h
    · have hold : x ∈ seamWitnessReading.sourceNeg :=
        image_mono (narrowBand_subset_neg hr1) hx
      have h := crossRegluedProductReading.boundary_iff_end x (Or.inr hold)
      change x ∈ frontier crossRegluedProductCell.domain ↔
        (seamWitnessCoord x).2.2 = 0 ∨ (seamWitnessCoord x).2.2 = 1 at h
      rw [seamWitnessCoord_of_mem_neg hold] at h
      rw [narrowCoord_of_mem_neg hr1 hx]
      exact h

theorem crossRegluedProductTubeReading_tubeSource_ssubset {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) :
    (crossRegluedProductTubeReading hr hr1).tubeSource ⊂ crossRegluedProductCell.domain :=
  (crossRegluedProductTubeReading hr hr1).source_ssubset_domain

end DifferentialGeometry.Topology.PiecewiseLinear
