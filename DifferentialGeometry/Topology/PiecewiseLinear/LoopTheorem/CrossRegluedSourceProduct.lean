/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamReadingWitness

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private noncomputable def stripCurlX (p : ℝ × ℝ) : ℝ :=
  seamRamp 5 (21 / 5) p + seamRamp (-5) (22 / 5) p +
    seamRamp (-10) (23 / 5) p + seamRamp 10 (24 / 5) p

private noncomputable def stripCurlY (p : ℝ × ℝ) : ℝ :=
  seamRamp 14 4 p + seamRamp (-15) (21 / 5) p + seamRamp (-5) (22 / 5) p +
    seamRamp 5 (23 / 5) p + seamRamp 10 (24 / 5) p

noncomputable def crossRegluedProductMap (p : ℝ × ℝ) : (ℝ × ℝ) × ℝ :=
  ((seamArcX p + stripCurlX p, seamArcY p + stripCurlY p), p.2)

private theorem isPiecewiseAffineOn_stripCurlX : IsPiecewiseAffineOn stripCurlX univ :=
  (((isPiecewiseAffineOn_seamRamp 5 (21 / 5)).add
    (isPiecewiseAffineOn_seamRamp (-5) (22 / 5))).add
      (isPiecewiseAffineOn_seamRamp (-10) (23 / 5))).add
        (isPiecewiseAffineOn_seamRamp 10 (24 / 5))

private theorem isPiecewiseAffineOn_stripCurlY : IsPiecewiseAffineOn stripCurlY univ :=
  ((((isPiecewiseAffineOn_seamRamp 14 4).add
    (isPiecewiseAffineOn_seamRamp (-15) (21 / 5))).add
      (isPiecewiseAffineOn_seamRamp (-5) (22 / 5))).add
        (isPiecewiseAffineOn_seamRamp 5 (23 / 5))).add
          (isPiecewiseAffineOn_seamRamp 10 (24 / 5))

theorem isPiecewiseAffineOn_crossRegluedProductMap :
    IsPiecewiseAffineOn crossRegluedProductMap univ :=
  ((isPiecewiseAffineOn_seamArcX.add isPiecewiseAffineOn_stripCurlX).prod_mk
    (isPiecewiseAffineOn_seamArcY.add isPiecewiseAffineOn_stripCurlY)).prod_mk
      isPiecewiseAffineOn_seamSnd

theorem crossRegluedProductMap_eq_seamModelMap {p : ℝ × ℝ} (hp : p.1 ≤ 4) :
    crossRegluedProductMap p = seamModelMap p := by
  have h4 : p.1 - 4 ≤ 0 := by linarith
  have h21 : p.1 - 21 / 5 ≤ 0 := by linarith
  have h22 : p.1 - 22 / 5 ≤ 0 := by linarith
  have h23 : p.1 - 23 / 5 ≤ 0 := by linarith
  have h24 : p.1 - 24 / 5 ≤ 0 := by linarith
  simp [crossRegluedProductMap, seamModelMap, stripCurlX, stripCurlY, seamRamp,
    max_eq_right h4, max_eq_right h21, max_eq_right h22, max_eq_right h23,
    max_eq_right h24]

private theorem crossRegluedProductMap_tail_first {p : ℝ × ℝ}
    (h4 : 4 ≤ p.1) (h21 : p.1 ≤ 21 / 5) :
    crossRegluedProductMap p = ((0, 15 * p.1 - 59), p.2) := by
  have h3 : 3 ≤ p.1 := by linarith
  have hx : seamArcX p = 0 := by
    rw [seamArcX_bandNeg h3, min_eq_right (by linarith : 0 ≤ 2 * p.1 - 7)]
  simp only [crossRegluedProductMap, hx, seamArcY_highFace h4, stripCurlX, stripCurlY,
    seamRamp]
  rw [max_eq_left (by linarith : 0 ≤ p.1 - 4),
    max_eq_right (by linarith : p.1 - 21 / 5 ≤ 0),
    max_eq_right (by linarith : p.1 - 22 / 5 ≤ 0),
    max_eq_right (by linarith : p.1 - 23 / 5 ≤ 0),
    max_eq_right (by linarith : p.1 - 24 / 5 ≤ 0)]
  congr 2 <;> ring

private theorem crossRegluedProductMap_tail_second {p : ℝ × ℝ}
    (h21 : 21 / 5 ≤ p.1) (h22 : p.1 ≤ 22 / 5) :
    crossRegluedProductMap p = ((5 * p.1 - 21, 4), p.2) := by
  have h4 : 4 ≤ p.1 := by linarith
  have hx : seamArcX p = 0 := by
    rw [seamArcX_bandNeg (by linarith : 3 ≤ p.1),
      min_eq_right (by linarith : 0 ≤ 2 * p.1 - 7)]
  simp only [crossRegluedProductMap, hx, seamArcY_highFace h4, stripCurlX, stripCurlY,
    seamRamp]
  rw [max_eq_left (by linarith : 0 ≤ p.1 - 4),
    max_eq_left (by linarith : 0 ≤ p.1 - 21 / 5),
    max_eq_right (by linarith : p.1 - 22 / 5 ≤ 0),
    max_eq_right (by linarith : p.1 - 23 / 5 ≤ 0),
    max_eq_right (by linarith : p.1 - 24 / 5 ≤ 0)]
  congr 2 <;> ring

private theorem crossRegluedProductMap_tail_third {p : ℝ × ℝ}
    (h22 : 22 / 5 ≤ p.1) (h23 : p.1 ≤ 23 / 5) :
    crossRegluedProductMap p = ((1, 26 - 5 * p.1), p.2) := by
  have h4 : 4 ≤ p.1 := by linarith
  have hx : seamArcX p = 0 := by
    rw [seamArcX_bandNeg (by linarith : 3 ≤ p.1),
      min_eq_right (by linarith : 0 ≤ 2 * p.1 - 7)]
  simp only [crossRegluedProductMap, hx, seamArcY_highFace h4, stripCurlX, stripCurlY,
    seamRamp]
  rw [max_eq_left (by linarith : 0 ≤ p.1 - 4),
    max_eq_left (by linarith : 0 ≤ p.1 - 21 / 5),
    max_eq_left (by linarith : 0 ≤ p.1 - 22 / 5),
    max_eq_right (by linarith : p.1 - 23 / 5 ≤ 0),
    max_eq_right (by linarith : p.1 - 24 / 5 ≤ 0)]
  congr 2 <;> ring

private theorem crossRegluedProductMap_tail_fourth {p : ℝ × ℝ}
    (h23 : 23 / 5 ≤ p.1) (h24 : p.1 ≤ 24 / 5) :
    crossRegluedProductMap p = ((47 - 10 * p.1, 3), p.2) := by
  have h4 : 4 ≤ p.1 := by linarith
  have hx : seamArcX p = 0 := by
    rw [seamArcX_bandNeg (by linarith : 3 ≤ p.1),
      min_eq_right (by linarith : 0 ≤ 2 * p.1 - 7)]
  simp only [crossRegluedProductMap, hx, seamArcY_highFace h4, stripCurlX, stripCurlY,
    seamRamp]
  rw [max_eq_left (by linarith : 0 ≤ p.1 - 4),
    max_eq_left (by linarith : 0 ≤ p.1 - 21 / 5),
    max_eq_left (by linarith : 0 ≤ p.1 - 22 / 5),
    max_eq_left (by linarith : 0 ≤ p.1 - 23 / 5),
    max_eq_right (by linarith : p.1 - 24 / 5 ≤ 0)]
  congr 2 <;> ring

private theorem crossRegluedProductMap_tail_fifth {p : ℝ × ℝ}
    (h24 : 24 / 5 ≤ p.1) :
    crossRegluedProductMap p = ((-1, 10 * p.1 - 45), p.2) := by
  have h4 : 4 ≤ p.1 := by linarith
  have hx : seamArcX p = 0 := by
    rw [seamArcX_bandNeg (by linarith : 3 ≤ p.1),
      min_eq_right (by linarith : 0 ≤ 2 * p.1 - 7)]
  simp only [crossRegluedProductMap, hx, seamArcY_highFace h4, stripCurlX, stripCurlY,
    seamRamp]
  rw [max_eq_left (by linarith : 0 ≤ p.1 - 4),
    max_eq_left (by linarith : 0 ≤ p.1 - 21 / 5),
    max_eq_left (by linarith : 0 ≤ p.1 - 22 / 5),
    max_eq_left (by linarith : 0 ≤ p.1 - 23 / 5),
    max_eq_left (by linarith : 0 ≤ p.1 - 24 / 5)]
  congr 2 <;> ring

theorem crossRegluedProductMap_notMem_spliceCylinder {p : ℝ × ℝ} (hp : 4 < p.1) :
    crossRegluedProductMap p ∉ spliceCylinder := by
  have hy : 1 < (crossRegluedProductMap p).1.2 := by
    rcases le_or_gt p.1 (21 / 5) with h | h
    · rw [crossRegluedProductMap_tail_first hp.le h]
      dsimp
      linarith
    rcases le_or_gt p.1 (22 / 5) with h' | h'
    · rw [crossRegluedProductMap_tail_second h.le h']
      norm_num
    rcases le_or_gt p.1 (23 / 5) with h'' | h''
    · rw [crossRegluedProductMap_tail_third h'.le h'']
      dsimp
      linarith
    rcases le_or_gt p.1 (24 / 5) with h''' | h'''
    · rw [crossRegluedProductMap_tail_fourth h''.le h''']
      norm_num
    · rw [crossRegluedProductMap_tail_fifth h'''.le]
      dsimp
      linarith
  intro hcyl
  exact (not_le_of_gt hy) ((mem_spliceSquare.mp hcyl.1).2.2)

theorem crossRegluedProductMap_mem_spliceCylinder_iff {p : ℝ × ℝ} :
    crossRegluedProductMap p ∈ spliceCylinder ↔ seamModelMap p ∈ spliceCylinder := by
  by_cases hp : p.1 ≤ 4
  · rw [crossRegluedProductMap_eq_seamModelMap hp]
  · have h4 : 4 < p.1 := lt_of_not_ge hp
    have hnot := seamModelMap_notMem_spliceCylinder
      (p := p) (by rintro ⟨-, h2⟩; linarith) (by rintro ⟨-, h4'⟩; linarith)
    exact iff_of_false (crossRegluedProductMap_notMem_spliceCylinder h4) hnot

noncomputable def crossRegluedProductCell : SingularTwoCell (EuclideanSpace ℝ (Fin 3)) where
  domain := seamWitnessCell.domain
  isPLBall_domain := seamWitnessCell.isPLBall_domain
  toFun := ⇑spliceEmbedding ∘ crossRegluedProductMap ∘ ⇑seamWitnessPlane.symm
  isPLOn := by
    have hdom := seamWitnessCell.isPLBall_domain.isPolyhedron
    have hcomp := isPiecewiseAffineOn_crossRegluedProductMap.comp
      (isPiecewiseAffineOn_seamWitnessPlaneSymm hdom)
    rw [preimage_univ, inter_univ] at hcomp
    have hpa := hcomp.affine_comp spliceEmbedding.toLinearMap.toAffineMap
    exact fun x hx => ⟨hpa.continuousOn x hx, hpa x hx⟩

theorem crossRegluedProductCell_eq_on_tubeSource :
    EqOn (⇑crossRegluedProductCell) (⇑seamWitnessCell) seamWitnessReading.tubeSource := by
  intro x hx
  have h4 : (seamWitnessPlane.symm x).1 ≤ 4 := by
    rcases hx with hx | hx
    · have h := mem_image_seamWitnessPlane.mp hx
      linarith [h.1.2]
    · exact (mem_image_seamWitnessPlane.mp hx).1.2
  change spliceEmbedding (crossRegluedProductMap (seamWitnessPlane.symm x)) = _
  rw [crossRegluedProductMap_eq_seamModelMap h4]
  rfl

theorem crossRegluedProductCell_preimage_spliceCylinder :
    ⇑crossRegluedProductCell ⁻¹' (⇑spliceEmbedding '' spliceCylinder) =
      ⇑seamWitnessCell ⁻¹' (⇑spliceEmbedding '' spliceCylinder) := by
  ext x
  change spliceEmbedding (crossRegluedProductMap (seamWitnessPlane.symm x)) ∈
      spliceEmbedding '' spliceCylinder ↔
    spliceEmbedding (seamModelMap (seamWitnessPlane.symm x)) ∈
      spliceEmbedding '' spliceCylinder
  simp only [Set.mem_image, spliceEmbedding.injective.eq_iff, exists_eq_right]
  exact crossRegluedProductMap_mem_spliceCylinder_iff

noncomputable def crossRegluedProductReading :
    PLCrossSeamReading (⇑spliceEmbedding) crossRegluedProductCell where
  coord := seamWitnessReading.coord
  sourcePos := seamWitnessReading.sourcePos
  sourceNeg := seamWitnessReading.sourceNeg
  face := seamWitnessReading.face
  isPLHomeomorphOn_pos := seamWitnessReading.isPLHomeomorphOn_pos
  isPLHomeomorphOn_neg := seamWitnessReading.isPLHomeomorphOn_neg
  coord_fst_pos := seamWitnessReading.coord_fst_pos
  coord_fst_neg := seamWitnessReading.coord_fst_neg
  source_eq := by
    rw [crossRegluedProductCell_preimage_spliceCylinder]
    exact seamWitnessReading.source_eq
  isPolyhedron_face := seamWitnessReading.isPolyhedron_face
  union_eq := seamWitnessReading.union_eq
  reglued_eq := crossRegluedProductCell_eq_on_tubeSource.trans seamWitnessReading.reglued_eq
  overlap_lateral := seamWitnessReading.overlap_lateral
  boundary_iff_end := seamWitnessReading.boundary_iff_end

theorem crossRegluedProductReading_tubeSource_ssubset :
    crossRegluedProductReading.tubeSource ⊂ crossRegluedProductCell.domain :=
  crossRegluedProductReading.source_ssubset_domain

theorem crossRegluedProductMap_curl_first (t : ℝ) :
    crossRegluedProductMap (62 / 15, t) = ((0, 3), t) := by
  rw [crossRegluedProductMap_tail_first (by norm_num) (by norm_num)]
  norm_num

theorem crossRegluedProductMap_curl_second (t : ℝ) :
    crossRegluedProductMap (47 / 10, t) = ((0, 3), t) := by
  rw [crossRegluedProductMap_tail_fourth (by norm_num) (by norm_num)]
  norm_num

theorem crossRegluedProductCell_curl_mem_doublePointSet {t : ℝ} (ht : t ∈ Icc 0 1) :
    spliceEmbedding ((0, 3), t) ∈
      doublePointSet (⇑crossRegluedProductCell) crossRegluedProductCell.domain := by
  refine ⟨seamWitnessPlane (62 / 15, t), ?_, seamWitnessPlane (47 / 10, t), ?_, ?_, ?_, ?_⟩
  · exact ⟨(62 / 15, t), ⟨⟨by norm_num, by norm_num⟩, ht⟩, rfl⟩
  · exact ⟨(47 / 10, t), ⟨⟨by norm_num, by norm_num⟩, ht⟩, rfl⟩
  · intro h
    have := congrArg Prod.fst (seamWitnessPlane.injective h)
    norm_num at this
  · change spliceEmbedding (crossRegluedProductMap
      (seamWitnessPlane.symm (seamWitnessPlane (62 / 15, t)))) = _
    rw [ContinuousLinearEquiv.symm_apply_apply, crossRegluedProductMap_curl_first]
  · change spliceEmbedding (crossRegluedProductMap
      (seamWitnessPlane.symm (seamWitnessPlane (47 / 10, t)))) = _
    rw [ContinuousLinearEquiv.symm_apply_apply, crossRegluedProductMap_curl_second]

theorem crossRegluedProductCell_curl_notMem_tube (t : ℝ) :
    spliceEmbedding ((0, 3), t) ∉ ⇑spliceEmbedding '' spliceCylinder := by
  rintro ⟨p, hp, heq⟩
  have hp' : p = ((0, 3), t) := spliceEmbedding.injective heq
  rw [hp'] at hp
  have h := (mem_spliceSquare.mp hp.1).2.2
  norm_num at h

private noncomputable def stripSwitch (p : ℝ × ℝ) : ℝ :=
  seamRamp (-2) (3 / 2) p + seamRamp 4 2 p + seamRamp (-4) 3 p +
    seamRamp 2 (7 / 2) p

noncomputable def crossingProductMap (p : ℝ × ℝ) : (ℝ × ℝ) × ℝ :=
  crossRegluedProductMap p + ((stripSwitch p, -stripSwitch p), 0)

@[simp]
theorem crossingProductMap_snd (p : ℝ × ℝ) : (crossingProductMap p).2 = p.2 := by
  simp [crossingProductMap, crossRegluedProductMap]

private theorem isPiecewiseAffineOn_stripSwitch : IsPiecewiseAffineOn stripSwitch univ :=
  (((isPiecewiseAffineOn_seamRamp (-2) (3 / 2)).add
    (isPiecewiseAffineOn_seamRamp 4 2)).add
      (isPiecewiseAffineOn_seamRamp (-4) 3)).add
        (isPiecewiseAffineOn_seamRamp 2 (7 / 2))

theorem isPiecewiseAffineOn_crossingProductMap :
    IsPiecewiseAffineOn crossingProductMap univ := by
  have hneg : IsPiecewiseAffineOn (fun p => -stripSwitch p) univ :=
    (isPiecewiseAffineOn_stripSwitch.affine_comp (seamScale (-1))).congr
      (fun _ _ => by simp [seamScale])
  exact isPiecewiseAffineOn_crossRegluedProductMap.add
    ((isPiecewiseAffineOn_stripSwitch.prod_mk hneg).prod_mk isPiecewiseAffineOn_seamZero)

theorem crossingProductMap_eq_crossRegluedProductMap_of_le {p : ℝ × ℝ}
    (hp : p.1 ≤ 3 / 2) : crossingProductMap p = crossRegluedProductMap p := by
  have hswitch : stripSwitch p = 0 := by
    simp [stripSwitch, seamRamp,
      max_eq_right (by linarith : p.1 - 3 / 2 ≤ 0),
      max_eq_right (by linarith : p.1 - 2 ≤ 0),
      max_eq_right (by linarith : p.1 - 3 ≤ 0),
      max_eq_right (by linarith : p.1 - 7 / 2 ≤ 0)]
  simp [crossingProductMap, hswitch]

theorem crossingProductMap_eq_crossRegluedProductMap_of_ge {p : ℝ × ℝ}
    (hp : 7 / 2 ≤ p.1) : crossingProductMap p = crossRegluedProductMap p := by
  have hswitch : stripSwitch p = 0 := by
    simp only [stripSwitch, seamRamp]
    rw [max_eq_left (by linarith : 0 ≤ p.1 - 3 / 2),
      max_eq_left (by linarith : 0 ≤ p.1 - 2),
      max_eq_left (by linarith : 0 ≤ p.1 - 3),
      max_eq_left (by linarith : 0 ≤ p.1 - 7 / 2)]
    ring
  simp [crossingProductMap, hswitch]

private theorem crossingProductMap_first {p : ℝ × ℝ} (hp : p.1 ≤ 1) :
    crossingProductMap p = ((2 - p.1, 0), p.2) := by
  rw [crossingProductMap_eq_crossRegluedProductMap_of_le (by linarith),
    crossRegluedProductMap_eq_seamModelMap (by linarith)]
  simp only [seamModelMap, seamArcX_lowFace hp, seamArcY, seamRamp]
  rw [max_eq_right (by linarith : p.1 - 3 / 2 ≤ 0),
    max_eq_right (by linarith : p.1 - 5 / 2 ≤ 0),
    max_eq_right (by linarith : p.1 - 3 ≤ 0),
    max_eq_right (by linarith : p.1 - 7 / 2 ≤ 0),
    max_eq_right (by linarith : p.1 - 4 ≤ 0)]
  simp

private theorem crossingProductMap_second {p : ℝ × ℝ}
    (h1 : 1 ≤ p.1) (h2 : p.1 ≤ 2) :
    crossingProductMap p = ((3 - 2 * p.1, 0), p.2) := by
  simp only [crossingProductMap, crossRegluedProductMap_eq_seamModelMap (by linarith : p.1 ≤ 4),
    seamModelMap, seamArcX, seamArcY, stripSwitch, seamRamp, Prod.mk_add_mk, add_zero]
  rw [max_eq_left (by linarith : 0 ≤ p.1 - 1),
    max_eq_right (by linarith : p.1 - 2 ≤ 0),
    max_eq_right (by linarith : p.1 - 5 / 2 ≤ 0),
    max_eq_right (by linarith : p.1 - 3 ≤ 0),
    max_eq_right (by linarith : p.1 - 7 / 2 ≤ 0),
    max_eq_right (by linarith : p.1 - 4 ≤ 0)]
  congr 2 <;> ring

private theorem crossingProductMap_third {p : ℝ × ℝ}
    (h2 : 2 ≤ p.1) (h25 : p.1 ≤ 5 / 2) :
    crossingProductMap p = ((3 - 2 * p.1, 8 - 4 * p.1), p.2) := by
  simp only [crossingProductMap, crossRegluedProductMap_eq_seamModelMap (by linarith : p.1 ≤ 4),
    seamModelMap, seamArcX, seamArcY, stripSwitch, seamRamp, Prod.mk_add_mk, add_zero]
  rw [max_eq_left (by linarith : 0 ≤ p.1 - 1),
    max_eq_left (by linarith : 0 ≤ p.1 - 3 / 2),
    max_eq_left (by linarith : 0 ≤ p.1 - 2),
    max_eq_right (by linarith : p.1 - 5 / 2 ≤ 0),
    max_eq_right (by linarith : p.1 - 3 ≤ 0),
    max_eq_right (by linarith : p.1 - 7 / 2 ≤ 0),
    max_eq_right (by linarith : p.1 - 4 ≤ 0)]
  congr 2 <;> ring

private theorem crossingProductMap_fourth {p : ℝ × ℝ}
    (h25 : 5 / 2 ≤ p.1) (h3 : p.1 ≤ 3) :
    crossingProductMap p = ((4 * p.1 - 12, 2 * p.1 - 7), p.2) := by
  simp only [crossingProductMap, crossRegluedProductMap_eq_seamModelMap (by linarith : p.1 ≤ 4),
    seamModelMap, seamArcX, seamArcY, stripSwitch, seamRamp, Prod.mk_add_mk, add_zero]
  rw [max_eq_left (by linarith : 0 ≤ p.1 - 1),
    max_eq_left (by linarith : 0 ≤ p.1 - 3 / 2),
    max_eq_left (by linarith : 0 ≤ p.1 - 2),
    max_eq_left (by linarith : 0 ≤ p.1 - 5 / 2),
    max_eq_right (by linarith : p.1 - 3 ≤ 0),
    max_eq_right (by linarith : p.1 - 7 / 2 ≤ 0),
    max_eq_right (by linarith : p.1 - 4 ≤ 0)]
  congr 2 <;> ring

private theorem crossingProductMap_fifth {p : ℝ × ℝ}
    (h3 : 3 ≤ p.1) (h4 : p.1 ≤ 4) :
    crossingProductMap p = ((0, 2 * p.1 - 7), p.2) := by
  simp only [crossingProductMap, crossRegluedProductMap_eq_seamModelMap h4,
    seamModelMap, seamArcX, seamArcY, stripSwitch, seamRamp, Prod.mk_add_mk, add_zero]
  rw [max_eq_left (by linarith : 0 ≤ p.1 - 1),
    max_eq_left (by linarith : 0 ≤ p.1 - 3 / 2),
    max_eq_left (by linarith : 0 ≤ p.1 - 2),
    max_eq_left (by linarith : 0 ≤ p.1 - 5 / 2),
    max_eq_left (by linarith : 0 ≤ p.1 - 3),
    max_eq_right (by linarith : p.1 - 4 ≤ 0)]
  congr 2 <;> ring

theorem crossingProductMap_core_first (t : ℝ) :
    crossingProductMap (3 / 2, t) = ((0, 0), t) := by
  rw [crossingProductMap_second (by norm_num) (by norm_num)]
  norm_num

theorem crossingProductMap_core_second (t : ℝ) :
    crossingProductMap (7 / 2, t) = ((0, 0), t) := by
  rw [crossingProductMap_fifth (by norm_num) (by norm_num)]
  norm_num

theorem crossingProductMap_curl_first (t : ℝ) :
    crossingProductMap (62 / 15, t) = ((0, 3), t) := by
  rw [crossingProductMap_eq_crossRegluedProductMap_of_ge (by norm_num),
    crossRegluedProductMap_curl_first]

theorem crossingProductMap_curl_second (t : ℝ) :
    crossingProductMap (47 / 10, t) = ((0, 3), t) := by
  rw [crossingProductMap_eq_crossRegluedProductMap_of_ge (by norm_num),
    crossRegluedProductMap_curl_second]

noncomputable def crossingProductCell : SingularTwoCell (EuclideanSpace ℝ (Fin 3)) where
  domain := seamWitnessCell.domain
  isPLBall_domain := seamWitnessCell.isPLBall_domain
  toFun := ⇑spliceEmbedding ∘ crossingProductMap ∘ ⇑seamWitnessPlane.symm
  isPLOn := by
    have hdom := seamWitnessCell.isPLBall_domain.isPolyhedron
    have hcomp := isPiecewiseAffineOn_crossingProductMap.comp
      (isPiecewiseAffineOn_seamWitnessPlaneSymm hdom)
    rw [preimage_univ, inter_univ] at hcomp
    have hpa := hcomp.affine_comp spliceEmbedding.toLinearMap.toAffineMap
    exact fun x hx => ⟨hpa.continuousOn x hx, hpa x hx⟩

private theorem crossingProductMap_cases {p : ℝ × ℝ} (hp : p.1 ∈ Icc (0 : ℝ) 5) :
    (0 ≤ p.1 ∧ p.1 ≤ 1 ∧ crossingProductMap p = ((2 - p.1, 0), p.2)) ∨
    (1 ≤ p.1 ∧ p.1 ≤ 2 ∧ crossingProductMap p = ((3 - 2 * p.1, 0), p.2)) ∨
    (2 ≤ p.1 ∧ p.1 ≤ 5 / 2 ∧ crossingProductMap p =
      ((3 - 2 * p.1, 8 - 4 * p.1), p.2)) ∨
    (5 / 2 ≤ p.1 ∧ p.1 ≤ 3 ∧ crossingProductMap p =
      ((4 * p.1 - 12, 2 * p.1 - 7), p.2)) ∨
    (3 ≤ p.1 ∧ p.1 ≤ 4 ∧ crossingProductMap p = ((0, 2 * p.1 - 7), p.2)) ∨
    (4 ≤ p.1 ∧ p.1 ≤ 21 / 5 ∧ crossingProductMap p = ((0, 15 * p.1 - 59), p.2)) ∨
    (21 / 5 ≤ p.1 ∧ p.1 ≤ 22 / 5 ∧ crossingProductMap p = ((5 * p.1 - 21, 4), p.2)) ∨
    (22 / 5 ≤ p.1 ∧ p.1 ≤ 23 / 5 ∧ crossingProductMap p = ((1, 26 - 5 * p.1), p.2)) ∨
    (23 / 5 ≤ p.1 ∧ p.1 ≤ 24 / 5 ∧ crossingProductMap p = ((47 - 10 * p.1, 3), p.2)) ∨
    (24 / 5 ≤ p.1 ∧ p.1 ≤ 5 ∧ crossingProductMap p = ((-1, 10 * p.1 - 45), p.2)) := by
  rcases le_or_gt p.1 1 with h1 | h1
  · exact Or.inl ⟨hp.1, h1, crossingProductMap_first h1⟩
  apply Or.inr
  rcases le_or_gt p.1 2 with h2 | h2
  · exact Or.inl ⟨h1.le, h2, crossingProductMap_second h1.le h2⟩
  apply Or.inr
  rcases le_or_gt p.1 (5 / 2) with h25 | h25
  · exact Or.inl ⟨h2.le, h25, crossingProductMap_third h2.le h25⟩
  apply Or.inr
  rcases le_or_gt p.1 3 with h3 | h3
  · exact Or.inl ⟨h25.le, h3, crossingProductMap_fourth h25.le h3⟩
  apply Or.inr
  rcases le_or_gt p.1 4 with h4 | h4
  · exact Or.inl ⟨h3.le, h4, crossingProductMap_fifth h3.le h4⟩
  apply Or.inr
  rw [crossingProductMap_eq_crossRegluedProductMap_of_ge (by linarith)]
  rcases le_or_gt p.1 (21 / 5) with h21 | h21
  · exact Or.inl ⟨h4.le, h21, crossRegluedProductMap_tail_first h4.le h21⟩
  apply Or.inr
  rcases le_or_gt p.1 (22 / 5) with h22 | h22
  · exact Or.inl ⟨h21.le, h22, crossRegluedProductMap_tail_second h21.le h22⟩
  apply Or.inr
  rcases le_or_gt p.1 (23 / 5) with h23 | h23
  · exact Or.inl ⟨h22.le, h23, crossRegluedProductMap_tail_third h22.le h23⟩
  apply Or.inr
  rcases le_or_gt p.1 (24 / 5) with h24 | h24
  · exact Or.inl ⟨h23.le, h24, crossRegluedProductMap_tail_fourth h23.le h24⟩
  · exact Or.inr ⟨h24.le, hp.2, crossRegluedProductMap_tail_fifth h24.le⟩

theorem crossingProductMap_eq_iff_of_lt {p q : ℝ × ℝ}
    (hp : p.1 ∈ Icc (0 : ℝ) 5) (hq : q.1 ∈ Icc (0 : ℝ) 5) (hpq : p.1 < q.1) :
    crossingProductMap p = crossingProductMap q ↔
      p.2 = q.2 ∧ ((p.1 = 3 / 2 ∧ q.1 = 7 / 2) ∨
        (p.1 = 62 / 15 ∧ q.1 = 47 / 10)) := by
  constructor
  · intro h
    rcases crossingProductMap_cases hp with
      ⟨hp0, hp1, hpval⟩ | ⟨hp0, hp1, hpval⟩ | ⟨hp0, hp1, hpval⟩ |
      ⟨hp0, hp1, hpval⟩ | ⟨hp0, hp1, hpval⟩ | ⟨hp0, hp1, hpval⟩ |
      ⟨hp0, hp1, hpval⟩ | ⟨hp0, hp1, hpval⟩ | ⟨hp0, hp1, hpval⟩ |
      ⟨hp0, hp1, hpval⟩ <;>
      rcases crossingProductMap_cases hq with
        ⟨hq0, hq1, hqval⟩ | ⟨hq0, hq1, hqval⟩ | ⟨hq0, hq1, hqval⟩ |
        ⟨hq0, hq1, hqval⟩ | ⟨hq0, hq1, hqval⟩ | ⟨hq0, hq1, hqval⟩ |
        ⟨hq0, hq1, hqval⟩ | ⟨hq0, hq1, hqval⟩ | ⟨hq0, hq1, hqval⟩ |
        ⟨hq0, hq1, hqval⟩
    all_goals
      rw [hpval, hqval] at h
      obtain ⟨hxy, ht⟩ := Prod.mk.inj h
      obtain ⟨hx, hy⟩ := Prod.mk.inj hxy
      refine ⟨ht, ?_⟩
      first
      | exact Or.inl ⟨by linarith, by linarith⟩
      | exact Or.inr ⟨by linarith, by linarith⟩
  · rintro ⟨ht, (⟨hp, hq⟩ | ⟨hp, hq⟩)⟩
    · have hp' : p = (3 / 2, p.2) := Prod.ext hp rfl
      have hq' : q = (7 / 2, p.2) := Prod.ext hq ht.symm
      rw [hp', hq', crossingProductMap_core_first, crossingProductMap_core_second]
    · have hp' : p = (62 / 15, p.2) := Prod.ext hp rfl
      have hq' : q = (47 / 10, p.2) := Prod.ext hq ht.symm
      rw [hp', hq', crossingProductMap_curl_first, crossingProductMap_curl_second]

theorem crossingProductMap_eq_iff {p q : ℝ × ℝ}
    (hp : p.1 ∈ Icc (0 : ℝ) 5) (hq : q.1 ∈ Icc (0 : ℝ) 5) :
    crossingProductMap p = crossingProductMap q ↔
      p.2 = q.2 ∧ (p.1 = q.1 ∨ (p.1 = 3 / 2 ∧ q.1 = 7 / 2) ∨
        (p.1 = 7 / 2 ∧ q.1 = 3 / 2) ∨ (p.1 = 62 / 15 ∧ q.1 = 47 / 10) ∨
          (p.1 = 47 / 10 ∧ q.1 = 62 / 15)) := by
  constructor
  · intro h
    have ht : p.2 = q.2 := by simpa only [crossingProductMap_snd] using congrArg Prod.snd h
    refine ⟨ht, ?_⟩
    rcases lt_trichotomy p.1 q.1 with hlt | heq | hgt
    · rcases (crossingProductMap_eq_iff_of_lt hp hq hlt).mp h with ⟨-, h | h⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl heq
    · rcases (crossingProductMap_eq_iff_of_lt hq hp hgt).mp h.symm with ⟨-, h | h⟩
      · exact Or.inr (Or.inr (Or.inl h.symm))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h.symm)))
  · rintro ⟨ht, h | h | h | h | h⟩
    · exact congrArg crossingProductMap (Prod.ext h ht)
    · exact (crossingProductMap_eq_iff_of_lt hp hq (by rw [h.1, h.2]; norm_num)).mpr
        ⟨ht, Or.inl h⟩
    · exact ((crossingProductMap_eq_iff_of_lt hq hp (by rw [h.1, h.2]; norm_num)).mpr
        ⟨ht.symm, Or.inl h.symm⟩).symm
    · exact (crossingProductMap_eq_iff_of_lt hp hq (by rw [h.1, h.2]; norm_num)).mpr
        ⟨ht, Or.inr h⟩
    · exact ((crossingProductMap_eq_iff_of_lt hq hp (by rw [h.1, h.2]; norm_num)).mpr
        ⟨ht.symm, Or.inr h.symm⟩).symm

theorem crossingProductMap_doublePointSet :
    doublePointSet crossingProductMap seamSourceRect =
      ({((0 : ℝ), (0 : ℝ))} ∪ {((0 : ℝ), (3 : ℝ))}) ×ˢ Icc (0 : ℝ) 1 := by
  apply Subset.antisymm
  · rintro y ⟨p, hp, q, hq, hpq, hpy, hqy⟩
    have heq := (crossingProductMap_eq_iff hp.1 hq.1).mp (hpy.trans hqy.symm)
    have ht : y.2 = p.2 := by
      simpa only [crossingProductMap_snd] using (congrArg Prod.snd hpy).symm
    refine ⟨?_, ht ▸ hp.2⟩
    rcases heq.2 with h | ⟨hp', hq'⟩ | ⟨hp', hq'⟩ | ⟨hp', hq'⟩ | ⟨hp', hq'⟩
    · exact (hpq (Prod.ext h heq.1)).elim
    · have hpp : p = (3 / 2, p.2) := Prod.ext hp' rfl
      rw [hpp, crossingProductMap_core_first] at hpy
      exact Or.inl (congrArg Prod.fst hpy).symm
    · have hpp : p = (7 / 2, p.2) := Prod.ext hp' rfl
      rw [hpp, crossingProductMap_core_second] at hpy
      exact Or.inl (congrArg Prod.fst hpy).symm
    · have hpp : p = (62 / 15, p.2) := Prod.ext hp' rfl
      rw [hpp, crossingProductMap_curl_first] at hpy
      exact Or.inr (congrArg Prod.fst hpy).symm
    · have hpp : p = (47 / 10, p.2) := Prod.ext hp' rfl
      rw [hpp, crossingProductMap_curl_second] at hpy
      exact Or.inr (congrArg Prod.fst hpy).symm
  · rintro ⟨⟨x, y⟩, t⟩ ⟨h | h, ht⟩
    · have hxy : (x, y) = ((0 : ℝ), (0 : ℝ)) := h
      refine ⟨(3 / 2, t), ⟨⟨by norm_num, by norm_num⟩, ht⟩,
        (7 / 2, t), ⟨⟨by norm_num, by norm_num⟩, ht⟩, ?_, ?_, ?_⟩
      · intro h
        have := congrArg Prod.fst h
        norm_num at this
      · rw [crossingProductMap_core_first, hxy]
      · rw [crossingProductMap_core_second, hxy]
    · have hxy : (x, y) = ((0 : ℝ), (3 : ℝ)) := h
      refine ⟨(62 / 15, t), ⟨⟨by norm_num, by norm_num⟩, ht⟩,
        (47 / 10, t), ⟨⟨by norm_num, by norm_num⟩, ht⟩, ?_, ?_, ?_⟩
      · intro h
        have := congrArg Prod.fst h
        norm_num at this
      · rw [crossingProductMap_curl_first, hxy]
      · rw [crossingProductMap_curl_second, hxy]

theorem crossingProductCell_doublePointSet :
    doublePointSet (⇑crossingProductCell) crossingProductCell.domain =
      ⇑spliceEmbedding ''
        (({((0 : ℝ), (0 : ℝ))} ∪ {((0 : ℝ), (3 : ℝ))}) ×ˢ Icc (0 : ℝ) 1) := by
  change doublePointSet ((⇑spliceEmbedding ∘ crossingProductMap) ∘ ⇑seamWitnessPlane.symm)
      (⇑seamWitnessPlane '' seamSourceRect) = _
  rw [doublePointSet_comp_of_bijOn (bijOn_seamWitnessPlaneSymm seamSourceRect)]
  rw [image_doublePointSet_of_injOn spliceEmbedding.injective.injOn,
    crossingProductMap_doublePointSet]

theorem crossingProductMap_eq_or_eq_of_eq {p q r : ℝ × ℝ}
    (hp : p.1 ∈ Icc (0 : ℝ) 5) (hq : q.1 ∈ Icc (0 : ℝ) 5)
    (hr : r.1 ∈ Icc (0 : ℝ) 5) (hpq : p ≠ q)
    (heq : crossingProductMap p = crossingProductMap q)
    (her : crossingProductMap p = crossingProductMap r) : r = p ∨ r = q := by
  obtain ⟨htq, hq⟩ := (crossingProductMap_eq_iff hp hq).mp heq
  obtain ⟨htr, hr⟩ := (crossingProductMap_eq_iff hp hr).mp her
  rcases hq with hq | ⟨hpq1, hpq2⟩ | ⟨hpq1, hpq2⟩ | ⟨hpq1, hpq2⟩ | ⟨hpq1, hpq2⟩
  · exact (hpq (Prod.ext hq htq)).elim
  all_goals
    rcases hr with hr | ⟨hpr1, hpr2⟩ | ⟨hpr1, hpr2⟩ | ⟨hpr1, hpr2⟩ | ⟨hpr1, hpr2⟩
    all_goals
      first
      | exact Or.inl (Prod.ext (by linarith) htr.symm)
      | exact Or.inr (Prod.ext (by linarith) (htr.symm.trans htq))

theorem crossingProductMap_fiber_le_two (y : (ℝ × ℝ) × ℝ) :
    (seamSourceRect ∩ crossingProductMap ⁻¹' {y}).encard ≤ 2 := by
  by_cases h : (seamSourceRect ∩ crossingProductMap ⁻¹' {y}).Nontrivial
  · obtain ⟨p, hp, q, hq, hpq⟩ := h
    have hsub : seamSourceRect ∩ crossingProductMap ⁻¹' {y} ⊆ {p, q} := by
      rintro r hr
      rcases crossingProductMap_eq_or_eq_of_eq hp.1.1 hq.1.1 hr.1.1 hpq
          (hp.2.trans hq.2.symm) (hp.2.trans hr.2.symm) with h | h
      · exact Or.inl h
      · exact Or.inr h
    exact (Set.encard_le_encard hsub).trans (by rw [Set.encard_pair hpq])
  · have hsingle : (seamSourceRect ∩ crossingProductMap ⁻¹' {y}).Subsingleton := by
      intro p hp q hq
      by_contra hpq
      exact h ⟨p, hp, q, hq, hpq⟩
    exact (Set.encard_le_one_iff_subsingleton.mpr hsingle).trans (by norm_num)

theorem crossingProductCell_fiber_le_two (y : EuclideanSpace ℝ (Fin 3)) :
    (crossingProductCell.domain ∩ ⇑crossingProductCell ⁻¹' {y}).encard ≤ 2 := by
  have hmaps : MapsTo (⇑seamWitnessPlane.symm)
      (crossingProductCell.domain ∩ ⇑crossingProductCell ⁻¹' {y})
      (seamSourceRect ∩ crossingProductMap ⁻¹' {spliceEmbedding.symm y}) := by
    rintro x ⟨hx, heq⟩
    refine ⟨mem_image_seamWitnessPlane.mp hx, ?_⟩
    apply spliceEmbedding.injective
    change crossingProductCell x = spliceEmbedding (spliceEmbedding.symm y)
    simpa only [ContinuousLinearEquiv.apply_symm_apply, Set.mem_preimage,
      Set.mem_singleton_iff] using heq
  exact (Set.encard_le_encard_of_injOn hmaps seamWitnessPlane.symm.injective.injOn).trans
    (crossingProductMap_fiber_le_two _)

theorem crossingProductMap_injOn_strip (s : ℝ) :
    InjOn crossingProductMap
      (seamSourceRect ∩ Prod.fst ⁻¹' Ioo (s - 1 / 10) (s + 1 / 10)) := by
  rintro p ⟨hp, hp0, hp1⟩ q ⟨hq, hq0, hq1⟩ heq
  obtain ⟨ht, h⟩ := (crossingProductMap_eq_iff hp.1 hq.1).mp heq
  apply Prod.ext _ ht
  rcases h with h | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> linarith

theorem crossingProductCell_locallyInjective :
    ∀ x ∈ crossingProductCell.domain,
      ∃ V ∈ 𝓝[crossingProductCell.domain] x, InjOn (⇑crossingProductCell) V := by
  intro x hx
  let s := (seamWitnessPlane.symm x).1
  let O := (Prod.fst ∘ ⇑seamWitnessPlane.symm) ⁻¹' Ioo (s - 1 / 10) (s + 1 / 10)
  have hO : IsOpen O := isOpen_Ioo.preimage
    (continuous_fst.comp seamWitnessPlane.symm.continuous)
  have hxO : x ∈ O := by
    change s - 1 / 10 < s ∧ s < s + 1 / 10
    constructor <;> linarith
  refine ⟨crossingProductCell.domain ∩ O,
    Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (hO.mem_nhds hxO)), ?_⟩
  rintro p ⟨hp, hpO⟩ q ⟨hq, hqO⟩ heq
  apply seamWitnessPlane.symm.injective
  apply crossingProductMap_injOn_strip s
    ⟨mem_image_seamWitnessPlane.mp hp, hpO⟩ ⟨mem_image_seamWitnessPlane.mp hq, hqO⟩
  exact spliceEmbedding.injective heq

def crossingProductBox : Set ((ℝ × ℝ) × ℝ) :=
  (Icc (-3 : ℝ) 2 ×ˢ Icc (-3 : ℝ) 5) ×ˢ Icc (0 : ℝ) 1

noncomputable def crossingProductSide : Set (EuclideanSpace ℝ (Fin 3)) :=
  ⇑spliceEmbedding '' crossingProductBox

theorem isHPolytope_crossingProductBox : IsHPolytope crossingProductBox :=
  (isHPolytope_Icc.prod isHPolytope_Icc).prod isHPolytope_Icc

theorem isCompact_crossingProductSide : IsCompact crossingProductSide :=
  isHPolytope_crossingProductBox.isPolyhedron.isCompact.image spliceEmbedding.continuous

theorem crossingProductMap_bounds {p : ℝ × ℝ} (hp : p.1 ∈ Icc (0 : ℝ) 5) :
    -3 < (crossingProductMap p).1.1 ∧ (crossingProductMap p).1.1 ≤ 2 ∧
      -3 < (crossingProductMap p).1.2 ∧ (crossingProductMap p).1.2 ≤ 5 ∧
        ((crossingProductMap p).1.1 = 2 ↔ p.1 = 0) ∧
          ((crossingProductMap p).1.2 = 5 ↔ p.1 = 5) := by
  rcases crossingProductMap_cases hp with
    ⟨h0, h1, hval⟩ | ⟨h0, h1, hval⟩ | ⟨h0, h1, hval⟩ | ⟨h0, h1, hval⟩ |
    ⟨h0, h1, hval⟩ | ⟨h0, h1, hval⟩ | ⟨h0, h1, hval⟩ | ⟨h0, h1, hval⟩ |
    ⟨h0, h1, hval⟩ | ⟨h0, h1, hval⟩ <;> rw [hval]
  all_goals
    dsimp
    refine ⟨by linarith, by linarith, by linarith, by linarith, ?_, ?_⟩ <;>
      constructor <;> intro h <;> linarith

theorem crossingProductMap_mapsTo_box :
    MapsTo crossingProductMap seamSourceRect crossingProductBox := by
  intro p hp
  obtain ⟨hx0, hx1, hy0, hy1, -⟩ := crossingProductMap_bounds hp.1
  exact ⟨⟨⟨hx0.le, hx1⟩, ⟨hy0.le, hy1⟩⟩, by simpa using hp.2⟩

theorem crossingProductMap_mem_frontier_box_iff {p : ℝ × ℝ} (hp : p ∈ seamSourceRect) :
    crossingProductMap p ∈ frontier crossingProductBox ↔ p ∈ frontier seamSourceRect := by
  have hboxclosed := isHPolytope_crossingProductBox.isPolyhedron.isClosed
  have hmap := crossingProductMap_mapsTo_box hp
  obtain ⟨hx0, hx1, hy0, hy1, hxend, hyend⟩ := crossingProductMap_bounds hp.1
  rw [hboxclosed.frontier_eq, frontier_seamSourceRect, mem_sdiff, mem_sdiff,
    and_iff_right hmap, and_iff_right hp, crossingProductBox,
    interior_prod_eq, interior_prod_eq, interior_Icc, interior_Icc, interior_Icc]
  apply not_congr
  simp only [mem_prod, mem_Ioo, crossingProductMap_snd]
  constructor
  · rintro ⟨⟨hx, hy⟩, ht⟩
    refine ⟨⟨lt_of_le_of_ne hp.1.1 ?_, lt_of_le_of_ne hp.1.2 ?_⟩, ht⟩
    · intro h
      exact (ne_of_lt hx.2) (hxend.mpr h.symm)
    · intro h
      exact (ne_of_lt hy.2) (hyend.mpr h)
  · rintro ⟨hs, ht⟩
    refine ⟨⟨⟨hx0, lt_of_le_of_ne hx1 ?_⟩, ⟨hy0, lt_of_le_of_ne hy1 ?_⟩⟩, ht⟩
    · intro h
      exact (ne_of_gt hs.1) (hxend.mp h)
    · intro h
      exact (ne_of_lt hs.2) (hyend.mp h)

theorem crossingProductCell_mapsTo_side :
    MapsTo (⇑crossingProductCell) crossingProductCell.domain crossingProductSide := by
  intro x hx
  refine ⟨crossingProductMap (seamWitnessPlane.symm x),
    crossingProductMap_mapsTo_box (mem_image_seamWitnessPlane.mp hx), rfl⟩

theorem crossingProductCell_preimage_frontier_side :
    crossingProductCell.domain ∩ ⇑crossingProductCell ⁻¹' frontier crossingProductSide =
      frontier crossingProductCell.domain := by
  have hfront : frontier crossingProductSide = ⇑spliceEmbedding '' frontier crossingProductBox :=
    (spliceEmbedding.toHomeomorph.image_frontier crossingProductBox).symm
  have hfrontD : frontier crossingProductCell.domain =
      ⇑seamWitnessPlane '' frontier seamSourceRect := frontier_seamWitnessCell_domain
  rw [hfront, hfrontD]
  ext x
  constructor
  · rintro ⟨hx, y, hy, hxy⟩
    have hy' : y = crossingProductMap (seamWitnessPlane.symm x) :=
      spliceEmbedding.injective hxy
    rw [hy'] at hy
    exact mem_image_seamWitnessPlane.mpr
      ((crossingProductMap_mem_frontier_box_iff (mem_image_seamWitnessPlane.mp hx)).mp hy)
  · intro hx
    have hx' := mem_image_seamWitnessPlane.mp hx
    have hxD : x ∈ crossingProductCell.domain :=
      mem_image_seamWitnessPlane.mpr
        (isPolyhedron_seamSourceRect.isClosed.frontier_subset hx')
    exact ⟨hxD, crossingProductMap (seamWitnessPlane.symm x),
      (crossingProductMap_mem_frontier_box_iff (mem_image_seamWitnessPlane.mp hxD)).mpr hx', rfl⟩

theorem crossingProductCell_image_inter_frontier_side :
    ⇑crossingProductCell '' crossingProductCell.domain ∩ frontier crossingProductSide =
      Set.range crossingProductCell.boundary := by
  rw [← image_inter_preimage, crossingProductCell_preimage_frontier_side]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.property, rfl⟩

theorem crossingProductCell_boundary_not_injOn :
    ¬InjOn (⇑crossingProductCell)
      (frontier crossingProductCell.domain ∩
        (Prod.fst ∘ ⇑seamWitnessPlane.symm) ⁻¹' Icc (7 / 2 : ℝ) 5) := by
  let p := seamWitnessPlane (62 / 15, (0 : ℝ))
  let q := seamWitnessPlane (47 / 10, (0 : ℝ))
  have hp : p ∈ frontier crossingProductCell.domain := by
    rw [show crossingProductCell.domain = seamWitnessCell.domain from rfl,
      frontier_seamWitnessCell_domain, mem_image_seamWitnessPlane, frontier_seamSourceRect]
    simp only [p, ContinuousLinearEquiv.symm_apply_apply, seamSourceRect,
      mem_sdiff, mem_prod, mem_Icc, mem_Ioo]
    norm_num
  have hq : q ∈ frontier crossingProductCell.domain := by
    rw [show crossingProductCell.domain = seamWitnessCell.domain from rfl,
      frontier_seamWitnessCell_domain, mem_image_seamWitnessPlane, frontier_seamSourceRect]
    simp only [q, ContinuousLinearEquiv.symm_apply_apply, seamSourceRect,
      mem_sdiff, mem_prod, mem_Icc, mem_Ioo]
    norm_num
  intro hinj
  have hpq : p = q := hinj ⟨hp, by norm_num [p]⟩ ⟨hq, by norm_num [q]⟩ (by
    change spliceEmbedding (crossingProductMap (seamWitnessPlane.symm p)) =
      spliceEmbedding (crossingProductMap (seamWitnessPlane.symm q))
    simp only [p, q, ContinuousLinearEquiv.symm_apply_apply, crossingProductMap_curl_first,
      crossingProductMap_curl_second])
  have h := congrArg Prod.fst (seamWitnessPlane.injective hpq)
  norm_num at h

theorem crossingProductMap_eq_crossRegluedProductMap_reflection {p : ℝ × ℝ}
    (h15 : 3 / 2 ≤ p.1) (h35 : p.1 ≤ 7 / 2) :
    crossingProductMap p = crossRegluedProductMap (5 - p.1, p.2) := by
  rw [crossRegluedProductMap_eq_seamModelMap (by dsimp; linarith)]
  rcases le_or_gt p.1 2 with h2 | h2
  · rw [crossingProductMap_second (by linarith) h2]
    unfold seamModelMap
    rw [seamArcX_bandNeg (by dsimp; linarith),
      seamArcY_bandNeg (by dsimp; linarith) (by dsimp; linarith)]
    dsimp
    rw [min_eq_left (by linarith : 2 * (5 - p.1) - 7 ≤ 0),
      max_eq_right (by linarith : 2 * (5 - p.1) - 7 ≤ 0)]
    congr 2
    ring
  rcases le_or_gt p.1 (5 / 2) with h25 | h25
  · rw [crossingProductMap_third h2.le h25]
    unfold seamModelMap
    rw [seamArcX_connectorHigh (by dsimp; linarith) (by dsimp; linarith)]
    simp only [seamArcY, seamRamp]
    rw [max_eq_left (by linarith : 0 ≤ 5 - p.1 - 3 / 2),
      max_eq_left (by linarith : 0 ≤ 5 - p.1 - 5 / 2),
      max_eq_right (by linarith : 5 - p.1 - 3 ≤ 0),
      max_eq_right (by linarith : 5 - p.1 - 7 / 2 ≤ 0),
      max_eq_right (by linarith : 5 - p.1 - 4 ≤ 0)]
    congr 2 <;> ring
  rcases le_or_gt p.1 3 with h3 | h3
  · rw [crossingProductMap_fourth h25.le h3]
    unfold seamModelMap
    rw [seamArcY_connectorLow (by dsimp; linarith) (by dsimp; linarith)]
    simp only [seamArcX, seamRamp]
    rw [max_eq_left (by linarith : 0 ≤ 5 - p.1 - 1),
      max_eq_left (by linarith : 0 ≤ 5 - p.1 - 3 / 2),
      max_eq_left (by linarith : 0 ≤ 5 - p.1 - 2),
      max_eq_right (by linarith : 5 - p.1 - 5 / 2 ≤ 0),
      max_eq_right (by linarith : 5 - p.1 - 7 / 2 ≤ 0)]
    congr 2 <;> ring
  · rw [crossingProductMap_fifth h3.le (by linarith)]
    unfold seamModelMap
    rw [seamArcX_bandPos (by dsimp; linarith) (by dsimp; linarith),
      seamArcY_bandPos (by dsimp; linarith)]
    dsimp
    rw [max_eq_right (by linarith : 3 - 2 * (5 - p.1) ≤ 0),
      min_eq_left (by linarith : 3 - 2 * (5 - p.1) ≤ 0)]
    congr 2
    ring

theorem crossRegluedProductMap_eq_crossingProductMap_reflection {p : ℝ × ℝ}
    (h15 : 3 / 2 ≤ p.1) (h35 : p.1 ≤ 7 / 2) :
    crossRegluedProductMap p = crossingProductMap (5 - p.1, p.2) := by
  rw [crossingProductMap_eq_crossRegluedProductMap_reflection
    (by dsimp; linarith) (by dsimp; linarith)]
  congr 1
  exact Prod.ext (by dsimp; ring) rfl

theorem crossingProductMap_image :
    crossingProductMap '' seamSourceRect = crossRegluedProductMap '' seamSourceRect := by
  apply Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    rcases le_or_gt p.1 (3 / 2) with h15 | h15
    · exact ⟨p, hp, (crossingProductMap_eq_crossRegluedProductMap_of_le h15).symm⟩
    rcases le_or_gt p.1 (7 / 2) with h35 | h35
    · exact ⟨(5 - p.1, p.2), ⟨⟨by dsimp; linarith, by dsimp; linarith⟩, hp.2⟩,
        (crossingProductMap_eq_crossRegluedProductMap_reflection h15.le h35).symm⟩
    · exact ⟨p, hp, (crossingProductMap_eq_crossRegluedProductMap_of_ge h35.le).symm⟩
  · rintro _ ⟨p, hp, rfl⟩
    rcases le_or_gt p.1 (3 / 2) with h15 | h15
    · exact ⟨p, hp, crossingProductMap_eq_crossRegluedProductMap_of_le h15⟩
    rcases le_or_gt p.1 (7 / 2) with h35 | h35
    · exact ⟨(5 - p.1, p.2), ⟨⟨by dsimp; linarith, by dsimp; linarith⟩, hp.2⟩,
        (crossRegluedProductMap_eq_crossingProductMap_reflection h15.le h35).symm⟩
    · exact ⟨p, hp, crossingProductMap_eq_crossRegluedProductMap_of_ge h35.le⟩

theorem crossingProductCell_image :
    ⇑crossingProductCell '' crossingProductCell.domain =
      ⇑crossRegluedProductCell '' crossRegluedProductCell.domain := by
  change (⇑spliceEmbedding ∘ crossingProductMap ∘ ⇑seamWitnessPlane.symm) ''
      (⇑seamWitnessPlane '' seamSourceRect) =
    (⇑spliceEmbedding ∘ crossRegluedProductMap ∘ ⇑seamWitnessPlane.symm) ''
      (⇑seamWitnessPlane '' seamSourceRect)
  rw [Set.image_comp, Set.image_comp, Set.image_comp, Set.image_comp,
    seamWitnessPlane.symm_image_image, crossingProductMap_image]

theorem crossingProductCell_image_crossingFigure :
    ⇑spliceEmbedding '' crossingFigure =
      ⇑crossingProductCell '' crossingProductCell.domain ∩ ⇑spliceEmbedding '' spliceCylinder := by
  rw [crossingProductCell_image]
  have h := crossRegluedProductReading.reglued_eq.image_eq
  change ⇑crossRegluedProductCell '' crossRegluedProductReading.tubeSource =
    (⇑spliceEmbedding ∘ crossSeamInclude ∘ crossRegluedProductReading.coord) ''
      crossRegluedProductReading.tubeSource at h
  rw [Set.image_comp, Set.image_comp, crossRegluedProductReading.bijOn_coord.image_eq,
    image_crossSeamInclude, bentFigure_eq_crossingFigure] at h
  rw [crossRegluedProductReading.tubeSource_eq, Set.image_inter_preimage] at h
  exact h.symm

theorem crossingProductCell_doublePointSet_inter_tube :
    doublePointSet (⇑crossingProductCell) crossingProductCell.domain ∩
      ⇑spliceEmbedding '' tubeWitnessTube = ⇑spliceEmbedding '' spliceCore := by
  rw [crossingProductCell_doublePointSet,
    ← Set.InjOn.image_inter spliceEmbedding.injective.injOn (subset_univ _) (subset_univ _)]
  apply congrArg (⇑spliceEmbedding '' ·)
  ext p
  constructor
  · rintro ⟨⟨h | h, ht⟩, hU⟩
    · exact ⟨h, ht⟩
    · have h' : p.1 = ((0 : ℝ), (3 : ℝ)) := h
      have hy := hU.1.2.2
      rw [h'] at hy
      norm_num at hy
  · rintro ⟨h, ht⟩
    refine ⟨⟨Or.inl h, ht⟩, ?_⟩
    simp only [tubeWitnessTube, mem_prod, mem_Ioo]
    have h' : p.1 = ((0 : ℝ), (0 : ℝ)) := h
    rw [h']
    exact ⟨⟨by norm_num, by norm_num⟩, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩

theorem crossSeamTubeCore_crossingProductCell :
    CrossSeamTubeCore (⇑spliceEmbedding)
      (⇑crossingProductCell '' crossingProductCell.domain)
      (doublePointSet (⇑crossingProductCell) crossingProductCell.domain)
      (⇑spliceEmbedding '' spliceCore) (⇑spliceEmbedding '' tubeWitnessTube) where
  isOpen_tube := crossSeamTubeCore_spliceEmbedding.isOpen_tube
  continuousOn_chart := spliceEmbedding.continuous.continuousOn
  injOn_chart := spliceEmbedding.injective.injOn
  image_subset_tube := crossSeamTubeCore_spliceEmbedding.image_subset_tube
  image_spliceCore := rfl
  image_crossingFigure := crossingProductCell_image_crossingFigure
  double_inter_tube := crossingProductCell_doublePointSet_inter_tube

theorem spliceCylinder_subset_crossingProductBox : spliceCylinder ⊆ crossingProductBox := by
  intro p hp
  have hxy := mem_spliceSquare.mp hp.1
  exact ⟨⟨⟨by linarith [hxy.1.1], by linarith [hxy.1.2]⟩,
    ⟨by linarith [hxy.2.1], by linarith [hxy.2.2]⟩⟩, hp.2⟩

theorem spliceCylinder_inter_frontier_crossingProductBox :
    spliceCylinder ∩ frontier crossingProductBox = spliceEndDisks := by
  rw [isHPolytope_crossingProductBox.isPolyhedron.isClosed.frontier_eq]
  have hint : interior crossingProductBox =
      (Ioo (-3 : ℝ) 2 ×ˢ Ioo (-3 : ℝ) 5) ×ˢ Ioo (0 : ℝ) 1 := by
    rw [crossingProductBox, interior_prod_eq, interior_prod_eq,
      interior_Icc, interior_Icc, interior_Icc]
  rw [hint]
  apply Subset.antisymm
  · rintro p ⟨hp, -, hpint⟩
    refine ⟨hp.1, ?_⟩
    by_contra hend
    have h0 : p.2 ≠ 0 := fun h => hend (Or.inl h)
    have h1 : p.2 ≠ 1 := fun h => hend (Or.inr h)
    have hxy := mem_spliceSquare.mp hp.1
    exact hpint ⟨⟨⟨by linarith [hxy.1.1], by linarith [hxy.1.2]⟩,
      ⟨by linarith [hxy.2.1], by linarith [hxy.2.2]⟩⟩,
      lt_of_le_of_ne hp.2.1 h0.symm, lt_of_le_of_ne hp.2.2 h1⟩
  · intro p hp
    have hcyl := spliceEndDisks_subset_spliceCylinder hp
    refine ⟨hcyl, spliceCylinder_subset_crossingProductBox hcyl, ?_⟩
    rintro ⟨-, h0, h1⟩
    rcases hp.2 with h | h
    · exact (ne_of_gt h0) h
    · exact (ne_of_lt h1) h

theorem crossingProductTube_boundary :
    ⇑spliceEmbedding '' spliceCylinder ∩ frontier crossingProductSide =
      ⇑spliceEmbedding '' spliceEndDisks := by
  rw [show frontier crossingProductSide = ⇑spliceEmbedding '' frontier crossingProductBox from
    (spliceEmbedding.toHomeomorph.image_frontier crossingProductBox).symm,
    ← Set.InjOn.image_inter spliceEmbedding.injective.injOn (subset_univ _) (subset_univ _),
    spliceCylinder_inter_frontier_crossingProductBox]

theorem crossingProductTube_side :
    ⇑spliceEmbedding '' spliceCylinder ⊆ crossingProductSide :=
  Set.image_mono spliceCylinder_subset_crossingProductBox

theorem crossingProductMap_of_mem_core_horizontal {p : ℝ × ℝ}
    (hp : p.1 ∈ Icc (1 : ℝ) 2) :
    crossingProductMap p = ((3 - 2 * p.1, 0), p.2) :=
  crossingProductMap_second hp.1 hp.2

theorem crossingProductMap_of_mem_core_vertical {p : ℝ × ℝ}
    (hp : p.1 ∈ Icc (3 : ℝ) 4) :
    crossingProductMap p = ((0, 2 * p.1 - 7), p.2) :=
  crossingProductMap_fifth hp.1 hp.2

theorem crossingProductMap_of_mem_curl_horizontal {p : ℝ × ℝ}
    (hp : p.1 ∈ Icc (23 / 5 : ℝ) (24 / 5)) :
    crossingProductMap p = ((47 - 10 * p.1, 3), p.2) := by
  rw [crossingProductMap_eq_crossRegluedProductMap_of_ge (by linarith [hp.1])]
  exact crossRegluedProductMap_tail_fourth hp.1 hp.2

theorem crossingProductMap_of_mem_curl_vertical {p : ℝ × ℝ}
    (hp : p.1 ∈ Icc (4 : ℝ) (21 / 5)) :
    crossingProductMap p = ((0, 15 * p.1 - 59), p.2) := by
  rw [crossingProductMap_eq_crossRegluedProductMap_of_ge (by linarith [hp.1])]
  exact crossRegluedProductMap_tail_first hp.1 hp.2

end DifferentialGeometry.Topology.PiecewiseLinear
