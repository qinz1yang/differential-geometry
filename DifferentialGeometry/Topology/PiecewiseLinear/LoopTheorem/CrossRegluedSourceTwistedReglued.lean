/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceTwistedCut

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def crossRegluedTwistedLift (p : ℝ × ℝ) : (ℝ × ℝ) × ℝ :=
  ((p.1 + seamRamp (-2) 0 p + seamRamp 2 1 p, p.1 - 1 / 2), p.2)

noncomputable def crossRegluedTwistedMap : (ℝ × ℝ) → halfTurnQuotient :=
  halfTurnProjection ∘ crossRegluedTwistedLift

theorem isPiecewiseAffineOn_crossRegluedTwistedLift :
    IsPiecewiseAffineOn crossRegluedTwistedLift univ := by
  have hx := isPiecewiseAffineOn_of_affine (LinearMap.fst ℝ ℝ ℝ).toAffineMap isOpen_univ
  exact (((hx.add (isPiecewiseAffineOn_seamRamp (-2) 0)).add
    (isPiecewiseAffineOn_seamRamp 2 1)).prod_mk
      (isPiecewiseAffineOn_seamShift (1 / 2))).prod_mk isPiecewiseAffineOn_seamSnd

theorem crossRegluedTwistedLift_left {p : ℝ × ℝ} (hp : p.1 ≤ 0) :
    crossRegluedTwistedLift p = ((p.1, p.1 - 1 / 2), p.2) := by
  simp [crossRegluedTwistedLift, seamRamp, max_eq_right hp,
    max_eq_right (by linarith : p.1 - 1 ≤ 0)]

theorem crossRegluedTwistedLift_middle {p : ℝ × ℝ} (hp : p.1 ∈ Icc 0 1) :
    crossRegluedTwistedLift p = ((-p.1, p.1 - 1 / 2), p.2) := by
  simp only [crossRegluedTwistedLift, seamRamp, sub_zero, max_eq_left hp.1,
    max_eq_right (by linarith [hp.2] : p.1 - 1 ≤ 0)]
  congr 2
  ring

theorem crossRegluedTwistedLift_right {p : ℝ × ℝ} (hp : 1 ≤ p.1) :
    crossRegluedTwistedLift p = ((p.1 - 2, p.1 - 1 / 2), p.2) := by
  simp only [crossRegluedTwistedLift, seamRamp, sub_zero,
    max_eq_left (by linarith : 0 ≤ p.1), max_eq_left (by linarith : 0 ≤ p.1 - 1)]
  congr 2
  ring

theorem crossRegluedTwistedMap_left {p : ℝ × ℝ} (hp : p.1 ≤ 0) :
    crossRegluedTwistedMap p = twistedStripMap p := by
  change halfTurnProjection (crossRegluedTwistedLift p) = _
  rw [crossRegluedTwistedLift_left hp]
  rfl

theorem crossRegluedTwistedMap_middle {p : ℝ × ℝ} (hp : p.1 ∈ Icc 0 1) :
    crossRegluedTwistedMap p = twistedStripMap (1 - p.1, 1 - p.2) := by
  have h : crossRegluedTwistedLift p =
      halfTurnTranslation (-1) (((1 - p.1), (1 - p.1) - 1 / 2), 1 - p.2) := by
    rw [crossRegluedTwistedLift_middle hp]
    ext <;> simp [halfTurnTranslation] <;> ring
  change halfTurnProjection (crossRegluedTwistedLift p) = _
  rw [h, halfTurnProjection_translation]
  rfl

theorem crossRegluedTwistedMap_right {p : ℝ × ℝ} (hp : 1 ≤ p.1) :
    crossRegluedTwistedMap p = twistedStripMap p := by
  have h : crossRegluedTwistedLift p =
      halfTurnTranslation (-2) ((p.1, p.1 - 1 / 2), p.2) := by
    rw [crossRegluedTwistedLift_right hp]
    (ext <;> simp [halfTurnTranslation]); ring
  change halfTurnProjection (crossRegluedTwistedLift p) = _
  rw [h, halfTurnProjection_translation]
  rfl

theorem isPL_crossRegluedTwistedMap :
    IsPL 2 3 (crossRegluedTwistedMap ∘ ⇑seamWitnessPlane.symm) := by
  have hpa := (isPiecewiseAffineOn_crossRegluedTwistedLift.comp
    (isPiecewiseAffineOn_of_affine seamWitnessPlane.symm.toAffineEquiv.toAffineMap
      isOpen_univ)).affine_comp spliceEmbedding.toAffineEquiv.toAffineMap
  simp only [preimage_univ, inter_univ] at hpa
  have hpl : IsPL 2 3
      (⇑spliceEmbedding ∘ crossRegluedTwistedLift ∘ ⇑seamWitnessPlane.symm) :=
    fun x => ⟨hpa.continuousOn x (mem_univ x), hpa x (mem_univ x)⟩
  have heq : halfTurnEuclideanProjection ∘
      (⇑spliceEmbedding ∘ crossRegluedTwistedLift ∘ ⇑seamWitnessPlane.symm) =
      crossRegluedTwistedMap ∘ ⇑seamWitnessPlane.symm := by
    funext x
    change halfTurnProjection (spliceEmbedding.symm
      (spliceEmbedding (crossRegluedTwistedLift (seamWitnessPlane.symm x)))) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
    rfl
  rw [← heq]
  exact isPL_halfTurnEuclideanProjection.comp hpl

noncomputable def crossRegluedTwistedCell : SingularTwoCell halfTurnQuotient where
  domain := twistedStripCell.domain
  isPLBall_domain := twistedStripCell.isPLBall_domain
  toFun := crossRegluedTwistedMap ∘ ⇑seamWitnessPlane.symm
  isPLOn := fun x _ => IsPLWithinAt.mono_of_isPolyhedron
    (isPL_crossRegluedTwistedMap x) twistedStripCell.isPLBall_domain.isPolyhedron (subset_univ _)

theorem crossRegluedTwistedCell_eq_left :
    EqOn (⇑crossRegluedTwistedCell) (⇑twistedStripCell)
      (seamWitnessPlane '' (Icc (-1 / 4 : ℝ) 0 ×ˢ Icc (0 : ℝ) 1)) := by
  rintro z ⟨p, hp, rfl⟩
  change crossRegluedTwistedMap (seamWitnessPlane.symm (seamWitnessPlane p)) =
    twistedStripMap (seamWitnessPlane.symm (seamWitnessPlane p))
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using crossRegluedTwistedMap_left hp.1.2

theorem crossRegluedTwistedCell_eq_middle :
    EqOn (⇑crossRegluedTwistedCell) (⇑twistedStripCell ∘ ⇑twistedStripReflection)
      (seamWitnessPlane '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) := by
  rintro z ⟨⟨s, t⟩, hp, rfl⟩
  simp only [Function.comp_apply, twistedStripReflection_apply]
  change crossRegluedTwistedMap (seamWitnessPlane.symm (seamWitnessPlane (s, t))) =
    twistedStripMap (seamWitnessPlane.symm (seamWitnessPlane (1 - s, 1 - t)))
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using crossRegluedTwistedMap_middle hp.1

theorem crossRegluedTwistedCell_eq_right :
    EqOn (⇑crossRegluedTwistedCell) (⇑twistedStripCell)
      (seamWitnessPlane '' (Icc (1 : ℝ) (5 / 4) ×ˢ Icc (0 : ℝ) 1)) := by
  rintro z ⟨p, hp, rfl⟩
  change crossRegluedTwistedMap (seamWitnessPlane.symm (seamWitnessPlane p)) =
    twistedStripMap (seamWitnessPlane.symm (seamWitnessPlane p))
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using crossRegluedTwistedMap_right hp.1.1

theorem crossRegluedTwistedMap_image :
    crossRegluedTwistedMap '' twistedSourceRect = twistedStripMap '' twistedSourceRect := by
  apply Subset.antisymm
  · rintro y ⟨p, hp, rfl⟩
    rcases le_or_gt p.1 0 with h0 | h0
    · exact ⟨p, hp, (crossRegluedTwistedMap_left h0).symm⟩
    rcases le_or_gt 1 p.1 with h1 | h1
    · exact ⟨p, hp, (crossRegluedTwistedMap_right h1).symm⟩
    exact ⟨(1 - p.1, 1 - p.2),
      ⟨⟨by linarith, by linarith⟩, ⟨by linarith [hp.2.2], by linarith [hp.2.1]⟩⟩,
      (crossRegluedTwistedMap_middle ⟨h0.le, h1.le⟩).symm⟩
  · rintro y ⟨p, hp, rfl⟩
    rcases le_or_gt p.1 0 with h0 | h0
    · exact ⟨p, hp, crossRegluedTwistedMap_left h0⟩
    rcases le_or_gt 1 p.1 with h1 | h1
    · exact ⟨p, hp, crossRegluedTwistedMap_right h1⟩
    refine ⟨(1 - p.1, 1 - p.2),
      ⟨⟨by linarith, by linarith⟩, ⟨by linarith [hp.2.2], by linarith [hp.2.1]⟩⟩, ?_⟩
    rw [crossRegluedTwistedMap_middle ⟨by dsimp; linarith, by dsimp; linarith⟩]
    congr 1
    ext <;> dsimp <;> ring

theorem crossRegluedTwistedCell_image :
    crossRegluedTwistedCell '' crossRegluedTwistedCell.domain =
      twistedStripCell '' twistedStripCell.domain := by
  change (crossRegluedTwistedMap ∘ ⇑seamWitnessPlane.symm) ''
    (⇑seamWitnessPlane '' twistedSourceRect) =
      (twistedStripMap ∘ ⇑seamWitnessPlane.symm) '' (⇑seamWitnessPlane '' twistedSourceRect)
  simp only [image_comp, ContinuousLinearEquiv.symm_image_image]
  exact crossRegluedTwistedMap_image

theorem twistedStripReflection_mapsTo_middle :
    MapsTo (⇑twistedStripReflection)
      (seamWitnessPlane '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
      (seamWitnessPlane '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) := by
  rintro z ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩
  rw [twistedStripReflection_apply]
  exact ⟨(1 - s, 1 - t), ⟨⟨by linarith [hs.2], by linarith [hs.1]⟩,
    ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩, rfl⟩

theorem isPLHomeomorphOn_twistedStripReflection_middle :
    IsPLHomeomorphOn (⇑twistedStripReflection)
      (seamWitnessPlane '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
      (seamWitnessPlane '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) := by
  have hpoly := (isPLBall_seamWitnessPlane_image_Icc_prod (by norm_num : (0 : ℝ) < 1)).isPolyhedron
  apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hpoly
    ((isPiecewiseAffineOn_of_affine twistedStripReflection isOpen_univ).mono_of_isPolyhedron
      hpoly (subset_univ _))
  exact ⟨twistedStripReflection_mapsTo_middle, twistedStripReflection_involutive.injective.injOn,
    fun z hz => ⟨twistedStripReflection z, twistedStripReflection_mapsTo_middle hz,
      twistedStripReflection_involutive z⟩⟩

theorem crossRegluedTwistedCell_core_double {t : ℝ} (ht : t ∈ Icc 0 1) :
    twistedStripMap (0, t) ∈
      doublePointSet (⇑crossRegluedTwistedCell) crossRegluedTwistedCell.domain := by
  refine ⟨seamWitnessPlane (0, t), ⟨(0, t), ⟨by norm_num, ht⟩, rfl⟩,
    seamWitnessPlane (1, 1 - t),
    ⟨(1, 1 - t), ⟨by norm_num, ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩, rfl⟩, ?_, ?_, ?_⟩
  · intro heq
    have := congrArg Prod.fst (seamWitnessPlane.injective heq)
    norm_num at this
  · change crossRegluedTwistedMap (seamWitnessPlane.symm (seamWitnessPlane (0, t))) = _
    rw [ContinuousLinearEquiv.symm_apply_apply, crossRegluedTwistedMap_left (by norm_num)]
  · change crossRegluedTwistedMap (seamWitnessPlane.symm (seamWitnessPlane (1, 1 - t))) = _
    rw [ContinuousLinearEquiv.symm_apply_apply, crossRegluedTwistedMap_right (by norm_num)]
    exact (twistedStripMap_seam t).symm

end DifferentialGeometry.Topology.PiecewiseLinear
