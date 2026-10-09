/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceTwistedAtlas

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem isPLBall_twistedSourceRect : IsPLBall 2 twistedSourceRect :=
  isPLBall_two_prod (isPLBall_Icc (by norm_num)) (isPLBall_Icc (by norm_num))

private noncomputable def twistedStripAffine : (ℝ × ℝ) →ᵃ[ℝ] ((ℝ × ℝ) × ℝ) :=
  ((LinearMap.fst ℝ ℝ ℝ).toAffineMap.prod
    ((LinearMap.fst ℝ ℝ ℝ).toAffineMap - AffineMap.const ℝ _ (1 / 2))).prod
      (LinearMap.snd ℝ ℝ ℝ).toAffineMap

theorem isPL_twistedStripMap : IsPL 2 3 (twistedStripMap ∘ ⇑seamWitnessPlane.symm) := by
  let A := spliceEmbedding.toAffineEquiv.toAffineMap.comp
    (twistedStripAffine.comp seamWitnessPlane.symm.toAffineEquiv.toAffineMap)
  have hpa := isPiecewiseAffineOn_of_affine A isOpen_univ
  have hpl : IsPL 2 3 A := fun x =>
    ⟨hpa.continuousOn x (mem_univ x), hpa x (mem_univ x)⟩
  have heq : halfTurnEuclideanProjection ∘ ⇑A =
      twistedStripMap ∘ ⇑seamWitnessPlane.symm := by
    funext x
    change halfTurnProjection (spliceEmbedding.symm
      (spliceEmbedding (twistedStripAffine (seamWitnessPlane.symm x)))) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
    rfl
  rw [← heq]
  exact isPL_halfTurnEuclideanProjection.comp hpl

noncomputable def twistedStripCell : SingularTwoCell halfTurnQuotient where
  domain := ⇑seamWitnessPlane '' twistedSourceRect
  isPLBall_domain := isPLBall_twistedSourceRect.of_isPLHomeomorphOn
    (isPLHomeomorphOn_seamWitnessPlane isPLBall_twistedSourceRect.isPolyhedron)
  toFun := twistedStripMap ∘ ⇑seamWitnessPlane.symm
  isPLOn := by
    have hdom := isPolyhedron_image_seamWitnessPlane isPLBall_twistedSourceRect.isPolyhedron
    exact fun x _ => IsPLWithinAt.mono_of_isPolyhedron
      (isPL_twistedStripMap x) hdom (subset_univ _)

theorem twistedStripCell_fiber_le_two (y : halfTurnQuotient) :
    (twistedStripCell.domain ∩ ⇑twistedStripCell ⁻¹' {y}).encard ≤ 2 := by
  have hmaps : MapsTo (⇑seamWitnessPlane.symm)
      (twistedStripCell.domain ∩ ⇑twistedStripCell ⁻¹' {y})
      (twistedSourceRect ∩ twistedStripMap ⁻¹' {y}) := by
    rintro p ⟨hp, hpy⟩
    exact ⟨mem_image_seamWitnessPlane.mp hp, hpy⟩
  exact (Set.encard_le_encard_of_injOn hmaps seamWitnessPlane.symm.injective.injOn).trans
    (twistedStripMap_fiber_le_two y)

theorem twistedStripCell_locallyInjective :
    ∀ x ∈ twistedStripCell.domain,
      ∃ V ∈ 𝓝[twistedStripCell.domain] x, InjOn (⇑twistedStripCell) V := by
  intro x _
  let s := (seamWitnessPlane.symm x).1
  let V := (Prod.fst ∘ ⇑seamWitnessPlane.symm) ⁻¹' Ioo (s - 1 / 4) (s + 1 / 4)
  have hV : IsOpen V := isOpen_Ioo.preimage
    (continuous_fst.comp seamWitnessPlane.symm.continuous)
  have hxV : x ∈ V := by change s - 1 / 4 < s ∧ s < s + 1 / 4; constructor <;> linarith
  refine ⟨V, mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hxV), ?_⟩
  intro p hp q hq heq
  apply seamWitnessPlane.symm.injective
  exact twistedStripMap_injOn_slab s hp hq heq

theorem twistedStripMap_doublePointSet :
    doublePointSet twistedStripMap twistedSourceRect =
      (fun t : ℝ => twistedStripMap (0, t)) '' Icc (0 : ℝ) 1 := by
  apply Subset.antisymm
  · rintro y ⟨p, hp, q, hq, hpq, hpy, hqy⟩
    rcases (twistedStripMap_eq_iff hp.1 hq.1).mp (hpy.trans hqy.symm) with
      heq | ⟨hp0, -, -⟩ | ⟨-, hq0, -⟩
    · exact (hpq heq).elim
    · refine ⟨p.2, hp.2, ?_⟩
      have hp' : p = (0, p.2) := Prod.ext hp0 rfl
      exact (congrArg twistedStripMap hp').symm.trans hpy
    · refine ⟨q.2, hq.2, ?_⟩
      have hq' : q = (0, q.2) := Prod.ext hq0 rfl
      exact (congrArg twistedStripMap hq').symm.trans hqy
  · rintro y ⟨t, ht, rfl⟩
    refine ⟨(0, t), ⟨by norm_num, ht⟩, (1, 1 - t),
      ⟨by norm_num, ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩, ?_, rfl,
      (twistedStripMap_seam t).symm⟩
    intro heq
    exact (by norm_num : (0 : ℝ) ≠ 1) (congrArg Prod.fst heq)

theorem twistedStripCell_doublePointSet :
    doublePointSet (⇑twistedStripCell) twistedStripCell.domain =
      (fun t : ℝ => twistedStripMap (0, t)) '' Icc (0 : ℝ) 1 := by
  change doublePointSet (twistedStripMap ∘ ⇑seamWitnessPlane.symm)
    (⇑seamWitnessPlane '' twistedSourceRect) = _
  rw [doublePointSet_comp_of_bijOn (bijOn_seamWitnessPlaneSymm twistedSourceRect),
    twistedStripMap_doublePointSet]

theorem twistedStripCell_not_injOn : ¬ InjOn (⇑twistedStripCell) twistedStripCell.domain := by
  intro hinj
  apply twistedStripMap_not_injOn
  intro p hp q hq heq
  apply seamWitnessPlane.injective
  apply hinj (mem_image_of_mem _ hp) (mem_image_of_mem _ hq)
  simpa only [twistedStripCell, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
    using heq

theorem twistedStripCell_reversing_endpoints :
    twistedStripCell (seamWitnessPlane (0, 0)) = twistedStripCell (seamWitnessPlane (1, 1)) ∧
    twistedStripCell (seamWitnessPlane (0, 1)) = twistedStripCell (seamWitnessPlane (1, 0)) ∧
    twistedStripCell (seamWitnessPlane (0, 0)) ≠ twistedStripCell (seamWitnessPlane (0, 1)) := by
  simp only [twistedStripCell, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  refine ⟨by simpa using twistedStripMap_seam 0, by simpa using twistedStripMap_seam 1, ?_⟩
  intro heq
  have h := (twistedStripMap_eq_iff (by norm_num) (by norm_num)).mp heq
  norm_num at h

def twistedSideLift : Set ((ℝ × ℝ) × ℝ) :=
  (univ ×ˢ Icc (-3 / 4 : ℝ) (3 / 4)) ×ˢ Icc (0 : ℝ) 1

def twistedStripSide : Set halfTurnQuotient := halfTurnProjection '' twistedSideLift

private theorem halfTurnTranslation_mapsTo_side (n : ℤ) :
    MapsTo (halfTurnTranslation n) twistedSideLift twistedSideLift := by
  intro p hp
  have hs : (-1 : ℝ) ^ n = 1 ∨ (-1 : ℝ) ^ n = -1 := by
    rw [neg_one_zpow_eq_ite]
    split_ifs <;> simp
  rcases hs with hs | hs
  · simpa only [twistedSideLift, halfTurnTranslation, hs, one_mul, sub_add_cancel,
      mem_prod, mem_univ, true_and] using And.intro hp.1.2 hp.2
  · change ⟨⟨p.1.1 + n, (-1 : ℝ) ^ n * p.1.2⟩,
      (-1 : ℝ) ^ n * (p.2 - 1 / 2) + 1 / 2⟩ ∈ twistedSideLift
    refine ⟨⟨mem_univ _, ?_⟩, ?_⟩
    · change -3 / 4 ≤ (-1 : ℝ) ^ n * p.1.2 ∧ (-1 : ℝ) ^ n * p.1.2 ≤ 3 / 4
      rw [hs]
      constructor <;> linarith [hp.1.2.1, hp.1.2.2]
    · change 0 ≤ (-1 : ℝ) ^ n * (p.2 - 1 / 2) + 1 / 2 ∧
        (-1 : ℝ) ^ n * (p.2 - 1 / 2) + 1 / 2 ≤ 1
      rw [hs]
      constructor <;> linarith [hp.2.1, hp.2.2]

theorem halfTurnProjection_preimage_twistedStripSide :
    halfTurnProjection ⁻¹' twistedStripSide = twistedSideLift := by
  apply Subset.antisymm
  · rintro p ⟨q, hq, hpq⟩
    obtain ⟨n, rfl⟩ := halfTurnProjection_eq_iff.mp hpq
    exact halfTurnTranslation_mapsTo_side n hq
  · intro p hp
    exact mem_image_of_mem _ hp

theorem isClosed_twistedSideLift : IsClosed twistedSideLift :=
  (isClosed_univ.prod isClosed_Icc).prod isClosed_Icc

theorem isClosed_twistedStripSide : IsClosed twistedStripSide := by
  apply (isQuotientMap_quotient_mk' (s := halfTurnSetoid)).isClosed_preimage.mp
  change IsClosed (halfTurnProjection ⁻¹' twistedStripSide)
  rw [halfTurnProjection_preimage_twistedStripSide]
  exact isClosed_twistedSideLift

theorem halfTurnProjection_preimage_frontier_twistedStripSide :
    halfTurnProjection ⁻¹' frontier twistedStripSide = frontier twistedSideLift := by
  rw [isOpenMap_halfTurnProjection.preimage_frontier_eq_frontier_preimage
    continuous_halfTurnProjection, halfTurnProjection_preimage_twistedStripSide]

theorem frontier_twistedSourceRect :
    frontier twistedSourceRect =
      twistedSourceRect \ Ioo (-1 / 4 : ℝ) (5 / 4) ×ˢ Ioo (0 : ℝ) 1 := by
  rw [isPLBall_twistedSourceRect.isPolyhedron.isClosed.frontier_eq,
    twistedSourceRect, interior_prod_eq, interior_Icc, interior_Icc]

theorem twistedStripMap_mem_frontier_side_iff {p : ℝ × ℝ} (hp : p ∈ twistedSourceRect) :
    twistedStripMap p ∈ frontier twistedStripSide ↔ p ∈ frontier twistedSourceRect := by
  change ((p.1, p.1 - 1 / 2), p.2) ∈
    halfTurnProjection ⁻¹' frontier twistedStripSide ↔ _
  rw [halfTurnProjection_preimage_frontier_twistedStripSide,
    isClosed_twistedSideLift.frontier_eq, frontier_twistedSourceRect]
  have hmap : ((p.1, p.1 - 1 / 2), p.2) ∈ twistedSideLift :=
    ⟨⟨mem_univ _, ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩⟩, hp.2⟩
  rw [mem_sdiff, mem_sdiff, and_iff_right hmap, and_iff_right hp]
  apply not_congr
  simp only [twistedSideLift, interior_prod_eq, interior_univ, interior_Icc,
    mem_prod, mem_univ, true_and, mem_Ioo]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, ht⟩
    exact ⟨⟨by linarith, by linarith⟩, ht⟩
  · rintro ⟨⟨hlo, hhi⟩, ht⟩
    exact ⟨⟨by linarith, by linarith⟩, ht⟩

theorem twistedStripCell_mapsTo_side :
    MapsTo (⇑twistedStripCell) twistedStripCell.domain twistedStripSide := by
  intro x hx
  have hp := mem_image_seamWitnessPlane.mp hx
  refine ⟨(((seamWitnessPlane.symm x).1, (seamWitnessPlane.symm x).1 - 1 / 2),
    (seamWitnessPlane.symm x).2), ?_, rfl⟩
  exact ⟨⟨mem_univ _, ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩⟩, hp.2⟩

theorem frontier_twistedStripCell_domain :
    frontier twistedStripCell.domain = ⇑seamWitnessPlane '' frontier twistedSourceRect :=
  (seamWitnessPlane.toHomeomorph.image_frontier twistedSourceRect).symm

theorem twistedStripCell_preimage_frontier_side :
    twistedStripCell.domain ∩ ⇑twistedStripCell ⁻¹' frontier twistedStripSide =
      frontier twistedStripCell.domain := by
  rw [frontier_twistedStripCell_domain]
  ext x
  constructor
  · rintro ⟨hx, hxb⟩
    exact mem_image_seamWitnessPlane.mpr
      ((twistedStripMap_mem_frontier_side_iff (mem_image_seamWitnessPlane.mp hx)).mp hxb)
  · intro hx
    have hx' := mem_image_seamWitnessPlane.mp hx
    have hxD := isPLBall_twistedSourceRect.isPolyhedron.isClosed.frontier_subset hx'
    exact ⟨mem_image_seamWitnessPlane.mpr hxD,
      (twistedStripMap_mem_frontier_side_iff hxD).mpr hx'⟩

theorem twistedStripCell_image_inter_frontier_side :
    ⇑twistedStripCell '' twistedStripCell.domain ∩ frontier twistedStripSide =
      Set.range twistedStripCell.boundary := by
  rw [← image_inter_preimage, twistedStripCell_preimage_frontier_side]
  ext y
  exact ⟨fun ⟨x, hx, hxy⟩ => ⟨⟨x, hx⟩, hxy⟩,
    fun ⟨x, hxy⟩ => ⟨x, x.property, hxy⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
