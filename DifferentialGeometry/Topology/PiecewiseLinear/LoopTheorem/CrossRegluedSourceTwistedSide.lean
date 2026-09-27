/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceTwistedChart
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceProductSide

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private noncomputable def sideCoordinate (a : ℝ) : ((ℝ × ℝ) × ℝ) ≃ₜ ((ℝ × ℝ) × ℝ) where
  toFun p := ((p.1.1 - a, 16 / 3 * p.1.2 + 1), p.2)
  invFun p := ((p.1.1 + a, 3 / 16 * (p.1.2 - 1)), p.2)
  left_inv p := by ext <;> dsimp <;> ring
  right_inv p := by ext <;> dsimp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private noncomputable def sideAffine (a : ℝ) : ((ℝ × ℝ) × ℝ) →ᵃ[ℝ] ((ℝ × ℝ) × ℝ) :=
  let x := ((LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ)).toAffineMap
  let y := ((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ)).toAffineMap
  let z := (LinearMap.snd ℝ (ℝ × ℝ) ℝ).toAffineMap
  ((x - AffineMap.const ℝ _ a).prod
    ((16 / 3 : ℝ) • y + AffineMap.const ℝ _ 1)).prod z

private noncomputable def placedSideCoordinate (a : ℝ) :
    EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3) :=
  (spliceEmbedding.toHomeomorph.symm.trans (sideCoordinate a)).trans spliceEmbedding.toHomeomorph

private theorem placedSideCoordinate_mem_groupoid (a : ℝ) :
    (placedSideCoordinate a).toOpenPartialHomeomorph ∈ plGroupoid 3 := by
  let A := spliceEmbedding.toLinearMap.toAffineMap.comp
    ((sideAffine a).comp spliceEmbedding.symm.toLinearMap.toAffineMap)
  apply mem_plGroupoid_of_isPiecewiseAffineOn
  exact (isPiecewiseAffineOn_of_affine A isOpen_univ).congr fun _ _ => rfl

private theorem trans_mem_atlas {e : OpenPartialHomeomorph halfTurnQuotient
    (EuclideanSpace ℝ (Fin 3))} {k : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3))
      (EuclideanSpace ℝ (Fin 3))}
    (he : e ∈ (plGroupoid 3).maximalAtlas halfTurnQuotient) (hk : k ∈ plGroupoid 3) :
    e.trans k ∈ (plGroupoid 3).maximalAtlas halfTurnQuotient := by
  intro e' he'
  obtain ⟨h₁, h₂⟩ := he e' he'
  constructor
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc]
    exact (plGroupoid 3).trans ((plGroupoid 3).symm hk) h₁
  · rw [← OpenPartialHomeomorph.trans_assoc]
    exact (plGroupoid 3).trans h₂ hk

private theorem sideCoordinate_mem {a : ℝ} {p : (ℝ × ℝ) × ℝ}
    (hp : p.1.1 ∈ Ioo (a - 1 / 4) (a + 1 / 4)) :
    p ∈ twistedSideLift ↔ sideCoordinate a p ∈ crossingProductBox := by
  change ((p.1.1 ∈ univ ∧ -3 / 4 ≤ p.1.2 ∧ p.1.2 ≤ 3 / 4) ∧
    0 ≤ p.2 ∧ p.2 ≤ 1) ↔
      (((-3 ≤ p.1.1 - a ∧ p.1.1 - a ≤ 2) ∧
        -3 ≤ 16 / 3 * p.1.2 + 1 ∧ 16 / 3 * p.1.2 + 1 ≤ 5) ∧ 0 ≤ p.2 ∧ p.2 ≤ 1)
  constructor
  · rintro ⟨⟨_, hy₁, hy₂⟩, ht⟩
    exact ⟨⟨⟨by linarith [hp.1], by linarith [hp.2]⟩,
      by linarith, by linarith⟩, ht⟩
  · rintro ⟨⟨_, hy₁, hy₂⟩, ht⟩
    exact ⟨⟨mem_univ _, by linarith, by linarith⟩, ht⟩

private theorem sideCoordinate_interior {a : ℝ} {p : (ℝ × ℝ) × ℝ}
    (hp : p.1.1 ∈ Ioo (a - 1 / 4) (a + 1 / 4)) :
    p ∈ interior twistedSideLift ↔ sideCoordinate a p ∈ interior crossingProductBox := by
  simp only [twistedSideLift, crossingProductBox, interior_prod_eq, interior_univ, interior_Icc]
  change ((p.1.1 ∈ univ ∧ -3 / 4 < p.1.2 ∧ p.1.2 < 3 / 4) ∧
    0 < p.2 ∧ p.2 < 1) ↔
      (((-3 < p.1.1 - a ∧ p.1.1 - a < 2) ∧
        -3 < 16 / 3 * p.1.2 + 1 ∧ 16 / 3 * p.1.2 + 1 < 5) ∧ 0 < p.2 ∧ p.2 < 1)
  constructor
  · rintro ⟨⟨_, hy₁, hy₂⟩, ht⟩
    exact ⟨⟨⟨by linarith [hp.1], by linarith [hp.2]⟩,
      by linarith, by linarith⟩, ht⟩
  · rintro ⟨⟨_, hy₁, hy₂⟩, ht⟩
    exact ⟨⟨mem_univ _, by linarith, by linarith⟩, ht⟩

private theorem side_chart_pair (a : ℝ) {q : halfTurnQuotient}
    (hq : q ∈ (halfTurnSlabChart a).source) :
    (q ∈ twistedStripSide ↔
      placedSideCoordinate a (halfTurnSlabChart a q) ∈ crossingProductSide) ∧
    (q ∈ frontier twistedStripSide ↔
      placedSideCoordinate a (halfTurnSlabChart a q) ∈ frontier crossingProductSide) := by
  let p := spliceEmbedding.symm (halfTurnSlabChart a q)
  have hp : p.1.1 ∈ Ioo (a - 1 / 4) (a + 1 / 4) := (halfTurnSlabChart a).map_source hq
  have hqeq : halfTurnProjection p = q := (halfTurnSlabChart a).left_inv hq
  have hside : q ∈ twistedStripSide ↔ p ∈ twistedSideLift := by
    rw [← hqeq]
    change p ∈ halfTurnProjection ⁻¹' twistedStripSide ↔ _
    rw [halfTurnProjection_preimage_twistedStripSide]
  have hfront : q ∈ frontier twistedStripSide ↔ p ∈ frontier twistedSideLift := by
    rw [← hqeq]
    change p ∈ halfTurnProjection ⁻¹' frontier twistedStripSide ↔ _
    rw [halfTurnProjection_preimage_frontier_twistedStripSide]
  constructor
  · rw [hside]
    change p ∈ twistedSideLift ↔ spliceEmbedding (sideCoordinate a p) ∈
      spliceEmbedding '' crossingProductBox
    rw [spliceEmbedding.injective.mem_set_image]
    exact sideCoordinate_mem hp
  · rw [hfront]
    have hf : frontier crossingProductSide = spliceEmbedding '' frontier crossingProductBox :=
      (spliceEmbedding.toHomeomorph.image_frontier _).symm
    rw [hf]
    change p ∈ frontier twistedSideLift ↔ spliceEmbedding (sideCoordinate a p) ∈
      spliceEmbedding '' frontier crossingProductBox
    rw [spliceEmbedding.injective.mem_set_image,
      isClosed_twistedSideLift.frontier_eq,
      isHPolytope_crossingProductBox.isPolyhedron.isClosed.frontier_eq,
      mem_sdiff, mem_sdiff, sideCoordinate_mem hp, sideCoordinate_interior hp]

theorem isPLHalfSpacePairAt_twistedStripSide (z : halfTurnQuotient) :
    IsPLHalfSpacePairAt twistedStripSide (frontier twistedStripSide) z := by
  obtain ⟨p, rfl⟩ := surjective_halfTurnProjection z
  let a := p.1.1
  let e₀ := halfTurnSlabChart a
  let k := e₀.trans (placedSideCoordinate a).toOpenPartialHomeomorph
  have hk := trans_mem_atlas (halfTurnSlabChart_mem_maximalAtlas a)
    (placedSideCoordinate_mem_groupoid a)
  have hz₀ : halfTurnProjection p ∈ e₀.source :=
    (halfTurnSlabChart_side (a := a) (p := p) ⟨by dsimp [a]; linarith, by dsimp [a]; linarith⟩).1
  have hzk : halfTurnProjection p ∈ k.source := ⟨hz₀, mem_univ _⟩
  obtain ⟨e, ℓ, he, hℓ, hz, hW, hH⟩ := isPLHalfSpacePairAt_crossingProductSide
    (k (halfTurnProjection p))
  have heG : e ∈ plGroupoid 3 := by
    have h := (he (OpenPartialHomeomorph.refl _) (by simp)).2
    simpa only [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_trans] using h
  refine ⟨k.trans e, ℓ, trans_mem_atlas hk heG, hℓ, ⟨hzk, hz⟩, ?_, ?_⟩
  · intro q hq
    exact (side_chart_pair a hq.1.1).1.trans (hW (k q) hq.2)
  · intro q hq
    exact (side_chart_pair a hq.1.1).2.trans (hH (k q) hq.2)

theorem isPLBoundarySide_twistedStripCell :
    IsPLBoundarySide twistedStripCell twistedStripSide (frontier twistedStripSide) := by
  refine ⟨image_subset_iff.mpr twistedStripCell_mapsTo_side,
    isClosed_twistedStripSide, isClosed_frontier, ?_,
    fun z _ => isPLHalfSpacePairAt_twistedStripSide z⟩
  rintro y ⟨x, ⟨hx, hnot⟩, rfl⟩
  have hside := twistedStripCell_mapsTo_side hx
  by_contra hint
  apply hnot
  rw [← twistedStripCell_preimage_frontier_side]
  exact ⟨hx, subset_closure hside, hint⟩

end DifferentialGeometry.Topology.PiecewiseLinear
