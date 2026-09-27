/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceTwistedCell

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

def halfTurnSlab (a : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {p | (spliceEmbedding.symm p).1.1 ∈ Ioo (a - 1 / 4) (a + 1 / 4)}

theorem isOpen_halfTurnSlab (a : ℝ) : IsOpen (halfTurnSlab a) :=
  isOpen_Ioo.preimage spliceEmbedding.symm.continuous.fst.fst

theorem halfTurnEuclideanProjection_injOn_slab (a : ℝ) :
    InjOn halfTurnEuclideanProjection (halfTurnSlab a) := by
  intro p hp q hq hpq
  exact spliceEmbedding.symm.injective (halfTurnProjection_injOn_slab a hp hq hpq)

noncomputable def halfTurnSlabChart (a : ℝ) :
    OpenPartialHomeomorph halfTurnQuotient (EuclideanSpace ℝ (Fin 3)) :=
  (OpenPartialHomeomorph.ofContinuousOpen
    (halfTurnEuclideanProjection_injOn_slab a).toPartialEquiv
    continuous_halfTurnEuclideanProjection.continuousOn
    isLocalHomeomorph_halfTurnEuclideanProjection.isOpenMap (isOpen_halfTurnSlab a)).symm

theorem halfTurnSlabChart_symm (a : ℝ) :
    ⇑(halfTurnSlabChart a).symm = halfTurnEuclideanProjection := rfl

theorem halfTurnSlabChart_target (a : ℝ) : (halfTurnSlabChart a).target = halfTurnSlab a := rfl

theorem halfTurnSlabChart_source (a : ℝ) :
    (halfTurnSlabChart a).source = halfTurnEuclideanProjection '' halfTurnSlab a := rfl

theorem halfTurnSlabChart_apply {a : ℝ} {p : (ℝ × ℝ) × ℝ}
    (hp : p.1.1 ∈ Ioo (a - 1 / 4) (a + 1 / 4)) :
    halfTurnSlabChart a (halfTurnProjection p) = spliceEmbedding p := by
  have hx : spliceEmbedding p ∈ (halfTurnSlabChart a).target := by
    change (spliceEmbedding.symm (spliceEmbedding p)).1.1 ∈ Ioo (a - 1 / 4) (a + 1 / 4)
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hp
  have h := (halfTurnSlabChart a).right_inv hx
  simpa only [halfTurnSlabChart_symm, halfTurnEuclideanProjection,
    ContinuousLinearEquiv.symm_apply_apply] using h

private theorem chart_comp_halfTurnProjection {U : Set (EuclideanSpace ℝ (Fin 3))}
    (hU : IsOpen U) (q : EuclideanSpace ℝ (Fin 3))
    (hmap : MapsTo halfTurnEuclideanProjection U (halfTurnChart q).source) :
    IsPiecewiseAffineOn (halfTurnChart q ∘ halfTurnEuclideanProjection) U := by
  intro x hx
  have he : halfTurnChart q ∈ (plGroupoid 3).maximalAtlas halfTurnQuotient :=
    (plGroupoid 3).subset_maximalAtlas (mem_range_self q)
  have hpa := ((isPLAt_iff_of_mem_maximalAtlas
    ((plGroupoid 3).chart_mem_maximalAtlas x) (mem_chart_source _ x)
    he (hmap hx)).mp (isPL_halfTurnEuclideanProjection x)).2
  change IsPiecewiseAffineWithinAt (halfTurnChart q ∘ halfTurnEuclideanProjection) univ x at hpa
  simpa only [univ_inter] using hpa.inter_of_mem_nhds (hU.mem_nhds hx)

theorem halfTurnSlabChart_mem_maximalAtlas (a : ℝ) :
    halfTurnSlabChart a ∈ (plGroupoid 3).maximalAtlas halfTurnQuotient := by
  rintro e ⟨q, rfl⟩
  let k := (halfTurnSlabChart a).symm.trans (halfTurnChart q)
  have hk : k ∈ plGroupoid 3 := by
    apply mem_plGroupoid_of_isPiecewiseAffineOn
    exact (chart_comp_halfTurnProjection k.open_source q (fun _ h => h.2)).congr
      fun _ _ => rfl
  exact ⟨hk, mem_plGroupoid_of_isPiecewiseAffineOn (mem_plGroupoid_iff.mp hk).2⟩

theorem halfTurnSlabChart_side {a : ℝ} {p : (ℝ × ℝ) × ℝ}
    (hp : p.1.1 ∈ Ioo (a - 1 / 4) (a + 1 / 4)) :
    halfTurnProjection p ∈ (halfTurnSlabChart a).source ∧
      (halfTurnProjection p ∈ twistedStripSide ↔ p ∈ twistedSideLift) ∧
      (halfTurnProjection p ∈ frontier twistedStripSide ↔ p ∈ frontier twistedSideLift) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [halfTurnSlabChart_source]
    refine ⟨spliceEmbedding p, ?_, ?_⟩
    · change (spliceEmbedding.symm (spliceEmbedding p)).1.1 ∈ Ioo (a - 1 / 4) (a + 1 / 4)
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hp
    · change halfTurnProjection (spliceEmbedding.symm (spliceEmbedding p)) = _
      rw [ContinuousLinearEquiv.symm_apply_apply]
  · change p ∈ halfTurnProjection ⁻¹' twistedStripSide ↔ _
    rw [halfTurnProjection_preimage_twistedStripSide]
  · change p ∈ halfTurnProjection ⁻¹' frontier twistedStripSide ↔ _
    rw [halfTurnProjection_preimage_frontier_twistedStripSide]

end DifferentialGeometry.Topology.PiecewiseLinear
