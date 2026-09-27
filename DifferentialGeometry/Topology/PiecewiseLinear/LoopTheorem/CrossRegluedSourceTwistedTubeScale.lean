/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceTubeRestriction
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceProductTube
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceTwistedBranch
import
  DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceTwistedNeighborhood

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def twistedScaledTubeChart (r : ℝ) (hr : r ≠ 0) :
    ((ℝ × ℝ) × ℝ) → halfTurnQuotient :=
  twistedTubeChart ∘ crossingProductTubeScale r hr

theorem crossSeamTubeCore_twistedScaledTubeChart {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    CrossSeamTubeCore (twistedScaledTubeChart r hr.ne')
      (⇑twistedStripCell '' twistedStripCell.domain)
      (doublePointSet (⇑twistedStripCell) twistedStripCell.domain)
      (doublePointSet (⇑twistedStripCell) twistedStripCell.domain)
      (halfTurnSlabChart 0).source :=
  crossSeamTubeCore_twistedStripCell.precomp
    (crossingProductTubeScale r hr.ne').continuous.continuousOn
    (crossingProductTubeScale r hr.ne').injective.injOn
    (crossingProductTubeScale_mapsTo_cylinder hr hr1)
    (crossingProductTubeScale_image_core hr.ne')
    (crossingProductTubeScale_image_crossingFigure hr hr1)

theorem nonempty_plSeamTubeChart_twistedScaledTubeChart {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) :
    Nonempty (PLSeamTubeChart halfTurnQuotient (twistedScaledTubeChart r hr.ne')) := by
  obtain ⟨C⟩ := nonempty_plSeamTubeChart_twistedTubeChart
  apply C.nonempty_precomp _ (crossingProductTubeScale_mapsTo_cylinder hr hr1)
  let e := crossingProductTubeScale r hr.ne'
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn
    isHPolytope_spliceCylinder.isPolyhedron
    ((isPiecewiseAffineOn_of_affine e.toLinearMap.toAffineMap isOpen_univ).mono_of_isPolyhedron
      isHPolytope_spliceCylinder.isPolyhedron (subset_univ _)) e.injective.injOn.bijOn_image

theorem twistedScaledTubeChart_side {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    twistedScaledTubeChart r hr.ne' '' spliceCylinder ⊆ twistedStripSide := by
  rintro _ ⟨p, hp, rfl⟩
  exact twistedTubeChart_side
    ⟨_, crossingProductTubeScale_mapsTo_cylinder hr hr1 hp, rfl⟩

theorem twistedScaledTubeChart_boundary {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    twistedScaledTubeChart r hr.ne' '' spliceCylinder ∩ frontier twistedStripSide =
      twistedScaledTubeChart r hr.ne' '' spliceEndDisks := by
  apply Subset.antisymm
  · rintro z ⟨⟨p, hp, rfl⟩, hz⟩
    have hpc := crossingProductTubeScale_mapsTo_cylinder hr hr1 hp
    obtain ⟨q, hq, hqp⟩ := twistedTubeChart_boundary.subset ⟨⟨_, hpc, rfl⟩, hz⟩
    have heq := twistedTubeChart_injOn (spliceEndDisks_subset_spliceCylinder hq) hpc hqp
    refine ⟨p, ⟨hp.1, ?_⟩, rfl⟩
    have ht := congrArg (fun z : (ℝ × ℝ) × ℝ => z.2) heq
    change q.2 = p.2 at ht
    exact ht ▸ hq.2
  · rintro _ ⟨p, hp, rfl⟩
    have hpc := crossingProductTubeScale_mapsTo_cylinder hr hr1
      (spliceEndDisks_subset_spliceCylinder hp)
    exact ⟨⟨p, spliceEndDisks_subset_spliceCylinder hp, rfl⟩,
      (twistedTubeChart_boundary.symm.subset ⟨_, ⟨hpc.1, hp.2⟩, rfl⟩).2⟩

theorem twistedStripCell_core_end_mem_boundary {t : ℝ} (ht : t = 0 ∨ t = 1) :
    twistedStripMap (0, t) ∈ Set.range twistedStripCell.boundary := by
  have htI : t ∈ Icc (0 : ℝ) 1 := by rcases ht with rfl | rfl <;> norm_num
  rw [← twistedStripCell_image_inter_frontier_side]
  refine ⟨?_, (twistedStripMap_core_mem_frontier_iff htI).mpr ht⟩
  refine ⟨seamWitnessPlane (0, t), mem_image_of_mem _ ⟨by norm_num, htI⟩, ?_⟩
  change twistedStripMap (seamWitnessPlane.symm (seamWitnessPlane (0, t))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]

private theorem exists_model_radius_end_buffer {B : Set halfTurnQuotient}
    {t : ℝ} (ht : t = 0 ∨ t = 1)
    (hB : ∀ z ∈ Set.range twistedStripCell.boundary,
      B ∈ 𝓝[frontier twistedStripSide] z) :
    ∃ δ > 0, ∀ p : (ℝ × ℝ) × ℝ, dist p ((0, 0), t) < δ →
      twistedTubeChart p ∈ frontier twistedStripSide →
      B ∈ 𝓝[frontier twistedStripSide] (twistedTubeChart p) := by
  have hbuf := hB _ (twistedStripCell_core_end_mem_boundary ht)
  obtain ⟨U, hU, hxU, hUB⟩ := mem_nhdsWithin.mp (eventually_mem_nhdsWithin_iff.mpr hbuf)
  have hxU' : twistedTubeChart ((0, 0), t) ∈ U := by
    rw [twistedTubeChart_core]
    exact hxU
  have hpre := continuous_twistedTubeChart.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU')
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  exact ⟨δ, hδ, fun p hp hpBd => hUB ⟨hball hp, hpBd⟩⟩

private theorem scale_dist_core_le {r : ℝ} (hr : 0 ≤ r) {p : ℝ × ℝ}
    (hp : p ∈ spliceSquare) (t : ℝ) :
    dist ((r * p.1, r * p.2), t) ((0, 0), t) ≤ r := by
  have hx : |p.1| ≤ 1 := abs_le.mpr (mem_spliceSquare.mp hp).1
  have hy : |p.2| ≤ 1 := abs_le.mpr (mem_spliceSquare.mp hp).2
  simp only [Prod.dist_eq, Real.dist_eq, sub_zero, sub_self, abs_zero,
    abs_mul, abs_of_nonneg hr, max_le_iff]
  exact ⟨⟨by nlinarith, by nlinarith⟩, hr⟩

theorem twistedStripCell_exists_tube_end_buffer_lt {B : Set halfTurnQuotient}
    (hB : ∀ z ∈ Set.range twistedStripCell.boundary,
      B ∈ 𝓝[frontier twistedStripSide] z) {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℝ) (hr : 0 < r), r ≤ 1 ∧ r < ε ∧
      ∀ z ∈ twistedScaledTubeChart r hr.ne' '' spliceEndDisks,
        B ∈ 𝓝[frontier twistedStripSide] z := by
  obtain ⟨δ₀, hδ₀, hbuf₀⟩ := exists_model_radius_end_buffer (Or.inl rfl) hB
  obtain ⟨δ₁, hδ₁, hbuf₁⟩ := exists_model_radius_end_buffer (Or.inr rfl) hB
  let r := min (δ₀ / 2) (min (δ₁ / 2) (min 1 (ε / 2)))
  have hr : 0 < r :=
    lt_min (half_pos hδ₀) (lt_min (half_pos hδ₁) (lt_min zero_lt_one (half_pos hε)))
  have hr₀ : r < δ₀ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ₀)
  have hr₁ : r < δ₁ := lt_of_le_of_lt
    ((min_le_right _ _).trans (min_le_left _ _)) (half_lt_self hδ₁)
  have hrrest : r ≤ min 1 (ε / 2) := (min_le_right _ _).trans (min_le_right _ _)
  have hrle : r ≤ 1 := hrrest.trans (min_le_left _ _)
  have hrε : r < ε := (hrrest.trans (min_le_right _ _)).trans_lt (half_lt_self hε)
  refine ⟨r, hr, hrle, hrε, ?_⟩
  rintro z ⟨p, hp, rfl⟩
  have hBd := ((twistedScaledTubeChart_boundary hr hrle).symm.subset ⟨p, hp, rfl⟩).2
  rcases hp.2 with ht | ht
  · apply hbuf₀ _ ?_ hBd
    change dist ((r * p.1.1, r * p.1.2), p.2) ((0, 0), 0) < δ₀
    rw [ht]
    exact (scale_dist_core_le hr.le hp.1 0).trans_lt hr₀
  · apply hbuf₁ _ ?_ hBd
    change dist ((r * p.1.1, r * p.1.2), p.2) ((0, 0), 1) < δ₁
    rw [show p.2 = 1 from ht]
    exact (scale_dist_core_le hr.le hp.1 1).trans_lt hr₁

theorem twistedStripCell_exists_tube_end_buffer {B : Set halfTurnQuotient}
    (hB : ∀ z ∈ Set.range twistedStripCell.boundary,
      B ∈ 𝓝[frontier twistedStripSide] z) :
    ∃ (r : ℝ) (hr : 0 < r), r ≤ 1 ∧
      ∀ z ∈ twistedScaledTubeChart r hr.ne' '' spliceEndDisks,
        B ∈ 𝓝[frontier twistedStripSide] z := by
  obtain ⟨r, hr, hr1, -, hbuf⟩ :=
    twistedStripCell_exists_tube_end_buffer_lt hB (by norm_num : (0 : ℝ) < 2)
  exact ⟨r, hr, hr1, hbuf⟩

theorem twistedStripCell_exists_buffered_branchTube {B : Set halfTurnQuotient}
    (hD : NormalSingularCellData twistedStripCell (frontier twistedStripSide) B)
    (hB : ∀ z ∈ Set.range twistedStripCell.boundary,
      B ∈ 𝓝[frontier twistedStripSide] z) :
    ∃ (c : hD.singularSet.Branch) (r : ℝ) (hr : 0 < r)
      (T : CrossSeamTubeData hD c (halfTurnSlabChart 0).source),
      hD.singularSet.complexity = 1 ∧ hD.singularSet.IsBoundaryBranch c ∧
      hD.singularSet.branchCarrier c =
        doublePointSet (⇑twistedStripCell) twistedStripCell.domain ∧
      r ≤ 1 ∧ T.chart = twistedScaledTubeChart r hr.ne' ∧
      Nonempty (PLSeamTubeChart halfTurnQuotient T.chart) ∧
      T.chart '' spliceCylinder ⊆ twistedStripSide ∧
      T.chart '' spliceCylinder ∩ frontier twistedStripSide = T.chart '' spliceEndDisks ∧
      ∀ z ∈ T.chart '' spliceEndDisks, B ∈ 𝓝[frontier twistedStripSide] z := by
  obtain ⟨e, he, hb⟩ := twistedStripCell_exists_branch_equiv hD.singularSet
  obtain ⟨r, hr, hr1, hbuf⟩ := twistedStripCell_exists_tube_end_buffer hB
  let T : CrossSeamTubeData hD (e ()) (halfTurnSlabChart 0).source := {
    chart := twistedScaledTubeChart r hr.ne'
    isTube := by rw [he]; exact crossSeamTubeCore_twistedScaledTubeChart hr hr1 }
  exact ⟨e (), r, hr, T, twistedStripCell_complexity_eq_one hD.singularSet, hb, he,
    hr1, rfl, nonempty_plSeamTubeChart_twistedScaledTubeChart hr hr1,
    twistedScaledTubeChart_side hr hr1, twistedScaledTubeChart_boundary hr hr1, hbuf⟩

end DifferentialGeometry.Topology.PiecewiseLinear
