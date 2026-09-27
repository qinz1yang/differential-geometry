/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import
  DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceProductNeighborhood

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def crossingProductTubeScale (r : ℝ) (hr : r ≠ 0) :
    ((ℝ × ℝ) × ℝ) ≃L[ℝ] ((ℝ × ℝ) × ℝ) :=
  ((LinearEquiv.smulOfNeZero ℝ (ℝ × ℝ) r hr).prodCongr
    (LinearEquiv.refl ℝ ℝ)).toContinuousLinearEquiv

theorem crossingProductTubeScale_apply (r : ℝ) (hr : r ≠ 0) (p : (ℝ × ℝ) × ℝ) :
    crossingProductTubeScale r hr p = ((r * p.1.1, r * p.1.2), p.2) := rfl

noncomputable def crossingProductTubeChart (r : ℝ) (hr : r ≠ 0) :
    ((ℝ × ℝ) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (crossingProductTubeScale r hr).trans spliceEmbedding

theorem crossingProductTubeChart_apply (r : ℝ) (hr : r ≠ 0) (p : (ℝ × ℝ) × ℝ) :
    crossingProductTubeChart r hr p = spliceEmbedding ((r * p.1.1, r * p.1.2), p.2) := rfl

private theorem scale_mem_square {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    {p : ℝ × ℝ} (hp : p ∈ spliceSquare) : (r * p.1, r * p.2) ∈ spliceSquare := by
  rcases mem_spliceSquare.mp hp with ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
  rw [mem_spliceSquare]
  dsimp
  constructor <;> constructor <;> nlinarith

theorem crossingProductTubeScale_mapsTo_cylinder {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    MapsTo (crossingProductTubeScale r hr.ne') spliceCylinder spliceCylinder := by
  intro p hp
  exact ⟨scale_mem_square hr.le hr1 hp.1, hp.2⟩

theorem crossingProductTubeScale_image_core {r : ℝ} (hr : r ≠ 0) :
    crossingProductTubeScale r hr '' spliceCore = spliceCore := by
  have hfix : EqOn (crossingProductTubeScale r hr) id spliceCore := by
    rintro ⟨⟨x, y⟩, t⟩ ⟨hxy, _⟩
    have hxy' : (x, y) = ((0 : ℝ), 0) := hxy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxy'
    simp [crossingProductTubeScale_apply]
  rw [hfix.image_eq, image_id]

private theorem crossingFigure_mem_iff {p : (ℝ × ℝ) × ℝ} :
    p ∈ crossingFigure ↔ p ∈ spliceCylinder ∧ (p.1.1 = 0 ∨ p.1.2 = 0) := by
  simp only [crossingFigure, crossingArcX, crossingArcY, spliceCylinder,
    mem_prod, mem_union, mem_ofPred_eq]
  tauto

theorem crossingProductTubeScale_image_crossingFigure {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    crossingProductTubeScale r hr.ne' '' crossingFigure =
      crossingFigure ∩ crossingProductTubeScale r hr.ne' '' spliceCylinder := by
  apply Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    rcases crossingFigure_mem_iff.mp hp with ⟨hp, hx | hy⟩
    · exact ⟨crossingFigure_mem_iff.mpr
        ⟨crossingProductTubeScale_mapsTo_cylinder hr hr1 hp, Or.inl (by
          change r * p.1.1 = 0
          rw [hx, mul_zero])⟩, p, hp, rfl⟩
    · exact ⟨crossingFigure_mem_iff.mpr
        ⟨crossingProductTubeScale_mapsTo_cylinder hr hr1 hp, Or.inr (by
          change r * p.1.2 = 0
          rw [hy, mul_zero])⟩, p, hp, rfl⟩
  · rintro q ⟨hq, p, hp, rfl⟩
    refine ⟨p, crossingFigure_mem_iff.mpr ⟨hp, ?_⟩, rfl⟩
    rcases (crossingFigure_mem_iff.mp hq).2 with hx | hy
    · exact Or.inl ((mul_eq_zero.mp hx).resolve_left hr.ne')
    · exact Or.inr ((mul_eq_zero.mp hy).resolve_left hr.ne')

theorem crossSeamTubeCore_crossingProductTubeChart {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    CrossSeamTubeCore (crossingProductTubeChart r hr.ne')
      (crossingProductCell '' crossingProductCell.domain)
      (doublePointSet crossingProductCell crossingProductCell.domain)
      (spliceEmbedding '' spliceCore) (spliceEmbedding '' tubeWitnessTube) := by
  have hbase := crossSeamTubeCore_crossingProductCell
  have hcyl : crossingProductTubeChart r hr.ne' '' spliceCylinder ⊆
      spliceEmbedding '' spliceCylinder := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨_, crossingProductTubeScale_mapsTo_cylinder hr hr1 hp, rfl⟩
  refine ⟨hbase.isOpen_tube, (crossingProductTubeChart r hr.ne').continuous.continuousOn,
    (crossingProductTubeChart r hr.ne').injective.injOn,
    hcyl.trans hbase.image_subset_tube, ?_, ?_, hbase.double_inter_tube⟩
  · apply Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩
      exact ⟨_, (crossingProductTubeScale_image_core hr.ne').subset ⟨p, hp, rfl⟩, rfl⟩
    · rintro _ ⟨p, hp, rfl⟩
      obtain ⟨q, hq, hqp⟩ := (crossingProductTubeScale_image_core hr.ne').symm.subset hp
      refine ⟨q, hq, ?_⟩
      change spliceEmbedding (crossingProductTubeScale r hr.ne' q) = spliceEmbedding p
      rw [hqp]
  · apply Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩
      have hfig := ((crossingProductTubeScale_image_crossingFigure hr hr1).subset
        ⟨p, hp, rfl⟩).1
      exact ⟨(hbase.image_crossingFigure.subset ⟨_, hfig, rfl⟩).1,
        p, (crossingFigure_mem_iff.mp hp).1, rfl⟩
    · rintro z ⟨hz, p, hp, rfl⟩
      obtain ⟨q, hq, hqp⟩ := hbase.image_crossingFigure.symm.subset
        ⟨hz, hcyl ⟨p, hp, rfl⟩⟩
      have hfig : crossingProductTubeScale r hr.ne' p ∈ crossingFigure :=
        spliceEmbedding.injective hqp ▸ hq
      obtain ⟨q, hq, hqp⟩ := (crossingProductTubeScale_image_crossingFigure hr hr1).symm.subset
        ⟨hfig, p, hp, rfl⟩
      have heq : q = p := (crossingProductTubeScale r hr.ne').injective hqp
      exact ⟨q, hq, heq ▸ rfl⟩

theorem crossingProductTubeChart_side {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    crossingProductTubeChart r hr.ne' '' spliceCylinder ⊆ crossingProductSide := by
  rintro _ ⟨p, hp, rfl⟩
  exact crossingProductTube_side
    ⟨_, crossingProductTubeScale_mapsTo_cylinder hr hr1 hp, rfl⟩

theorem crossingProductTubeChart_boundary {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    crossingProductTubeChart r hr.ne' '' spliceCylinder ∩ frontier crossingProductSide =
      crossingProductTubeChart r hr.ne' '' spliceEndDisks := by
  apply Subset.antisymm
  · rintro z ⟨⟨p, hp, rfl⟩, hz⟩
    have hends := crossingProductTube_boundary.subset
      ⟨⟨_, crossingProductTubeScale_mapsTo_cylinder hr hr1 hp, rfl⟩, hz⟩
    obtain ⟨q, hq, hqp⟩ := hends
    have heq := congrArg Prod.snd (spliceEmbedding.injective hqp)
    refine ⟨p, ⟨hp.1, ?_⟩, rfl⟩
    exact heq ▸ hq.2
  · rintro _ ⟨p, hp, rfl⟩
    refine ⟨⟨p, spliceEndDisks_subset_spliceCylinder hp, rfl⟩, ?_⟩
    apply (crossingProductTube_boundary.symm.subset ?_).2
    exact ⟨crossingProductTubeScale r hr.ne' p,
      ⟨scale_mem_square hr.le hr1 hp.1, hp.2⟩, rfl⟩

theorem nonempty_plSeamTubeChart_crossingProductTubeChart {r : ℝ} (hr : r ≠ 0) :
    Nonempty (PLSeamTubeChart (EuclideanSpace ℝ (Fin 3))
      (crossingProductTubeChart r hr)) := by
  let e := crossingProductTubeChart r hr
  obtain ⟨K, hfin, hspace⟩ := isHPolytope_spliceCylinder.isPolyhedron.exists_simplicialComplex
  have hbij : BijOn e K.space (e '' spliceCylinder) := by
    rw [hspace]
    exact e.injective.injOn.bijOn_image
  have hpa : IsPiecewiseAffineOn e K.space :=
    (isPiecewiseAffineOn_of_affine e.toLinearMap.toAffineMap isOpen_univ).mono_of_isPolyhedron
      (hspace.symm ▸ isHPolytope_spliceCylinder.isPolyhedron) (subset_univ _)
  have himage : IsPolyhedron (e '' spliceCylinder) := by
    simpa only [hspace] using
      hpa.isPolyhedron_image (hspace.symm ▸ isHPolytope_spliceCylinder.isPolyhedron)
  have hpa' : IsPiecewiseAffineOn e.symm (e '' spliceCylinder) :=
    (isPiecewiseAffineOn_of_affine e.symm.toLinearMap.toAffineMap isOpen_univ).mono_of_isPolyhedron
      himage (subset_univ _)
  refine ⟨⟨⟨K, hfin, e, hbij, e.continuous.continuousOn, ?_, ?_⟩, hspace, rfl⟩⟩
  · intro chart hc
    have he : chart = OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 3)) :=
      chartedSpaceSelf_atlas.mp hc
    subst he
    simp only [OpenPartialHomeomorph.refl_source, preimage_univ, inter_univ]
    exact hpa.congr fun _ _ => rfl
  · intro chart hc
    have he : chart = OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 3)) :=
      chartedSpaceSelf_atlas.mp hc
    subst he
    simp only [OpenPartialHomeomorph.refl_target, OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply, preimage_id_eq, univ_inter]
    refine hpa'.congr fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := hy
    change Function.invFunOn e K.space (e x) = e.symm (e x)
    rw [e.symm_apply_apply]
    exact e.injective (hbij.invOn_invFunOn.2 ⟨x, hx, rfl⟩)

theorem crossingProductCell_core_end_mem_boundary {t : ℝ} (ht : t = 0 ∨ t = 1) :
    spliceEmbedding ((0, 0), t) ∈ Set.range crossingProductCell.boundary := by
  have hx : seamWitnessPlane (3 / 2, t) ∈ frontier crossingProductCell.domain := by
    change seamWitnessPlane (3 / 2, t) ∈ frontier seamWitnessCell.domain
    rw [frontier_seamWitnessCell_domain]
    refine ⟨(3 / 2, t), ?_, rfl⟩
    rw [frontier_seamSourceRect]
    rcases ht with rfl | rfl <;> norm_num [seamSourceRect]
  refine ⟨⟨seamWitnessPlane (3 / 2, t), hx⟩, ?_⟩
  change spliceEmbedding (crossingProductMap (seamWitnessPlane.symm
    (seamWitnessPlane (3 / 2, t)))) = _
  rw [seamWitnessPlane.symm_apply_apply, crossingProductMap_core_first]

private theorem exists_model_radius_end_buffer {B : Set (EuclideanSpace ℝ (Fin 3))}
    {t : ℝ} (ht : t = 0 ∨ t = 1)
    (hB : ∀ z ∈ Set.range crossingProductCell.boundary,
      B ∈ 𝓝[frontier crossingProductSide] z) :
    ∃ δ > 0, ∀ p : (ℝ × ℝ) × ℝ, dist p ((0, 0), t) < δ →
      spliceEmbedding p ∈ frontier crossingProductSide →
      B ∈ 𝓝[frontier crossingProductSide] (spliceEmbedding p) := by
  have hbuf := hB _ (crossingProductCell_core_end_mem_boundary ht)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhdsWithin_iff.mp
    (eventually_mem_nhdsWithin_iff.mpr hbuf)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.continuousAt_iff.mp
    (spliceEmbedding.continuous.continuousAt (x := ((0, 0), t))) ε hε
  exact ⟨δ, hδ, fun p hp hpBd => hεsub ⟨hδsub hp, hpBd⟩⟩

private theorem scale_dist_core_le {r : ℝ} (hr : 0 ≤ r) {p : ℝ × ℝ}
    (hp : p ∈ spliceSquare) (t : ℝ) :
    dist ((r * p.1, r * p.2), t) ((0, 0), t) ≤ r := by
  have hx : |p.1| ≤ 1 := abs_le.mpr (mem_spliceSquare.mp hp).1
  have hy : |p.2| ≤ 1 := abs_le.mpr (mem_spliceSquare.mp hp).2
  simp only [Prod.dist_eq, Real.dist_eq, sub_zero, sub_self, abs_zero,
    abs_mul, abs_of_nonneg hr, max_le_iff]
  exact ⟨⟨by nlinarith, by nlinarith⟩, hr⟩

theorem crossingProductCell_exists_tube_end_buffer {B : Set (EuclideanSpace ℝ (Fin 3))}
    (hB : ∀ z ∈ Set.range crossingProductCell.boundary,
      B ∈ 𝓝[frontier crossingProductSide] z) :
    ∃ (r : ℝ) (hr : 0 < r), r ≤ 1 ∧
      ∀ z ∈ crossingProductTubeChart r hr.ne' '' spliceEndDisks,
        B ∈ 𝓝[frontier crossingProductSide] z := by
  obtain ⟨δ₀, hδ₀, hbuf₀⟩ := exists_model_radius_end_buffer (Or.inl rfl) hB
  obtain ⟨δ₁, hδ₁, hbuf₁⟩ := exists_model_radius_end_buffer (Or.inr rfl) hB
  let r := min (δ₀ / 2) (min (δ₁ / 2) 1)
  have hr : 0 < r := lt_min (half_pos hδ₀) (lt_min (half_pos hδ₁) zero_lt_one)
  have hr₀ : r < δ₀ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ₀)
  have hr₁ : r < δ₁ := lt_of_le_of_lt
    ((min_le_right _ _).trans (min_le_left _ _)) (half_lt_self hδ₁)
  have hrle : r ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r, hr, hrle, ?_⟩
  rintro z ⟨p, hp, rfl⟩
  have hBd : crossingProductTubeChart r hr.ne' p ∈ frontier crossingProductSide :=
    ((crossingProductTubeChart_boundary hr hrle).symm.subset ⟨p, hp, rfl⟩).2
  rcases hp.2 with ht | ht
  · apply hbuf₀ _ ?_ hBd
    change dist ((r * p.1.1, r * p.1.2), p.2) ((0, 0), 0) < δ₀
    rw [ht]
    exact (scale_dist_core_le hr.le hp.1 0).trans_lt hr₀
  · apply hbuf₁ _ ?_ hBd
    change dist ((r * p.1.1, r * p.1.2), p.2) ((0, 0), 1) < δ₁
    rw [show p.2 = 1 from ht]
    exact (scale_dist_core_le hr.le hp.1 1).trans_lt hr₁

end DifferentialGeometry.Topology.PiecewiseLinear
