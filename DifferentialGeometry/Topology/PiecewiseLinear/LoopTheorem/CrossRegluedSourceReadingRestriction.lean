/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceProductTube
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceTubeRestriction

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem scale_mem_bentSheetPos_iff {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {p : (ℝ × ℝ) × ℝ} (hp : p ∈ spliceCylinder) :
    crossingProductTubeScale r hr.ne' p ∈ bentSheetPos ↔ p ∈ bentSheetPos := by
  have hb := mem_spliceSquare.mp hp.1
  have hs := mem_spliceSquare.mp (crossingProductTubeScale_mapsTo_cylinder hr hr1 hp).1
  change r * p.1.1 ∈ Icc (-1 : ℝ) 1 ∧ r * p.1.2 ∈ Icc (-1 : ℝ) 1 at hs
  simp only [bentSheetPos, mem_prod, mem_bentArcPos, crossingProductTubeScale_apply]
  constructor
  · rintro ⟨h | h, ht⟩
    · exact ⟨Or.inl ⟨⟨by nlinarith [h.1.1], hb.1.2⟩,
        (mul_eq_zero.mp h.2).resolve_left hr.ne'⟩, ht⟩
    · exact ⟨Or.inr ⟨(mul_eq_zero.mp h.1).resolve_left hr.ne',
        hb.2.1, by nlinarith [h.2.2]⟩, ht⟩
  · rintro ⟨h | h, ht⟩
    · exact ⟨Or.inl ⟨⟨mul_nonneg hr.le h.1.1, hs.1.2⟩,
        by rw [h.2, mul_zero]⟩, ht⟩
    · exact ⟨Or.inr ⟨by rw [h.1, mul_zero], hs.2.1,
        mul_nonpos_of_nonneg_of_nonpos hr.le h.2.2⟩, ht⟩

private theorem scale_mem_bentSheetNeg_iff {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {p : (ℝ × ℝ) × ℝ} (hp : p ∈ spliceCylinder) :
    crossingProductTubeScale r hr.ne' p ∈ bentSheetNeg ↔ p ∈ bentSheetNeg := by
  have hb := mem_spliceSquare.mp hp.1
  have hs := mem_spliceSquare.mp (crossingProductTubeScale_mapsTo_cylinder hr hr1 hp).1
  change r * p.1.1 ∈ Icc (-1 : ℝ) 1 ∧ r * p.1.2 ∈ Icc (-1 : ℝ) 1 at hs
  simp only [bentSheetNeg, mem_prod, mem_bentArcNeg, crossingProductTubeScale_apply]
  constructor
  · rintro ⟨h | h, ht⟩
    · exact ⟨Or.inl ⟨⟨hb.1.1, by nlinarith [h.1.2]⟩,
        (mul_eq_zero.mp h.2).resolve_left hr.ne'⟩, ht⟩
    · exact ⟨Or.inr ⟨(mul_eq_zero.mp h.1).resolve_left hr.ne',
        by nlinarith [h.2.1], hb.2.2⟩, ht⟩
  · rintro ⟨h | h, ht⟩
    · exact ⟨Or.inl ⟨⟨hs.1.1, mul_nonpos_of_nonneg_of_nonpos hr.le h.1.2⟩,
        by rw [h.2, mul_zero]⟩, ht⟩
    · exact ⟨Or.inr ⟨by rw [h.1, mul_zero], mul_nonneg hr.le h.2.1, hs.2.2⟩, ht⟩

private theorem scale_image_sheet {r : ℝ} (hr : 0 < r) {Q : Set ((ℝ × ℝ) × ℝ)}
    (hQ : Q ⊆ spliceCylinder)
    (hmem : ∀ p ∈ spliceCylinder, crossingProductTubeScale r hr.ne' p ∈ Q ↔ p ∈ Q) :
    crossingProductTubeScale r hr.ne' '' Q =
      Q ∩ crossingProductTubeScale r hr.ne' '' spliceCylinder := by
  apply Subset.antisymm
  · rintro z ⟨p, hp, rfl⟩
    exact ⟨(hmem p (hQ hp)).mpr hp, p, hQ hp, rfl⟩
  · rintro z ⟨hz, p, hp, rfl⟩
    exact ⟨p, (hmem p hp).mp hz, rfl⟩

private theorem restricted_coordinate_homeomorph
    {c : EuclideanSpace ℝ (Fin 2) → (ℝ × ℝ) × ℝ}
    {S : Set (EuclideanSpace ℝ (Fin 2))} {Q : Set ((ℝ × ℝ) × ℝ)}
    (h : IsPLHomeomorphOn c S Q) (hQ : IsPolyhedron Q)
    (e : ((ℝ × ℝ) × ℝ) ≃L[ℝ] ((ℝ × ℝ) × ℝ))
    (heQ : e '' Q = Q ∩ e '' spliceCylinder) :
    IsPLHomeomorphOn (e.symm ∘ c) (S ∩ c ⁻¹' (e '' spliceCylinder)) Q := by
  have hepoly : IsPolyhedron (e '' spliceCylinder) :=
    isHPolytope_spliceCylinder.isPolyhedron.image_affineEquiv e.toAffineEquiv
  have hP := h.isPolyhedron_preimage (hQ.inter hepoly) inter_subset_left
  have hset : S ∩ c ⁻¹' (Q ∩ e '' spliceCylinder) =
      S ∩ c ⁻¹' (e '' spliceCylinder) := by
    ext x
    exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, h.bijOn.mapsTo hx.1, hx.2⟩⟩
  rw [hset] at hP
  apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hP
    ((h.isPiecewiseAffineOn.mono_of_isPolyhedron hP inter_subset_left).affine_comp
      e.symm.toLinearMap.toAffineMap)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨q, hq, heq⟩ := heQ.symm.subset ⟨h.bijOn.mapsTo hx.1, hx.2⟩
    change e.symm (c x) ∈ Q
    rw [← heq, e.symm_apply_apply]
    exact hq
  · intro x hx y hy hxy
    exact h.bijOn.injOn hx.1 hy.1 (e.symm.injective hxy)
  · intro q hq
    have heq := heQ.subset ⟨q, hq, rfl⟩
    obtain ⟨x, hx, hcx⟩ := h.bijOn.surjOn heq.1
    refine ⟨x, ⟨hx, by rw [mem_preimage, hcx]; exact heq.2⟩, ?_⟩
    change e.symm (c x) = q
    rw [hcx, e.symm_apply_apply]

private theorem square_interior_of_not_boundary {p : ℝ × ℝ} (hp : p ∈ spliceSquare)
    (hn : p ∉ spliceSquareBoundary) : p ∈ Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1 := by
  have hb := mem_spliceSquare.mp hp
  have hn' : ¬(p.1 = -1 ∨ p.1 = 1 ∨ p.2 = -1 ∨ p.2 = 1) :=
    fun h => hn (mem_spliceSquareBoundary.mpr ⟨hp, h⟩)
  exact ⟨⟨lt_of_le_of_ne hb.1.1 (Ne.symm (fun h => hn' (Or.inl h))),
      lt_of_le_of_ne hb.1.2 (fun h => hn' (Or.inr (Or.inl h)))⟩,
    lt_of_le_of_ne hb.2.1 (Ne.symm (fun h => hn' (Or.inr (Or.inr (Or.inl h))))),
    lt_of_le_of_ne hb.2.2 (fun h => hn' (Or.inr (Or.inr (Or.inr h))))⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {chart : (ℝ × ℝ) × ℝ → M} {G : SingularTwoCell M}

private theorem coordinate_mem_cylinder (R : PLCrossSeamReading chart G)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ R.tubeSource) :
    (R.coord x).2 ∈ spliceCylinder := by
  rcases hx with hx | hx
  · have h := R.isPLHomeomorphOn_pos.bijOn.mapsTo hx
    exact ⟨bentArcPos_subset_spliceSquare h.1, h.2⟩
  · have h := R.isPLHomeomorphOn_neg.bijOn.mapsTo hx
    exact ⟨bentArcNeg_subset_spliceSquare h.1, h.2⟩

private theorem continuousOn_coordinate (R : PLCrossSeamReading chart G) :
    ContinuousOn (fun x => (R.coord x).2) R.tubeSource :=
  (R.isPLHomeomorphOn_pos.isPiecewiseAffineOn.union_of_isClosed
    R.isPLHomeomorphOn_neg.isPiecewiseAffineOn R.isPolyhedron_sourcePos.isClosed
    R.isPolyhedron_sourceNeg.isClosed).continuousOn

private theorem restricted_coordinate_lateral (R : PLCrossSeamReading chart G)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ R.tubeSource ∩ (fun z => (R.coord z).2) ⁻¹'
      (crossingProductTubeScale r hr.ne' '' spliceCylinder))
    (hxf : x ∈ closure (G.domain \ (R.tubeSource ∩ (fun z => (R.coord z).2) ⁻¹'
      (crossingProductTubeScale r hr.ne' '' spliceCylinder)))) :
    (crossingProductTubeScale r hr.ne').symm (R.coord x).2 ∈
      spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1 := by
  let e := crossingProductTubeScale r hr.ne'
  let c := fun z => (R.coord z).2
  let q := e.symm (c x)
  have hq : q ∈ spliceCylinder := by
    obtain ⟨p, hp, hep⟩ := hx.2
    change e p = c x at hep
    simpa only [q, ← hep, ContinuousLinearEquiv.symm_apply_apply] using hp
  by_contra hlat
  have hqi := square_interior_of_not_boundary hq.1 (fun h => hlat ⟨h, hq.2⟩)
  have heq : c x = e q := (e.apply_symm_apply (c x)).symm
  have hci : (c x).1 ∈ Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1 := by
    rw [heq]
    change (-1 < r * q.1.1 ∧ r * q.1.1 < 1) ∧ (-1 < r * q.1.2 ∧ r * q.1.2 < 1)
    constructor
    · constructor <;>
        nlinarith [mul_lt_mul_of_pos_left hqi.1.1 hr, mul_lt_mul_of_pos_left hqi.1.2 hr]
    · constructor <;>
        nlinarith [mul_lt_mul_of_pos_left hqi.2.1 hr, mul_lt_mul_of_pos_left hqi.2.2 hr]
  have hnface : x ∉ R.face := by
    intro hf
    have hb := (mem_spliceSquareBoundary.mp (R.overlap_lateral x ⟨hx.1, hf⟩).1).2
    rcases hb with hb | hb | hb | hb <;>
      simp only [c] at hci <;> rcases hci with ⟨⟨h1, h2⟩, h3, h4⟩ <;> linarith
  have hsource : R.tubeSource ∈ 𝓝[G.domain] x := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (R.isPolyhedron_face.isClosed.isOpen_compl.mem_nhds hnface)]
      with z hz hzf
    exact ((R.tubeSource_union_face.symm ▸ hz) : z ∈ R.tubeSource ∪ R.face).resolve_right hzf
  have hcont : ContinuousWithinAt (e.symm ∘ c) G.domain x :=
    (e.symm.continuous.continuousAt.comp_continuousWithinAt
      (continuousOn_coordinate R x hx.1)).mono_left (nhdsWithin_le_of_mem hsource)
  have hopen : IsOpen {p : (ℝ × ℝ) × ℝ | p.1 ∈ Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1} :=
    (isOpen_Ioo.prod isOpen_Ioo).preimage continuous_fst
  have hpre := hcont.preimage_mem_nhdsWithin (hopen.mem_nhds hqi)
  have hnew : R.tubeSource ∩ c ⁻¹' (e '' spliceCylinder) ∈ 𝓝[G.domain] x := by
    filter_upwards [hsource, hpre] with z hz hzi
    refine ⟨hz, e.symm (c z), ⟨?_, (coordinate_mem_cylinder R hz).2⟩,
      e.apply_symm_apply (c z)⟩
    exact mem_spliceSquare.mpr ⟨⟨hzi.1.1.le, hzi.1.2.le⟩, hzi.2.1.le, hzi.2.2.le⟩
  obtain ⟨O, hO, hxO, hOP⟩ := mem_nhdsWithin.mp hnew
  obtain ⟨y, hyO, hy⟩ := mem_closure_iff.mp hxf O hO hxO
  exact hy.2 (hOP ⟨hyO, hy.1⟩)

theorem PLCrossSeamReading.nonempty_scale (R : PLCrossSeamReading chart G)
    (hchart : InjOn chart spliceCylinder) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    Nonempty (PLCrossSeamReading (chart ∘ crossingProductTubeScale r hr.ne') G) := by
  let e := crossingProductTubeScale r hr.ne'
  let c := fun z => (R.coord z).2
  let Sp := R.sourcePos ∩ c ⁻¹' (e '' spliceCylinder)
  let Sn := R.sourceNeg ∩ c ⁻¹' (e '' spliceCylinder)
  have hs : Sp ∪ Sn = R.tubeSource ∩ c ⁻¹' (e '' spliceCylinder) := by
    ext x
    simp only [Sp, Sn, PLCrossSeamReading.tubeSource, mem_union, mem_inter_iff]
    tauto
  have hpos : IsPLHomeomorphOn (e.symm ∘ c) Sp bentSheetPos :=
    restricted_coordinate_homeomorph R.isPLHomeomorphOn_pos
      isPLBall_bentSheetPos.isPolyhedron e
      (scale_image_sheet hr (fun _ h => ⟨bentArcPos_subset_spliceSquare h.1, h.2⟩)
        (fun _ h => scale_mem_bentSheetPos_iff hr hr1 h))
  have hneg : IsPLHomeomorphOn (e.symm ∘ c) Sn bentSheetNeg :=
    restricted_coordinate_homeomorph R.isPLHomeomorphOn_neg
      isPLBall_bentSheetNeg.isPolyhedron e
      (scale_image_sheet hr (fun _ h => ⟨bentArcNeg_subset_spliceSquare h.1, h.2⟩)
        (fun _ h => scale_mem_bentSheetNeg_iff hr hr1 h))
  have hSp : IsPolyhedron Sp := by
    rw [← hpos.symm.image_eq]
    exact isPLBall_bentSheetPos.isPolyhedron.image_of_isPiecewiseAffineOn
      hpos.symm.isPiecewiseAffineOn hpos.symm.bijOn.injOn
  have hSn : IsPolyhedron Sn := by
    rw [← hneg.symm.image_eq]
    exact isPLBall_bentSheetNeg.isPolyhedron.image_of_isPiecewiseAffineOn
      hneg.symm.isPiecewiseAffineOn hneg.symm.bijOn.injOn
  have hsub : Sp ∪ Sn ⊆ G.domain := by
    rw [hs]
    exact inter_subset_left.trans R.source_subset_domain
  have hsource : Sp ∪ Sn = G.domain ∩ ⇑G ⁻¹' ((chart ∘ e) '' spliceCylinder) := by
    rw [hs]
    apply Subset.antisymm
    · rintro x ⟨hx, p, hp, hep⟩
      refine ⟨R.source_subset_domain hx, p, hp, ?_⟩
      change chart (e p) = G x
      exact (congrArg chart hep).trans (R.reglued_eq hx).symm
    · rintro x ⟨hx, p, hp, hpx⟩
      have hep := crossingProductTubeScale_mapsTo_cylinder hr hr1 hp
      have hxold : x ∈ R.tubeSource := by
        rw [R.tubeSource_eq]
        exact ⟨hx, e p, hep, hpx⟩
      refine ⟨hxold, p, hp, ?_⟩
      exact hchart hep (coordinate_mem_cylinder R hxold) (hpx.trans (R.reglued_eq hxold))
  have hcover : Sp ∪ Sn ∪ closure (G.domain \ (Sp ∪ Sn)) = G.domain := by
    apply Subset.antisymm
    · exact union_subset hsub
        (closure_minimal sdiff_subset G.isPLBall_domain.isPolyhedron.isClosed)
    · intro x hx
      by_cases hp : x ∈ Sp ∪ Sn
      · exact Or.inl hp
      · exact Or.inr (subset_closure ⟨hx, hp⟩)
  refine ⟨{
    coord := fun x => ((R.coord x).1, e.symm (c x))
    sourcePos := Sp
    sourceNeg := Sn
    face := closure (G.domain \ (Sp ∪ Sn))
    isPLHomeomorphOn_pos := hpos
    isPLHomeomorphOn_neg := hneg
    coord_fst_pos := fun x hx => R.coord_fst_pos x hx.1
    coord_fst_neg := fun x hx => R.coord_fst_neg x hx.1
    source_eq := hsource
    isPolyhedron_face := G.isPLBall_domain.isPolyhedron.closure_sdiff (hSp.union hSn)
    union_eq := hcover
    reglued_eq := ?_
    overlap_lateral := ?_
    boundary_iff_end := ?_ }⟩
  · intro x hx
    change G x = chart (e (e.symm (c x)))
    rw [e.apply_symm_apply]
    exact R.reglued_eq ((hs.subset hx).1)
  · intro x hx
    apply restricted_coordinate_lateral R hr hr1 (hs.subset hx.1)
    simpa only [hs] using hx.2
  · intro x hx
    exact R.boundary_iff_end x (hs.subset hx).1

end DifferentialGeometry.Topology.PiecewiseLinear
