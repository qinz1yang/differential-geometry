import DifferentialGeometry.Geometry.Hyperbolic.Truncation
import DifferentialGeometry.Topology.Manifold.HalfLine
import DifferentialGeometry.Topology.Manifold.ModelTransport
import DifferentialGeometry.Topology.Manifold.InteriorImage
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.Ends.Cylindrical
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Piecewise

noncomputable section

open Set Filter Function Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation

open GC.Endpoint
open DifferentialGeometry.Topology.Manifold (halfSpaceOneHomeomorph)

variable {H : FiniteVolumeHyperbolicModel} (Tr : HyperbolicTruncation H)

private abbrev SeamDomain := Torus × Ioo (-1 : ℝ) 1

private def positiveHalf (t : ℝ) : EuclideanHalfSpace 1 :=
  halfSpaceOneHomeomorph.symm ⟨max t 0, le_max_right t 0⟩

private theorem continuous_positiveHalf : Continuous positiveHalf :=
  halfSpaceOneHomeomorph.symm.continuous.comp
    ((continuous_id.max continuous_const).subtype_mk (fun t => le_max_right t 0))

private theorem positiveHalf_coordinate (t : ℝ) : (positiveHalf t).val 0 = max t 0 := by
  exact congrArg Subtype.val (halfSpaceOneHomeomorph.apply_symm_apply ⟨max t 0, le_max_right t 0⟩)

private theorem positiveHalf_zero : positiveHalf 0 = halfZero := by
  apply halfSpaceOneHomeomorph.injective
  apply Subtype.ext
  change (positiveHalf 0).val 0 = 0
  rw [positiveHalf_coordinate]
  norm_num

private def seamPositive (i : Fin Tr.count) (q : SeamDomain) : H.Carrier :=
  Tr.cuspMap i (q.1, positiveHalf q.2.val)

private def seamNegative (i : Fin Tr.count) (q : SeamDomain) : H.Carrier :=
  Tr.inclusion (Tr.boundary.collar i (q.1, positiveHalf (-q.2.val)))

private theorem seamNegative_mem_source (i : Fin Tr.count) (q : SeamDomain) :
    (q.1, positiveHalf (-q.2.val)) ∈ (Tr.boundary.collar i).source := by
  rw [Tr.boundary.source_eq]
  change (positiveHalf (-q.2.val)).val 0 < 1
  rw [positiveHalf_coordinate]
  exact max_lt (by linarith [q.2.property.1]) (by norm_num)

private theorem continuous_seamPositive (i : Fin Tr.count) : Continuous (Tr.seamPositive i) :=
  (Tr.cuspEmbedding i).contMDiff.continuous.comp
    (continuous_fst.prodMk
      (continuous_positiveHalf.comp (continuous_subtype_val.comp continuous_snd)))

private theorem continuous_seamNegative (i : Fin Tr.count) : Continuous (Tr.seamNegative i) := by
  apply Tr.inclusion.continuous.comp
  exact (Tr.boundary.collar i).contMDiffOn.continuousOn.comp_continuous
    (continuous_fst.prodMk (continuous_positiveHalf.comp
      (continuous_subtype_val.comp continuous_snd).neg))
    (Tr.seamNegative_mem_source i)

private def seamMap (i : Fin Tr.count) (q : SeamDomain) : H.Carrier :=
  if 0 ≤ q.2.val then Tr.seamPositive i q else Tr.seamNegative i q

private theorem continuous_seamMap (i : Fin Tr.count) : Continuous (Tr.seamMap i) := by
  apply Continuous.if ?_ (Tr.continuous_seamPositive i) (Tr.continuous_seamNegative i)
  intro q hq
  have hh := (continuous_subtype_val.comp continuous_snd).frontier_preimage_subset (Ici (0 : ℝ)) hq
  have ht : q.2.val = 0 := by
    simpa only [mem_preimage, frontier_Ici, mem_singleton_iff, Function.comp_apply] using hh
  change Tr.cuspMap i (q.1, positiveHalf q.2.val) =
    Tr.inclusion (Tr.boundary.collar i (q.1, positiveHalf (-q.2.val)))
  rw [ht, neg_zero, positiveHalf_zero, Tr.cusp_zero]
  rfl

private theorem seamMap_zero (i : Fin Tr.count) (x : Torus) :
    Tr.seamMap i (x, ⟨0, by norm_num, by norm_num⟩) = Tr.cuspMap i (x, halfZero) := by
  simp only [seamMap, le_refl, ite_true, seamPositive, positiveHalf_zero]

private theorem seamPositive_injective (i : Fin Tr.count) {p q : SeamDomain}
    (hp : 0 ≤ p.2.val) (hq : 0 ≤ q.2.val)
    (he : Tr.seamPositive i p = Tr.seamPositive i q) : p = q := by
  have heq := (Tr.cuspEmbedding i).isEmbedding.injective he
  apply Prod.ext
  · exact congrArg (fun z : CuspHalfSpace => z.1) heq
  · apply Subtype.ext
    have h := congrArg (fun z : CuspHalfSpace => z.2.val 0) heq
    simpa only [positiveHalf_coordinate, max_eq_left hp, max_eq_left hq] using h

private theorem seamNegative_injective (i : Fin Tr.count) {p q : SeamDomain}
    (hp : p.2.val < 0) (hq : q.2.val < 0)
    (he : Tr.seamNegative i p = Tr.seamNegative i q) : p = q := by
  have heq := (Tr.boundary.collar i).toOpenPartialHomeomorph.injOn (Tr.seamNegative_mem_source i p)
    (Tr.seamNegative_mem_source i q) (Tr.embedding.isEmbedding.injective he)
  apply Prod.ext
  · exact congrArg (fun z : CuspHalfSpace => z.1) heq
  · apply Subtype.ext
    have h := congrArg (fun z : CuspHalfSpace => z.2.val 0) heq
    simp only [positiveHalf_coordinate, max_eq_left (neg_nonneg.mpr hp.le),
      max_eq_left (neg_nonneg.mpr hq.le)] at h
    linarith

private theorem seamNegative_ne_seamPositive (i : Fin Tr.count) (p q : SeamDomain)
    (hp : p.2.val < 0) : Tr.seamNegative i p ≠ Tr.seamPositive i q := by
  intro he
  have hint : Tr.seamNegative i p ∈ range Tr.inclusion ∩ range (Tr.cuspMap i) :=
    ⟨⟨_, rfl⟩, ⟨(q.1, positiveHalf q.2.val), he.symm⟩⟩
  rw [Tr.intersection i] at hint
  obtain ⟨x, hx⟩ := hint
  change Tr.cuspMap i (x, halfZero) = Tr.seamNegative i p at hx
  rw [Tr.cusp_zero i x] at hx
  have hs : (x, halfZero) ∈ (Tr.boundary.collar i).source := by
    rw [Tr.boundary.source_eq]
    change (0 : ℝ) < 1
    norm_num
  have heq := (Tr.boundary.collar i).toOpenPartialHomeomorph.injOn hs
    (Tr.seamNegative_mem_source i p)
    (Tr.embedding.isEmbedding.injective hx)
  have ht := congrArg (fun z : CuspHalfSpace => z.2.val 0) heq
  change 0 = (positiveHalf (-p.2.val)).val 0 at ht
  rw [positiveHalf_coordinate, max_eq_left (neg_nonneg.mpr hp.le)] at ht
  linarith

private theorem injective_seamMap (i : Fin Tr.count) : Injective (Tr.seamMap i) := by
  intro p q hpq
  by_cases hp : 0 ≤ p.2.val <;> by_cases hq : 0 ≤ q.2.val
  · exact Tr.seamPositive_injective i hp hq (by simpa only [seamMap, hp, hq, ite_true] using hpq)
  · exact False.elim (Tr.seamNegative_ne_seamPositive i q p (lt_of_not_ge hq)
      (by simpa only [seamMap, hp, hq, ite_true, ite_false] using hpq.symm))
  · exact False.elim (Tr.seamNegative_ne_seamPositive i p q (lt_of_not_ge hp)
      (by simpa only [seamMap, hp, hq, ite_true, ite_false] using hpq))
  · exact Tr.seamNegative_injective i (lt_of_not_ge hp) (lt_of_not_ge hq)
      (by simpa only [seamMap, hp, hq, ite_false] using hpq)

private theorem isOpen_range_seamMap (i : Fin Tr.count) : IsOpen (range (Tr.seamMap i)) := by
  let U : TopologicalSpace.Opens ℝ := ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩
  let _ : ChartedSpace ℝ (Ioo (-1 : ℝ) 1) := U.instChartedSpace
  let F := (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × ℝ
  let _ : ChartedSpace F SeamDomain := by
    change ChartedSpace
      (ModelProd (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) ℝ)
      (Torus × Ioo (-1 : ℝ) 1)
    infer_instance
  let L : F ≃L[ℝ] EuclideanSpace ℝ (Fin 3) := ContinuousLinearEquiv.ofFinrankEq (by simp [F])
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 3)) SeamDomain :=
    DifferentialGeometry.Manifold.chartedSpaceTransHomeomorph L.toHomeomorph
  exact (DifferentialGeometry.Topology.isOpenMap_of_continuous_injective
    (E := EuclideanSpace ℝ (Fin 3)) (Tr.continuous_seamMap i) (Tr.injective_seamMap i)).isOpen_range

theorem core_union_cusp_mem_nhds (i : Fin Tr.count) (x : Torus) :
    range Tr.inclusion ∪ range (Tr.cuspMap i) ∈ 𝓝 (Tr.cuspMap i (x, halfZero)) := by
  have hm : Tr.cuspMap i (x, halfZero) ∈ range (Tr.seamMap i) :=
    ⟨(x, ⟨0, by norm_num, by norm_num⟩), Tr.seamMap_zero i x⟩
  apply Filter.mem_of_superset ((Tr.isOpen_range_seamMap i).mem_nhds hm)
  rintro y ⟨q, rfl⟩
  by_cases hq : 0 ≤ q.2.val
  · exact Or.inr ⟨(q.1, positiveHalf q.2.val), by
      simp only [seamMap, hq, ite_true, seamPositive]⟩
  · exact Or.inl ⟨Tr.boundary.collar i (q.1, positiveHalf (-q.2.val)), by
      simp only [seamMap, hq, ite_false, seamNegative]⟩

private theorem half_eq_zero_of_coordinate (t : EuclideanHalfSpace 1) (ht : t.val 0 = 0) :
    t = halfZero := by
  apply halfSpaceOneHomeomorph.injective
  exact Subtype.ext ht

private theorem halfCollar_interior :
    halfCollarModel.interior CuspHalfSpace = {p | 0 < p.2.val 0} := by
  rw [ModelWithCorners.interior_prod]
  ext p
  change torusModel.IsInteriorPoint p.1 ∧ (𝓡∂ 1).IsInteriorPoint p.2 ↔ _
  have hi : torusModel.IsInteriorPoint p.1 := BoundarylessManifold.isInteriorPoint
  simp only [hi, true_and]
  change p.2.val ∈ interior (range (𝓡∂ 1)) ↔ _
  rw [interior_range_modelWithCornersEuclideanHalfSpace]
  rfl

private theorem isOpen_cusp_positive (i : Fin Tr.count) :
    IsOpen (Tr.cuspMap i '' {p | 0 < p.2.val 0}) := by
  rw [← halfCollar_interior]
  exact DifferentialGeometry.Topology.Manifold.isOpen_image_interior_of_isImmersion
    (Tr.cuspEmbedding i).isImmersion (by simp)

private theorem disjoint_core_interior_cusp (i : Fin Tr.count) :
    Disjoint (Tr.inclusion '' (Tr.core.interior : Set Tr.core.Carrier))
      (range (Tr.cuspMap i)) := by
  apply Set.disjoint_left.mpr
  rintro y ⟨x, hx, rfl⟩ hy
  have hm : Tr.inclusion x ∈ range Tr.inclusion ∩ range (Tr.cuspMap i) :=
    ⟨mem_range_self x, hy⟩
  rw [Tr.intersection i] at hm
  obtain ⟨t, ht⟩ := hm
  change Tr.cuspMap i (t, halfZero) = Tr.inclusion x at ht
  rw [Tr.cusp_zero] at ht
  have hxB := Tr.boundary.boundary_zero i t
  change Tr.core.model.IsBoundaryPoint (Tr.boundary.torusMap i t) at hxB
  rw [Tr.embedding.isEmbedding.injective ht] at hxB
  exact Set.disjoint_left.mp Tr.core.model.disjoint_interior_boundary hx hxB

private theorem disjoint_core_cusp_positive (i : Fin Tr.count) :
    Disjoint (range Tr.inclusion) (Tr.cuspMap i '' {p | 0 < p.2.val 0}) := by
  apply Set.disjoint_left.mpr
  rintro y hy ⟨p, hp, rfl⟩
  have hm : Tr.cuspMap i p ∈ range Tr.inclusion ∩ range (Tr.cuspMap i) :=
    ⟨hy, mem_range_self p⟩
  rw [Tr.intersection i] at hm
  obtain ⟨t, ht⟩ := hm
  have heq := (Tr.cuspEmbedding i).isEmbedding.injective ht
  have hz : p.2.val 0 = 0 := by
    rw [← heq]
    rfl
  exact hp.ne' hz

private theorem mem_core_or_cusp_positive (y : H.Carrier) :
    y ∈ range Tr.inclusion ∨ ∃ i, y ∈ Tr.cuspMap i '' {p | 0 < p.2.val 0} := by
  have hy : y ∈ range Tr.inclusion ∪ ⋃ i, range (Tr.cuspMap i) := by
    rw [Tr.exhausts]
    exact mem_univ y
  rcases hy with hy | hy
  · exact Or.inl hy
  · obtain ⟨i, p, rfl⟩ := mem_iUnion.mp hy
    by_cases hp : 0 < p.2.val 0
    · exact Or.inr ⟨i, p, hp, rfl⟩
    · have hp0 : p.2 = halfZero :=
        half_eq_zero_of_coordinate p.2 (le_antisymm (le_of_not_gt hp) p.2.property)
      exact Or.inl ⟨Tr.boundary.torusMap i p.1, by rw [← Tr.cusp_zero, ← hp0]⟩

theorem cuspMap_isClosedEmbedding (i : Fin Tr.count) :
    _root_.Topology.IsClosedEmbedding (Tr.cuspMap i) := by
  refine ⟨(Tr.cuspEmbedding i).isEmbedding, ?_⟩
  apply isOpen_compl_iff.mp
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hzero : IsClosed (range (fun t : Torus => Tr.cuspMap i (t, halfZero))) :=
    (isCompact_range ((Tr.cuspEmbedding i).contMDiff.continuous.comp
      (continuous_id.prodMk continuous_const))).isClosed
  have hyzero : y ∉ range (fun t : Torus => Tr.cuspMap i (t, halfZero)) := by
    rintro ⟨t, rfl⟩
    exact hy (mem_range_self _)
  rcases Tr.mem_core_or_cusp_positive y with hycore | ⟨j, p, hp, rfl⟩
  · obtain ⟨x, rfl⟩ := hycore
    rcases Tr.core.model.isInteriorPoint_or_isBoundaryPoint x with hx | hx
    · have hm : Tr.inclusion x ∈ Tr.inclusion '' (Tr.core.interior : Set Tr.core.Carrier) :=
        ⟨x, hx, rfl⟩
      filter_upwards [Tr.interior_image.mem_nhds hm] with z hz
      exact fun hzi => Set.disjoint_left.mp (Tr.disjoint_core_interior_cusp i) hz hzi
    · change x ∈ Tr.core.model.boundary Tr.core.Carrier at hx
      rw [Tr.boundary_exhausted] at hx
      obtain ⟨j, t, ht⟩ := mem_iUnion.mp hx
      have hyj : Tr.inclusion x = Tr.cuspMap j (t, halfZero) := by
        rw [Tr.cusp_zero, ht]
      have hji : j ≠ i := by
        intro hji
        subst j
        exact hy ⟨(t, halfZero), hyj.symm⟩
      have hn := Tr.core_union_cusp_mem_nhds j t
      rw [← hyj] at hn
      filter_upwards [hn, hzero.isOpen_compl.mem_nhds hyzero] with z hz hzi0
      intro hzi
      rcases hz with hzc | hzj
      · have hm : z ∈ range Tr.inclusion ∩ range (Tr.cuspMap i) := ⟨hzc, hzi⟩
        rw [Tr.intersection i] at hm
        exact hzi0 hm
      · exact Set.disjoint_left.mp (Tr.cusp_disjoint hji) hzj hzi
  · have hji : j ≠ i := by
      intro hji
      subst j
      exact hy (mem_range_self p)
    filter_upwards [(Tr.isOpen_cusp_positive j).mem_nhds ⟨p, hp, rfl⟩] with z hz
    intro hzi
    exact Set.disjoint_left.mp (Tr.cusp_disjoint hji)
      (image_subset_range _ _ hz) hzi

private def cuspCylinderHomeomorph : CuspHalfSpace ≃ₜ Torus × Ici (0 : ℝ) :=
  (Homeomorph.refl Torus).prodCongr halfSpaceOneHomeomorph

private theorem cuspCylinder_image_positive (i : Fin Tr.count) :
    (Tr.cuspMap i ∘ cuspCylinderHomeomorph.symm) '' {p | 0 < p.2.val} =
      Tr.cuspMap i '' {p | 0 < p.2.val 0} := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨cuspCylinderHomeomorph.symm p, ?_, rfl⟩
    have ht := congrArg Subtype.val (halfSpaceOneHomeomorph.apply_symm_apply p.2)
    change (halfSpaceOneHomeomorph.symm p.2).val 0 = p.2.val at ht
    change 0 < (halfSpaceOneHomeomorph.symm p.2).val 0
    rwa [ht]
  · rintro ⟨p, hp, rfl⟩
    exact ⟨cuspCylinderHomeomorph p, hp, congrArg (Tr.cuspMap i)
      (cuspCylinderHomeomorph.symm_apply_apply p)⟩

theorem endCount_eq_count :
    DifferentialGeometry.Geometry.Topology.endCount H.Carrier = (Tr.count : ℕ∞) := by
  let C : Fin Tr.count → Type := fun _ => Torus
  let e : (i : Fin Tr.count) → C i × Ici (0 : ℝ) → H.Carrier :=
    fun i => Tr.cuspMap i ∘ cuspCylinderHomeomorph.symm
  have he (i : Fin Tr.count) : _root_.Topology.IsClosedEmbedding (e i) :=
    (Tr.cuspMap_isClosedEmbedding i).comp cuspCylinderHomeomorph.symm.isClosedEmbedding
  have hopen (i : Fin Tr.count) : IsOpen (e i '' {p | 0 < p.2.val}) := by
    change IsOpen ((Tr.cuspMap i ∘ cuspCylinderHomeomorph.symm) '' {p | 0 < p.2.val})
    rw [Tr.cuspCylinder_image_positive]
    exact Tr.isOpen_cusp_positive i
  have hdisjoint : Pairwise fun i j => Disjoint
      (e i '' {p | 0 < p.2.val}) (e j '' {p | 0 < p.2.val}) := by
    intro i j hij
    change Disjoint ((Tr.cuspMap i ∘ cuspCylinderHomeomorph.symm) '' _)
      ((Tr.cuspMap j ∘ cuspCylinderHomeomorph.symm) '' _)
    rw [Tr.cuspCylinder_image_positive, Tr.cuspCylinder_image_positive]
    exact (Tr.cusp_disjoint hij).mono (image_subset_range _ _) (image_subset_range _ _)
  have hcore : (⋃ i, e i '' {p | 0 < p.2.val})ᶜ = range Tr.inclusion := by
    ext y
    constructor
    · intro hy
      rcases Tr.mem_core_or_cusp_positive y with hyc | ⟨i, hyi⟩
      · exact hyc
      · apply False.elim
        apply hy
        apply mem_iUnion.mpr
        refine ⟨i, ?_⟩
        change y ∈ (Tr.cuspMap i ∘ cuspCylinderHomeomorph.symm) '' _
        rwa [Tr.cuspCylinder_image_positive]
    · intro hy hyt
      obtain ⟨i, hi⟩ := mem_iUnion.mp hyt
      change y ∈ (Tr.cuspMap i ∘ cuspCylinderHomeomorph.symm) '' _ at hi
      rw [Tr.cuspCylinder_image_positive] at hi
      exact Set.disjoint_left.mp (Tr.disjoint_core_cusp_positive i) hy hi
  have hc : IsCompact (⋃ i, e i '' {p | 0 < p.2.val})ᶜ := by
    rw [hcore]
    exact isCompact_range Tr.inclusion.continuous
  simpa only [Nat.card_fin] using
    DifferentialGeometry.Geometry.Topology.endCount_eq_card_of_finite_cylindrical_ends
      C e he hopen hdisjoint hc

end DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation
