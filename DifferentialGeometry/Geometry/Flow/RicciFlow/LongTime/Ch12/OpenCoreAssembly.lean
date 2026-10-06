import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OpenCoreCompression
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import DifferentialGeometry.Topology.Manifold.ImmersionInterior

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

variable {H : FiniteVolumeHyperbolicModel.{u}} {T : HyperbolicTruncation H}
  (E : ∀ i : Fin T.count, CuspEndChart_CX1 T i)

theorem endChart_unique_CX1 {i j : Fin T.count} {x : H.Carrier}
    (hi : x ∈ (E i).chart.target) (hj : x ∈ (E j).chart.target) : i = j := by
  by_contra hij
  exact Set.disjoint_left.mp (endNeighborhood_disjoint_CX1 T hij)
    ((E i).end_subset hi) ((E j).end_subset hj)

/-- Simultaneously compress the finitely many disjoint ends. The empty family
uses the identity, so the same construction includes closed models. -/
def globalCompression_CX1 (x : H.Carrier) : H.Carrier :=
  open Classical in
  if h : ∃ i, x ∈ (E i).chart.target then endCompression_CX1 (E (Classical.choose h)) x else x

theorem globalCompression_on_CX1 {i : Fin T.count} {x : H.Carrier}
    (hx : x ∈ (E i).chart.target) :
    globalCompression_CX1 E x = endCompression_CX1 (E i) x := by
  classical
  have h : ∃ j, x ∈ (E j).chart.target := ⟨i, hx⟩
  rw [globalCompression_CX1, dite_eq_left h]
  rw [endChart_unique_CX1 E (Classical.choose_spec h) hx]

theorem globalCompression_off_CX1 {x : H.Carrier}
    (hx : ∀ i, x ∉ (E i).chart.target) : globalCompression_CX1 E x = x := by
  classical
  exact dite_eq_right (by rintro ⟨i, hi⟩; exact hx i hi)

theorem globalCompression_fixed_CX1 {x : H.Carrier}
    (hx : x ∉ ⋃ i, (E i).support) : globalCompression_CX1 E x = x := by
  by_cases h : ∃ i, x ∈ (E i).chart.target
  · obtain ⟨i, hi⟩ := h
    rw [globalCompression_on_CX1 E hi]
    exact endCompression_fixed_CX1 (E i) (fun h => hx (mem_iUnion.mpr ⟨i, h⟩))
  · exact globalCompression_off_CX1 E (fun i hi => h ⟨i, hi⟩)

theorem globalCompression_local_CX1 :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (globalCompression_CX1 E) := by
  intro x
  by_cases hx : ∃ i, x ∈ (E i).chart.target
  · obtain ⟨i, hi⟩ := hx
    apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq _ (endCompression_local_CX1 (E i) x)
    filter_upwards [(E i).chart.open_target.mem_nhds hi] with y hy
    exact globalCompression_on_CX1 E hy
  · have hK : IsClosed (⋃ i, (E i).support) := isClosed_iUnion_of_finite (fun i => (E i).support_closed)
    have hxK : x ∉ ⋃ i, (E i).support := by
      intro h
      obtain ⟨i, hi⟩ := mem_iUnion.mp h
      exact hx ⟨i, (E i).support_subset hi⟩
    apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq _
      ((Diffeomorph.refl (𝓡 3) H.Carrier ∞).isLocalDiffeomorph x)
    filter_upwards [hK.isOpen_compl.mem_nhds hxK] with y hy
    exact globalCompression_fixed_CX1 E hy

theorem globalCompression_mem_target_CX1 (i : Fin T.count) (x : H.Carrier) :
    globalCompression_CX1 E x ∈ (E i).chart.target ↔ x ∈ (E i).chart.target := by
  by_cases hx : ∃ j, x ∈ (E j).chart.target
  · obtain ⟨j, hj⟩ := hx
    rw [globalCompression_on_CX1 E hj]
    constructor
    · intro hi
      have hij := endChart_unique_CX1 E hi (endCompression_target_CX1 (E j) hj)
      exact hij.symm ▸ hj
    · intro hi
      have hij := endChart_unique_CX1 E hi hj
      subst j
      exact endCompression_target_CX1 (E i) hi
  · rw [globalCompression_off_CX1 E (fun j hj => hx ⟨j, hj⟩)]

theorem globalCompression_injective_CX1 : Injective (globalCompression_CX1 E) := by
  intro x y hxy
  by_cases hx : ∃ i, x ∈ (E i).chart.target
  · obtain ⟨i, hi⟩ := hx
    have hy : y ∈ (E i).chart.target :=
      (globalCompression_mem_target_CX1 E i y).mp
        (hxy ▸ (globalCompression_mem_target_CX1 E i x).mpr hi)
    rw [globalCompression_on_CX1 E hi, globalCompression_on_CX1 E hy] at hxy
    exact endCompression_injective_CX1 (E i) hi hy hxy
  · have hy : ∀ i, y ∉ (E i).chart.target := by
      intro i hi
      exact hx ⟨i, (globalCompression_mem_target_CX1 E i x).mp
        (hxy.symm ▸ (globalCompression_mem_target_CX1 E i y).mpr hi)⟩
    rwa [globalCompression_off_CX1 E (fun i hi => hx ⟨i, hi⟩),
      globalCompression_off_CX1 E hy] at hxy

theorem globalCompression_core_CX1 (x : H.Carrier) :
    globalCompression_CX1 E x ∈ T.inclusion '' (T.core.interior : Set T.core.Carrier) := by
  by_cases hx : ∃ i, x ∈ (E i).chart.target
  · obtain ⟨i, hi⟩ := hx
    rw [globalCompression_on_CX1 E hi]
    exact endCompression_core_CX1 (E i) hi
  · rw [globalCompression_off_CX1 E (fun i hi => hx ⟨i, hi⟩), mem_openCoreImage_iff_CX1]
    intro i hi
    exact hx ⟨i, cusp_range_subset_chart_CX1 (E i) hi⟩

theorem globalCompression_surjective_core_CX1 {y : H.Carrier}
    (hy : y ∈ T.inclusion '' (T.core.interior : Set T.core.Carrier)) :
    ∃ x, globalCompression_CX1 E x = y := by
  by_cases hyt : ∃ i, y ∈ (E i).chart.target
  · obtain ⟨i, hi⟩ := hyt
    obtain ⟨x, hx, hxy⟩ := endCompression_surjective_core_CX1 (E i) hi hy
    exact ⟨x, (globalCompression_on_CX1 E hx).trans hxy⟩
  · exact ⟨y, globalCompression_off_CX1 E (fun i hi => hyt ⟨i, hi⟩)⟩

/-- The open subset of the model given by the actual core inclusion. -/
def openCoreImage_CX1 (T : HyperbolicTruncation H) : TopologicalSpace.Opens H.Carrier :=
  ⟨T.inclusion '' (T.core.interior : Set T.core.Carrier), T.interior_image⟩

def compressionDiffeo_CX1 : Diffeomorph (𝓡 3) (𝓡 3) H.Carrier (openCoreImage_CX1 T) ∞ := by
  let f : H.Carrier → openCoreImage_CX1 T := fun x => ⟨globalCompression_CX1 E x,
    globalCompression_core_CX1 E x⟩
  have hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f := fun x =>
    DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
      (globalCompression_core_CX1 E) (globalCompression_local_CX1 E x)
  exact hf.diffeomorphOfBijective ⟨fun _ _ h => globalCompression_injective_CX1 E
    (congrArg Subtype.val h), fun y => by
      obtain ⟨x, hx⟩ := globalCompression_surjective_core_CX1 E y.property
      exact ⟨x, Subtype.ext hx⟩⟩

/-- On the open core, the given inclusion is a diffeomorphism onto its image. -/
def coreInclusionDiffeo_CX1 (T : HyperbolicTruncation H) :
    Diffeomorph T.core.model (𝓡 3) T.core.interior (openCoreImage_CX1 T) ∞ := by
  let f : T.core.interior → H.Carrier := fun x => T.inclusion x.val
  have hfl : IsLocalDiffeomorph T.core.model (𝓡 3) ∞ f := by
    intro x
    have hi := isLocalDiffeomorphAt_of_isInteriorPoint_of_isImmersion
      T.embedding.isImmersion x.property (by rfl)
    exact (DifferentialGeometry.isLocalDiffeomorph_subtype_val T.core.interior x).comp
      (𝓡 3) H.Carrier hi
  have himage (x : T.core.interior) : f x ∈ openCoreImage_CX1 T := ⟨x.val, x.property, rfl⟩
  have hf : IsLocalDiffeomorph T.core.model (𝓡 3) ∞
      (fun x => (⟨f x, himage x⟩ : openCoreImage_CX1 T)) := fun x =>
    DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict himage (hfl x)
  exact hf.diffeomorphOfBijective ⟨fun x y h =>
    Subtype.ext (T.embedding.isEmbedding.injective (congrArg Subtype.val h)), fun y => by
      obtain ⟨x, hx, heq⟩ := y.property
      exact ⟨⟨x, hx⟩, Subtype.ext heq⟩⟩

/-- HG16: opening the actual truncated core by a smooth stretch in each cusp.
The map is the given inclusion outside the inward end collars. -/
def openCoreDiffeo_CX1 (T : HyperbolicTruncation H) :
    Diffeomorph T.core.model (𝓡 3) T.core.interior H.Carrier ∞ :=
  (coreInclusionDiffeo_CX1 T).trans (compressionDiffeo_CX1 (cuspEndChart_CX1 T)).symm

/-- Away from the inward cusp collars the opening is the original inclusion. -/
theorem openCoreDiffeo_eq_inclusion_CX1 (T : HyperbolicTruncation H)
    (x : T.core.interior)
    (hx : ∀ i, T.inclusion x.val ∉ (cuspEndChart_CX1 T i).chart.target) :
    openCoreDiffeo_CX1 T x = T.inclusion x.val := by
  let C := compressionDiffeo_CX1 (cuspEndChart_CX1 T)
  apply C.injective
  change C (C.symm (coreInclusionDiffeo_CX1 T x)) = C (T.inclusion x.val)
  rw [C.apply_symm_apply]
  apply Subtype.ext
  exact (globalCompression_off_CX1 (cuspEndChart_CX1 T) hx).symm

/-- In the closed case there is no stretching. -/
theorem openCoreDiffeo_eq_inclusion_of_count_zero_CX1 (T : HyperbolicTruncation H)
    (hT : T.count = 0) (x : T.core.interior) :
    openCoreDiffeo_CX1 T x = T.inclusion x.val := by
  apply openCoreDiffeo_eq_inclusion_CX1 T x
  intro i
  exact (Nat.not_lt_zero i.val (hT ▸ i.isLt)).elim

end GC.LongTime.Ch12
