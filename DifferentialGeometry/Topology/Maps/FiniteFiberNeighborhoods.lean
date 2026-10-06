import Mathlib.Topology.SeparatedMap
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Separation.Regular

set_option autoImplicit false

open Set Filter Topology

namespace DifferentialGeometry.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A continuous locally injective map with compact domain has finite fibers. -/
theorem finite_fiber_of_isLocallyInjective [CompactSpace X] [T1Space Y]
    {f : X → Y} (hf : Continuous f) (hloc : IsLocallyInjective f) (y : Y) :
    (f ⁻¹' {y}).Finite := by
  apply ((isClosed_singleton.preimage hf).isCompact).finite
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro x hx
  obtain ⟨U, hU, hxU, hinj⟩ := hloc x
  refine ⟨U, hU, ?_⟩
  apply Set.ext
  intro z
  constructor
  · intro hz
    exact Set.mem_singleton_iff.mpr (hinj hz.1 hxU (hz.2.trans hx.symm))
  · rintro rfl
    exact ⟨hxU, hx⟩

/-- Near any target point of a continuous locally injective map with compact
Hausdorff domain, every source point lies in one of finitely many disjoint
embedded source neighborhoods, indexed by the actual fiber. The sheet images
may meet tangentially or coincide; no assertion about their intersections is
made. -/
theorem exists_disjoint_embedded_fiber_neighborhoods [CompactSpace X] [T2Space X]
    [T2Space Y] {f : X → Y} (hf : Continuous f) (hloc : IsLocallyInjective f)
    (y : Y) :
    (f ⁻¹' {y}).Finite ∧
      ∃ (U : (f ⁻¹' {y}) → Set X) (V : Set Y),
        (∀ a, IsOpen (U a) ∧ (a : X) ∈ U a ∧ IsEmbedding ((U a).domRestrict f)) ∧
        Pairwise (fun a b => Disjoint (U a) (U b)) ∧
        IsOpen V ∧ y ∈ V ∧ f ⁻¹' V ⊆ ⋃ a, U a := by
  classical
  have hfin := finite_fiber_of_isLocallyInjective hf hloc y
  obtain ⟨S, hS, hSdisj⟩ := hfin.t2_separation
  have hlocal (a : f ⁻¹' {y}) :
      ∃ U : Set X, IsOpen U ∧ (a : X) ∈ U ∧ U ⊆ S a ∧
        IsEmbedding (U.domRestrict f) := by
    obtain ⟨O, hO, haO, hinj⟩ := hloc a
    obtain ⟨K, hKa, hKclosed, hKsub⟩ :=
      exists_mem_nhds_isClosed_subset (((hS a).2.inter hO).mem_nhds ⟨(hS a).1, haO⟩)
    let : CompactSpace K := isCompact_iff_compactSpace.mp hKclosed.isCompact
    have hKemb : IsEmbedding (K.domRestrict f) :=
      ((hf.comp continuous_subtype_val).isClosedEmbedding
        (Set.injOn_iff_injective.mp (hinj.mono (hKsub.trans inter_subset_right)))).isEmbedding
    refine ⟨interior K, isOpen_interior, mem_interior_iff_mem_nhds.mpr hKa,
      interior_subset.trans (hKsub.trans inter_subset_left), ?_⟩
    simpa only [Set.domRestrict_eq, Function.comp_def] using
      hKemb.comp (IsEmbedding.inclusion (show interior K ⊆ K from interior_subset))
  choose U hUopen haU hUS hUemb using hlocal
  let V : Set Y := (f '' (⋃ a, U a)ᶜ)ᶜ
  refine ⟨hfin, U, V, fun a => ⟨hUopen a, haU a, hUemb a⟩, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact (hSdisj a.property b.property (fun h => hab (Subtype.ext h))).mono (hUS a) (hUS b)
  · exact (hf.isClosedMap _ (isOpen_iUnion hUopen).isClosed_compl).isOpen_compl
  · rintro ⟨x, hx, hxy⟩
    exact hx (Set.mem_iUnion.mpr ⟨⟨x, hxy⟩, haU ⟨x, hxy⟩⟩)
  · intro x hx
    by_contra hxU
    exact hx ⟨x, hxU, rfl⟩

end DifferentialGeometry.Topology
