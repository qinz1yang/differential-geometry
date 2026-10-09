import DifferentialGeometry.Topology.Maps.FiniteFiberNeighborhoods
import DifferentialGeometry.Topology.Maps.CollisionPairs

set_option autoImplicit false

open Set Filter Topology

namespace DifferentialGeometry.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Distinct points of the supplied map with the same value and the same
image-neighborhood filter. Other collisions are not included. -/
def coincidentGermPairs (f : X → Y) : Set (X × X) :=
  {p | p.1 ≠ p.2 ∧ f p.1 = f p.2 ∧
    Filter.map f (𝓝 p.1) = Filter.map f (𝓝 p.2)}

private theorem map_nhds_eq_image_nhdsWithin
    {f : X → Y} {U : Set X} (hU : IsOpen U)
    (hemb : IsEmbedding (U.domRestrict f)) {x : X} (hx : x ∈ U) :
    Filter.map f (𝓝 x) = 𝓝[f '' U] (f x) := by
  let z : U := ⟨x, hx⟩
  have hval : Filter.map (Subtype.val : U → X) (𝓝 z) = 𝓝 x :=
    hU.isOpenEmbedding_subtypeVal.map_nhds_eq z
  have he := hemb.map_nhds_eq z
  rw [Set.range_domRestrict] at he
  calc
    Filter.map f (𝓝 x) = Filter.map (U.domRestrict f) (𝓝 z) := by
      simpa only [Filter.map_map, Set.domRestrict_eq] using
        (congrArg (Filter.map f) hval).symm
    _ = 𝓝[f '' U] (f x) := he

/-- The first projection of the actual coincident-germ relation is open.
The images of two embedded source neighborhoods agree on a target
neighborhood, so nearby points still have a distinct coincident germ.
No closedness or global collision classification is assumed here. -/
theorem isOpen_fst_image_coincidentGermPairs
    [CompactSpace X] [T2Space X] [T2Space Y]
    {f : X → Y} (hf : Continuous f) (hloc : IsLocallyInjective f) :
    IsOpen (Prod.fst '' coincidentGermPairs f) := by
  classical
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨⟨a, b⟩, hab, rfl⟩
  obtain ⟨_, U, _, hU, hdisj, _, _, _⟩ :=
    exists_disjoint_embedded_fiber_neighborhoods hf hloc (f a)
  let a' : f ⁻¹' {f a} := ⟨a, rfl⟩
  let b' : f ⁻¹' {f a} := ⟨b, hab.2.1.symm⟩
  have hab' : a' ≠ b' := fun h => hab.1 (congrArg Subtype.val h)
  have hmapA : Filter.map f (𝓝 a) = 𝓝[f '' U a'] (f a) :=
    map_nhds_eq_image_nhdsWithin (hU a').1 (hU a').2.2 (hU a').2.1
  have hmapB : Filter.map f (𝓝 b) = 𝓝[f '' U b'] (f b) :=
    map_nhds_eq_image_nhdsWithin (hU b').1 (hU b').2.2 (hU b').2.1
  have hrelative : 𝓝[f '' U a'] (f a) = 𝓝[f '' U b'] (f a) := by
    have hh := hmapA.symm.trans (hab.2.2.trans hmapB)
    rwa [← hab.2.1] at hh
  have hsets : f '' U a' =ᶠ[𝓝 (f a)] f '' U b' :=
    nhdsWithin_eq_iff_eventuallyEqSet.mp hrelative
  obtain ⟨W, hWsub, hWopen, haW⟩ :=
    mem_nhds_iff.mp (eventuallyEqSet_iff.mp hsets)
  apply Filter.mem_of_superset
    (inter_mem ((hU a').1.mem_nhds (hU a').2.1)
      ((hWopen.preimage hf).mem_nhds haW))
  rintro z ⟨hzU, hzW⟩
  have hzB : f z ∈ f '' U b' := (hWsub hzW).mp ⟨z, hzU, rfl⟩
  obtain ⟨w, hwU, hfw⟩ := hzB
  have hzw : z ≠ w := by
    intro h
    subst w
    exact Set.disjoint_left.mp (hdisj hab') hzU hwU
  refine ⟨(z, w), ⟨hzw, hfw.symm, ?_⟩, rfl⟩
  rw [map_nhds_eq_image_nhdsWithin (hU a').1 (hU a').2.2 hzU,
    map_nhds_eq_image_nhdsWithin (hU b').1 (hU b').2.2 hwU, hfw]
  apply nhdsWithin_eq_iff_eventuallyEqSet.mpr
  apply eventuallyEqSet_iff.mpr
  exact Filter.mem_of_superset (hWopen.mem_nhds hzW) hWsub

/-- If the coincident-germ subset is closed inside the actual compact
off-diagonal collision relation, a singleton fiber on a connected source
excludes every distinct coincident germ. The required closedness is a
separate analytic input; the conclusion does not exclude other collisions. -/
theorem coincidentGermPairs_eq_empty_of_isClosed
    [CompactSpace X] [T2Space X] [PreconnectedSpace X] [T2Space Y]
    {f : X → Y} (hf : Continuous f) (hloc : IsLocallyInjective f)
    (hclosed : IsClosed {p : orderedCollisionPairs f |
      Filter.map f (𝓝 p.1.1) = Filter.map f (𝓝 p.1.2)})
    (hsingle : ∃ x₀ : X, ∀ x : X, f x = f x₀ → x = x₀) :
    coincidentGermPairs f = ∅ := by
  classical
  let C := orderedCollisionPairs f
  let E : Set C := {p | Filter.map f (𝓝 p.1.1) = Filter.map f (𝓝 p.1.2)}
  let : CompactSpace C :=
    isCompact_iff_compactSpace.mp (isCompact_orderedCollisionPairs f hf hloc)
  have himage : (Subtype.val : C → X × X) '' E = coincidentGermPairs f := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.property.1, q.property.2, hq⟩
    · intro hp
      exact ⟨⟨p, hp.1, hp.2.1⟩, hp.2.2, rfl⟩
  have hcompact : IsCompact (coincidentGermPairs f) := by
    rw [← himage]
    exact hclosed.isCompact.image continuous_subtype_val
  let S : Set X := Prod.fst '' coincidentGermPairs f
  have hS : IsClopen S :=
    ⟨(hcompact.image continuous_fst).isClosed,
      isOpen_fst_image_coincidentGermPairs hf hloc⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hSuniv : S = Set.univ := hS.eq_univ ⟨p.1, p, hp, rfl⟩
  obtain ⟨x₀, hx₀⟩ := hsingle
  have hx₀S : x₀ ∈ S := hSuniv.symm ▸ Set.mem_univ x₀
  obtain ⟨⟨x, y⟩, hxy, hxx₀⟩ := hx₀S
  change x = x₀ at hxx₀
  subst x
  exact hxy.1 (hx₀ y hxy.2.1.symm).symm

end DifferentialGeometry.Topology
