import DifferentialGeometry.Topology.Maps.CoincidentGermPairs

set_option autoImplicit false

open Set Filter Topology

namespace DifferentialGeometry.Topology

/-- A locally compact injective source germ admits an embedded open restriction
inside any prescribed open neighborhood. -/
private theorem exists_embedded_open_subset_of_locallyCompact
    {X Y : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) (hloc : IsLocallyInjective f)
    {x : X} {O : Set X} (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ O ∧ IsEmbedding (U.domRestrict f) := by
  obtain ⟨V, hV, hxV, hinj⟩ := hloc x
  obtain ⟨K, hK, hxK, hKsub⟩ := exists_compact_subset (hO.inter hV) ⟨hxO, hxV⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hemb : IsEmbedding (K.domRestrict f) :=
    ((hf.comp continuous_subtype_val).isClosedEmbedding
      (Set.injOn_iff_injective.mp (hinj.mono (hKsub.trans inter_subset_right)))).isEmbedding
  refine ⟨interior K, isOpen_interior, hxK,
    interior_subset.trans (hKsub.trans inter_subset_left), ?_⟩
  simpa only [Set.domRestrict_eq, Function.comp_def] using
    hemb.comp (IsEmbedding.inclusion (show interior K ⊆ K from interior_subset))

private theorem map_nhds_eq_image_nhdsWithin_of_embedded_open
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
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

/-- The actual coincident-germ projection is open on a locally compact
Hausdorff source. Only two disjoint embedded source neighborhoods are needed;
no compactness of the whole regular-value restriction is assumed. -/
theorem isOpen_fst_image_coincidentGermPairs_of_locallyCompact
    {X Y : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) (hloc : IsLocallyInjective f) :
    IsOpen (Prod.fst '' coincidentGermPairs f) := by
  classical
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨⟨a, b⟩, hab, rfl⟩
  obtain ⟨O, P, hO, hP, haO, hbP, hOP⟩ := t2_separation hab.1
  obtain ⟨U, hU, haU, hUO, hembU⟩ :=
    exists_embedded_open_subset_of_locallyCompact hf hloc hO haO
  obtain ⟨V, hV, hbV, hVP, hembV⟩ :=
    exists_embedded_open_subset_of_locallyCompact hf hloc hP hbP
  have hdisj : Disjoint U V := hOP.mono hUO hVP
  have hmapA : Filter.map f (𝓝 a) = 𝓝[f '' U] (f a) :=
    map_nhds_eq_image_nhdsWithin_of_embedded_open hU hembU haU
  have hmapB : Filter.map f (𝓝 b) = 𝓝[f '' V] (f b) :=
    map_nhds_eq_image_nhdsWithin_of_embedded_open hV hembV hbV
  have hrelative : 𝓝[f '' U] (f a) = 𝓝[f '' V] (f a) := by
    have hh := hmapA.symm.trans (hab.2.2.trans hmapB)
    rwa [← hab.2.1] at hh
  have hsets : f '' U =ᶠ[𝓝 (f a)] f '' V :=
    nhdsWithin_eq_iff_eventuallyEqSet.mp hrelative
  obtain ⟨W, hWsub, hWopen, haW⟩ :=
    mem_nhds_iff.mp (eventuallyEqSet_iff.mp hsets)
  apply Filter.mem_of_superset
    (inter_mem (hU.mem_nhds haU) ((hWopen.preimage hf).mem_nhds haW))
  rintro z ⟨hzU, hzW⟩
  have hzV : f z ∈ f '' V := (hWsub hzW).mp ⟨z, hzU, rfl⟩
  obtain ⟨w, hwV, hfw⟩ := hzV
  have hzw : z ≠ w := by
    intro h
    subst w
    exact Set.disjoint_left.mp hdisj hzU hwV
  refine ⟨(z, w), ⟨hzw, hfw.symm, ?_⟩, rfl⟩
  rw [map_nhds_eq_image_nhdsWithin_of_embedded_open hU hembU hzU,
    map_nhds_eq_image_nhdsWithin_of_embedded_open hV hembV hwV, hfw]
  apply nhdsWithin_eq_iff_eventuallyEqSet.mpr
  apply eventuallyEqSet_iff.mpr
  exact Filter.mem_of_superset (hWopen.mem_nhds hzW) hWsub

end DifferentialGeometry.Topology
