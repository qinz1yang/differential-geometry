import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Analysis.Normed.Module.Convex

/-!
# A compact set with open components has a finite list of components (FDC04, "all the lists are
finite")

Lane S-FINCOMP, group G1 (suffix `_FCP`). Blueprint `master207B.tex`, FDC04 (B:7367-7435): "compact
manifold bases have finitely many components, so all the lists are finite". Mathlib has the space
statement (`[LocallyConnectedSpace α] [CompactSpace α] : Finite (ConnectedComponents α)`, from
`finite_of_compact_of_discrete`); this module gives the SET forms the chapter needs.

* `finite_connectedComponents_of_isOpen_connectedComponent_FCP`: a compact space whose connected
  components are open has finitely many (the weakest hypothesis, strictly weaker than local
  connectedness).
* `finite_connectedComponents_of_isCompact_FCP`: set form, `s` compact and
  `connectedComponentIn s x ∈ 𝓝[s] x` for `x ∈ s`.
* `finite_connectedComponents_of_isCompact_locallyConnected_FCP`: the Mathlib instance in set form
  (`LocallyConnectedSpace s`).
* `exists_finite_components_of_isCompact_FCP` (and the local-connectedness form): the finite LIST
  `B : Fin m → Set X` of pairwise disjoint compact connected, relatively clopen components with
  `s = ⋃ i, B i` and `B i = connectedComponentIn s x` for `x ∈ B i`.
* `locallyConnectedSpace_of_forall_exists_preconnected_FCP`: the set-level criterion for
  `LocallyConnectedSpace s` (preconnected neighbourhoods of `x` in `s`, inside every neighbourhood
  of `x` in `X`) used to verify the hypothesis on concrete regions.
* `finite_connectedComponents_of_image_FCP` / `finite_connectedComponents_image_iff_FCP`: a compact
  `s` with a continuous map `f` to a Hausdorff space with connected fibres on `s` has as many
  components as `f '' s` (circle bundle `M₃ → C₁`: the components of `M₃` are the preimages of the
  components of `C₁`).
-/

set_option autoImplicit false

open Set Function Filter Topology

namespace DifferentialGeometry.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A compact space whose connected components are open has finitely many connected components. -/
theorem finite_connectedComponents_of_isOpen_connectedComponent_FCP [CompactSpace X]
    (h : ∀ x : X, IsOpen (connectedComponent x)) : Finite (ConnectedComponents X) := by
  have : DiscreteTopology (ConnectedComponents X) :=
    ConnectedComponents.discreteTopology_iff.mpr h
  exact finite_of_compact_of_discrete

/-- The component of `x` in the subtype `s`, seen in `s`, is open as soon as
`connectedComponentIn s y` is a neighbourhood of `y` within `s` for every `y ∈ s`. -/
theorem isOpen_connectedComponent_subtype_of_mem_nhdsWithin_FCP {s : Set X}
    (h : ∀ x ∈ s, connectedComponentIn s x ∈ 𝓝[s] x) (x : s) :
    IsOpen (connectedComponent x) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hmem := h y.1 y.2
  rw [connectedComponentIn_eq_image y.2] at hmem
  have hy' : connectedComponent y ∈ 𝓝 y := mem_nhds_subtype_iff_nhdsWithin.mpr hmem
  rwa [connectedComponent_eq hy]

/-- **Set form** of the finiteness: a compact set `s` such that `connectedComponentIn s x` is a
neighbourhood of `x` within `s` for every `x ∈ s` has finitely many connected components. -/
theorem finite_connectedComponents_of_isCompact_FCP {s : Set X} (hs : IsCompact s)
    (h : ∀ x ∈ s, connectedComponentIn s x ∈ 𝓝[s] x) : Finite (ConnectedComponents s) := by
  have : CompactSpace s := isCompact_iff_compactSpace.mp hs
  exact finite_connectedComponents_of_isOpen_connectedComponent_FCP
    (isOpen_connectedComponent_subtype_of_mem_nhdsWithin_FCP h)

/-- Mathlib's instance (`LocallyConnectedSpace` and `CompactSpace` give finitely many components)
in set form. -/
theorem finite_connectedComponents_of_isCompact_locallyConnected_FCP {s : Set X}
    (hs : IsCompact s) [LocallyConnectedSpace s] : Finite (ConnectedComponents s) := by
  have : CompactSpace s := isCompact_iff_compactSpace.mp hs
  infer_instance

/-- **The finite list of components** (the shape of the FDC04 lists): for a compact set `s` whose
components are neighbourhoods within `s`, finitely many pairwise disjoint compact connected sets
`B 0, …, B (m-1)`, each relatively clopen in `s` and equal to `connectedComponentIn s x` at each
of its points, with union `s`. -/
theorem exists_finite_components_of_isCompact_FCP {s : Set X} (hs : IsCompact s)
    (h : ∀ x ∈ s, connectedComponentIn s x ∈ 𝓝[s] x) :
    ∃ (m : ℕ) (B : Fin m → Set X), (∀ i, IsCompact (B i)) ∧ (∀ i, IsConnected (B i)) ∧
      (∀ i, B i ⊆ s) ∧ (∀ i, IsClopen (Subtype.val ⁻¹' B i : Set s)) ∧
      (∀ i, ∀ x ∈ B i, connectedComponentIn s x = B i) ∧
      Pairwise (Disjoint on B) ∧ s = ⋃ i, B i := by
  have hfin := finite_connectedComponents_of_isCompact_FCP hs h
  have : CompactSpace s := isCompact_iff_compactSpace.mp hs
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin (ConnectedComponents s)
  let rep : ConnectedComponents s → s := fun c =>
    Classical.choose (ConnectedComponents.surjective_coe c)
  have hrep : ∀ c, (rep c : ConnectedComponents s) = c := fun c =>
    Classical.choose_spec (ConnectedComponents.surjective_coe c)
  let B : Fin m → Set X := fun i =>
    connectedComponentIn s (rep (e.symm i)).1
  have hB : ∀ i, B i = Subtype.val '' connectedComponent (rep (e.symm i)) := fun i =>
    connectedComponentIn_eq_image (rep (e.symm i)).2
  have hBs : ∀ i, B i ⊆ s := fun i => connectedComponentIn_subset s _
  have hpre : ∀ i, (Subtype.val ⁻¹' B i : Set s) = connectedComponent (rep (e.symm i)) := by
    intro i
    rw [hB i]
    exact Subtype.val_injective.preimage_image _
  have hcl : ∀ i, IsClopen (Subtype.val ⁻¹' B i : Set s) := fun i => by
    rw [hpre i]
    exact ⟨isClosed_connectedComponent,
      isOpen_connectedComponent_subtype_of_mem_nhdsWithin_FCP h _⟩
  have hmax : ∀ i, ∀ x ∈ B i, connectedComponentIn s x = B i := fun i x hx =>
    (connectedComponentIn_eq hx).symm
  refine ⟨m, B, fun i => ?_, fun i => ?_, hBs, hcl, hmax, ?_, ?_⟩
  · rw [hB i]
    exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
  · exact isConnected_connectedComponentIn_iff.mpr (rep (e.symm i)).2
  · intro i j hij
    refine disjoint_left.mpr fun x hxi hxj => hij ?_
    have h1 : B i = B j := by
      rw [← hmax i x hxi, hmax j x hxj]
    have h3 : connectedComponent (rep (e.symm i)) = connectedComponent (rep (e.symm j)) := by
      rw [← hpre i, ← hpre j, h1]
    have h4 : e.symm i = e.symm j := by
      rw [← hrep (e.symm i), ← hrep (e.symm j)]
      exact ConnectedComponents.coe_eq_coe.mpr h3
    exact e.symm.injective h4
  · apply Subset.antisymm
    · intro x hx
      refine mem_iUnion.mpr ⟨e (ConnectedComponents.mk ⟨x, hx⟩), ?_⟩
      have h5 : (rep (e.symm (e (ConnectedComponents.mk ⟨x, hx⟩))) : ConnectedComponents s) =
          ConnectedComponents.mk ⟨x, hx⟩ := by
        rw [Equiv.symm_apply_apply]
        exact hrep _
      have h6 : connectedComponent (rep (e.symm (e (ConnectedComponents.mk ⟨x, hx⟩)))) =
          connectedComponent ⟨x, hx⟩ := ConnectedComponents.coe_eq_coe.mp h5
      rw [hB, h6]
      exact ⟨⟨x, hx⟩, mem_connectedComponent, rfl⟩
    · exact iUnion_subset hBs

/-- The finite list of components of a compact, locally connected set (Mathlib's instance in the
list shape). -/
theorem exists_finite_components_of_isCompact_locallyConnected_FCP {s : Set X}
    (hs : IsCompact s) [LocallyConnectedSpace s] :
    ∃ (m : ℕ) (B : Fin m → Set X), (∀ i, IsCompact (B i)) ∧ (∀ i, IsConnected (B i)) ∧
      (∀ i, B i ⊆ s) ∧ (∀ i, IsClopen (Subtype.val ⁻¹' B i : Set s)) ∧
      (∀ i, ∀ x ∈ B i, connectedComponentIn s x = B i) ∧
      Pairwise (Disjoint on B) ∧ s = ⋃ i, B i :=
  exists_finite_components_of_isCompact_FCP hs fun x hx => by
    rw [connectedComponentIn_eq_image hx]
    exact mem_nhds_subtype_iff_nhdsWithin.mp
      ((isOpen_connectedComponent (x := (⟨x, hx⟩ : s))).mem_nhds mem_connectedComponent)

/-- **Set-level criterion for local connectedness of a subset**: if every `x ∈ s` has, inside
every neighbourhood `U` of `x` in `X`, a preconnected neighbourhood of `x` within `s`, then the
subtype `s` is locally connected. (For a region cut out by inequalities this is the statement that
the region is locally a convex corner, checked chart by chart.) -/
theorem locallyConnectedSpace_of_forall_exists_preconnected_FCP {s : Set X}
    (h : ∀ x ∈ s, ∀ U ∈ 𝓝 x, ∃ V : Set X, V ∈ 𝓝[s] x ∧ IsPreconnected V ∧ V ⊆ s ∩ U) :
    LocallyConnectedSpace s := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro x U hU
  obtain ⟨u, hu, huU⟩ := mem_nhds_subtype s x U |>.mp hU
  obtain ⟨V, hV, hVc, hVsu⟩ := h x.1 x.2 u hu
  refine ⟨Subtype.val ⁻¹' V, preimage_coe_mem_nhds_subtype.mpr hV, ?_, fun z hz =>
    huU (hVsu hz).2⟩
  have himg : (Subtype.val '' (Subtype.val ⁻¹' V : Set s)) = V := by
    rw [Subtype.image_preimage_coe]
    exact inter_eq_right.mpr (fun z hz => (hVsu hz).1)
  rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, himg]
  exact hVc

/-- **Components of a compact set versus components of a continuous image with connected
fibres** (circle bundle `M₃ → C₁`): for `s` compact, `f` continuous on `s` into a Hausdorff space,
with `s ∩ f⁻¹{y}` connected for every `y ∈ f '' s`, the induced map from the components of `s` to
those of `f '' s` is bijective; in particular `s` has finitely many components as soon as
`f '' s` has. -/
theorem finite_connectedComponents_of_image_FCP [T2Space Y] {s : Set X} (hs : IsCompact s)
    {f : X → Y} (hf : ContinuousOn f s) (hfib : ∀ y ∈ f '' s, IsConnected (s ∩ f ⁻¹' {y}))
    (himg : Finite (ConnectedComponents (f '' s))) : Finite (ConnectedComponents s) := by
  have : CompactSpace s := isCompact_iff_compactSpace.mp hs
  let g : s → f '' s := fun x => ⟨f x, x.1, x.2, rfl⟩
  have hg : Continuous g :=
    (continuousOn_iff_continuous_domRestrict.mp hf).subtype_mk _
  have hgs : Surjective g := fun y => by
    obtain ⟨y, x, hx, rfl⟩ := y
    exact ⟨⟨x, hx⟩, rfl⟩
  have hco : Topology.IsCoinducing g := (hg.isClosedMap.isQuotientMap hg hgs).isCoinducing
  have hfibg : ∀ y : f '' s, IsConnected (g ⁻¹' {y}) := by
    intro y
    have himage : Subtype.val '' (g ⁻¹' {y} : Set s) = s ∩ f ⁻¹' {y.1} := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.2, congrArg Subtype.val hx⟩
      · rintro ⟨hzs, hz⟩
        exact ⟨⟨z, hzs⟩, Subtype.ext hz, rfl⟩
    have h1 := hfib y.1 y.2
    rw [← himage] at h1
    exact ⟨h1.nonempty.of_image,
      Topology.IsInducing.subtypeVal.isPreconnected_image.mp h1.isPreconnected⟩
  exact Finite.of_injective _ (hco.connectedComponentsMap_bijective hfibg).1

/-- Converse direction (a continuous surjection has at most as many components as its source). -/
theorem finite_connectedComponents_image_of_finite_FCP {s : Set X} {f : X → Y}
    (hf : ContinuousOn f s) (hs : Finite (ConnectedComponents s)) :
    Finite (ConnectedComponents (f '' s)) := by
  let g : s → f '' s := fun x => ⟨f x, x.1, x.2, rfl⟩
  have hg : Continuous g :=
    (continuousOn_iff_continuous_domRestrict.mp hf).subtype_mk _
  have hgs : Surjective g := fun y => by
    obtain ⟨y, x, hx, rfl⟩ := y
    exact ⟨⟨x, hx⟩, rfl⟩
  exact Finite.of_surjective _ (Continuous.connectedComponentsMap_surjective hg hgs)

/-- **A set that is locally a convex corner is locally connected.** If every `p ∈ s` lies in the
source of an open partial homeomorphism `e` to a real normed space with
`e '' (s ∩ e.source) = K ∩ e.target` for a convex set `K` (half space, quadrant, a whole chart:
the local models of a manifold with corners), then the subtype `s` is locally connected. -/
theorem locallyConnectedSpace_of_convex_charts_FCP {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Set X}
    (h : ∀ p ∈ s, ∃ e : OpenPartialHomeomorph X E, p ∈ e.source ∧
      ∃ K : Set E, Convex ℝ K ∧ e '' (s ∩ e.source) = K ∩ e.target) :
    LocallyConnectedSpace s := by
  refine locallyConnectedSpace_of_forall_exists_preconnected_FCP fun x hx U hU => ?_
  obtain ⟨e, hxe, K, hK, hKe⟩ := h x hx
  have hex : e x ∈ K ∩ e.target := hKe ▸ ⟨x, ⟨hx, hxe⟩, rfl⟩
  have hU' : U ∩ e.source ∈ 𝓝 x := inter_mem hU (e.open_source.mem_nhds hxe)
  have hsymm : e.symm ⁻¹' (U ∩ e.source) ∈ 𝓝 (e x) := by
    have h1 : U ∩ e.source ∈ 𝓝 (e.symm (e x)) := by
      rw [e.left_inv hxe]
      exact hU'
    exact e.continuousAt_symm (e.map_source hxe) h1
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hsymm (e.open_target.mem_nhds hex.2))
  have hbt : Metric.ball (e x) r ⊆ e.target := fun z hz => (hball hz).2
  have hbU : ∀ z ∈ Metric.ball (e x) r, e.symm z ∈ U ∩ e.source := fun z hz => (hball hz).1
  have hO : IsOpen (e.symm '' Metric.ball (e x) r) :=
    OpenPartialHomeomorph.isOpen_image_of_subset_source e.symm Metric.isOpen_ball
      (e.symm_source ▸ hbt)
  have hxO : x ∈ e.symm '' Metric.ball (e x) r :=
    ⟨e x, Metric.mem_ball_self hr, e.left_inv hxe⟩
  have hVs : ∀ z ∈ K ∩ Metric.ball (e x) r, e.symm z ∈ s := by
    intro z hz
    have hzK : z ∈ K ∩ e.target := ⟨hz.1, hbt hz.2⟩
    rw [← hKe] at hzK
    obtain ⟨w, hw, hwz⟩ := hzK
    rw [← hwz, e.left_inv hw.2]
    exact hw.1
  refine ⟨e.symm '' (K ∩ Metric.ball (e x) r), ?_, ?_, ?_⟩
  · refine mem_nhdsWithin.mpr ⟨_, hO, hxO, ?_⟩
    rintro z ⟨⟨b, hb, rfl⟩, hzs⟩
    have hzsrc : e.symm b ∈ e.source := (hbU b hb).2
    have hbK : b ∈ K := by
      have : e (e.symm b) ∈ K ∩ e.target := hKe ▸ ⟨e.symm b, ⟨hzs, hzsrc⟩, rfl⟩
      rw [e.right_inv (hbt hb)] at this
      exact this.1
    exact ⟨b, ⟨hbK, hb⟩, rfl⟩
  · exact (hK.inter (convex_ball (e x) r)).isPreconnected.image _
      (e.continuousOn_symm.mono fun z hz => hbt hz.2)
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨hVs z hz, (hbU z hz.2).1⟩

/-- **The finite list of components of a compact set that is locally a convex corner** (compact
manifold with corners; the shape of the FDC04 lists). -/
theorem exists_finite_components_of_convex_charts_FCP {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Set X} (hs : IsCompact s)
    (h : ∀ p ∈ s, ∃ e : OpenPartialHomeomorph X E, p ∈ e.source ∧
      ∃ K : Set E, Convex ℝ K ∧ e '' (s ∩ e.source) = K ∩ e.target) :
    ∃ (m : ℕ) (B : Fin m → Set X), (∀ i, IsCompact (B i)) ∧ (∀ i, IsConnected (B i)) ∧
      (∀ i, B i ⊆ s) ∧ (∀ i, IsClopen (Subtype.val ⁻¹' B i : Set s)) ∧
      (∀ i, ∀ x ∈ B i, connectedComponentIn s x = B i) ∧
      Pairwise (Disjoint on B) ∧ s = ⋃ i, B i :=
  haveI := locallyConnectedSpace_of_convex_charts_FCP h
  exists_finite_components_of_isCompact_locallyConnected_FCP hs

end DifferentialGeometry.Topology
