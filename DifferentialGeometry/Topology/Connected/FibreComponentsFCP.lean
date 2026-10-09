import DifferentialGeometry.Topology.Connected.CompactFiniteComponentsFCP
import DifferentialGeometry.Topology.Connected.LocalFacesFiniteComponentsFCP

/-!
# Components of a compact space fibred over a base with open components (FDC04, `M₃ → C₁`)

Lane S-FINCOMP, group G3 (suffix `_FCP`). The circle bundle `M₃ = E⁻¹(C₁) → C₁` has connected
fibres and a compact total space; hence its connected components are the preimages of the
components of `C₁`, and they are open as soon as those of `C₁` are. Space-level kernels (the
total space is a subtype of the bundle domain, not a subset of the ambient carrier):

* `isOpen_connectedComponent_of_fibres_FCP`: `f : T → Z` continuous onto a Hausdorff `Z` with
  connected fibres, `T` compact: open components of `Z` give open components of `T`.
* `exists_finite_components_of_embedding_FCP`: for a compact space `T` with open components and an
  embedding `g : T → Z`, the finite list `B : Fin m → Set Z` of the images of the components
  (compact, connected, pairwise disjoint, union `range g`).
-/

set_option autoImplicit false

open Set Function Filter Topology Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology

variable {T Z : Type*} [TopologicalSpace T] [TopologicalSpace Z]

/-- **Open components descend to the total space of a closed connected-fibre map**: if `T` is
compact, `f : T → Z` is a continuous surjection onto a Hausdorff space with connected fibres, and
the connected components of `Z` are open, so are those of `T` (they are the preimages). -/
theorem isOpen_connectedComponent_of_fibres_FCP [CompactSpace T] [T2Space Z] {f : T → Z}
    (hf : Continuous f) (hs : Surjective f) (hfib : ∀ z, IsConnected (f ⁻¹' {z}))
    (hZ : ∀ z : Z, IsOpen (connectedComponent z)) (x : T) : IsOpen (connectedComponent x) := by
  have hco : IsCoinducing f := (hf.isClosedMap.isQuotientMap hf hs).isCoinducing
  rw [← hco.preimage_connectedComponent hfib x]
  exact (hZ (f x)).preimage hf

/-- **The finite list of components of a compact space with open components, pushed forward along
an embedding**: finitely many pairwise disjoint compact connected sets `B 0, …, B (m-1)` of `Z`
with union `range g`. -/
theorem exists_finite_components_of_embedding_FCP [CompactSpace T] {g : T → Z}
    (hg : IsEmbedding g) (h : ∀ x : T, IsOpen (connectedComponent x)) :
    ∃ (m : ℕ) (B : Fin m → Set Z), (∀ i, IsCompact (B i)) ∧ (∀ i, IsConnected (B i)) ∧
      (∀ i, B i ⊆ range g) ∧ Pairwise (Disjoint on B) ∧ range g = ⋃ i, B i := by
  have hfin := finite_connectedComponents_of_isOpen_connectedComponent_FCP h
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin (ConnectedComponents T)
  let rep : ConnectedComponents T → T := fun c =>
    Classical.choose (ConnectedComponents.surjective_coe c)
  have hrep : ∀ c, (rep c : ConnectedComponents T) = c := fun c =>
    Classical.choose_spec (ConnectedComponents.surjective_coe c)
  let B : Fin m → Set Z := fun i => g '' connectedComponent (rep (e.symm i))
  refine ⟨m, B, fun i => ?_, fun i => ?_, fun i => ?_, ?_, ?_⟩
  · exact (isClosed_connectedComponent.isCompact).image hg.continuous
  · exact isConnected_connectedComponent.image g hg.continuous.continuousOn
  · exact image_subset_range _ _
  · intro i j hij
    refine disjoint_left.mpr fun z hzi hzj => hij ?_
    obtain ⟨a, ha, rfl⟩ := hzi
    obtain ⟨b, hb, hba⟩ := hzj
    have hab : b = a := hg.injective hba
    subst hab
    have h4 : e.symm i = e.symm j := by
      rw [← hrep (e.symm i), ← hrep (e.symm j)]
      exact ConnectedComponents.coe_eq_coe.mpr
        ((connectedComponent_eq ha).trans (connectedComponent_eq hb).symm)
    exact e.symm.injective h4
  · apply Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      refine mem_iUnion.mpr ⟨e (ConnectedComponents.mk x), ?_⟩
      have h5 : (rep (e.symm (e (ConnectedComponents.mk x))) : ConnectedComponents T) =
          ConnectedComponents.mk x := by
        rw [Equiv.symm_apply_apply]
        exact hrep _
      have h6 : connectedComponent (rep (e.symm (e (ConnectedComponents.mk x)))) =
          connectedComponent x := ConnectedComponents.coe_eq_coe.mp h5
      exact ⟨x, h6 ▸ mem_connectedComponent, rfl⟩
    · exact iUnion_subset fun i => image_subset_range _ _

/-- **The local face model makes `S` locally connected** (the space form of
`finite_components_of_local_faces_FCP`): same hypotheses, conclusion the instance. -/
theorem locallyConnectedSpace_of_local_faces_FCP {B : Type*} [TopologicalSpace B]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) B] [IsManifold (𝓡 2) ∞ B] {ι : Type*} {S : Set B}
    (h : ∀ c ∈ frontier S, ∃ U : TopologicalSpace.Opens B, c ∈ U ∧
      ∃ (L : Finset ι) (φ : ι → B → ℝ),
        (∀ f ∈ L, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) U) ∧
        (Surjective fun w : TangentSpace (𝓡 2) c =>
          fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) c w) ∧
        S ∩ U = {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0}) :
    LocallyConnectedSpace S := by
  have hlc : LocallyConnectedSpace B :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) B
  refine locallyConnectedSpace_of_forall_exists_preconnected_FCP fun x hx U hU => ?_
  by_cases hfr : x ∈ frontier S
  · obtain ⟨U0, hxU0, L, φ, hφ, hsurj, hS0⟩ := h x hfr
    exact exists_preconnected_nhds_of_faces_FCP U0.isOpen hxU0 hx L φ hφ hsurj hS0 hU
  · have hxi : x ∈ interior S := by
      by_contra hxi
      exact hfr ⟨subset_closure hx, hxi⟩
    obtain ⟨V, hV, hVc, hVU⟩ := locallyConnectedSpace_iff_connected_subsets.mp hlc x
      (U ∩ interior S) (inter_mem hU (isOpen_interior.mem_nhds hxi))
    exact ⟨V, nhdsWithin_le_nhds hV, hVc, fun z hz => ⟨interior_subset (hVU hz).2, (hVU hz).1⟩⟩

end DifferentialGeometry.Topology
