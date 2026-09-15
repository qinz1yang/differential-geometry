import DifferentialGeometry.Topology.Connected.Loop
import DifferentialGeometry.Topology.PiecewiseLinear.CurveInclusion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem IsPLSphere.isConnected_sdiff_singleton_one {S : Set E} (hS : IsPLSphere 1 S) (p : E) :
    IsConnected (S \ {p}) := by
  obtain ⟨f, hf⟩ := hS
  have hmap : MapsTo stdTriangleLoop (Icc 0 1) (stdSimplexBoundary 2) :=
    fun t ht => stdTriangleLoop_image.subset ⟨t, ht, rfl⟩
  have hc : ContinuousOn (f ∘ stdTriangleLoop) (Icc 0 1) :=
    hf.isPiecewiseAffineOn.continuousOn.comp continuous_stdTriangleLoop.continuousOn hmap
  have hclose : (f ∘ stdTriangleLoop) 0 = (f ∘ stdTriangleLoop) 1 := by
    norm_num [Function.comp_apply, stdTriangleLoop]
  have hinj : InjOn (f ∘ stdTriangleLoop) (Ico 0 1) := by
    intro s hs t ht hst
    exact injOn_stdTriangleLoop hs ht
      (hf.bijOn.injOn (hmap ⟨hs.1, hs.2.le⟩) (hmap ⟨ht.1, ht.2.le⟩) hst)
  have himage : (f ∘ stdTriangleLoop) '' Icc 0 1 = S := by
    rw [image_comp, stdTriangleLoop_image, hf.image_eq]
  rw [← himage]
  exact isConnected_image_Icc_sdiff_singleton (by norm_num) hc hclose hinj p

omit [FiniteDimensional ℝ E] in
theorem IsPLSphere.not_singleton_mem_nhdsWithin_one {S : Set E} (hS : IsPLSphere 1 S)
    {p : E} (hp : p ∈ S) : {p} ∉ 𝓝[S] p := by
  intro hisolated
  let _ : ConnectedSpace S := Subtype.connectedSpace hS.isConnected_one
  have hopen : IsOpen ((↑) ⁻¹' ({p} : Set E) : Set S) := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hxp : (x : E) = p := hx
    have hnhds : {p} ∈ 𝓝[S] (x : E) := hxp.symm ▸ hisolated
    rwa [nhdsWithin_eq_map_subtype_coe] at hnhds
  have hfull := (show IsClopen ((↑) ⁻¹' ({p} : Set E) : Set S) from
    ⟨isClosed_singleton.preimage continuous_subtype_val, hopen⟩).eq_univ ⟨⟨p, hp⟩, rfl⟩
  obtain ⟨q, hqS, hqp⟩ := (hS.isConnected_sdiff_singleton_one p).nonempty
  exact hqp (show (⟨q, hqS⟩ : S) ∈ ((↑) ⁻¹' ({p} : Set E) : Set S) by rw [hfull]; trivial)

open Classical in
theorem face_mem_of_inter_space_sdiff_singleton_nonempty
    (H G : Geometry.SimplicialComplex ℝ E) [Finite G.faces] (hHG : H ≤ G)
    (hH : IsCombinatorialManifold 1 H) (hcard : ∀ s ∈ G.faces, s.card ≤ 2)
    (p : E) (hdegree : ∀ v ∈ G.vertices, v ≠ p → {w | w ≠ v ∧ {v, w} ∈ G.faces}.ncard = 2)
    {s : Finset E} (hs : s ∈ G.faces)
    (hinter : ((convexHull ℝ (s : Set E) ∩ H.space) \ {p}).Nonempty) : s ∈ H.faces := by
  obtain ⟨x, ⟨hxs, hxH⟩, hxp⟩ := hinter
  obtain ⟨t, ht, hxt⟩ := H.mem_space_iff.mp hxH
  have hxinter := G.inter_subset_convexHull hs (hHG ht) ⟨hxs, hxt⟩
  have hex : ∃ v ∈ (s : Set E) ∩ (t : Set E), v ≠ p := by
    by_contra! h
    have hsub : (s : Set E) ∩ (t : Set E) ⊆ {p} := fun v hv => h v hv
    have hxp' := convexHull_mono hsub hxinter
    rw [convexHull_singleton] at hxp'
    exact hxp hxp'
  obtain ⟨v, ⟨hvs, hvt⟩, hvp⟩ := hex
  have hvH : v ∈ H.vertices := H.down_closed ht (Finset.singleton_subset_iff.mpr hvt)
    (Finset.singleton_nonempty v)
  exact face_mem_of_vertex_mem_of_le_of_neighborSet_ncard_eq_two H G hHG hH hcard hs hvs hvH
    (hdegree v (hHG hvH) hvp)

open Classical in
theorem isClopen_preimage_space_sdiff_singleton_of_le_of_degree_eq_two_except
    (H G : Geometry.SimplicialComplex ℝ E) [Finite G.faces] (hHG : H ≤ G)
    (hH : IsCombinatorialManifold 1 H) (hcard : ∀ s ∈ G.faces, s.card ≤ 2)
    (p : E) (hdegree : ∀ v ∈ G.vertices, v ≠ p → {w | w ≠ v ∧ {v, w} ∈ G.faces}.ncard = 2) :
    IsClopen ((↑) ⁻¹' H.space : Set ↥(G.space \ {p})) := by
  let _ : Finite H.faces := ((Set.toFinite G.faces).subset hHG).to_subtype
  let C : Set E := ⋃ s ∈ G.faces \ H.faces, convexHull ℝ (s : Set E)
  have hCclosed : IsClosed C := ((Set.toFinite G.faces).subset sdiff_subset).isClosed_biUnion
    (fun s _ => (s.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed)
  have hcompl : (((↑) ⁻¹' H.space : Set ↥(G.space \ {p})))ᶜ = ((↑) ⁻¹' C) := by
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs, hxs⟩ := G.mem_space_iff.mp x.property.1
      exact mem_iUnion₂.mpr ⟨s, ⟨hs, fun h => hx (H.convexHull_subset_space h hxs)⟩, hxs⟩
    · intro hx hxH
      obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
      exact hs.2 (face_mem_of_inter_space_sdiff_singleton_nonempty H G hHG hH hcard p hdegree
        hs.1 ⟨x, ⟨hxs, hxH⟩, x.property.2⟩)
  refine ⟨(isPolyhedron_space H).isClosed.preimage continuous_subtype_val, ?_⟩
  rw [← isClosed_compl_iff, hcompl]
  exact hCclosed.preimage continuous_subtype_val

open Classical in
theorem eq_of_isPLSphere_one_of_mem_inter_of_degree_eq_two_except
    (G : Geometry.SimplicialComplex ℝ E) [Finite G.faces]
    (hcard : ∀ s ∈ G.faces, s.card ≤ 2) (p : E)
    (hdegree : ∀ v ∈ G.vertices, v ≠ p → {w | w ≠ v ∧ {v, w} ∈ G.faces}.ncard = 2)
    {J T : Set E} (hJ : IsPLSphere 1 J) (hT : IsPLSphere 1 T)
    (hJG : J ⊆ G.space) (hTG : T ⊆ G.space) {x : E} (hxJ : x ∈ J) (hxT : x ∈ T)
    (hxp : x ≠ p) : J = T := by
  let H := restrict G J
  let _ : Finite H.faces := (restrict_faces_finite G J).to_subtype
  have hHspace : H.space = J := restrict_space_eq_of_isPLSphere_one G hcard hJ hJG
  have hH : IsCombinatorialManifold 1 H := (hHspace.symm ▸ hJ).isCombinatorialManifold
  have hclopen := isClopen_preimage_space_sdiff_singleton_of_le_of_degree_eq_two_except H G
    (restrict_faces_subset G J) hH hcard p hdegree
  let i : ↥(T \ {p}) → ↥(G.space \ {p}) := fun y => ⟨y, hTG y.property.1, y.property.2⟩
  have hi : Continuous i := continuous_subtype_val.subtype_mk _
  have hJclopen : IsClopen ((↑) ⁻¹' J : Set ↥(T \ {p})) := by
    simpa only [hHspace, preimage_preimage, Function.comp_def, i] using hclopen.preimage hi
  let _ : ConnectedSpace ↥(T \ {p}) := Subtype.connectedSpace (hT.isConnected_sdiff_singleton_one p)
  have hfull := hJclopen.eq_univ ⟨⟨x, hxT, hxp⟩, hxJ⟩
  have hsub : T \ {p} ⊆ J := fun y hy =>
    (show (⟨y, hy⟩ : ↥(T \ {p})) ∈ ((↑) ⁻¹' J : Set ↥(T \ {p})) by rw [hfull]; trivial)
  have hcover : T ⊆ J ∪ {p} := by
    intro y hy
    by_cases hyp : y = p
    · exact Or.inr hyp
    · exact Or.inl (hsub ⟨hy, hyp⟩)
  have hTJ : T ⊆ J := by
    intro y hy
    rcases hcover hy with hyJ | hyp
    · exact hyJ
    · have hyp' : y = p := hyp
      subst y
      by_contra hpJ
      obtain ⟨z, -, hzJ, hzp⟩ := isPreconnected_closed_iff.mp hT.isConnected_one.isPreconnected
        J {p} hJ.isPolyhedron.isClosed isClosed_singleton hcover ⟨x, hxT, hxJ⟩ ⟨p, hy, rfl⟩
      exact hpJ (hzp ▸ hzJ)
  exact (eq_of_subset_of_isPLSphere_one hT hJ hTJ).symm

end DifferentialGeometry.Topology.PiecewiseLinear
