import DifferentialGeometry.Topology.PiecewiseLinear.FiniteGraphCircles
import DifferentialGeometry.Topology.PiecewiseLinear.SphereInclusion
import DifferentialGeometry.Topology.SimplicialComplex.EdgeGraph

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem neighbors_eq_of_le_of_neighborSet_ncard_eq_two
    (H G : Geometry.SimplicialComplex ℝ E) [Finite G.faces] (hHG : H ≤ G)
    (hH : IsCombinatorialManifold 1 H) {v : E} (hv : v ∈ H.vertices)
    (hdegree : {w | w ≠ v ∧ {v, w} ∈ G.faces}.ncard = 2) :
    {w | w ≠ v ∧ {v, w} ∈ H.faces} = {w | w ≠ v ∧ {v, w} ∈ G.faces} := by
  let _ : Finite H.faces := ((Set.toFinite G.faces).subset hHG).to_subtype
  obtain ⟨a, b, hab, hpair⟩ := (isCombinatorialManifold_one_iff H).mp hH |>.2 v hv
  refine Set.eq_of_subset_of_ncard_le (fun w hw => ⟨hw.1, hHG hw.2⟩) ?_ ?_
  · rw [hpair, Set.ncard_pair hab, hdegree]
  · exact ((SimplicialComplex.finite_vertices G).subset (fun w hw =>
      G.down_closed hw.2 (by simp) (Finset.singleton_nonempty w)))

open Classical in
theorem face_mem_of_vertex_mem_of_le_of_neighborSet_ncard_eq_two
    (H G : Geometry.SimplicialComplex ℝ E) [Finite G.faces] (hHG : H ≤ G)
    (hH : IsCombinatorialManifold 1 H) (hcard : ∀ s ∈ G.faces, s.card ≤ 2)
    {s : Finset E} (hs : s ∈ G.faces) {v : E} (hvs : v ∈ s) (hv : v ∈ H.vertices)
    (hdegree : {w | w ≠ v ∧ {v, w} ∈ G.faces}.ncard = 2) : s ∈ H.faces := by
  by_cases hcard₁ : s.card = 1
  · obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp hcard₁
    exact Finset.mem_singleton.mp hvs ▸ hv
  · have hcard₂ : s.card = 2 := by
      have := Finset.card_pos.mpr (G.nonempty_of_mem_faces hs)
      have := hcard s hs
      omega
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard₂
    have hn := neighbors_eq_of_le_of_neighborSet_ncard_eq_two H G hHG hH hv hdegree
    rcases Finset.mem_insert.mp hvs with rfl | hvb
    · have hb : b ∈ {w | w ≠ v ∧ {v, w} ∈ H.faces} := hn.symm ▸ And.intro hab.symm hs
      exact hb.2
    · have hvb' : v = b := Finset.mem_singleton.mp hvb
      subst v
      have ha : a ∈ {w | w ≠ b ∧ {b, w} ∈ H.faces} := by
        rw [hn]
        exact ⟨hab, by simpa only [Finset.pair_comm] using hs⟩
      simpa only [Finset.pair_comm] using ha.2

open Classical in
theorem neighbors_eq_of_le_isCombinatorialManifold_one
    (H K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hHK : H ≤ K)
    (hH : IsCombinatorialManifold 1 H) (hK : IsCombinatorialManifold 1 K)
    {v : E} (hv : v ∈ H.vertices) :
    {w | w ≠ v ∧ {v, w} ∈ H.faces} = {w | w ≠ v ∧ {v, w} ∈ K.faces} := by
  obtain ⟨a, b, hab, hpair⟩ := (isCombinatorialManifold_one_iff K).mp hK |>.2 v (hHK hv)
  apply neighbors_eq_of_le_of_neighborSet_ncard_eq_two H K hHK hH hv
  rw [hpair, Set.ncard_pair hab]

open Classical in
theorem face_mem_of_vertex_mem_of_le_isCombinatorialManifold_one
    (H K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hHK : H ≤ K)
    (hH : IsCombinatorialManifold 1 H) (hK : IsCombinatorialManifold 1 K)
    {s : Finset E} (hs : s ∈ K.faces) {v : E} (hvs : v ∈ s) (hv : v ∈ H.vertices) :
    s ∈ H.faces := by
  obtain ⟨a, b, hab, hpair⟩ := (isCombinatorialManifold_one_iff K).mp hK |>.2 v (hHK hv)
  apply face_mem_of_vertex_mem_of_le_of_neighborSet_ncard_eq_two H K hHK hH
    (fun t ht => hK.card_le K ht) hs hvs hv
  rw [hpair, Set.ncard_pair hab]

open Classical in
theorem face_mem_of_inter_space_nonempty_of_le_isCombinatorialManifold_one
    (H K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hHK : H ≤ K)
    (hH : IsCombinatorialManifold 1 H) (hK : IsCombinatorialManifold 1 K)
    {s : Finset E} (hs : s ∈ K.faces)
    (hinter : (convexHull ℝ (s : Set E) ∩ H.space).Nonempty) : s ∈ H.faces := by
  obtain ⟨x, hxs, hxH⟩ := hinter
  obtain ⟨t, ht, hxt⟩ := H.mem_space_iff.mp hxH
  obtain ⟨v, hvs, hvt⟩ := convexHull_nonempty_iff.mp
    ⟨x, K.inter_subset_convexHull hs (hHK ht) ⟨hxs, hxt⟩⟩
  exact face_mem_of_vertex_mem_of_le_isCombinatorialManifold_one H K hHK hH hK hs hvs
    (H.down_closed ht (Finset.singleton_subset_iff.mpr hvt) (Finset.singleton_nonempty v))

theorem isClopen_preimage_space_of_le_isCombinatorialManifold_one
    (H K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hHK : H ≤ K)
    (hH : IsCombinatorialManifold 1 H) (hK : IsCombinatorialManifold 1 K) :
    IsClopen ((↑) ⁻¹' H.space : Set K.space) := by
  classical
  let _ : Finite H.faces := ((Set.toFinite K.faces).subset hHK).to_subtype
  have hdiff : K.space \ H.space = ⋃ s ∈ K.faces \ H.faces, convexHull ℝ (s : Set E) := by
    ext x
    constructor
    · rintro ⟨hxK, hxH⟩
      obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hxK
      exact mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨⟨hs, fun h => hxH (H.convexHull_subset_space h hxs)⟩, hxs⟩⟩
    · intro hx
      obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
      refine ⟨K.convexHull_subset_space hs.1 hxs, fun hxH => ?_⟩
      exact hs.2 (face_mem_of_inter_space_nonempty_of_le_isCombinatorialManifold_one
        H K hHK hH hK hs.1 ⟨x, hxs, hxH⟩)
  have hclosed : IsClosed (K.space \ H.space) := by
    rw [hdiff]
    have hfaces : (K.faces \ H.faces).Finite := (Set.toFinite K.faces).subset sdiff_subset
    exact hfaces.isClosed_biUnion
      (fun s _ => (s.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed)
  refine ⟨(isPolyhedron_space H).isClosed.preimage continuous_subtype_val, ?_⟩
  apply isClosed_compl_iff.mp
  convert hclosed.preimage continuous_subtype_val using 1
  ext x
  simp only [mem_compl_iff, mem_preimage, mem_sdiff, x.property, true_and]

theorem space_eq_of_le_isCombinatorialManifold_one
    (H K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hHK : H ≤ K)
    (hH : IsCombinatorialManifold 1 H) (hK : IsCombinatorialManifold 1 K)
    (hconnected : IsPreconnected K.space) (hne : H.space.Nonempty) : H.space = K.space := by
  let _ : PreconnectedSpace K.space := Subtype.preconnectedSpace hconnected
  have hsub : H.space ⊆ K.space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := H.mem_space_iff.mp hx
    exact K.convexHull_subset_space (hHK hs) hxs
  have hnonempty : (((↑) ⁻¹' H.space : Set K.space)).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨⟨x, hsub hx⟩, hx⟩
  have hfull := (isClopen_preimage_space_of_le_isCombinatorialManifold_one H K hHK hH hK).eq_univ hnonempty
  apply Subset.antisymm hsub
  intro x hx
  exact (show (⟨x, hx⟩ : K.space) ∈ ((↑) ⁻¹' H.space : Set K.space) by rw [hfull]; trivial)

omit [FiniteDimensional ℝ E] in
theorem IsPLSphere.isConnected_one {S : Set E} (hS : IsPLSphere 1 S) : IsConnected S :=
  hS.isConnected

theorem eq_of_subset_of_isPLSphere_one {S T : Set E}
    (hS : IsPLSphere 1 S) (hT : IsPLSphere 1 T) (hST : S ⊆ T) : S = T :=
  eq_of_subset_of_isPLSphere hS hT hST

end DifferentialGeometry.Topology.PiecewiseLinear
