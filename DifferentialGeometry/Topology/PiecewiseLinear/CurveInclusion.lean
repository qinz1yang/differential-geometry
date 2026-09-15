import DifferentialGeometry.Topology.PiecewiseLinear.FiniteGraphCircles
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarSchoenflies

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem neighbors_eq_of_le_isCombinatorialManifold_one
    (H K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hHK : H ≤ K)
    (hH : IsCombinatorialManifold 1 H) (hK : IsCombinatorialManifold 1 K)
    {v : E} (hv : v ∈ H.vertices) :
    {w | w ≠ v ∧ {v, w} ∈ H.faces} = {w | w ≠ v ∧ {v, w} ∈ K.faces} := by
  let _ : Finite H.faces := ((Set.toFinite K.faces).subset hHK).to_subtype
  obtain ⟨a, b, hab, hHpair⟩ := (isCombinatorialManifold_one_iff H).mp hH |>.2 v hv
  obtain ⟨c, d, hcd, hKpair⟩ := (isCombinatorialManifold_one_iff K).mp hK |>.2 v (hHK hv)
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ ?_
  · exact fun w hw => ⟨hw.1, hHK hw.2⟩
  · rw [hHpair, hKpair, Set.ncard_pair hab, Set.ncard_pair hcd]
  · rw [hKpair]
    exact Set.toFinite _

open Classical in
theorem face_mem_of_vertex_mem_of_le_isCombinatorialManifold_one
    (H K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hHK : H ≤ K)
    (hH : IsCombinatorialManifold 1 H) (hK : IsCombinatorialManifold 1 K)
    {s : Finset E} (hs : s ∈ K.faces) {v : E} (hvs : v ∈ s) (hv : v ∈ H.vertices) :
    s ∈ H.faces := by
  have hcard : s.card ≤ 2 := hK.card_le K hs
  by_cases hcard₁ : s.card = 1
  · obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp hcard₁
    have hvw : v = w := Finset.mem_singleton.mp hvs
    exact hvw ▸ hv
  · have hcard₂ : s.card = 2 := by
      have := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)
      omega
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard₂
    have hneighbors := neighbors_eq_of_le_isCombinatorialManifold_one H K hHK hH hK hv
    rcases Finset.mem_insert.mp hvs with hva | h
    · subst v
      have hb : b ∈ {w | w ≠ a ∧ {a, w} ∈ H.faces} := by
        rw [hneighbors]
        exact ⟨hab.symm, hs⟩
      exact hb.2
    · have hvb : v = b := Finset.mem_singleton.mp h
      subst v
      have ha : a ∈ {w | w ≠ b ∧ {b, w} ∈ H.faces} := by
        rw [hneighbors]
        exact ⟨hab, by simpa only [Finset.pair_comm] using hs⟩
      simpa only [Finset.pair_comm] using ha.2

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
theorem IsPLSphere.isConnected_one {S : Set E} (hS : IsPLSphere 1 S) : IsConnected S := by
  let J := polygonalCircleOfAffineIndependentTriple
    LeanEval.Topology.ClassificationOfSurfaces.Moise.standardTrianglePosition
    LeanEval.Topology.ClassificationOfSurfaces.Moise.standardTrianglePosition_affineIndependent
  obtain ⟨f, hf⟩ := hS
  obtain ⟨g, hg⟩ := isPLSphere_one_carrier J
  have hbij := hf.bijOn.comp hg.symm.bijOn
  rw [← hbij.image_eq]
  exact J.isConnected_carrier.image _ (hf.isPiecewiseAffineOn.continuousOn.comp
    hg.symm.isPiecewiseAffineOn.continuousOn hg.symm.bijOn.mapsTo)

theorem eq_of_subset_of_isPLSphere_one {S T : Set E}
    (hS : IsPLSphere 1 S) (hT : IsPLSphere 1 T) (hST : S ⊆ T) : S = T := by
  classical
  obtain ⟨K, hKfin, hKspace⟩ := hT.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsCombinatorialManifold 1 K := (hKspace.symm ▸ hT).isCombinatorialManifold
  let H := restrict K S
  let _ : Finite H.faces := (restrict_faces_finite K S).to_subtype
  have hHspace : H.space = S :=
    restrict_space_eq_of_isPLSphere_one K (fun s hs => hK.card_le K hs) hS (hST.trans_eq hKspace.symm)
  have hH : IsCombinatorialManifold 1 H := (hHspace.symm ▸ hS).isCombinatorialManifold
  have heq := space_eq_of_le_isCombinatorialManifold_one H K (restrict_faces_subset K S) hH hK
    (hKspace.symm ▸ hT.isConnected_one.isPreconnected) (hHspace.symm ▸ hS.nonempty)
  exact hHspace.symm.trans (heq.trans hKspace)

end DifferentialGeometry.Topology.PiecewiseLinear
