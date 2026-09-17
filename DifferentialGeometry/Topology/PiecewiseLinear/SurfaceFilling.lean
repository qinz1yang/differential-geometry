import DifferentialGeometry.Topology.PiecewiseLinear.BoundedSurfaceComponent
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldNeighborhood
import DifferentialGeometry.Topology.Connected.ComponentNeighborhood

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem isCombinatorialManifoldWithBoundary_of_space_eq_closure_connectedComponentIn_compl
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 2 L) (hdim : Module.finrank ℝ E = 3)
    {a b : E} (hdis : Disjoint (connectedComponentIn L.spaceᶜ a)
      (connectedComponentIn L.spaceᶜ b))
    (hmeet : closure (connectedComponentIn L.spaceᶜ a) ∩
      closure (connectedComponentIn L.spaceᶜ b) = L.space)
    (R : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (hR : R.space = closure (connectedComponentIn L.spaceᶜ a)) :
    IsCombinatorialManifoldWithBoundary 3 R := by
  obtain ⟨T, hT, hTcard, hRT⟩ := exists_affineIndependent_openSimplex_superset 3 hdim
    (isPolyhedron_space R).isCompact.isBounded
  let K := simplexComplex T hT
  let _ : Finite K.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hKspace : K.space = convexHull ℝ (T : Set E) :=
    simplexComplex_space T hT (Finset.card_pos.mp (by omega))
  have hKball : IsPLBall 3 K.space := hKspace.symm ▸
    isPLBall_convexHull_of_affineIndependent T hT hTcard
  have hK := hKball.isCombinatorialManifoldWithBoundary
  have hint : interior K.space = openSimplex T := by
    rw [hKspace, interior_convexHull_eq_openSimplex hT (by omega)]
  have hRint : R.space ⊆ interior K.space := hRT.trans hint.symm.subset
  have hLR : L.space ⊆ R.space := by
    rw [hR]
    exact hmeet.symm.subset.trans inter_subset_left
  have hLint : L.space ⊆ interior K.space := hLR.trans hRint
  apply isCombinatorialManifoldWithBoundary_of_isPLBall_neighborhoods R
  intro p hp
  by_cases hpL : p ∈ L.space
  · have hpB : p ∉ (boundaryComplex 3 K).space := by
      rw [← frontier_space_eq_boundaryComplex_space_of_finrank hdim K hK]
      exact fun h => h.2 (hLint hpL)
    obtain ⟨C, -, -, hCnhds, -, x, -, y, -, -, hcover, hX, hY, -, hlocal⟩ :=
      hK.exists_isPLBall_neighborhood_pair_sdiff hL (hLint.trans interior_subset)
        hpL hpB Filter.univ_mem
    rw [nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp (hRint hp))] at hCnhds
    have hlocal' := Topology.local_component_closure_neighborhood isClosed_univ
      (subset_univ C) (by simpa only [nhdsWithin_univ] using hCnhds) hpL
      (by simpa only [← compl_eq_univ_sdiff] using hdis)
      (by simpa only [← compl_eq_univ_sdiff] using hmeet) hcover hlocal
    simp only [← compl_eq_univ_sdiff] at hlocal'
    rcases hlocal' with ⟨hsub, hnhds⟩ | ⟨hsub, hnhds⟩
    · exact ⟨_, hX, by rwa [hR], by rwa [hR]⟩
    · exact ⟨_, hY, by rwa [hR], by rwa [hR]⟩
  · have hpA : p ∈ connectedComponentIn L.spaceᶜ a :=
      (Topology.closure_connectedComponentIn_inter L.spaceᶜ a).subset ⟨hR.subset hp, hpL⟩
    have hopen : IsOpen (connectedComponentIn L.spaceᶜ a) :=
      (isPolyhedron_space L).isClosed.isOpen_compl.connectedComponentIn
    have hRnhds : R.space ∈ 𝓝[K.space] p := by
      apply mem_nhdsWithin_of_mem_nhds
      rw [hR]
      exact Filter.mem_of_superset (hopen.mem_nhds hpA) subset_closure
    obtain ⟨C, hC, hsub, hnhds⟩ :=
      hK.exists_isPLBall_subset_of_mem_nhdsWithin (interior_subset (hRint hp)) hRnhds
    exact ⟨C, hC, hsub.trans inter_subset_right,
      nhdsWithin_mono p (hRint.trans interior_subset) hnhds⟩

open Classical in
theorem IsCombinatorialManifold.exists_isCombinatorialManifoldWithBoundary_boundaryComplex
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 2 L) (hdim : Module.finrank ℝ E = 3)
    (hconn : IsConnected L.space) :
    ∃ R : Geometry.SimplicialComplex ℝ E, R.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 R ∧
      (boundaryComplex 3 R).space = L.space ∧ frontier R.space = L.space ∧
      closure (interior R.space) = R.space ∧ IsConnected (interior R.space) ∧
      IsConnected R.spaceᶜ := by
  obtain ⟨U, hUopen, hUconn, -, hUfront, hpoly, hUint, hfront, hVconn⟩ :=
    hL.exists_isOpen_isBounded_frontier L hdim hconn
  obtain ⟨R, hRfin, hR⟩ := hpoly.exists_simplicialComplex
  let _ : Finite R.faces := hRfin.to_subtype
  have hcomp (W : Set E) (hW : IsOpen W) (hcW : IsPreconnected W)
      (hfW : frontier W = L.space) (p : E) (hp : p ∈ W) :
      connectedComponentIn L.spaceᶜ p = W := by
    have hsub : W ⊆ L.spaceᶜ := by
      intro x hx hxf
      exact (hW.frontier_eq ▸ hfW.symm.subset hxf).2 hx
    apply Subset.antisymm
    · apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hW
        ⟨p, mem_connectedComponentIn (hsub hp), hp⟩
      rintro x ⟨hxcl, hxcomp⟩
      by_contra hxW
      exact connectedComponentIn_subset _ _ hxcomp
        (hfW.subset (hW.frontier_eq.symm.subset ⟨hxcl, hxW⟩))
    · exact hcW.subset_connectedComponentIn hp hsub
  obtain ⟨a, ha⟩ := hUconn.nonempty
  obtain ⟨b, hb⟩ := hVconn.nonempty
  have hA := hcomp U hUopen hUconn.isPreconnected hUfront a ha
  have hB := hcomp (closure U)ᶜ isClosed_closure.isOpen_compl hVconn.isPreconnected
    (by rwa [frontier_compl]) b hb
  have hdis : Disjoint (connectedComponentIn L.spaceᶜ a)
      (connectedComponentIn L.spaceᶜ b) := by
    rw [hA, hB]
    exact disjoint_compl_right.mono_left subset_closure
  have hmeet : closure (connectedComponentIn L.spaceᶜ a) ∩
      closure (connectedComponentIn L.spaceᶜ b) = L.space := by
    rw [hA, hB, closure_compl, hUint]
    exact hUopen.frontier_eq.symm.trans hUfront
  have hman : IsCombinatorialManifoldWithBoundary 3 R :=
    isCombinatorialManifoldWithBoundary_of_space_eq_closure_connectedComponentIn_compl
      L hL hdim hdis hmeet R (by rwa [hA])
  refine ⟨R, hRfin, hman, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← frontier_space_eq_boundaryComplex_space_of_finrank hdim R hman, hR, hfront]
  · rwa [hR]
  · rw [hR, hUint]
  · rwa [hR, hUint]
  · rwa [hR]

end DifferentialGeometry.Topology.PiecewiseLinear
