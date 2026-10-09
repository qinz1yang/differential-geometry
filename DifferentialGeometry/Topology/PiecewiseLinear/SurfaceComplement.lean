/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceComponents
import DifferentialGeometry.Topology.PiecewiseLinear.FrontierBoundary
import DifferentialGeometry.Topology.Connected.TwoSided

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifold.exists_connected_neighborhood_pair_sdiff
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 2 L) (hdim : Module.finrank ℝ E = 3)
    {p : E} (hp : p ∈ L.space) {U : Set E} (hU : U ∈ 𝓝 p) :
    ∃ C ∈ 𝓝 p, C ⊆ U ∧
      ∃ A B : Set E, IsConnected A ∧ IsConnected B ∧ A ∪ B = C \ L.space ∧
        C ∩ L.space ⊆ closure A ∧ C ∩ L.space ⊆ closure B := by
  obtain ⟨T, hT, hTcard, hLT⟩ := exists_affineIndependent_openSimplex_superset 3 hdim
    (isPolyhedron_space L).isCompact.isBounded
  let K := simplexComplex T hT
  let _ : Finite K.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hKspace : K.space = convexHull ℝ (T : Set E) :=
    simplexComplex_space T hT (Finset.card_pos.mp (by omega))
  have hKball : IsPLBall 3 K.space := hKspace.symm ▸
    isPLBall_convexHull_of_affineIndependent T hT hTcard
  have hK := hKball.isCombinatorialManifoldWithBoundary
  have hint : interior K.space = openSimplex T := by
    rw [hKspace, interior_convexHull_eq_openSimplex hT (by omega)]
  have hLint : L.space ⊆ interior K.space := hLT.trans hint.symm.subset
  have hpB : p ∉ (boundaryComplex 3 K).space := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank hdim K hK]
    exact fun h => h.2 (hLint hp)
  obtain ⟨C, _, hCU, hCnhds, _, a, ha, b, hb, _, hunion, _, _, _, hinter⟩ :=
    hK.exists_isPLBall_neighborhood_pair_sdiff hL (hLint.trans interior_subset) hp hpB
      (nhdsWithin_le_nhds hU)
  rw [nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp (hLint hp))] at hCnhds
  refine ⟨C, hCnhds, hCU.trans inter_subset_right,
    connectedComponentIn (C \ L.space) a, connectedComponentIn (C \ L.space) b,
    isConnected_connectedComponentIn_iff.mpr ha, isConnected_connectedComponentIn_iff.mpr hb,
    hunion, hinter.symm.subset.trans inter_subset_left, hinter.symm.subset.trans inter_subset_right⟩

open Classical in
theorem IsCombinatorialManifold.exists_connectedComponentIn_pair_compl
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 2 L) (hdim : Module.finrank ℝ E = 3)
    (hconn : IsConnected L.space) :
    ∃ a ∈ L.spaceᶜ, ∃ b ∈ L.spaceᶜ,
      let A := connectedComponentIn L.spaceᶜ a
      let B := connectedComponentIn L.spaceᶜ b
      Disjoint A B ∧ A ∪ B = L.spaceᶜ ∧ closure A ∪ closure B = univ ∧
        closure A ∩ closure B = L.space ∧ frontier A = L.space ∧ frontier B = L.space := by
  let _ : LocallyConnectedSpace (univ : Set E) := isOpen_univ.locallyConnectedSpace
  have hsep : ¬IsPreconnected ((univ : Set E) \ L.space) := by
    simpa only [← compl_eq_univ_sdiff] using hL.not_isPreconnected_compl L hdim hconn.nonempty
  obtain ⟨a, ha, b, hb, hdis, hunion, hclunion, hinter⟩ :=
    Topology.exists_connectedComponentIn_pair_sdiff_of_local_separation isPreconnected_univ
      isClosed_univ hconn (isPolyhedron_space L).isClosed (subset_univ L.space)
      (fun p hp => by
        simpa only [nhdsWithin_univ] using
          hL.exists_connected_neighborhood_pair_sdiff L hdim hp Filter.univ_mem) hsep
  simp only [← compl_eq_univ_sdiff] at ha hb hdis hunion hclunion hinter
  have hfront (c : E) (hsub : L.space ⊆ closure (connectedComponentIn L.spaceᶜ c)) :
      frontier (connectedComponentIn L.spaceᶜ c) = L.space := by
    have hopen := (isPolyhedron_space L).isClosed.isOpen_compl.connectedComponentIn (x := c)
    rw [frontier, hopen.interior_eq]
    ext z
    constructor
    · rintro ⟨hz, hnot⟩
      by_contra hzL
      exact hnot ((Topology.closure_connectedComponentIn_inter L.spaceᶜ c).subset ⟨hz, hzL⟩)
    · intro hz
      exact ⟨hsub hz, fun hzC => connectedComponentIn_subset L.spaceᶜ c hzC hz⟩
  exact ⟨a, ha, b, hb, hdis, hunion, hclunion, hinter,
    hfront a (hinter.symm.subset.trans inter_subset_left),
    hfront b (hinter.symm.subset.trans inter_subset_right)⟩

open Classical in
theorem IsCombinatorialManifold.isTwoSided
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 2 L) (hdim : Module.finrank ℝ E = 3)
    (hconn : IsConnected L.space) : Topology.IsTwoSided L.space := by
  obtain ⟨a, _, b, _, hdis, hunion, _, hinter, _, _⟩ :=
    hL.exists_connectedComponentIn_pair_compl L hdim hconn
  let A := connectedComponentIn L.spaceᶜ a
  let B := connectedComponentIn L.spaceᶜ b
  have hAopen : IsOpen A := (isPolyhedron_space L).isClosed.isOpen_compl.connectedComponentIn
  have hBopen : IsOpen B := (isPolyhedron_space L).isClosed.isOpen_compl.connectedComponentIn
  intro x hx
  rw [hconn.isPreconnected.connectedComponentIn hx]
  refine ⟨univ, Filter.univ_mem, ?_⟩
  intro W hW _ _ hpre
  have hxW := mem_nhdsSet_iff_forall.mp hW x hx
  have hxAB := hinter.symm.subset hx
  obtain ⟨p, hpW, hpA⟩ := (mem_closure_iff_nhds.mp hxAB.1) W hxW
  obtain ⟨q, hqW, hqB⟩ := (mem_closure_iff_nhds.mp hxAB.2) W hxW
  have hAsub : A ⊆ L.spaceᶜ := connectedComponentIn_subset _ _
  have hBsub : B ⊆ L.spaceᶜ := connectedComponentIn_subset _ _
  obtain ⟨z, _, hzA, hzB⟩ := hpre A B hAopen hBopen
    (fun z hz => hunion.symm.subset hz.2)
    ⟨p, ⟨hpW, hAsub hpA⟩, hpA⟩ ⟨q, ⟨hqW, hBsub hqB⟩, hqB⟩
  exact disjoint_left.mp hdis hzA hzB

end DifferentialGeometry.Topology.PiecewiseLinear
