/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SubsurfaceInteriorComponent
import DifferentialGeometry.Topology.PiecewiseLinear.SeparatingPolygonDisk
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerSeams

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLTorus.boundsDiskIn_boundary_of_isPLSphere [d : DecidableEq E3]
    (R : Geometry.SimplicialComplex ℝ E3) [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary 2 R) {T : Set E3} (hT : IsPLTorus T)
    (hRT : R.space ⊆ T) (hB : IsPLSphere 1 (boundaryComplex 2 R).space) :
    boundsDiskIn (boundaryComplex 2 R).space T := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  obtain ⟨K, hKfin, hK, -, hKT⟩ := hT.exists_combinatorial_triangulation
  let _ : Finite K.faces := hKfin.to_subtype
  have hKb : (boundaryComplex 2 K).space = ∅ := by
    rw [Geometry.SimplicialComplex.space, hK.boundaryComplex_faces_eq_empty K]
    simp
  have hmeet : R.space ∩ closure (T \ R.space) = (boundaryComplex 2 R).space := by
    simpa only [hKT] using inter_closure_sdiff_eq_boundaryComplex_of_disjoint_boundary K R
      hK.isCombinatorialManifoldWithBoundary hR (hRT.trans hKT.symm.subset)
      (by rw [hKb]; exact disjoint_empty _)
  have hBT := (boundaryComplex_space_subset 2 R).trans hRT
  apply hT.exists_isPLHomeomorphOn_disk_of_not_isPreconnected_sdiff hB hBT
  intro hpre
  have hcover : T \ (boundaryComplex 2 R).space ⊆ R.space ∪ closure (T \ R.space) := by
    intro x hx
    by_cases hxR : x ∈ R.space
    · exact Or.inl hxR
    · exact Or.inr (subset_closure ⟨hx.1, hxR⟩)
  have hemp : (T \ (boundaryComplex 2 R).space) ∩
      (R.space ∩ closure (T \ R.space)) = ∅ := by
    rw [hmeet]
    exact eq_empty_iff_forall_notMem.mpr fun _ hx => hx.1.2 hx.2
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hpre R.space
      (closure (T \ R.space)) (isPolyhedron_space R).isClosed isClosed_closure hcover hemp
      with hin | hout
  · obtain ⟨z, hz⟩ := hB.nonempty
    obtain ⟨x, hxT, hxR⟩ := closure_nonempty_iff.mp
      (show (closure (T \ R.space)).Nonempty from ⟨z, (hmeet.symm.subset hz).2⟩)
    exact hxR (hin ⟨hxT, fun hxB => hxR (boundaryComplex_space_subset 2 R hxB)⟩)
  · obtain ⟨z, hz⟩ := hB.nonempty
    obtain ⟨x, hxR, hxB⟩ := closure_nonempty_iff.mp
      (show (closure (R.space \ (boundaryComplex 2 R).space)).Nonempty from
        ⟨z, hR.space_subset_closure_sdiff_boundaryComplex_space
          (boundaryComplex_space_subset 2 R hz)⟩)
    exact hxB (hmeet.subset ⟨hxR, hout ⟨hRT hxR, hxB⟩⟩)

theorem IsCombinatorialManifoldWithBoundary.exists_annulus_of_essential_torus_boundary
    [d : DecidableEq E3] (R : Geometry.SimplicialComplex ℝ E3) [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary 2 R) (hconn : IsConnected R.space)
    {S : Set E3} (hS : IsCombinatorialSolidTorus S) (hRS : R.space ⊆ frontier S)
    (h286 : Moise286) (n : ℕ) (G : Fin n → Set E3) (hn : 0 < n)
    (hG : ∀ i, IsPLSphere 1 (G i)) (hdis : Pairwise fun i j => Disjoint (G i) (G j))
    (hboundary : (boundaryComplex 2 R).space = ⋃ i, G i)
    (hess : ∀ i, ¬ boundsDiskIn (G i) (frontier S)) :
    ∃ i j : Fin n, i ≠ j ∧ IsPLAnnulusWithEnds R.space (G i) (G j) := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  have hn2 : 1 < n := by
    by_contra hnot
    have hn1 : n = 1 := by omega
    subst n
    have hb : (boundaryComplex 2 R).space = G 0 := by
      rw [hboundary]
      refine Subset.antisymm ?_ (subset_iUnion G 0)
      intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      have hj0 : j = 0 := Subsingleton.elim _ _
      exact hj0 ▸ hj
    apply hess 0
    rw [← hb]
    exact hS.isPLTorus_frontier.boundsDiskIn_boundary_of_isPLSphere R hR hRS (hb.symm ▸ hG 0)
  have hGS (i : Fin n) : G i ⊆ frontier S :=
    ((subset_iUnion G i).trans hboundary.symm.subset).trans
      ((boundaryComplex_space_subset 2 R).trans hRS)
  obtain ⟨K, hKfin, hK, -, hKS⟩ := hS.isPLTorus_frontier.exists_combinatorial_triangulation
  let _ : Finite K.faces := hKfin.to_subtype
  have hKb : (boundaryComplex 2 K).space = ∅ := by
    rw [Geometry.SimplicialComplex.space, hK.boundaryComplex_faces_eq_empty K]
    simp
  obtain ⟨x, hx⟩ := (hR.isConnected_sdiff_boundaryComplex_space hconn).nonempty
  have hclosure : closure (connectedComponentIn (frontier S \ ⋃ i, G i) x) = R.space := by
    rw [← hboundary, ← hKS]
    exact hR.closure_connectedComponentIn_sdiff_boundaryComplex_eq K R
      hK.isCombinatorialManifoldWithBoundary hconn.isPreconnected (hRS.trans hKS.symm.subset)
      (by rw [hKb]; exact disjoint_empty _) hx
  obtain ⟨i, j, hij, hann⟩ := h286 S hS n G hn2 hG hGS hdis hess x
    ⟨hRS hx.1, by rw [← hboundary]; exact hx.2⟩
  exact ⟨i, j, hij, hclosure ▸ hann⟩

end DifferentialGeometry.Topology.PiecewiseLinear
