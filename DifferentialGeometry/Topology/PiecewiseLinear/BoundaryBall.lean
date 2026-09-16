import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.ConvexCone
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPLBall_subset_inter_frontier {n : ℕ}
    (hn : Module.finrank ℝ E = n + 1) {C D : Set E}
    (hC : IsPLBall (n + 1) C) (hD : IsPLBall n D) (hDC : D ⊆ frontier C) :
    ∃ Q : Set E, IsPLBall (n + 1) Q ∧ Q ⊆ C ∧ Q ∩ frontier C = D ∧ D ⊆ frontier Q := by
  classical
  obtain ⟨T, hT, hcard, -, -, hRn⟩ :=
    exists_affineIndependent_openSimplex_subset hn (0 : E) Filter.univ_mem
  let R := convexHull ℝ (T : Set E)
  have hR : IsPLBall (n + 1) R := isPLBall_convexHull_of_affineIndependent T hT hcard
  have hRi : (0 : E) ∈ interior R := mem_interior_iff_mem_nhds.mpr hRn
  have hRc : IsClosed R := hR.isPolyhedron.isClosed
  have hCc : IsClosed C := hC.isPolyhedron.isClosed
  obtain ⟨u, hu⟩ := hR
  obtain ⟨v, hv⟩ := hC
  let f := v ∘ Function.invFunOn u (stdSimplex ℝ (Fin (n + 2)))
  have hf : IsPLHomeomorphOn f R C := hu.symm.trans hv
  let g := Function.invFunOn f R
  have hD0 : IsPLBall n (g '' D) :=
    hD.of_isPLHomeomorphOn (hf.symm.restrict hD.isPolyhedron (hDC.trans hCc.frontier_subset))
  have hgfront : g '' frontier C = frontier R := IsPLHomeomorphOn.image_frontier hf.symm rfl hCc hRc
  have hD0R : g '' D ⊆ frontier R := hgfront ▸ image_mono hDC
  obtain ⟨L, hLfin, hLspace⟩ := hD0.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  have hLR : L.space ⊆ frontier R := hLspace ▸ hD0R
  let hpL := isConeBase_of_space_subset_frontier_convex (convex_convexHull ℝ _) hRc hRi L hLR
  have hcone : IsPLBall (n + 1) (coneComplex hpL).space :=
    hpL.isPLBall_of_isPLBall (hLspace.symm ▸ hD0)
  have hconeR : (coneComplex hpL).space ⊆ R :=
    coneComplex_space_subset_convex (convex_convexHull ℝ _) (interior_subset hRi) hpL
      (hLR.trans hRc.frontier_subset)
  have hconefront : (coneComplex hpL).space ∩ frontier R = L.space :=
    coneComplex_space_inter_frontier (convex_convexHull ℝ _) hRc hRi hpL hLR
  let Q := f '' (coneComplex hpL).space
  have hQ : IsPLBall (n + 1) Q :=
    hcone.of_isPLHomeomorphOn (hf.restrict hcone.isPolyhedron hconeR)
  have hQC : Q ⊆ C := (image_mono hconeR).trans hf.image_eq.le
  have hmeet : Q ∩ frontier C = D := by
    rw [← IsPLHomeomorphOn.image_frontier hf rfl hRc hCc,
      ← hf.bijOn.injOn.image_inter hconeR hRc.frontier_subset, hconefront, hLspace, image_image]
    have hfix : EqOn (f ∘ g) id D :=
      fun x hx => hf.bijOn.invOn_invFunOn.2 (hCc.frontier_subset (hDC hx))
    exact hfix.image_eq.trans (image_id _)
  refine ⟨Q, hQ, hQC, hmeet, ?_⟩
  intro x hx
  have hxQ : x ∈ Q := (hmeet.symm ▸ hx).1
  have hxC : x ∈ frontier C := hDC hx
  exact ⟨subset_closure hxQ, fun h => hxC.2 (interior_mono hQC h)⟩

theorem exists_isPLBall_inter_frontier_eq_of_subset {n : ℕ}
    (hn : Module.finrank ℝ E = n + 1) {M C D : Set E}
    (hC : IsPLBall (n + 1) C) (hCM : C ⊆ M) (hD : IsPLBall n D)
    (hDC : D ⊆ C) (hDM : D ⊆ frontier M) :
    ∃ Q : Set E, IsPLBall (n + 1) Q ∧ Q ⊆ M ∧ Q ∩ frontier M = D ∧ D ⊆ frontier Q := by
  have hfront : C ∩ frontier M ⊆ frontier C := by
    rintro x ⟨hxC, hxM⟩
    exact ⟨subset_closure hxC, fun hx => hxM.2 (interior_mono hCM hx)⟩
  obtain ⟨Q, hQ, hQC, hQD, hDQ⟩ := exists_isPLBall_subset_inter_frontier hn hC hD
    (fun x hx => hfront ⟨hDC hx, hDM hx⟩)
  refine ⟨Q, hQ, hQC.trans hCM, ?_, hDQ⟩
  apply Subset.antisymm
  · rintro x ⟨hxQ, hxM⟩
    exact hQD ▸ ⟨hxQ, hfront ⟨hQC hxQ, hxM⟩⟩
  · intro x hx
    exact ⟨(hQD.symm ▸ hx).1, hDM hx⟩

open Classical in
theorem exists_nhdsWithin_boundary_disk_balls {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + 1)))) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ frontier K.space) :
    ∃ U : Set (EuclideanSpace ℝ (Fin (n + 1))), U ∈ 𝓝[K.space] x ∧
      ∀ D : Set (EuclideanSpace ℝ (Fin (n + 1))), IsPLBall n D → D ⊆ U →
        D ⊆ frontier K.space →
        ∃ Q : Set (EuclideanSpace ℝ (Fin (n + 1))), IsPLBall (n + 1) Q ∧ Q ⊆ K.space ∧
          Q ∩ frontier K.space = D ∧ D ⊆ frontier Q := by
  have hxB : x ∈ (@boundaryComplex _ _ _ (Classical.decEq _) (n + 1) K).space :=
    frontier_space_eq_boundaryComplex_space hK ▸ hx
  obtain ⟨C, hC, hCK, hCn, -⟩ := exists_isPLBall_subset_inter_boundary K hK x hxB
  exact ⟨C, hCn, fun D hD hDC hDK =>
    exists_isPLBall_inter_frontier_eq_of_subset (by simp) hC hCK hD hDC hDK⟩

end DifferentialGeometry.Topology.PiecewiseLinear
