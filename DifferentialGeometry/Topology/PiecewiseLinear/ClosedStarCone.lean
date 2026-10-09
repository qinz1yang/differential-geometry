/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConeSlab
import DifferentialGeometry.Topology.PiecewiseLinear.ConeManifold
import DifferentialGeometry.Topology.PiecewiseLinear.ClosedStarFiber
import DifferentialGeometry.Topology.PiecewiseLinear.SlabFiberInterior
import DifferentialGeometry.Topology.PiecewiseLinear.BallRegularClosed
import DifferentialGeometry.Topology.SlabBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCombinatorialManifoldWithBoundary.isPLBall_closedStar {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {p : E} (hp : {p} ∈ K.faces) :
    IsPLBall (n + 1) (closedStar K p) := by
  classical
  let _ : Finite (SimplicialComplex.geometricLink K {p}).faces :=
    ((Set.toFinite K.faces).subset (SimplicialComplex.geometricLink_le K {p})).to_subtype
  rw [closedStar_eq_coneComplex_space K hp]
  rcases hK p hp with hL | hL
  · exact (isConeBase_geometricLink K).isPLBall_of_isPLSphere hL
  · exact (isConeBase_geometricLink K).isPLBall_of_isPLBall hL

open Classical in
theorem exists_isPLBall_coneComplex_eq_closedStar_slab
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hdim : Module.finrank ℝ E = 3)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {p : E} (hp : {p} ∈ K.faces) {b : ℝ} (hpb : ℓ p < b)
    (hgap : ∀ v ∈ K.vertices, v ≠ p → ℓ v < ℓ p ∨ b < ℓ v)
    (hD : IsPLBall 2 (K.space ∩ {x | ℓ x = ℓ p}))
    (hS : IsPLSphere 2 (frontier (closedStar K p ∩ ℓ ⁻¹' Icc (ℓ p) b))) :
    ∃ (L : Geometry.SimplicialComplex ℝ E) (hL : IsConeBase p L), L.faces.Finite ∧
      IsPLBall 2 L.space ∧ (coneComplex hL).space = closedStar K p ∩ ℓ ⁻¹' Icc (ℓ p) b := by
  classical
  let B := SimplicialComplex.geometricLink K {p}
  let _ : Finite B.faces :=
    ((Set.toFinite K.faces).subset (SimplicialComplex.geometricLink_le K {p})).to_subtype
  obtain ⟨L, hL, hLfin, -, hcone⟩ :=
    (isConeBase_geometricLink K (p := p)).exists_coneComplex_inter_slab
      ℓ.toLinearMap.toAffineMap hpb
  let _ : Finite L.faces := hLfin.to_subtype
  have heq : (coneComplex hL).space = closedStar K p ∩ ℓ ⁻¹' Icc (ℓ p) b := by
    rw [closedStar_eq_coneComplex_space K hp]
    exact hcone
  let A := starComplex K p
  let _ : Finite A.faces := (starComplex_faces_finite K p).to_subtype
  have hAspace : A.space = closedStar K p := starComplex_space K p hp
  have hstar : IsPLBall 3 (closedStar K p) := hK.isPLBall_closedStar hp
  have hAreg : closure (interior A.space) = A.space := by
    rw [hAspace]
    exact hstar.closure_interior_of_finrank hdim
  have hAD : IsPLBall 2 (A.space ∩ {x | ℓ.toLinearMap x = ℓ.toLinearMap p}) := by
    rw [hAspace]
    exact isPLBall_closedStar_inter_fiber K hp ℓ.toLinearMap hD
  have hreg : closure (interior (closedStar K p ∩ ℓ ⁻¹' Icc (ℓ p) b)) =
      closedStar K p ∩ ℓ ⁻¹' Icc (ℓ p) b := by
    have h := closure_interior_space_inter_slab_of_isPLBall_fiber A hAreg ℓ.toLinearMap
      (hinj.mono (fun _ hv => starComplex_faces_subset K p hv)) hpb ⟨le_rfl, hpb.le⟩
      (fun v hv => hgap v (starComplex_faces_subset K p hv)) hAD
    rwa [hAspace] at h
  have hpstar : p ∈ closedStar K p := by
    rw [closedStar_eq_coneComplex_space K hp]
    exact apex_mem_coneComplex_space (isConeBase_geometricLink K)
  have hpfront : p ∈ frontier (closedStar K p ∩ ℓ ⁻¹' Icc (ℓ p) b) := by
    rw [Topology.frontier_inter_preimage_Icc_of_ne_zero hstar.isPolyhedron.isClosed ℓ hℓ hpb.le]
    exact Or.inr ⟨hpstar, by simp⟩
  refine ⟨L, hL, hLfin, ?_, heq⟩
  apply hL.isPLBall_of_isPLSphere_frontier hdim
  · rwa [heq]
  · rwa [heq]
  · rwa [heq]

end DifferentialGeometry.Topology.PiecewiseLinear
