/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskMove
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscut

open Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise
  (Plane standardTrianglePosition standardTrianglePosition_affineIndependent)

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPLHomeomorphOn_map_disk_eqOn_boundary
    {D A B : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hA : IsPLBall 2 A) (hB : IsPLBall 2 B)
    (hAD : A ⊆ D \ r '' stdSimplexBoundary 2)
    (hBD : B ⊆ D \ r '' stdSimplexBoundary 2) :
    ∃ G : E → E, IsPLHomeomorphOn G D D ∧ G '' A = B ∧
      EqOn G id (r '' stdSimplexBoundary 2) := by
  classical
  let T : Set Plane := convexHull ℝ (range standardTrianglePosition)
  have hT : IsPLBall 2 T := isPLBall_two_of_isTriangle
    ⟨standardTrianglePosition, standardTrianglePosition_affineIndependent, rfl⟩
  obtain ⟨t, ht⟩ := hT
  have hT : IsPLBall 2 T := ⟨t, ht⟩
  let φ := t ∘ Function.invFunOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
  have hφ : IsPLHomeomorphOn φ D T := hr.symm.trans ht
  have hφJ : φ '' (r '' stdSimplexBoundary 2) = frontier T := by
    rw [image_image]
    exact (hr.trans hφ).image_stdSimplexBoundary
  have hJ : r '' stdSimplexBoundary 2 ⊆ D :=
    (image_mono (fun _ hx => hx.1)).trans hr.image_eq.subset
  have hsub {C : Set E} (hCD : C ⊆ D \ r '' stdSimplexBoundary 2) :
      φ '' C ⊆ interior T := by
    rintro _ ⟨x, hx, rfl⟩
    apply (mem_interior_iff_notMem_frontier (hφ.bijOn.mapsTo (hCD hx).1)).mpr
    intro hxfront
    obtain ⟨y, hy, heq⟩ := hφJ.symm ▸ hxfront
    exact (hCD hx).2 ((hφ.bijOn.injOn (hJ hy) (hCD hx).1 heq) ▸ hy)
  have hA' := hA.of_isPLHomeomorphOn (hφ.restrict hA.isPolyhedron (hAD.trans sdiff_subset))
  have hB' := hB.of_isPLHomeomorphOn (hφ.restrict hB.isPolyhedron (hBD.trans sdiff_subset))
  obtain ⟨g, hg, hgfix, hgA⟩ := exists_isPLHomeomorphOn_map_disk_eqOn_compl hA' hB'
    isOpen_interior hT.isConnected_interior.isPreconnected (hsub hAD) (hsub hBD)
  have hgT : g '' T = T := by
    have hU : g '' (interior T)ᶜ = (interior T)ᶜ := hgfix.image_eq.trans (image_id _)
    have hI : g '' interior T = interior T := by
      have h := g.image_compl (interior T)ᶜ
      simpa only [compl_compl, hU] using h
    rw [← hT.closure_interior, g.image_closure, hI]
  have hgr : IsPLHomeomorphOn g T T := by
    have h := hg.restrict hT.isPolyhedron (subset_univ T)
    rwa [hgT] at h
  let G := Function.invFunOn φ D ∘ g ∘ φ
  have hG : IsPLHomeomorphOn G D D := (hφ.trans hgr).trans hφ.symm
  refine ⟨G, hG, ?_, ?_⟩
  · change (Function.invFunOn φ D ∘ g ∘ φ) '' A = B
    rw [image_comp, image_comp, hgA, image_image]
    have hInv : EqOn (Function.invFunOn φ D ∘ φ) id B :=
      fun x hx => hφ.bijOn.invOn_invFunOn.1 (hBD hx).1
    exact hInv.image_eq.trans (image_id B)
  · intro x hx
    change Function.invFunOn φ D (g (φ x)) = x
    have hxf : φ x ∈ frontier T := hφJ ▸ mem_image_of_mem φ hx
    rw [hgfix hxf.2]
    exact hφ.bijOn.invOn_invFunOn.1 (hJ hx)

end DifferentialGeometry.Topology.PiecewiseLinear
