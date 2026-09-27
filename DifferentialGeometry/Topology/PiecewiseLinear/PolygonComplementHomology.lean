/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.Algebra.FreeModuleCancellation
import DifferentialGeometry.Topology.Homology.FirstHomologyProduct
import DifferentialGeometry.Topology.Homology.MayerVietorisProduct
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereTopHomology
import DifferentialGeometry.Topology.PiecewiseLinear.CircleSolidTorus
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRayEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsGeneralPositionSolidTorusRelative
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusInteriorHomology
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Analysis.Normed.Module.Connected

open Set Topology
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "C2" => Metric.sphere (0 : E2) 1

private theorem exists_circle_subcomplex_in_ball {G : Set E3} (hG : IsPLSphere 1 G) :
    ∃ R C : Geometry.SimplicialComplex ℝ E3, R.faces.Finite ∧ C.faces.Finite ∧
      IsPLBall 3 R.space ∧ C.faces ⊆ R.faces ∧ C.space = G ∧ C.space ⊆ interior R.space := by
  classical
  have hdim : Module.finrank ℝ E3 = 3 := by simp
  obtain ⟨L, hLfin, hLsp⟩ := hG.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  obtain ⟨T, hT, hTcard, hGT⟩ := exists_affineIndependent_openSimplex_superset 3 hdim
    hG.isPolyhedron.isCompact.isBounded
  let K := simplexComplex T hT
  let _ : Finite K.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hKsp : K.space = convexHull ℝ (T : Set E3) :=
    simplexComplex_space T hT (Finset.card_pos.mp (by omega))
  have hKball : IsPLBall 3 K.space := hKsp.symm ▸
    isPLBall_convexHull_of_affineIndependent T hT hTcard
  have hGK : G ⊆ interior K.space := by
    rw [hKsp, interior_convexHull_eq_openSimplex hT (by omega)]
    exact hGT
  have hLK : L.space ⊆ K.space := hLsp.subset.trans (hGK.trans interior_subset)
  obtain ⟨R, hRfin, hRsp, -, hRL⟩ := exists_simplicialComplex_space_union K L
  let _ : Finite R.faces := hRfin.to_subtype
  have hRspace : R.space = K.space := hRsp.trans (union_eq_self_of_subset_right hLK)
  have hRball : IsPLBall 3 R.space := hRspace.symm ▸ hKball
  let C := restrict R L.space
  let _ : Finite C.faces := (restrict_faces_finite R L.space).to_subtype
  have hCsp : C.space = G := hRL.space_eq.trans hLsp
  refine ⟨R, C, hRfin, restrict_faces_finite R L.space, hRball,
    restrict_faces_subset R L.space, hCsp, ?_⟩
  rw [hCsp, hRspace]
  exact hGK

private theorem exists_circle_neighborhood_product {G : Set E3} (hG : IsPLSphere 1 G) :
    ∃ N : Set E3, IsTopologicalSolidTorus N ∧ IsClosed N ∧ G ⊆ interior N ∧
      Nonempty ((frontier N × Ioo (0 : ℝ) 1) ≃ₜ ↥(interior N \ G)) := by
  classical
  let _ : DecidableEq E3 := Classical.decEq E3
  obtain ⟨R, C, hRfin, hCfin, hRball, hCR, hCsp, hCint⟩ :=
    exists_circle_subcomplex_in_ball hG
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite C.faces := hCfin.to_subtype
  have hC : IsPLSphere 1 C.space := hCsp.symm ▸ hG
  obtain ⟨f, hf, hends⟩ := exists_cylindricalDiagram_derivedNeighborhood_circle_eq_ends
    R C hRball.isCombinatorialManifoldWithBoundary hCR
    hC.isCombinatorialManifold hC.isConnected (isOrientable_of_isPLBall hRball)
  let N := derivedNeighborhood R C
  let _ : Finite N.faces := (derivedNeighborhood_faces_finite R C).to_subtype
  have hNR : N.space ⊆ interior R.space := derivedNeighborhood_space_subset_interior
    (by simp) hRball.isCombinatorialManifoldWithBoundary hCR hCint
  refine ⟨N.space, hf.isTopologicalSolidTorus_of_eq_ends (isPLBall_stdSimplex 2) hends,
    (isPolyhedron_space N).isClosed, ?_, ?_⟩
  · intro x hx
    have hRx : R.space ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp (hCint (hCsp.symm.subset hx))
    have hNx := derivedNeighborhood_mem_nhdsWithin hCR (hCsp.symm.subset hx)
    rw [nhdsWithin_eq_nhds.mpr hRx] at hNx
    exact mem_interior_iff_mem_nhds.mpr hNx
  · have he := nonempty_homeomorph_derivedNeighborhood_interior_sdiff_of_subset_interior
      R C hCR hNR
    rwa [hCsp] at he

private theorem nonempty_firstHomology_interior_equiv_int {S : Set E3}
    (hS : IsTopologicalSolidTorus S) :
    Nonempty (integralSingularHomology 1 (interior S) ≃ₗ[ℤ] ℤ) := by
  obtain ⟨φ⟩ := hS
  let D := Metric.closedBall (0 : E2) 1
  let p : D := ⟨0, by simp [D]⟩
  let e : S ≃ₕ C2 := φ.toHomotopyEquiv.trans
    ((Homeomorph.prodComm D C2).toHomotopyEquiv.trans
      (DifferentialGeometry.HomotopyEquiv.productConvex C2 (convex_closedBall _ _) p))
  let i : C(interior S, S) := ⟨inclusion interior_subset, continuous_inclusion interior_subset⟩
  let q : C(interior S, C2) := e.toFun.comp i
  let j : C(C2, interior S) :=
    ⟨fun θ => ⟨φ.symm (p, θ),
      mem_interior_of_homeomorph_closedBall_prod_sphere φ p θ (by simp [p])⟩,
      (continuous_subtype_val.comp (φ.symm.continuous.comp
        (continuous_const.prodMk continuous_id))).subtype_mk _⟩
  have hqi : Function.Injective (integralSingularHomologyMap 1 q) := by
    intro a b hab
    apply IsTopologicalSolidTorus.integralSingularHomologyMap_interior_injective ⟨φ⟩
    apply (integralSingularHomologyHomotopyEquiv 1 e).injective
    change integralSingularHomologyMap 1 e.toFun (integralSingularHomologyMap 1 i a) =
      integralSingularHomologyMap 1 e.toFun (integralSingularHomologyMap 1 i b)
    simpa only [q, integralSingularHomologyMap_comp, LinearMap.comp_apply] using hab
  have hqj : q.comp j = ContinuousMap.id C2 := by
    apply ContinuousMap.ext
    intro θ
    change (φ (φ.symm (p, θ))).2 = θ
    rw [φ.apply_symm_apply]
  have hqs : Function.Surjective (integralSingularHomologyMap 1 q) := by
    intro a
    refine ⟨integralSingularHomologyMap 1 j a, ?_⟩
    rw [← LinearMap.comp_apply, ← integralSingularHomologyMap_comp, hqj,
      integralSingularHomologyMap_id, LinearMap.id_apply]
  exact ⟨(LinearEquiv.ofBijective (integralSingularHomologyMap 1 q) ⟨hqi, hqs⟩).trans
    (integralSphereTopHomologyEquiv 0 E2 (by simp))⟩

private theorem nonempty_firstHomology_frontier_equiv_int_prod {S : Set E3}
    (hS : IsTopologicalSolidTorus S) (hSc : IsClosed S) :
    Nonempty (integralSingularHomology 1 (frontier S) ≃ₗ[ℤ] (ℤ × ℤ)) := by
  obtain ⟨e⟩ := hS.nonempty_homeomorph_frontier hSc
  let _ : PathConnectedSpace C2 := isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_sphere (by simp [← Module.finrank_eq_rank]) 0 zero_le_one)
  let q := integralSphereTopHomologyEquiv 0 E2 (by simp)
  exact ⟨(((integralSingularHomologyHomotopyEquiv 1 e.toHomotopyEquiv).toAddEquiv.trans
    integralSingularHomologyOneProdEquiv.toAddEquiv).trans
      (q.toAddEquiv.prodCongr q.toAddEquiv)).toIntLinearEquiv⟩

namespace TorusLinking

theorem nonempty_firstHomology_complement_addEquiv_int
    {G : Set (EuclideanSpace ℝ (Fin 3))} (hG : IsPLSphere 1 G) :
    Nonempty (integralSingularHomology 1 (Gᶜ : Set (EuclideanSpace ℝ (Fin 3))) ≃+ ℤ) := by
  obtain ⟨N, hN, hNc, hGN, ⟨e⟩⟩ := exists_circle_neighborhood_product hG
  obtain ⟨eI⟩ := nonempty_firstHomology_interior_equiv_int hN
  obtain ⟨eT⟩ := nonempty_firstHomology_frontier_equiv_int_prod hN hNc
  let p : Ioo (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩
  let q : (interior N ∩ Gᶜ : Set E3) ≃ₕ frontier N := e.symm.toHomotopyEquiv.trans
    (DifferentialGeometry.HomotopyEquiv.productConvex (frontier N) (convex_Ioo 0 1) p)
  let eQ : integralSingularHomology 1 (interior N ∩ Gᶜ : Set E3) ≃ₗ[ℤ] (ℤ × ℤ) :=
    (integralSingularHomologyHomotopyEquiv 1 q).trans eT
  have hcover : interior N ∪ Gᶜ = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ G
    · exact Or.inl (hGN hx)
    · exact Or.inr hx
  have hbij := bijective_integralSingularHomologyMap_intersection isOpen_interior
    hG.isPolyhedron.isClosed.isOpen_compl hcover 1
    (integralSingularHomology_subsingleton_of_contractible 1 one_ne_zero E3)
    (integralSingularHomology_subsingleton_of_contractible 2 (by omega) E3)
  let f : integralSingularHomology 1 (interior N ∩ Gᶜ : Set E3) →+
      integralSingularHomology 1 (interior N) × integralSingularHomology 1 (Gᶜ : Set E3) :=
    (integralSingularHomologyMap 1
      (⟨inclusion inter_subset_left, continuous_inclusion inter_subset_left⟩ :
        C((interior N ∩ Gᶜ : Set E3), interior N))).toAddMonoidHom.prod
      (integralSingularHomologyMap 1
        (⟨inclusion inter_subset_right, continuous_inclusion inter_subset_right⟩ :
          C((interior N ∩ Gᶜ : Set E3), (Gᶜ : Set E3)))).toAddMonoidHom
  let eMV := AddEquiv.ofBijective f hbij
  let eProd : (ℤ × integralSingularHomology 1 (Gᶜ : Set E3)) ≃ₗ[ℤ] (ℤ × ℤ) :=
    (((eI.toAddEquiv.symm.prodCongr (AddEquiv.refl _)).trans eMV.symm).trans
      eQ.toAddEquiv).toIntLinearEquiv
  obtain ⟨eH⟩ := DifferentialGeometry.nonempty_linearEquiv_of_prod_equiv_of_pid
    (R := ℤ) (M := ℤ) (P := ℤ) eProd.toAddEquiv.toIntLinearEquiv
  exact ⟨eH.toAddEquiv⟩

end TorusLinking

end DifferentialGeometry.Topology.PiecewiseLinear
