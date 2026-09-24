/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodPolygon
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodCoreBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusOnPolyhedralCylinder
import DifferentialGeometry.Topology.PiecewiseLinear.CircleHomotopy
import DifferentialGeometry.Topology.PiecewiseLinear.EssentialPolygonProductCoordinates
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCircleNeighborhood

/-! # Derived Neighborhood Circle Levels -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem carriesFundamentalGroupOnto_derivedNeighborhood
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] (hLK : L.faces ⊆ K.faces) :
    CarriesFundamentalGroupOnto L.space (derivedNeighborhood K L).space := by
  classical
  have hsub := subcomplex_space_subset_derivedNeighborhood hLK
  let H := derivedNeighborhoodHomotopyEquiv hLK
  let r := derivedNeighborhoodStrongDeformationRetract hLK
  refine ⟨hsub, fun hsub b => ?_⟩
  apply (bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse H
    (⟨inclusion hsub, continuous_inclusion hsub⟩ :
      C(L.space, (derivedNeighborhood K L).space)) ?_ b).2
  intro x
  apply Subtype.ext
  change ((r.retraction (inclusion hsub x) : (derivedNeighborhood K L).space) : E) = (x : E)
  exact congrArg Subtype.val (r.retraction_eq (x := inclusion hsub x) x.2)

open Classical in
theorem IsPLSphere.not_isPLBall_between_derivedNeighborhood
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] (hLK : L.faces ⊆ K.faces)
    (hL : IsPLSphere 1 L.space) {D : Set E} {n : ℕ}
    (hD : IsPLBall n D) (hLD : L.space ⊆ D)
    (hDN : D ⊆ (derivedNeighborhood K L).space) : False := by
  classical
  have : Finite L.faces := ((Set.toFinite K.faces).subset hLK).to_subtype
  let N := (derivedNeighborhood K L).space
  have hNconn : PathConnectedSpace N :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_derivedNeighborhood_space
      hLK hL.isConnected)
  have hDsc : SimplyConnectedSpace D := hD.simplyConnectedSpace
  have hc := carriesFundamentalGroupOnto_derivedNeighborhood hLK
  obtain ⟨b, hb⟩ := hL.isConnected.nonempty
  have hNsc : SimplyConnectedSpace N := by
    refine (simplyConnectedSpace_iff_fundamentalGroup_eq_one (⟨b, hc.1 hb⟩ : N)).mpr ?_
    intro g
    obtain ⟨a, rfl⟩ := hc.2 hc.1 ⟨b, hb⟩ g
    let iLD : C(L.space, D) := ⟨inclusion hLD, continuous_inclusion hLD⟩
    let iDN : C(D, N) := ⟨inclusion hDN, continuous_inclusion hDN⟩
    have he := DFunLike.congr_fun (fundamentalGroup_map_continuousMap_comp
      iLD iDN ⟨b, hb⟩) a
    rw [MonoidHom.comp_apply, Subsingleton.elim (FundamentalGroup.map iLD _ a) 1,
      map_one] at he
    exact he
  exact hL.not_simplyConnectedSpace_one
    (derivedNeighborhoodHomotopyEquiv hLK).symm.simplyConnectedSpace

open Classical in
theorem exists_isPLHomeomorphOn_annulus_derivedNeighborhood_circle_level
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hLK : L.faces ⊆ K.faces)
    (hL : IsPLSphere 1 L.space) (hor : IsOrientable 2 K) :
    ∃ (φ : (Fin 3 → ℝ) × ℝ → E) (t : ℝ),
      IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc 0 1) (derivedNeighborhood K L).space ∧
      t ∈ Ioo (0 : ℝ) 1 ∧ φ '' (stdSimplexBoundary 2 ×ˢ {t}) = L.space := by
  classical
  have : Finite L.faces := ((Set.toFinite K.faces).subset hLK).to_subtype
  have : Finite (derivedNeighborhood K L).faces :=
    (derivedNeighborhood_faces_finite K L).to_subtype
  obtain ⟨ψ, hψ⟩ := exists_isPLHomeomorphOn_annulus_derivedNeighborhood_circle K L
    hK.isCombinatorialManifoldWithBoundary hLK hL.isCombinatorialManifold hL.isConnected hor
  have : Finite (simplexBoundary (stdVertices 1) (stdVertices_affineIndependent 1)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have hJpoly : IsPolyhedron (stdSimplexBoundary 2) := by
    rw [← simplexBoundary_stdVertices_space 1]
    exact isPolyhedron_space _
  have hJstd : IsPLSphere 1 (stdSimplexBoundary 2) := ⟨id, hJpoly.isPLHomeomorphOn_id⟩
  have hbd := hψ.boundaryComplex_eq_annulus_ends hJstd zero_lt_one (derivedNeighborhood K L)
  have hcore := hK.disjoint_derivedNeighborhood_boundary K L hLK
  have hCR : L.space ⊆ (derivedNeighborhood K L).space \
      (ψ '' (stdSimplexBoundary 2 ×ˢ {0}) ∪ ψ '' (stdSimplexBoundary 2 ×ˢ {1})) := by
    intro x hx
    refine ⟨subcomplex_space_subset_derivedNeighborhood hLK hx, ?_⟩
    intro he
    apply disjoint_left.mp hcore hx
    rw [hbd, ← singleton_union, prod_union, image_union]
    exact he
  obtain ⟨φ, s, hφ, -, -, hlevel⟩ := hψ.exists_prism_levels_of_essential
    (C := {L.space}) (finite_singleton _) (by intro c hc; simpa using hc ▸ hL)
    (by intro c hc; simpa using hc ▸ hCR) (by
      intro c hc
      rw [mem_singleton_iff] at hc
      subst c
      rintro ⟨D, q, hq, hDN, hqb⟩
      apply hL.not_isPLBall_between_derivedNeighborhood hLK (⟨q, hq⟩ : IsPLBall 2 D) ?_ hDN
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hqb.symm.subset hx
      exact hq.bijOn.mapsTo hy.1)
    (subsingleton_singleton.pairwise _)
  exact ⟨φ, s L.space, hφ, hlevel L.space (mem_singleton _)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
