/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.FundamentalGroup.SimplyConnected
import DifferentialGeometry.Topology.Connected.PhragmenBrouwer
import DifferentialGeometry.Topology.PiecewiseLinear.NullhomotopyNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSimplyConnected
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusCapping

/-!
# Compression and essential loops on closed surfaces
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifold.exists_neighborhood_nontrivial_fundamentalGroup_kernel
    {n : ℕ} (hdim : Module.finrank ℝ E = n + 1)
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 2 L) (hconn : IsConnected L.space)
    (hnot : ¬ IsPLSphere 2 L.space) {U : Set E} (hU : IsOpen U)
    (hLU : L.space ⊆ U) [SimplyConnectedSpace U] (x : L.space) :
    ∃ g : FundamentalGroup L.space x, g ≠ 1 ∧
      ∃ N : Geometry.SimplicialComplex ℝ E, N.faces.Finite ∧
        IsCombinatorialManifoldWithBoundary (n + 1) N ∧ N.space ⊆ U ∧
        L.space ⊆ N.space \ (boundaryComplex (n + 1) N).space ∧
        ∀ hLN : L.space ⊆ N.space,
          FundamentalGroup.map (⟨Set.inclusion hLN, continuous_inclusion hLN⟩ :
            C(L.space, N.space)) x g = 1 := by
  let _ : PathConnectedSpace L.space := isPathConnected_iff_pathConnectedSpace.mp
    (SimplicialComplex.isPathConnected_geometricSpace L hconn)
  have hnot' : ¬ SimplyConnectedSpace L.space := by
    intro h
    let _ := h
    exact hnot (hL.isPLSphere_two_of_simplyConnectedSpace L)
  obtain ⟨g, hg⟩ := exists_fundamentalGroup_ne_one_of_not_simplyConnectedSpace hnot' x
  obtain ⟨N, hNfin, hN, hLN, hNU, hmap⟩ :=
    exists_neighborhood_fundamentalGroup_map_eq_one_of_simplyConnectedSpace
      hdim (isPolyhedron_space L).isCompact hU hLU x g
  let _ := hNfin.to_subtype
  refine ⟨g, hg, N, hNfin, hN, hNU, ?_, hmap⟩
  intro y hy
  refine ⟨interior_subset (hLN hy), ?_⟩
  rw [← frontier_space_eq_boundaryComplex_space_of_finrank hdim N hN]
  exact fun hfront => hfront.2 (hLN hy)

open Classical in
theorem IsCombinatorialManifold.exists_separating_surface_bettiOne_lt_of_annulus_capping
    (K R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite R.faces]
    (hK : IsCombinatorialManifold 2 K) (hKc : IsConnected K.space)
    (hdim : Module.finrank ℝ E = 3) (hR : IsCombinatorialManifoldWithBoundary 2 R)
    {J W : Set E} (hJ : IsPLSphere 1 J) (hJK : J ⊆ K.space) {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W)
    (hzero : ∀ x ∈ J, ρ (x, 0) = x) (hWnhds : W ∈ 𝓝ˢ[K.space] J)
    (hcover : W ∪ R.space = K.space)
    (htrace : W ∩ R.space = ρ '' (J ×ˢ {(-1 : ℝ), 1}))
    (hboundary : (boundaryComplex 2 R).space = ρ '' (J ×ˢ {(-1 : ℝ), 1}))
    (hnon : ¬ (⟨Set.inclusion hJK, continuous_inclusion hJK⟩ : C(J, K.space)).Nullhomotopic)
    {D₀ D₁ : Set E} {r₀ r₁ : (Fin 3 → ℝ) → E}
    (hr₀ : IsPLHomeomorphOn r₀ (stdSimplex ℝ (Fin 3)) D₀)
    (hr₁ : IsPLHomeomorphOn r₁ (stdSimplex ℝ (Fin 3)) D₁) (hdis : Disjoint D₀ D₁)
    (hmeet₀ : R.space ∩ D₀ = r₀ '' stdSimplexBoundary 2)
    (hmeet₁ : R.space ∩ D₁ = r₁ '' stdSimplexBoundary 2)
    (hbd₀ : r₀ '' stdSimplexBoundary 2 = ρ '' (J ×ˢ {(-1 : ℝ)}))
    (hbd₁ : r₁ '' stdSimplexBoundary 2 = ρ '' (J ×ˢ {(1 : ℝ)}))
    {H T : Set E} (hH : IsPreconnected H) (hT : IsPreconnected T)
    (hsep : Separates (R.space ∪ D₀ ∪ D₁) H T) :
    ∃ (P : Geometry.SimplicialComplex ℝ E) (hPfin : P.faces.Finite),
      letI := hPfin.to_subtype
      IsCombinatorialManifold 2 P ∧ IsConnected P.space ∧ IsOrientable 2 P ∧
      IsTwoSided P.space ∧ P.space ⊆ R.space ∪ D₀ ∪ D₁ ∧ Separates P.space H T ∧
      Homology.bettiOne P.space < Homology.bettiOne K.space := by
  by_cases hcircle : IsPreconnected (K.space \ J)
  · have hRc := Topology.isConnected_complement_of_bicollar hJ.isConnected
      hJ.isPolyhedron.isCompact (isPolyhedron_space R).isClosed
      (by rwa [union_comm]) (by rwa [inter_comm])
      hρ.isPiecewiseAffineOn.continuousOn hρ.bijOn hzero hcircle
    obtain ⟨P, hPfin, hP, hPc, hPo, -, -, hβ, hPspace⟩ :=
      hK.exists_capped_annulus_complement K R hKc hdim hR hRc hJ
        (by norm_num : (-1 : ℝ) < 1) hρ hcover htrace hboundary
        hr₀ hr₁ hdis hmeet₀ hmeet₁ hbd₀ hbd₁
    let _ : Finite P.faces := hPfin.to_subtype
    exact ⟨P, hPfin, hP, hPc, hPo, hP.isTwoSided P hdim hPc,
      hPspace.subset, hPspace.symm ▸ hsep, hβ⟩
  · obtain ⟨P, Q, hPfin, hQfin, hP, hQ, hPc, hQc, hPo, hQo, -, -, hPQ, -, -, hPβ, hQβ,
        hPQspace⟩ := hK.exists_capped_pair_of_separating_essential_annulus K R hKc hdim hR
      hJ hJK hρ hzero hWnhds hcover htrace hboundary hcircle hnon
      hr₀ hr₁ hdis hmeet₀ hmeet₁ hbd₀ hbd₁
    let _ : Finite P.faces := hPfin.to_subtype
    let _ : Finite Q.faces := hQfin.to_subtype
    rcases phragmen_brouwer (isPolyhedron_space P).isClosed (isPolyhedron_space Q).isClosed
      hPQ hH hT (hPQspace.symm ▸ hsep) with hPsep | hQsep
    · exact ⟨P, hPfin, hP, hPc, hPo, hP.isTwoSided P hdim hPc,
        subset_union_left.trans hPQspace.subset, hPsep, hPβ⟩
    · exact ⟨Q, hQfin, hQ, hQc, hQo, hQ.isTwoSided Q hdim hQc,
        subset_union_right.trans hPQspace.subset, hQsep, hQβ⟩

end DifferentialGeometry.Topology.PiecewiseLinear
