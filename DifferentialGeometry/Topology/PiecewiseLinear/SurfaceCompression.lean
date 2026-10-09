/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.FundamentalGroup.SimplyConnected
import DifferentialGeometry.Topology.Connected.PhragmenBrouwer
import DifferentialGeometry.Topology.Connected.ClosedCover
import DifferentialGeometry.Topology.PiecewiseLinear.NullhomotopyNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSimplyConnected
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusCapping
import DifferentialGeometry.Topology.Homotopy.FreeLoopNullhomotopy

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifold.exists_connected_neighborhood_nontrivial_fundamentalGroup_kernel
    {n : ℕ} (hdim : Module.finrank ℝ E = n + 1)
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 2 L) (hconn : IsConnected L.space)
    (hnot : ¬ IsPLSphere 2 L.space) {U : Set E} (hU : IsOpen U)
    (hLU : L.space ⊆ U) [SimplyConnectedSpace U] (x : L.space) :
    ∃ g : FundamentalGroup L.space x, g ≠ 1 ∧
      ∃ N : Geometry.SimplicialComplex ℝ E, N.faces.Finite ∧
        IsCombinatorialManifoldWithBoundary (n + 1) N ∧ IsConnected N.space ∧ N.space ⊆ U ∧
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
  obtain ⟨N, hNfin, hN, hNc, hLN, hNU, hmap⟩ :=
    exists_connected_neighborhood_fundamentalGroup_map_eq_one
      hdim (isPolyhedron_space L).isCompact hconn hU hLU x g (Subsingleton.elim _ _)
  let _ := hNfin.to_subtype
  refine ⟨g, hg, N, hNfin, hN, hNc, hNU, ?_, hmap⟩
  intro y hy
  refine ⟨interior_subset (hLN hy), ?_⟩
  rw [← frontier_space_eq_boundaryComplex_space_of_finrank hdim N hN]
  exact fun hfront => hfront.2 (hLN hy)

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
  obtain ⟨g, hg, N, hNfin, hN, _, hNU, hLN, hmap⟩ :=
    hL.exists_connected_neighborhood_nontrivial_fundamentalGroup_kernel
      hdim L hconn hnot hU hLU x
  exact ⟨g, hg, N, hNfin, hN, hNU, hLN, hmap⟩

theorem IsCombinatorialManifold.exists_essential_singular_disk_in_neighborhood
    {n : ℕ} (hdim : Module.finrank ℝ E = n + 1)
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 2 L) (hconn : IsConnected L.space)
    (hnot : ¬ IsPLSphere 2 L.space) {U : Set E} (hU : IsOpen U)
    (hLU : L.space ⊆ U) [SimplyConnectedSpace U] (x : L.space) :
    ∃ p : Path x x, Path.Homotopic.Quotient.mk p ≠ (1 : FundamentalGroup L.space x) ∧
      ∃ N : Geometry.SimplicialComplex ℝ E, N.faces.Finite ∧
        IsCombinatorialManifoldWithBoundary (n + 1) N ∧
        L.space ⊆ interior N.space ∧ N.space ⊆ U ∧
        (∀ hLN : L.space ⊆ N.space,
          FundamentalGroup.map (⟨Set.inclusion hLN, continuous_inclusion hLN⟩ :
            C(L.space, N.space)) x (Path.Homotopic.Quotient.mk p) = 1) ∧
        ∃ (P : Set (EuclideanSpace ℝ (Fin 2))) (f : EuclideanSpace ℝ (Fin 2) → E),
          IsPLBall 2 P ∧ IsPiecewiseAffineOn f P ∧ MapsTo f P (interior N.space) ∧
          ∃ (b : C(frontier P, L.space)) (e : loopCircle ≃ₜ frontier P),
            (∀ z : frontier P, f z = (b z : E)) ∧
            (pathToCircle p).Homotopic (b.comp (e : C(loopCircle, frontier P))) ∧
            ¬ b.Nullhomotopic := by
  obtain ⟨g, hg, -⟩ := hL.exists_neighborhood_nontrivial_fundamentalGroup_kernel
    hdim L hconn hnot hU hLU x
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective g
  let a : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 2) ℝ).symm
  let C := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  have ha : IsPLHomeomorphOn a C (a '' C) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isPLBall_unit_square.isPolyhedron
      ((isPiecewiseAffineOn_of_affine a.toLinearMap.toAffineMap isOpen_univ).mono_of_isPolyhedron
        isPLBall_unit_square.isPolyhedron (subset_univ _)) a.injective.injOn.bijOn_image
  have hP : IsPLBall 2 (a '' C) := isPLBall_unit_square.of_isPLHomeomorphOn ha
  obtain ⟨N, hNfin, hN, hLN, hNU, f, hf, hfN, b, e, htrace, hhom⟩ :=
    exists_neighborhood_isPiecewiseAffineOn_filling hdim L hU hLU hP (pathToCircle p)
  have hnon : ¬ b.Nullhomotopic := by
    intro hb
    have hnull := FreeLoop.nullhomotopic_of_homotopic hhom.symm (hb.comp_left
      (e : C(loopCircle, frontier (a '' C))))
    exact hg (Path.Homotopic.Quotient.eq.mpr ((pathToCircle_nullhomotopic_iff p).mp hnull))
  refine ⟨p, hg, N, hNfin, hN, hLN, hNU, ?_, a '' C, f, hP, hf, hfN,
    b, e, htrace, hhom, hnon⟩
  intro hLN'
  let i : C(L.space, N.space) := ⟨Set.inclusion hLN', continuous_inclusion hLN'⟩
  let F : C(a '' C, N.space) :=
    ⟨fun z => ⟨f z, interior_subset (hfN z.property)⟩, hf.continuousOn.domRestrict.subtype_mk _⟩
  let j : C(frontier (a '' C), a '' C) :=
    ⟨Set.inclusion hP.isPolyhedron.isClosed.frontier_subset, continuous_inclusion _⟩
  have hboundary : i.comp b = F.comp j := by
    ext z
    exact (htrace z).symm
  let _ := hP.contractibleSpace
  have hb : (i.comp b).Nullhomotopic := by
    rw [hboundary]
    exact ((id_nullhomotopic (a '' C)).comp_right F).comp_left j
  have hnull := FreeLoop.nullhomotopic_of_homotopic
    ((ContinuousMap.Homotopic.refl i).comp hhom).symm
    (by simpa only [ContinuousMap.comp_assoc] using
      (hb.comp_left (e : C(loopCircle, frontier (a '' C)))))
  rw [← pathToCircle_natural i x p] at hnull
  exact Path.Homotopic.Quotient.eq.mpr
    ((pathToCircle_nullhomotopic_iff (p.map i.continuous)).mp hnull)

open Classical in
theorem IsCombinatorialManifold.exists_separating_component_bettiOne_lt_of_annulus_capping
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
    (hr₀ : IsPLHomeomorphOn r₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀)
    (hr₁ : IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁) (hdis : Disjoint D₀ D₁)
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
      Homology.bettiOne P.space < Homology.bettiOne K.space ∧
      ∀ x ∈ P.space, connectedComponentIn (R.space ∪ D₀ ∪ D₁) x = P.space := by
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
    refine ⟨P, hPfin, hP, hPc, hPo, hP.isTwoSided P hdim hPc,
      hPspace.subset, hPspace.symm ▸ hsep, hβ, ?_⟩
    intro x hx
    rw [← hPspace]
    exact hPc.isPreconnected.connectedComponentIn hx
  · obtain ⟨P, Q, hPfin, hQfin, hP, hQ, hPc, hQc, hPo, hQo, -, -, hPQ, -, -, hPβ, hQβ,
        hPQspace⟩ := hK.exists_capped_pair_of_separating_essential_annulus K R hKc hdim hR
      hJ hJK hρ hzero hWnhds hcover htrace hboundary hcircle hnon
      hr₀ hr₁ hdis hmeet₀ hmeet₁ hbd₀ hbd₁
    let _ : Finite P.faces := hPfin.to_subtype
    let _ : Finite Q.faces := hQfin.to_subtype
    have hcomponent {A B : Set E} (hA : IsClosed A) (hB : IsClosed B)
        (hc : IsPreconnected A) (hd : Disjoint A B) {x : E} (hx : x ∈ A) :
        connectedComponentIn (A ∪ B) x = A := by
      have hsdiff : A \ B = A := sdiff_eq_left.mpr hd
      have h := connectedComponentIn_sdiff_inter_eq_sdiff hA hB
        (hsdiff.symm ▸ hc) ⟨hx, disjoint_left.mp hd hx⟩
      simpa only [hd.inter_eq, sdiff_empty, hsdiff] using h
    rcases phragmen_brouwer (isPolyhedron_space P).isClosed (isPolyhedron_space Q).isClosed
      hPQ hH hT (hPQspace.symm ▸ hsep) with hPsep | hQsep
    · refine ⟨P, hPfin, hP, hPc, hPo, hP.isTwoSided P hdim hPc,
        subset_union_left.trans hPQspace.subset, hPsep, hPβ, ?_⟩
      intro x hx
      rw [← hPQspace]
      exact hcomponent (isPolyhedron_space P).isClosed (isPolyhedron_space Q).isClosed
        hPc.isPreconnected hPQ hx
    · refine ⟨Q, hQfin, hQ, hQc, hQo, hQ.isTwoSided Q hdim hQc,
        subset_union_right.trans hPQspace.subset, hQsep, hQβ, ?_⟩
      intro x hx
      rw [← hPQspace, union_comm]
      exact hcomponent (isPolyhedron_space Q).isClosed (isPolyhedron_space P).isClosed
        hQc.isPreconnected hPQ.symm hx

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
    (hr₀ : IsPLHomeomorphOn r₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀)
    (hr₁ : IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁) (hdis : Disjoint D₀ D₁)
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
  obtain ⟨P, hPfin, hP, hPc, hPo, hPt, hPsub, hPsep, hβ, _⟩ :=
    hK.exists_separating_component_bettiOne_lt_of_annulus_capping K R hKc hdim hR
      hJ hJK hρ hzero hWnhds hcover htrace hboundary hnon hr₀ hr₁ hdis
      hmeet₀ hmeet₁ hbd₀ hbd₁ hH hT hsep
  exact ⟨P, hPfin, hP, hPc, hPo, hPt, hPsub, hPsep, hβ⟩

end DifferentialGeometry.Topology.PiecewiseLinear
