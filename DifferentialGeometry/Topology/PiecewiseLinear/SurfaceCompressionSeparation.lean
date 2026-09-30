/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCompression
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCappingSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifold.exists_separating_component_bettiOne_lt_of_annulus_replacement
    (S : Geometry.SimplicialComplex ℝ E) [Finite S.faces]
    (hS : IsCombinatorialManifold 2 S) (hconn : IsConnected S.space)
    (hdim : Module.finrank ℝ E = 3) {J W N : Set E}
    (hJ : IsPLSphere 1 J) (hJS : J ⊆ S.space) {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W)
    (hzero : ∀ x ∈ J, ρ (x, 0) = x)
    (hnon : ¬ (⟨Set.inclusion hJS, continuous_inclusion hJS⟩ : C(J, S.space)).Nullhomotopic)
    (hN : IsPLBall 3 N) (hwall : S.space ∩ N = W)
    {D₀ D₁ : Set E} {r₀ r₁ : (Fin 3 → ℝ) → E}
    (hr₀ : IsPLHomeomorphOn r₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀)
    (hr₁ : IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁) (hdis : Disjoint D₀ D₁)
    (hfront : frontier N = W ∪ D₀ ∪ D₁)
    (hmeet₀ : W ∩ D₀ = r₀ '' stdSimplexBoundary 2)
    (hmeet₁ : W ∩ D₁ = r₁ '' stdSimplexBoundary 2)
    (hbd₀ : r₀ '' stdSimplexBoundary 2 = ρ '' (J ×ˢ {(-1 : ℝ)}))
    (hbd₁ : r₁ '' stdSimplexBoundary 2 = ρ '' (J ×ˢ {(1 : ℝ)}))
    {H T : Set E} (hH : IsPreconnected H) (hT : IsPreconnected T)
    (hsep : Separates S.space H T) (hHN : H ⊆ Nᶜ) (hTN : T ⊆ Nᶜ) :
    ∃ (P : Geometry.SimplicialComplex ℝ E) (hPfin : P.faces.Finite),
      letI := hPfin.to_subtype
      let C := closure (S.space \ W) ∪ D₀ ∪ D₁
      IsCombinatorialManifold 2 P ∧ IsConnected P.space ∧ IsOrientable 2 P ∧
      IsTwoSided P.space ∧ P.space ⊆ C ∧ Separates P.space H T ∧
      Homology.bettiOne P.space < Homology.bettiOne S.space ∧
      ∀ x ∈ P.space, connectedComponentIn C x = P.space := by
  have hWS : W ⊆ S.space := hwall.symm.subset.trans inter_subset_left
  obtain ⟨A, R, _, hRfin, _, hR, hAspace, hRspace, _, hRbd, hAR, hAS⟩ :=
    hS.exists_annulus_complement S hJ (by norm_num : (-1 : ℝ) < 1) hρ hWS
  let _ : Finite R.faces := hRfin.to_subtype
  have htrace : W ∩ R.space = ρ '' (J ×ˢ {(-1 : ℝ), 1}) := by rwa [hAspace] at hAR
  have hcover : W ∪ R.space = S.space := by rwa [hAspace] at hAS
  have hends : J ×ˢ {(-1 : ℝ), 1} ⊆ J ×ˢ Icc (-1 : ℝ) 1 := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    refine ⟨hx, ?_⟩
    rcases ht with rfl | rfl <;> norm_num
  have hJavoid : J ⊆ R.spaceᶜ := by
    intro x hx hxR
    have hxW : x ∈ W := by
      rw [← hzero x hx]
      exact hρ.bijOn.mapsTo ⟨hx, by norm_num⟩
    obtain ⟨y, hy, hyx⟩ := htrace.subset ⟨hxW, hxR⟩
    have heq := hρ.bijOn.injOn (hends hy) ⟨hx, by norm_num⟩
      (hyx.trans (hzero x hx).symm)
    have ht : y.2 = 0 := congrArg Prod.snd heq
    have hbad : (0 : ℝ) ∈ ({-1, 1} : Set ℝ) := ht ▸ hy.2
    norm_num at hbad
  have hWnhds : W ∈ 𝓝ˢ[S.space] J := by
    refine mem_nhdsSetWithin.mpr ⟨R.spaceᶜ, (isPolyhedron_space R).isClosed.isOpen_compl,
      hJavoid, ?_⟩
    intro x hx
    exact (hcover.symm.subset hx.2).resolve_right hx.1
  have hcaps : D₀ ∪ D₁ ⊆ N := by
    apply Subset.trans _ hN.isPolyhedron.isClosed.frontier_subset
    rw [hfront]
    rintro x (hx | hx)
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx
  have hRmeet {D C : Set E} (hDN : D ⊆ N) (hWD : W ∩ D = C)
      (hCR : C ⊆ R.space) : R.space ∩ D = C := by
    apply Subset.antisymm
    · intro x hx
      exact hWD.subset ⟨hwall.subset ⟨hcover.subset (Or.inr hx.1), hDN hx.2⟩, hx.2⟩
    · exact fun x hx => ⟨hCR hx, (hWD.symm.subset hx).2⟩
  have hRmeet₀ : R.space ∩ D₀ = r₀ '' stdSimplexBoundary 2 := by
    apply hRmeet (subset_union_left.trans hcaps) hmeet₀
    rw [hbd₀]
    have hsub : J ×ˢ {(-1 : ℝ)} ⊆ J ×ˢ {(-1 : ℝ), 1} :=
      fun _ hx => ⟨hx.1, Or.inl hx.2⟩
    exact (image_mono hsub).trans
      (hRbd.symm.subset.trans (boundaryComplex_space_subset 2 R))
  have hRmeet₁ : R.space ∩ D₁ = r₁ '' stdSimplexBoundary 2 := by
    apply hRmeet (subset_union_right.trans hcaps) hmeet₁
    rw [hbd₁]
    have hsub : J ×ˢ {(1 : ℝ)} ⊆ J ×ˢ {(-1 : ℝ), 1} :=
      fun _ hx => ⟨hx.1, Or.inr hx.2⟩
    exact (image_mono hsub).trans
      (hRbd.symm.subset.trans (boundaryComplex_space_subset 2 R))
  have hcapSep := hS.separates_capped_surface S R hdim hconn hsep hN
    ⟨r₀, hr₀⟩ ⟨r₁, hr₁⟩ hwall hcover hfront hHN hTN
  obtain ⟨P, hPfin, hP, hPc, hPo, hPt, hPsub, hPsep, hβ, hcomponent⟩ :=
    hS.exists_separating_component_bettiOne_lt_of_annulus_capping S R hconn hdim hR
      hJ hJS hρ hzero hWnhds hcover htrace hRbd hnon hr₀ hr₁ hdis
      hRmeet₀ hRmeet₁ hbd₀ hbd₁ hH hT hcapSep
  rw [hRspace] at hPsub hcomponent
  exact ⟨P, hPfin, hP, hPc, hPo, hPt, hPsub, hPsep, hβ, hcomponent⟩

open Classical in
theorem IsCombinatorialManifold.exists_separating_component_bettiOne_lt_of_spanning_disk
    (S : Geometry.SimplicialComplex ℝ E) [Finite S.faces]
    (hS : IsCombinatorialManifold 2 S) (hconn : IsConnected S.space)
    (hdim : Module.finrank ℝ E = 3) {D W N : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hmeet : D ∩ S.space = r '' stdSimplexBoundary 2)
    (hnon : ¬ (⟨Set.inclusion (hmeet.symm.subset.trans inter_subset_right),
      continuous_inclusion _⟩ : C(r '' stdSimplexBoundary 2, S.space)).Nullhomotopic)
    {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ ((r '' stdSimplexBoundary 2) ×ˢ Icc (-1 : ℝ) 1) W)
    (hzero : ∀ x ∈ r '' stdSimplexBoundary 2, ρ (x, 0) = x)
    (hN : IsPLBall 3 N) (hwall : S.space ∩ N = W)
    {D₀ D₁ : Set E} {r₀ r₁ : (Fin 3 → ℝ) → E}
    (hr₀ : IsPLHomeomorphOn r₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀)
    (hr₁ : IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁) (hdis : Disjoint D₀ D₁)
    (hfront : frontier N = W ∪ D₀ ∪ D₁)
    (hmeet₀ : W ∩ D₀ = r₀ '' stdSimplexBoundary 2)
    (hmeet₁ : W ∩ D₁ = r₁ '' stdSimplexBoundary 2)
    (hbd₀ : r₀ '' stdSimplexBoundary 2 = ρ '' ((r '' stdSimplexBoundary 2) ×ˢ {(-1 : ℝ)}))
    (hbd₁ : r₁ '' stdSimplexBoundary 2 = ρ '' ((r '' stdSimplexBoundary 2) ×ˢ {(1 : ℝ)}))
    {H T : Set E} (hH : IsPreconnected H) (hT : IsPreconnected T)
    (hsep : Separates S.space H T) (hHN : H ⊆ Nᶜ) (hTN : T ⊆ Nᶜ) :
    ∃ (P : Geometry.SimplicialComplex ℝ E) (hPfin : P.faces.Finite),
      letI := hPfin.to_subtype
      let C := closure (S.space \ W) ∪ D₀ ∪ D₁
      IsCombinatorialManifold 2 P ∧ IsConnected P.space ∧ IsOrientable 2 P ∧
      IsTwoSided P.space ∧ P.space ⊆ C ∧ Separates P.space H T ∧
      Homology.bettiOne P.space < Homology.bettiOne S.space ∧
      ∀ x ∈ P.space, connectedComponentIn C x = P.space :=
  hS.exists_separating_component_bettiOne_lt_of_annulus_replacement S hconn hdim
    hr.isPLSphere_image_stdSimplexBoundary (hmeet.symm.subset.trans inter_subset_right)
    hρ hzero hnon hN hwall hr₀ hr₁ hdis hfront hmeet₀ hmeet₁ hbd₀ hbd₁ hH hT hsep hHN hTN

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
open Classical in
theorem IsSphericalShell.exists_separating_component_bettiOne_lt_of_spanning_disk
    {X B₀ B₁ : Set (EuclideanSpace ℝ (Fin 3))} (hX : IsSphericalShell X B₀ B₁)
    (S : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite S.faces]
    (hS : IsCombinatorialManifold 2 S) (hconn : IsConnected S.space)
    (hsep : Separates S.space B₀ B₁)
    {D W N : Set (EuclideanSpace ℝ (Fin 3))}
    {r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hmeet : D ∩ S.space = r '' stdSimplexBoundary 2)
    (hnon : ¬ (⟨Set.inclusion (hmeet.symm.subset.trans inter_subset_right),
      continuous_inclusion _⟩ : C(r '' stdSimplexBoundary 2, S.space)).Nullhomotopic)
    {ρ : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hρ : IsPLHomeomorphOn ρ ((r '' stdSimplexBoundary 2) ×ˢ Icc (-1 : ℝ) 1) W)
    (hzero : ∀ x ∈ r '' stdSimplexBoundary 2, ρ (x, 0) = x)
    (hN : IsPLBall 3 N) (hwall : S.space ∩ N = W) (hNX : N ⊆ interior X)
    {D₀ D₁ : Set (EuclideanSpace ℝ (Fin 3))}
    {r₀ r₁ : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hr₀ : IsPLHomeomorphOn r₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀)
    (hr₁ : IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁) (hdis : Disjoint D₀ D₁)
    (hfront : frontier N = W ∪ D₀ ∪ D₁)
    (hmeet₀ : W ∩ D₀ = r₀ '' stdSimplexBoundary 2)
    (hmeet₁ : W ∩ D₁ = r₁ '' stdSimplexBoundary 2)
    (hbd₀ : r₀ '' stdSimplexBoundary 2 = ρ '' ((r '' stdSimplexBoundary 2) ×ˢ {(-1 : ℝ)}))
    (hbd₁ : r₁ '' stdSimplexBoundary 2 = ρ '' ((r '' stdSimplexBoundary 2) ×ˢ {(1 : ℝ)})) :
    ∃ (P : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) (hPfin : P.faces.Finite),
      letI := hPfin.to_subtype
      let C := closure (S.space \ W) ∪ D₀ ∪ D₁
      IsCombinatorialManifold 2 P ∧ IsConnected P.space ∧ IsOrientable 2 P ∧
      IsTwoSided P.space ∧ P.space ⊆ C ∧ P.space ⊆ interior X ∧ Separates P.space B₀ B₁ ∧
      Homology.bettiOne P.space < Homology.bettiOne S.space ∧
      ∀ x ∈ P.space, connectedComponentIn C x = P.space := by
  have havoid : B₀ ∪ B₁ ⊆ Nᶜ :=
    fun _ hx hxN => (hX.frontier_eq.symm.subset hx).2 (hNX hxN)
  obtain ⟨P, hPfin, hP, hPc, hPo, hPt, hPsub, hPsep, hβ, hcomponent⟩ :=
    hS.exists_separating_component_bettiOne_lt_of_spanning_disk S hconn (by simp)
      hr hmeet hnon hρ hzero hN hwall hr₀ hr₁ hdis hfront hmeet₀ hmeet₁ hbd₀ hbd₁
      hX.isConnected_left.isPreconnected hX.isConnected_right.isPreconnected hsep
      (subset_union_left.trans havoid) (subset_union_right.trans havoid)
  exact ⟨P, hPfin, hP, hPc, hPo, hPt, hPsub,
    hX.subset_interior_of_separates hPc.isPreconnected hPsep, hPsep, hβ, hcomponent⟩

end DifferentialGeometry.Topology.PiecewiseLinear
