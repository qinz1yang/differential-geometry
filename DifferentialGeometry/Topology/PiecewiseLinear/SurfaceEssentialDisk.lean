/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCutKernel
import DifferentialGeometry.Topology.FundamentalGroup.Nullhomotopy
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCompressionSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCircleBicollar

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_essential_disk_of_loop_theorem
    (h252 : Moise252) {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hdim : Module.finrank ℝ E = 3)
    (hLint : L.space ⊆ K.space \ (boundaryComplex 3 K).space)
    (hKc : IsPreconnected K.space) (hLc : IsConnected L.space)
    (s : L.space) (g : FundamentalGroup L.space s) (hg : g ≠ 1)
    (hnull : FundamentalGroup.map
      (⟨Set.inclusion (hLint.trans sdiff_subset), continuous_inclusion _⟩ :
        C(L.space, K.space)) s g = 1)
    {U : Set E} (hU : U ∈ 𝓝ˢ[K.space] L.space) :
    ∃ (hLK : L.space ⊆ K.space) (c : ThreeManifold.TwoSidedCollar (Set.inclusion hLK)),
      range (((↑) : K.space → E) ∘ c.toFun) ⊆ U ∧
      ∃ (D : Set E) (r : (Fin 3 → ℝ) → E),
        IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
        D ⊆ K.space \ (boundaryComplex 3 K).space ∧
        D ∩ L.space = r '' stdSimplexBoundary 2 ∧
        ∃ hboundary : r '' stdSimplexBoundary 2 ⊆ L.space,
          ¬ (⟨Set.inclusion hboundary, continuous_inclusion hboundary⟩ :
            C(r '' stdSimplexBoundary 2, L.space)).Nullhomotopic := by
  obtain ⟨hLK, c, hc, R, hRfin, hR, _, hRo, hRK, hRbd, d, hd, hsub, x, a, ha, han⟩ :=
    hK.exists_boundary_component_kernel_of_interior_inclusion hL hdim hLint
      hKc hLc s g hg hnull hU
  let _ : Finite R.faces := hRfin.to_subtype
  obtain ⟨γ, hγ, hγnull⟩ :=
    exists_non_nullhomotopic_freeLoop_of_nontrivial_fundamentalGroup_kernel
      (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ :
        C((PiecewiseLinear.connectedComponentComplex (boundaryComplex 3 R) d).space,
          R.space)) x a ha han
  obtain ⟨D, r, hr, hDR, hDbd, hboundary, hnon⟩ :=
    h252 R inferInstance hR hRo d hsub γ hγnull hγ
  have hJL : r '' stdSimplexBoundary 2 ⊆ L.space := hboundary.trans hd.subset
  have hmeet : D ∩ L.space = r '' stdSimplexBoundary 2 := by
    apply Subset.antisymm
    · exact fun _ hx => hDbd.subset ⟨hx.1, hRbd.symm.subset (Or.inl hx.2)⟩
    · exact fun _ hx => ⟨(hDbd.symm.subset hx).1, hJL hx⟩
  have hDK : D ⊆ K.space \ (boundaryComplex 3 K).space := by
    intro y hy
    refine ⟨hRK (hDR hy), ?_⟩
    intro hyold
    have hybd : y ∈ (boundaryComplex 3 R).space :=
      hRbd.symm.subset (Or.inr ⟨hDR hy, hyold⟩)
    exact (hLint (hJL (hDbd.subset ⟨hy, hybd⟩))).2 hyold
  refine ⟨hLK, c, hc, D, r, hr, hDK, hmeet, ?_⟩
  rw [← hd]
  exact ⟨hboundary, hnon⟩

open Classical in
theorem IsCombinatorialManifold.exists_essential_disk_in_neighborhood_of_fundamentalGroup_map_eq_one
    (h252 : Moise252) (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 2 L) (hdim : Module.finrank ℝ E = 3)
    (hLc : IsConnected L.space) {U : Set E} (hU : IsOpen U) (hLU : L.space ⊆ U)
    (x : L.space) (g : FundamentalGroup L.space x) (hg : g ≠ 1)
    (hmap : FundamentalGroup.map (⟨Set.inclusion hLU, continuous_inclusion hLU⟩ :
      C(L.space, U)) x g = 1) :
    ∃ (D : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ U ∧
      D ∩ L.space = r '' stdSimplexBoundary 2 ∧
      ∃ hboundary : r '' stdSimplexBoundary 2 ⊆ L.space,
        ¬ (⟨Set.inclusion hboundary, continuous_inclusion hboundary⟩ :
          C(r '' stdSimplexBoundary 2, L.space)).Nullhomotopic := by
  obtain ⟨K, hKfin, hK, hKc, hLK, hKU, hnull⟩ :=
    exists_connected_neighborhood_fundamentalGroup_map_eq_one hdim
      (isPolyhedron_space L).isCompact hLc hU hLU x g hmap
  let _ : Finite K.faces := hKfin.to_subtype
  have hLint : L.space ⊆ K.space \ (boundaryComplex 3 K).space := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank hdim K hK]
    exact fun y hy => ⟨interior_subset (hLK hy), fun hz => hz.2 (hLK hy)⟩
  obtain ⟨_, _, _, D, r, hr, hDK, hmeet, hboundary, hnon⟩ :=
    IsCombinatorialManifoldWithBoundary.exists_essential_disk_of_loop_theorem
      h252 hK hL hdim hLint hKc.isPreconnected hLc x g hg (hnull _)
      (mem_nhdsSetWithin.mpr ⟨U, hU, hLU, inter_subset_left⟩)
  exact ⟨D, r, hr, hDK.trans (sdiff_subset.trans hKU), hmeet, hboundary, hnon⟩

open Classical in
theorem IsCombinatorialManifold.exists_essential_disk_in_neighborhood_of_loop_theorem
    (h252 : Moise252) (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 2 L) (hdim : Module.finrank ℝ E = 3)
    (hLc : IsConnected L.space) (hnot : ¬ IsPLSphere 2 L.space)
    {U : Set E} (hU : IsOpen U) (hLU : L.space ⊆ U) [SimplyConnectedSpace U] :
    ∃ (D : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ U ∧
      D ∩ L.space = r '' stdSimplexBoundary 2 ∧
      ∃ hboundary : r '' stdSimplexBoundary 2 ⊆ L.space,
        ¬ (⟨Set.inclusion hboundary, continuous_inclusion hboundary⟩ :
          C(r '' stdSimplexBoundary 2, L.space)).Nullhomotopic := by
  obtain ⟨x, hx⟩ := hLc.nonempty
  let s : L.space := ⟨x, hx⟩
  obtain ⟨g, hg, K, hKfin, hK, hKc, hKU, hLK, hmap⟩ :=
    hL.exists_connected_neighborhood_nontrivial_fundamentalGroup_kernel
      hdim L hLc hnot hU hLU s
  let _ : Finite K.faces := hKfin.to_subtype
  obtain ⟨_, _, _, D, r, hr, hDK, hmeet, hboundary, hnon⟩ :=
    IsCombinatorialManifoldWithBoundary.exists_essential_disk_of_loop_theorem
      h252 hK hL hdim hLK hKc.isPreconnected hLc s g hg (hmap _)
      (mem_nhdsSetWithin.mpr ⟨U, hU, hLU, inter_subset_left⟩)
  exact ⟨D, r, hr, hDK.trans (sdiff_subset.trans hKU), hmeet, hboundary, hnon⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
open Classical in
theorem IsSphericalShell.exists_essential_disk_annulus_of_loop_theorem
    (h252 : Moise252) {X B₀ B₁ : Set (EuclideanSpace ℝ (Fin 3))}
    (hX : IsSphericalShell X B₀ B₁)
    (S : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite S.faces]
    (hS : IsCombinatorialManifold 2 S) (hconn : IsConnected S.space)
    (hnot : ¬ IsPLSphere 2 S.space) (hsep : Separates S.space B₀ B₁) :
    ∃ (D W : Set (EuclideanSpace ℝ (Fin 3)))
      (r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3))
      (ρ : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3))
      (_ : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
      (hmeet : D ∩ S.space = r '' stdSimplexBoundary 2),
      D ⊆ interior X ∧ (D \ S.space).Nonempty ∧
      ¬ (⟨Set.inclusion (hmeet.symm.subset.trans inter_subset_right),
        continuous_inclusion _⟩ : C(r '' stdSimplexBoundary 2, S.space)).Nullhomotopic ∧
      IsPLSphere 1 (r '' stdSimplexBoundary 2) ∧
      IsPolyhedron W ∧ W ⊆ S.space ∧ W ⊆ interior X ∧
      W ∈ 𝓝ˢ[S.space] (r '' stdSimplexBoundary 2) ∧
      IsPLHomeomorphOn ρ ((r '' stdSimplexBoundary 2) ×ˢ Icc (-1 : ℝ) 1) W ∧
      (∀ x ∈ r '' stdSimplexBoundary 2, ρ (x, 0) = x) ∧
      ∀ (N D₀ D₁ : Set (EuclideanSpace ℝ (Fin 3)))
        (r₀ r₁ : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
        IsPLBall 3 N → S.space ∩ N = W → N ⊆ interior X →
        IsPLHomeomorphOn r₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀ →
        IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁ → Disjoint D₀ D₁ →
        frontier N = W ∪ D₀ ∪ D₁ →
        W ∩ D₀ = r₀ '' stdSimplexBoundary 2 → W ∩ D₁ = r₁ '' stdSimplexBoundary 2 →
        r₀ '' stdSimplexBoundary 2 = ρ '' ((r '' stdSimplexBoundary 2) ×ˢ {(-1 : ℝ)}) →
        r₁ '' stdSimplexBoundary 2 = ρ '' ((r '' stdSimplexBoundary 2) ×ˢ {(1 : ℝ)}) →
        ∃ (P : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) (hPfin : P.faces.Finite),
          letI := hPfin.to_subtype
          let C := closure (S.space \ W) ∪ D₀ ∪ D₁
          IsCombinatorialManifold 2 P ∧ IsConnected P.space ∧ IsOrientable 2 P ∧
          IsTwoSided P.space ∧ P.space ⊆ C ∧ P.space ⊆ interior X ∧
          Separates P.space B₀ B₁ ∧ Homology.bettiOne P.space < Homology.bettiOne S.space ∧
          ∀ x ∈ P.space, connectedComponentIn C x = P.space := by
  let _ : SimplyConnectedSpace (interior X) := hX.simplyConnectedSpace_interior
  have hSX := hX.subset_interior_of_separates hconn.isPreconnected hsep
  obtain ⟨D, r, hr, hDX, hmeet, hJS, hnon⟩ :=
    IsCombinatorialManifold.exists_essential_disk_in_neighborhood_of_loop_theorem
      h252 S hS (by simp) hconn hnot isOpen_interior hSX
  have hJ := hr.isPLSphere_image_stdSimplexBoundary
  obtain ⟨W, ρ, hW, hWS, hWX, hWnhds, hρ, hzero⟩ :=
    hS.exists_bicollar_of_isPLSphere_one S
      (hS.isOrientable_of_finrank_eq_three S (by simp) hconn) hJ hJS
      (mem_nhdsSetWithin.mpr ⟨interior X, isOpen_interior, hJS.trans hSX, inter_subset_left⟩)
  have hremain : (D \ S.space).Nonempty := by
    have hp : r (stdCenter 1) ∈ D \ r '' stdSimplexBoundary 2 := by
      rw [← hr.image_openSimplex_stdVertices]
      exact mem_image_of_mem r (stdCenter_mem_openSimplex 1)
    exact ⟨r (stdCenter 1), hp.1, fun h => hp.2 (hmeet.subset ⟨hp.1, h⟩)⟩
  refine ⟨D, W, r, ρ, hr, hmeet, hDX, hremain, hnon, hJ,
    hW, hWS, hWX, hWnhds, hρ, hzero, ?_⟩
  intro N D₀ D₁ r₀ r₁ hN hwall hNX hr₀ hr₁ hdis hfront hmeet₀ hmeet₁ hbd₀ hbd₁
  exact hX.exists_separating_component_bettiOne_lt_of_spanning_disk S hS hconn hsep
    hr hmeet hnon hρ hzero hN hwall hNX hr₀ hr₁ hdis hfront hmeet₀ hmeet₁ hbd₀ hbd₁

end DifferentialGeometry.Topology.PiecewiseLinear
