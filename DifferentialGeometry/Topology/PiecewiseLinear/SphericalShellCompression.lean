/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SpanningDiskCompression
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceEssentialDisk

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem IsSphericalShell.exists_compression_of_essential_disk
    {X B₀ B₁ : Set (EuclideanSpace ℝ (Fin 3))} (hX : IsSphericalShell X B₀ B₁)
    (S : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite S.faces]
    (hS : IsCombinatorialManifold 2 S) (hconn : IsConnected S.space)
    (hsep : Separates S.space B₀ B₁) {D U : Set (EuclideanSpace ℝ (Fin 3))}
    {r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hmeet : D ∩ S.space = r '' stdSimplexBoundary 2)
    (hnon : ¬ (⟨Set.inclusion (hmeet.symm.subset.trans inter_subset_right),
      continuous_inclusion _⟩ : C(r '' stdSimplexBoundary 2, S.space)).Nullhomotopic)
    (hDX : D ⊆ interior X) (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ (N W D₀ D₁ : Set (EuclideanSpace ℝ (Fin 3)))
      (f : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3))
      (ρ : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3))
      (r₀ r₁ : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 N ∧ N ⊆ U ∧ N ⊆ interior X ∧ D ⊆ N ∧ D \ S.space ⊆ interior N ∧
      D ∩ frontier N = r '' stdSimplexBoundary 2 ∧ N ∈ 𝓝ˢ[S.space ∪ D] D ∧
      IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) N ∧
      (∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), f (x, 0) = r x) ∧
      S.space ∩ N = W ∧ W = f '' (stdSimplexBoundary 2 ×ˢ Icc (-1 : ℝ) 1) ∧
      IsPolyhedron W ∧ W ∈ 𝓝ˢ[S.space] (r '' stdSimplexBoundary 2) ∧
      IsPLHomeomorphOn ρ ((r '' stdSimplexBoundary 2) ×ˢ Icc (-1 : ℝ) 1) W ∧
      (∀ x ∈ r '' stdSimplexBoundary 2, ρ (x, 0) = x) ∧
      (∀ x ∈ stdSimplexBoundary 2, ∀ t ∈ Icc (-1 : ℝ) 1, ρ (r x, t) = f (x, t)) ∧
      IsPLHomeomorphOn r₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀ ∧
      IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁ ∧ Disjoint D₀ D₁ ∧
      frontier N = W ∪ D₀ ∪ D₁ ∧
      W ∩ D₀ = r₀ '' stdSimplexBoundary 2 ∧ W ∩ D₁ = r₁ '' stdSimplexBoundary 2 ∧
      r₀ '' stdSimplexBoundary 2 = ρ '' ((r '' stdSimplexBoundary 2) ×ˢ {(-1 : ℝ)}) ∧
      r₁ '' stdSimplexBoundary 2 = ρ '' ((r '' stdSimplexBoundary 2) ×ˢ {(1 : ℝ)}) ∧
      ∃ (P : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) (hPfin : P.faces.Finite),
        letI := hPfin.to_subtype
        let C := closure (S.space \ W) ∪ D₀ ∪ D₁
        IsCombinatorialManifold 2 P ∧ IsConnected P.space ∧ IsOrientable 2 P ∧
        IsTwoSided P.space ∧ P.space ⊆ C ∧ P.space ⊆ interior X ∧ Separates P.space B₀ B₁ ∧
        Homology.bettiOne P.space < Homology.bettiOne S.space ∧
        ∀ x ∈ P.space, connectedComponentIn C x = P.space := by
  obtain ⟨N, W, D₀, D₁, f, ρ, r₀, r₁, hN, hNU, hDN, hinside, hproper, hNnear,
    hf, hzero, hwall, hW, hWpoly, hWnear, hρ, hρzero, hcompatible,
    hr₀, hr₁, hdis, hfront, hmeet₀, hmeet₁, hbd₀, hbd₁⟩ :=
    hS.exists_compression_neighborhood_of_spanning_disk S hconn (by simp) hr hmeet
      (hU.inter isOpen_interior) (fun x hx => ⟨hDU hx, hDX hx⟩)
  have hNX : N ⊆ interior X := hNU.trans inter_subset_right
  refine ⟨N, W, D₀, D₁, f, ρ, r₀, r₁, hN, hNU.trans inter_subset_left, hNX, hDN,
    hinside, hproper, hNnear, hf, hzero, hwall, hW, hWpoly, hWnear, hρ, hρzero,
    hcompatible, hr₀, hr₁, hdis, hfront, hmeet₀, hmeet₁, hbd₀, hbd₁, ?_⟩
  exact hX.exists_separating_component_bettiOne_lt_of_spanning_disk S hS hconn hsep
    hr hmeet hnon hρ hρzero hN hwall hNX hr₀ hr₁ hdis hfront hmeet₀ hmeet₁ hbd₀ hbd₁

open Classical in
theorem IsSphericalShell.exists_separating_component_bettiOne_lt_of_loop_theorem
    (h252 : Moise252) {X B₀ B₁ : Set (EuclideanSpace ℝ (Fin 3))}
    (hX : IsSphericalShell X B₀ B₁)
    (S : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite S.faces]
    (hS : IsCombinatorialManifold 2 S) (hconn : IsConnected S.space)
    (hnot : ¬ IsPLSphere 2 S.space) (hsep : Separates S.space B₀ B₁) :
    ∃ (P : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) (hPfin : P.faces.Finite),
      letI := hPfin.to_subtype
      IsCombinatorialManifold 2 P ∧ IsConnected P.space ∧ IsOrientable 2 P ∧
      IsTwoSided P.space ∧ P.space ⊆ interior X ∧ Separates P.space B₀ B₁ ∧
      Homology.bettiOne P.space < Homology.bettiOne S.space := by
  let _ : SimplyConnectedSpace (interior X) := hX.simplyConnectedSpace_interior
  have hSX := hX.subset_interior_of_separates hconn.isPreconnected hsep
  obtain ⟨D, r, hr, hDX, hmeet, _, hnon⟩ :=
    IsCombinatorialManifold.exists_essential_disk_in_neighborhood_of_loop_theorem
      h252 S hS (by simp) hconn hnot isOpen_interior hSX
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, P, hPfin, hP, hPc, hPo, hPt, _, hPX, hPsep, hβ, _⟩ :=
    hX.exists_compression_of_essential_disk S hS hconn hsep hr hmeet hnon hDX
      isOpen_interior hDX
  exact ⟨P, hPfin, hP, hPc, hPo, hPt, hPX, hPsep, hβ⟩

theorem moise304_of_moise252 (h252 : Moise252) : Moise304 := by
  intro X B₀ B₁ hX
  obtain ⟨S, hSfin, hS, hSc, _, _, hSX, hsep, hmin⟩ :=
    hX.exists_connected_separating_surface_bettiOne_min
  let _ : Finite S.faces := hSfin.to_subtype
  have hsphere : IsPLSphere 2 S.space := by
    by_contra hnot
    obtain ⟨P, hPfin, hP, hPc, _, _, _, hPsep, hβ⟩ :=
      IsSphericalShell.exists_separating_component_bettiOne_lt_of_loop_theorem
        h252 hX S hS hSc hnot hsep
    exact (not_lt_of_ge (hmin P hPfin hP hPc hPsep)) hβ
  exact ⟨S.space, hsphere, hSX, hsep⟩

end DifferentialGeometry.Topology.PiecewiseLinear
