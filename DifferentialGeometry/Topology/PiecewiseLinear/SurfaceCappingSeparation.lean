/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceComplement
import DifferentialGeometry.Topology.PiecewiseLinear.BallRegularClosed
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalShell
import DifferentialGeometry.Topology.Connected.BoundaryReplacement

/-! Preservation of separation under replacement of a surface wall by caps. -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCombinatorialManifold.separates_of_boundary_replacement
    (S : Geometry.SimplicialComplex ℝ E) [Finite S.faces]
    (hS : IsCombinatorialManifold 2 S) (hdim : Module.finrank ℝ E = 3)
    (hconn : IsConnected S.space) {C N H T : Set E} (hsep : Separates S.space H T)
    (hC : IsClosed C) (hN : closure (interior N) = N)
    (hNconn : IsPreconnected (interior N)) (htrace : S.space ∩ N ⊆ frontier N)
    (hout : S.space \ N = C \ N) (hfront : frontier N ⊆ S.space ∪ C)
    (hHN : H ⊆ Nᶜ) (hTN : T ⊆ Nᶜ) : Separates C H T := by
  have hHC : H ⊆ Cᶜ := fun x hx hxC =>
    hsep.left_subset_compl hx (hout.symm.subset ⟨hxC, hHN hx⟩).1
  have hTC : T ⊆ Cᶜ := fun x hx hxC =>
    hsep.right_subset_compl hx (hout.symm.subset ⟨hxC, hTN hx⟩).1
  by_cases hHne : H.Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty.mp hHne]
    exact separates_empty_left hC hTC
  by_cases hTne : T.Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty.mp hTne]
    exact (separates_empty_left hC hHC).symm
  obtain ⟨a, ha, b, hb, _, hcomp, _, hcl, _, _⟩ :=
    hS.exists_connectedComponentIn_pair_compl S hdim hconn
  have hside {U V : Set E} (hU : IsOpen U) (hV : IsOpen V) (hd : Disjoint U V)
      (hUV : U ∪ V = S.spaceᶜ) (hVne : V.Nonempty) : S.space ⊆ closure V := by
    obtain ⟨v, hv⟩ := hVne
    have hvS : v ∈ S.spaceᶜ := hUV.subset (Or.inr hv)
    have finish {c : E} (hc : c ∈ S.spaceᶜ)
        (hvcomp : v ∈ connectedComponentIn S.spaceᶜ c)
        (hScl : S.space ⊆ closure (connectedComponentIn S.spaceᶜ c)) :
        S.space ⊆ closure V := by
      apply hScl.trans (closure_mono ?_)
      have hpre := (isConnected_connectedComponentIn_iff.mpr hc).isPreconnected
      exact hpre.subset_left_of_subset_union hV hU hd.symm
          (fun x hx => by
            simpa only [union_comm] using hUV.symm.subset (connectedComponentIn_subset _ _ hx))
          ⟨v, hvcomp, hv⟩
    rcases hcomp.symm.subset hvS with hvA | hvB
    · exact finish ha hvA (hcl.symm.subset.trans inter_subset_left)
    · exact finish hb hvB (hcl.symm.subset.trans inter_subset_right)
  have hlocal : ∀ x ∈ S.space, ∀ W ∈ 𝓝 x, ∃ O ∈ 𝓝 x, O ⊆ W ∧
      ∃ A B : Set E, IsPreconnected A ∧ IsPreconnected B ∧ A ∪ B = O \ S.space := by
    intro x hx W hW
    obtain ⟨O, hO, hOW, A, B, hA, hB, hAB, _, _⟩ :=
      hS.exists_connected_neighborhood_pair_sdiff S hdim hx hW
    exact ⟨O, hO, hOW, A, B, hA.isPreconnected, hB.isPreconnected, hAB⟩
  have hNclosed : IsClosed N := hN ▸ isClosed_closure
  have finish {U V H T : Set E} (hU : IsOpen U) (hV : IsOpen V)
      (hd : Disjoint U V) (hUV : U ∪ V = S.spaceᶜ)
      (hHU : H ⊆ U) (hTV : T ⊆ V) (hTne : T.Nonempty)
      (hNU : interior N ⊆ U) (hHN : H ⊆ Nᶜ)
      (hHC : H ⊆ Cᶜ) (hTC : T ⊆ Cᶜ) : Separates C H T := by
    have hfrontW : frontier (U \ N) ⊆ C :=
      frontier_sdiff_subset_of_local_separation hU hV hd hUV
        (inter_subset_left.trans (hside hU hV hd hUV (hTne.mono hTV))) hN hNU hC
        (hout.subset.trans sdiff_subset) hfront (fun x hx => hlocal x hx.1)
    have hH : H ⊆ interior (U \ N) := by
      rw [(hU.sdiff hNclosed).interior_eq]
      exact fun x hx => ⟨hHU hx, hHN hx⟩
    have hT : T ⊆ interior (U \ N)ᶜ := hTV.trans
      (interior_maximal (fun _ hxV hxU => disjoint_left.mp hd hxU.1 hxV) hV)
    exact (separates_frontier hH hT).mono hC hfrontW hHC hTC
  obtain ⟨U, V, hU, hV, hd, hUV, hHU, hTV⟩ := hsep
  have hNsub : interior N ⊆ U ∪ V := by
    intro x hx
    apply hUV.symm.subset
    intro hxS
    exact (htrace ⟨hxS, interior_subset hx⟩).2 hx
  rcases hNconn.subset_or_subset hU hV hd hNsub with hNU | hNV
  · exact finish hU hV hd hUV hHU hTV hTne hNU hHN hHC hTC
  · exact (finish hV hU hd.symm (by rwa [union_comm]) hTV hHU hHne hNV hTN hTC hHC).symm

theorem IsCombinatorialManifold.separates_of_ball_boundary_replacement
    (S : Geometry.SimplicialComplex ℝ E) [Finite S.faces]
    (hS : IsCombinatorialManifold 2 S) (hdim : Module.finrank ℝ E = 3)
    (hconn : IsConnected S.space) {C N H T : Set E} (hsep : Separates S.space H T)
    (hC : IsClosed C) (hN : IsPLBall 3 N) (htrace : S.space ∩ N ⊆ frontier N)
    (hout : S.space \ N = C \ N) (hfront : frontier N ⊆ S.space ∪ C)
    (hHN : H ⊆ Nᶜ) (hTN : T ⊆ Nᶜ) : Separates C H T :=
  hS.separates_of_boundary_replacement S hdim hconn hsep hC
    (hN.closure_interior_of_finrank hdim)
    (hN.isConnected_interior_of_finrank hdim).isPreconnected htrace hout hfront hHN hTN

theorem IsCombinatorialManifold.separates_capped_surface
    (S R : Geometry.SimplicialComplex ℝ E) [Finite S.faces] [Finite R.faces]
    (hS : IsCombinatorialManifold 2 S) (hdim : Module.finrank ℝ E = 3)
    (hconn : IsConnected S.space) {N W D₀ D₁ H T : Set E}
    (hsep : Separates S.space H T) (hN : IsPLBall 3 N)
    (hD₀ : IsPLBall 2 D₀) (hD₁ : IsPLBall 2 D₁)
    (htrace : S.space ∩ N = W) (hcover : W ∪ R.space = S.space)
    (hfront : frontier N = W ∪ D₀ ∪ D₁) (hHN : H ⊆ Nᶜ) (hTN : T ⊆ Nᶜ) :
    Separates (R.space ∪ D₀ ∪ D₁) H T := by
  have hW : W ⊆ S.space ∩ N := htrace.symm.subset
  have hD₀N : D₀ ⊆ N :=
    (subset_union_right.trans (subset_union_left.trans hfront.symm.subset)).trans
      hN.isPolyhedron.isClosed.frontier_subset
  have hD₁N : D₁ ⊆ N :=
    (subset_union_right.trans hfront.symm.subset).trans hN.isPolyhedron.isClosed.frontier_subset
  apply hS.separates_of_ball_boundary_replacement S hdim hconn hsep
    (((isPolyhedron_space R).isClosed.union hD₀.isPolyhedron.isClosed).union
      hD₁.isPolyhedron.isClosed) hN
  · rw [htrace, hfront]
    exact subset_union_left.trans subset_union_left
  · ext x
    constructor
    · rintro ⟨hxS, hxN⟩
      refine ⟨Or.inl (Or.inl ?_), hxN⟩
      exact (hcover.symm.subset hxS).resolve_left (fun hxW => hxN (hW hxW).2)
    · rintro ⟨(hxR | hxD₀) | hxD₁, hxN⟩
      · exact ⟨hcover.subset (Or.inr hxR), hxN⟩
      · exact (hxN (hD₀N hxD₀)).elim
      · exact (hxN (hD₁N hxD₁)).elim
  · rw [hfront]
    rintro x ((hxW | hxD₀) | hxD₁)
    · exact Or.inl (hW hxW).1
    · exact Or.inr (Or.inl (Or.inr hxD₀))
    · exact Or.inr (Or.inr hxD₁)
  · exact hHN
  · exact hTN

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem IsSphericalShell.separates_capped_surface
    {X B₀ B₁ : Set (EuclideanSpace ℝ (Fin 3))} (hX : IsSphericalShell X B₀ B₁)
    (S R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    [Finite S.faces] [Finite R.faces]
    (hS : IsCombinatorialManifold 2 S) (hconn : IsConnected S.space)
    {N W D₀ D₁ : Set (EuclideanSpace ℝ (Fin 3))}
    (hsep : Separates S.space B₀ B₁) (hN : IsPLBall 3 N) (hNX : N ⊆ interior X)
    (hD₀ : IsPLBall 2 D₀) (hD₁ : IsPLBall 2 D₁)
    (htrace : S.space ∩ N = W) (hcover : W ∪ R.space = S.space)
    (hfront : frontier N = W ∪ D₀ ∪ D₁) :
    Separates (R.space ∪ D₀ ∪ D₁) B₀ B₁ ∧
      R.space ∪ D₀ ∪ D₁ ⊆ interior X ∧
      (R.space ∪ D₀ ∪ D₁) \ N = S.space \ N := by
  have hSX := hX.subset_interior_of_separates hconn.isPreconnected hsep
  have havoid : B₀ ∪ B₁ ⊆ Nᶜ :=
    fun _ hx hxN => (hX.frontier_eq.symm.subset hx).2 (hNX hxN)
  have hcap : D₀ ∪ D₁ ⊆ N := by
    apply Subset.trans _ hN.isPolyhedron.isClosed.frontier_subset
    rw [hfront]
    rintro x (hx | hx)
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx
  refine ⟨hS.separates_capped_surface S R (by simp) hconn hsep hN hD₀ hD₁
    htrace hcover hfront (subset_union_left.trans havoid) (subset_union_right.trans havoid),
    ?_, ?_⟩
  · rintro x ((hxR | hxD₀) | hxD₁)
    · exact hSX (hcover.subset (Or.inr hxR))
    · exact hNX (hcap (Or.inl hxD₀))
    · exact hNX (hcap (Or.inr hxD₁))
  · ext x
    constructor
    · rintro ⟨(hxR | hxD₀) | hxD₁, hxN⟩
      · exact ⟨hcover.subset (Or.inr hxR), hxN⟩
      · exact (hxN (hcap (Or.inl hxD₀))).elim
      · exact (hxN (hcap (Or.inr hxD₁))).elim
    · rintro ⟨hxS, hxN⟩
      refine ⟨Or.inl (Or.inl ?_), hxN⟩
      exact (hcover.symm.subset hxS).resolve_left
        (fun hxW => hxN (htrace.symm.subset hxW).2)

end DifferentialGeometry.Topology.PiecewiseLinear
