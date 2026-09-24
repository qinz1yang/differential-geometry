/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingSourceBicollar

/-! # Section34Piercing Source Sides -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem meets_interior_near_frontier {X : Type*} [TopologicalSpace X]
    {N P T : Set X} (hN : IsPreconnected N) (hP : IsClosed P) (hT : IsOpen T)
    (htrace : N ∩ frontier P ⊆ T) (hin : (N ∩ interior P).Nonempty)
    (hout : (N \ P).Nonempty) : (N ∩ T ∩ interior P).Nonempty := by
  by_contra hne
  have hcover : N ⊆ interior P ∪ (Pᶜ ∪ T) := by
    intro x hxN
    by_cases hxP : x ∈ P
    · by_cases hxI : x ∈ interior P
      · exact Or.inl hxI
      · exact Or.inr (Or.inr (htrace ⟨hxN, by rw [hP.frontier_eq]; exact ⟨hxP, hxI⟩⟩))
    · exact Or.inr (Or.inl hxP)
  obtain ⟨y, hyN, hyP⟩ := hout
  obtain ⟨x, hxN, hxP, hx⟩ := hN (interior P) (Pᶜ ∪ T) isOpen_interior
    (hP.isOpen_compl.union hT) hcover hin ⟨y, hyN, Or.inl hyP⟩
  rcases hx with hx | hx
  · exact hx (interior_subset hxP)
  · exact hne ⟨x, ⟨hxN, hx⟩, hxP⟩

theorem IsPLCellOn.isConnected_boundary_three {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {S B : Set M} (h : IsPLCellOn 3 S B) :
    IsConnected B := by
  obtain ⟨P, r, u, hr, hu, -, hB⟩ := h
  have hb : IsPLBall 3 P := ⟨r, hr⟩
  rw [IsPLHomeomorphOn.image_stdSimplexBoundary (n := 2) hr] at hB
  rw [hB]
  exact hb.isPLSphere_frontier.isConnected.image u
    (hu.continuousOn.mono hb.isPolyhedron.isClosed.frontier_subset)

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}

theorem section34_piercing_source_sides
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε) :
    ∀ e, (Bb e ∩ interior (Cp (ends e).1)).Nonempty ∧ (Bb e \ Cp (ends e).1).Nonempty := by
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, hAa, hBb, hTB, -, hBc, hΓ,
    hAb, hcomp, -⟩ := id hprep
  intro e
  obtain ⟨y, hy, -⟩ := (hcomp e).2
  have hAaCp : Aa e ⊆ Cp (ends e).1 := by
    rw [(hAa e).1]
    exact inter_subset_left.trans (hCp _).boundary_subset
  have hinside : (CpBd (ends e).2 ∩ interior (Cp (ends e).1)).Nonempty := by
    rw [(hCp _).boundary_eq_frontier]
    obtain ⟨ha, hb⟩ := (hAa e).2.boundaries_nonempty
    obtain ⟨a, ha⟩ := ha
    obtain ⟨b, hb⟩ := hb
    apply (hCp _).frontier_inter_interior_nonempty (hCp _).isCompact.isClosed
    · exact ⟨a, hAaCp ((hAa e).2.first_subset ha), (hAb e).1 ha⟩
    · refine ⟨b, hAaCp ((hAa e).2.second_subset hb), ?_⟩
      intro hbCp
      have hbmem : b ∈ Ab₁ e ∩ Cp (ends e).2 := ⟨hb, hbCp⟩
      rw [(hAb e).2] at hbmem
      exact hbmem
  obtain ⟨x, ⟨hxBd, hxT⟩, hxCp⟩ := meets_interior_near_frontier
    (hCp _).isConnected_boundary_three.isPreconnected (hCp _).isCompact.isClosed
    isOpen_interior (show CpBd (ends e).2 ∩ frontier (Cp (ends e).1) ⊆
      interior (Tn e) from by
        intro x hx
        rw [← (hCp _).boundary_eq_frontier] at hx
        exact ((hBc e).2 ((hΓ e ⟨hx.2, hx.1⟩).1)).2)
    hinside ⟨y, (hBb e).1 hy.1, hy.2⟩
  exact ⟨⟨x, (hTB e ⟨interior_subset hxT, hxBd⟩).1, hxCp⟩, y, hy⟩

end DifferentialGeometry.Topology.PiecewiseLinear
