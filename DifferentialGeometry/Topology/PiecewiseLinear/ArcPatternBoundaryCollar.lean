/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcPatternStripCollar
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDiskPairCollarExtension

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_collar_with_trace_of_arcPatternChart
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hF : IsPLSphere 2 (boundaryComplex 3 K).space)
    {S B β A : Set E} (hFS : (boundaryComplex 3 K).space ⊆ S) (hB : IsClosed B)
    (hBF : B ∩ (boundaryComplex 3 K).space = β)
    {Φ : (ℝ × ℝ) × ℝ → E} {N : Set ((ℝ × ℝ) × ℝ)} {Ω : Set E} {τ : ℝ}
    (hN : IsOpen N) (hΩ : IsOpen Ω) (hΦ : IsPLHomeomorphOn Φ N (S ∩ Ω))
    (hτ : 0 < τ) (hcore : coreSegment τ ⊆ N) (hβ : Φ '' coreSegment τ = β)
    (hΦK : ∀ p ∈ N, Φ p ∈ K.space ↔ 0 ≤ p.1.2)
    (hΦF : ∀ p ∈ N, Φ p ∈ (boundaryComplex 3 K).space ↔ p.1.2 = 0)
    (hΦB : ∀ p ∈ N, Φ p ∈ B ↔ p.1.1 = 0 ∧ 0 ≤ p.1.2 ∧ 0 ≤ p.2 ∧ p.2 ≤ τ)
    (hΦA : ∀ p ∈ N, p.1.1 = 0 → 0 ≤ p.1.2 → p.2 = 0 ∨ p.2 = τ → Φ p ∈ A) :
    ∃ (ε : ℝ) (W : Set E) (ρ : E × ℝ → E),
      0 < ε ∧ IsPolyhedron W ∧ W ⊆ K.space ∧
      W ∈ 𝓝ˢ[K.space] (boundaryComplex 3 K).space ∧
      IsPLHomeomorphOn ρ ((boundaryComplex 3 K).space ×ˢ Icc (0 : ℝ) ε) W ∧
      (∀ x ∈ (boundaryComplex 3 K).space, ρ (x, 0) = x) ∧
      W ∩ (boundaryComplex 3 K).space = (boundaryComplex 3 K).space ∧
      W ∩ B = ρ '' (β ×ˢ Icc (0 : ℝ) ε) ∧
      ρ '' ({Φ 0, Φ ((0, 0), τ)} ×ˢ Icc (0 : ℝ) ε) ⊆ A := by
  obtain ⟨P, W₀, ρ₀, hP, -, hPnhds, hW₀K, hρ₀, hbase₀, hW₀F, hW₀B, hends₀⟩ :=
    exists_disk_collar_of_arcPatternChart hFS hN hΩ hΦ hτ hcore hβ hΦK hΦF hΦB hΦA
  obtain ⟨ε, W, ρ, hε, hε1, hW, hWK, hWnhds, hρ, hfix, hbase, hWF, hWB⟩ :=
    hK.exists_collar_eqOn_boundary_disk_with_trace K hF hB hBF hP hPnhds
      hρ₀ hW₀K hbase₀ hW₀F hW₀B
  have hβF : β ⊆ (boundaryComplex 3 K).space := hBF.symm.subset.trans inter_subset_right
  obtain ⟨U, -, hβU, hUP⟩ := mem_nhdsSetWithin.mp hPnhds
  have hβP : β ⊆ P := fun x hx => hUP ⟨hβU hx, hβF hx⟩
  have hendsβ : {Φ 0, Φ ((0, 0), τ)} ⊆ β := by
    rw [← hβ]
    intro x hx
    rcases hx with hx | hx
    · exact ⟨0, ⟨rfl, le_rfl, hτ.le⟩, hx.symm⟩
    · exact ⟨((0, 0), τ), ⟨rfl, hτ.le, le_rfl⟩, hx.symm⟩
  refine ⟨ε, W, ρ, hε, hW, hWK, hWnhds, hρ, hbase, hWF, hWB, ?_⟩
  rintro x ⟨q, hq, rfl⟩
  rw [hfix ⟨hβP (hendsβ hq.1), hq.2⟩]
  exact hends₀ ⟨q, ⟨hq.1, hq.2.1, hq.2.2.trans hε1⟩, rfl⟩

end DifferentialGeometry.Topology.PiecewiseLinear
