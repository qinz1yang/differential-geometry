/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingSourceSides
import DifferentialGeometry.Topology.PiecewiseLinear.IsAnnulusOnCompact

/-! # Section34Piercing Source Buffers -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}

theorem exists_section34_connected_buffers_of_source_sides
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hside : ∀ e, (Bb e ∩ interior (Cp (ends e).1)).Nonempty ∧
      (Bb e \ Cp (ends e).1).Nonempty) :
    ∀ e, ∃ K₀ K₁ R : Set M₁, (IsCompact K₀ ∧ IsConnected K₀) ∧
      (IsCompact K₁ ∧ IsConnected K₁) ∧ IsCompact R ∧ K₀ ⊆ Bb e ∧ K₁ ⊆ Bb e ∧
      R ⊆ Bb e ∧ Bb e ⊆ K₀ ∪ K₁ ∪ R ∧ K₀ ⊆ interior (Cp (ends e).1) ∧
      Disjoint K₁ (Cp (ends e).1) ∧ R ⊆ interior (Tn e) := by
  obtain ⟨-, -, -, -, hcp, -, -, -, -, hΓ, hreg, -, -, -, -, hBb, hTnb, -⟩ := id hprep
  intro e
  let J := CpBd (ends e).1 ∩ CpBd (ends e).2
  have hJT : J ⊆ interior (Tn e) :=
    subset_interior_iff_mem_nhdsSet.mpr (hreg e).2.mem_nhdsSet
  have hJB : J ⊆ Bb e := fun x hx => (hTnb e ⟨interior_subset (hJT hx), hx.2⟩).1
  have hfrontier : Bb e ∩ frontier (Cp (ends e).1) = J := by
    ext x
    constructor
    · rintro ⟨hxB, hxF⟩
      exact ⟨(hcp (ends e).1).boundary_eq_frontier.symm ▸ hxF, (hBb e).1 hxB⟩
    · intro hx
      exact ⟨hJB hx, (hcp (ends e).1).boundary_eq_frontier ▸ hx.1⟩
  obtain ⟨W, R, ρ, hWc, hWB, hRc, hRN, hcover, htrace, hWnhds, hρ, hbij, hzero⟩ :=
    (hcp (ends e).2).exists_piercing_bicollar (hΓ e).1 inter_subset_right
      (hBb e).2.isCompact (hBb e).1 isOpen_interior hJT
      (fun x hx => (hTnb e ⟨interior_subset hx.1, hx.2⟩).1)
  let : LocallyConnectedSpace (Bb e) := (hBb e).2.locallyConnectedSpace
  obtain ⟨K₀, K₁, hK₀, hc₀, hK₁, hc₁, hK₀B, hK₁B, hK, hi, ho⟩ :=
    exists_compact_connected_buffers_of_bicollar (hBb e).2.isConnected.isPreconnected
      (hΓ e).1.isConnected (hΓ e).1.isPolyhedralManifold.isCompact hRc hRN hcover htrace
      hWnhds hρ hbij hzero (hcp (ends e).1).isCompact.isClosed hfrontier
      (hside e).1 (hside e).2
  exact ⟨K₀, K₁, W, ⟨hK₀, hc₀⟩, ⟨hK₁, hc₁⟩, hWc, hK₀B, hK₁B,
    hWB.trans inter_subset_left, hK.symm.subset, hi, ho, hWB.trans inter_subset_right⟩

theorem exists_section34_connected_buffers
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε) :
    ∀ e, ∃ K₀ K₁ R : Set M₁, (IsCompact K₀ ∧ IsConnected K₀) ∧
      (IsCompact K₁ ∧ IsConnected K₁) ∧ IsCompact R ∧ K₀ ⊆ Bb e ∧ K₁ ⊆ Bb e ∧
      R ⊆ Bb e ∧ Bb e ⊆ K₀ ∪ K₁ ∪ R ∧ K₀ ⊆ interior (Cp (ends e).1) ∧
      Disjoint K₁ (Cp (ends e).1) ∧ R ⊆ interior (Tn e) :=
  exists_section34_connected_buffers_of_source_sides hprep (section34_piercing_source_sides hprep)

end DifferentialGeometry.Topology.PiecewiseLinear
