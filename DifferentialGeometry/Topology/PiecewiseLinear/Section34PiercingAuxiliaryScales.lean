/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingBufferStability
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingSideStability
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingSourceBuffers

open Set

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
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}

theorem exists_auxiliary_scales_preserving_piercing_sides_of_connected_buffers
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hbuffers : ∀ e, ∃ K₀ K₁ R : Set M₁,
      (IsCompact K₀ ∧ IsConnected K₀) ∧ (IsCompact K₁ ∧ IsConnected K₁) ∧ IsCompact R ∧
      K₀ ⊆ Bb e ∧ K₁ ⊆ Bb e ∧ R ⊆ Cc (ends e).2 ∧ Bb e ⊆ K₀ ∪ K₁ ∪ R ∧
      K₀ ⊆ interior (Cp (ends e).1) ∧ Disjoint K₁ (Cp (ends e).1) ∧ R ⊆ interior (Tn e)) :
    ∃ δ : Section34VertexIndex 𝒦 𝒦' → ℝ,
      (∀ w, 0 < δ w) ∧ (∀ w, δ w < ε w) ∧
      ∀ G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
        (∀ w, IsPLHomeomorphInto 3 (G w) (Cc w)) →
        (∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < δ w) →
        (∀ e, G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' CpBd (ends e).2 ⊆
          interior (G (ends e).1 '' Tn e)) ∧
        (∀ e, G (ends e).1 '' Ab₀ e ⊆ interior (G (ends e).2 '' Cp (ends e).2)) ∧
        (∀ e, G (ends e).2 '' Bb e ⊆ interior (G (ends e).1 '' Sn e)) ∧
        (∀ e, ∃ y₀ ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1,
          ∀ z ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1,
            z ∉ G (ends e).1 '' Tn e →
            z ∈ connectedComponentIn
              (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) y₀) ∧
        (∀ e, ∃ y₀ ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1,
          ∀ z ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1,
            z ∉ G (ends e).1 '' Tn e →
            z ∈ connectedComponentIn
              (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) y₀) := by
  choose K₀ K₁ R hK₀ hK₁ hR hK₀B hK₁B hRb hcover hinside houtside hRT using hbuffers
  obtain ⟨dC, hdC, hdCε, hcomp⟩ :=
    exists_section34_component_stability_scales_of_connected_buffers hh hprep
      hK₀ hK₁ hR hK₀B hK₁B hRb hcover hinside houtside hRT
  obtain ⟨dT, hdT, -, htrace⟩ := exists_section34_trace_interior_stability_scales hh hprep
  obtain ⟨dI, hdI, -, hinner⟩ := exists_section34_inner_end_stability_scales hh hprep
  obtain ⟨dO, hdO, -, houter⟩ := exists_section34_outer_annulus_stability_scales hh hprep
  refine ⟨fun w => min (dC w) (min (dT w) (min (dI w) (dO w))),
    fun w => lt_min (hdC w) (lt_min (hdT w) (lt_min (hdI w) (hdO w))),
    fun w => (min_le_left _ _).trans_lt (hdCε w), fun G hG hclose => ?_⟩
  have hcloseC : ∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < dC w :=
    fun w x hx => (hclose w x hx).trans_le (min_le_left _ _)
  have hcloseT : ∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < dT w :=
    fun w x hx => (hclose w x hx).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  have hcloseI : ∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < dI w :=
    fun w x hx => (hclose w x hx).trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hcloseO : ∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < dO w :=
    fun w x hx => (hclose w x hx).trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  exact ⟨htrace G hG hcloseT, hinner G hG hcloseI, houter G hG hcloseO, hcomp G hG hcloseC⟩

theorem exists_auxiliary_scales_preserving_piercing_sides
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε) :
    ∃ δ : Section34VertexIndex 𝒦 𝒦' → ℝ,
      (∀ w, 0 < δ w) ∧ (∀ w, δ w < ε w) ∧
      ∀ G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
        (∀ w, IsPLHomeomorphInto 3 (G w) (Cc w)) →
        (∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < δ w) →
        (∀ e, G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' CpBd (ends e).2 ⊆
          interior (G (ends e).1 '' Tn e)) ∧
        (∀ e, G (ends e).1 '' Ab₀ e ⊆ interior (G (ends e).2 '' Cp (ends e).2)) ∧
        (∀ e, G (ends e).2 '' Bb e ⊆ interior (G (ends e).1 '' Sn e)) ∧
        (∀ e, ∃ y₀ ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1,
          ∀ z ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1,
            z ∉ G (ends e).1 '' Tn e →
            z ∈ connectedComponentIn
              (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) y₀) ∧
        (∀ e, ∃ y₀ ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1,
          ∀ z ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1,
            z ∉ G (ends e).1 '' Tn e →
            z ∈ connectedComponentIn
              (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) y₀) := by
  obtain ⟨-, -, hsubs, -, hCp, -, -, -, -, -, -, -, -, -, -, hBb, -⟩ := id hprep
  apply exists_auxiliary_scales_preserving_piercing_sides_of_connected_buffers hh hprep
  intro e
  obtain ⟨K₀, K₁, R, hK₀, hK₁, hR, hK₀B, hK₁B, hRB, hcover, hi, ho, hRT⟩ :=
    exists_section34_connected_buffers hprep e
  exact ⟨K₀, K₁, R, hK₀, hK₁, hR, hK₀B, hK₁B,
    hRB.trans ((hBb e).1.trans ((hCp _).boundary_subset.trans (hsubs _).2.1)),
    hcover, hi, ho, hRT⟩

end DifferentialGeometry.Topology.PiecewiseLinear
