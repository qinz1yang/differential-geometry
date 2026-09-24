/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

/-! # Section34Edge Ends -/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}

theorem exists_section34_edge_ends
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd) :
    ∃ ends : Section34EdgeIndex 𝒦 𝒦' →
        Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦',
      ∀ e, (ends e).1 ≠ (ends e).2 ∧
        (e.1 : Set Ea) = ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea) ∧
        src (.splitDisk e) = src (.vertexBall (ends e).1) ∩
          src (.vertexBall (ends e).2) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, he, -⟩ :=
    hframe
  choose a b hab using he
  exact ⟨fun e => (a e, b e), hab⟩

end DifferentialGeometry.Topology.PiecewiseLinear
