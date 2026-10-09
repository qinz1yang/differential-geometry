/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IncidentEdgeFinite

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [TopologicalSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

private def incidentEdges (w : Section34VertexIndex 𝒦 𝒦') :=
  {e : Section34EdgeIndex 𝒦 𝒦' // w = (ends e).1 ∨ w = (ends e).2}

theorem exists_section34_source_vertex_holed_chart
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hends : ∀ e, src (.splitDisk e) =
      src (.vertexBall (ends e).1) ∩ src (.vertexBall (ends e).2))
    (w : Section34VertexIndex 𝒦 𝒦') (i₀ : incidentEdges (ends := ends) w) :
    ∃ (P : Set E3) (u : E3 → M₁) (χ : E3 → Plane) (Δ : Set Plane),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧
      src (.vertexBall w) = u '' P ∧ srcBd (.vertexBall w) = u '' frontier P ∧
      IsPLBall 2 Δ ∧
      IsPLHomeomorphOn χ
        (frontier P \
          (Function.invFunOn u P '' src (.splitDisk i₀.1) \
            Function.invFunOn u P '' srcBd (.splitDisk i₀.1))) Δ ∧
      χ '' (Function.invFunOn u P '' srcBd (.splitDisk i₀.1)) = frontier Δ ∧
      ∀ i : incidentEdges (ends := ends) w, i ≠ i₀ →
        χ '' (Function.invFunOn u P '' src (.splitDisk i.1)) ⊆ interior Δ ∧
        IsPLHomeomorphOn χ (Function.invFunOn u P '' src (.splitDisk i.1))
          (χ '' (Function.invFunOn u P '' src (.splitDisk i.1))) ∧
        χ '' (Function.invFunOn u P '' srcBd (.splitDisk i.1)) =
          frontier (χ '' (Function.invFunOn u P '' src (.splitDisk i.1))) := by
  obtain ⟨hD, hDB, hdis⟩ := section34_source_vertex_boundary_disks hframe hends w
  exact (hframe.2.2.2.1 (.vertexBall w)).exists_planar_chart_boundary_complement
    (fun i : incidentEdges (ends := ends) w => src (.splitDisk i.1))
    (fun i : incidentEdges (ends := ends) w => srcBd (.splitDisk i.1))
    hD hDB hdis i₀

theorem exists_section34_target_vertex_holed_chart
    {Dv DvBd : Section34VertexIndex 𝒦 𝒦' → Set M₂}
    {Dd DdBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
    (hDv : ∀ w, IsPLCellOn 3 (Dv w) (DvBd w))
    (hDd : ∀ e, IsPLCellOn 2 (Dd e) (DdBd e))
    (hDdBd : ∀ e, Dd e ⊆ DvBd (ends e).1 ∩ DvBd (ends e).2)
    (hDddisj : ∀ e d, e ≠ d → Disjoint (Dd e) (Dd d))
    (w : Section34VertexIndex 𝒦 𝒦') (i₀ : incidentEdges (ends := ends) w) :
    ∃ (P : Set E3) (u : E3 → M₂) (χ : E3 → Plane) (Δ : Set Plane),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧
      Dv w = u '' P ∧ DvBd w = u '' frontier P ∧
      IsPLBall 2 Δ ∧
      IsPLHomeomorphOn χ
        (frontier P \
          (Function.invFunOn u P '' Dd i₀.1 \
            Function.invFunOn u P '' DdBd i₀.1)) Δ ∧
      χ '' (Function.invFunOn u P '' DdBd i₀.1) = frontier Δ ∧
      ∀ i : incidentEdges (ends := ends) w, i ≠ i₀ →
        χ '' (Function.invFunOn u P '' Dd i.1) ⊆ interior Δ ∧
        IsPLHomeomorphOn χ (Function.invFunOn u P '' Dd i.1)
          (χ '' (Function.invFunOn u P '' Dd i.1)) ∧
        χ '' (Function.invFunOn u P '' DdBd i.1) =
          frontier (χ '' (Function.invFunOn u P '' Dd i.1)) := by
  obtain ⟨hD, hDB, hdis⟩ :=
    section34_target_vertex_boundary_disks hDd hDdBd hDddisj w
  exact (hDv w).exists_planar_chart_boundary_complement
    (fun i : incidentEdges (ends := ends) w => Dd i.1)
    (fun i : incidentEdges (ends := ends) w => DdBd i.1)
    hD hDB hdis i₀

end DifferentialGeometry.Topology.PiecewiseLinear
