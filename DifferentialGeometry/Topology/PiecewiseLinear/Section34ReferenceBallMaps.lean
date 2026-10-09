/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ReferenceSphereMaps
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexIncidentEdge
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IncidentEdgeFinite

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  [FiniteDimensional ℝ Ea] {M₁ M₂ : Type u}
  [TopologicalSpace M₁] [T2Space M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
  {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q Dv DvBd : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Dd DdBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ :
    Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}

theorem exists_section34_reference_ball_maps
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends
      Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hDv : ∀ w, IsPLCellOn 3 (Dv w) (DvBd w))
    (hDd : ∀ e, IsPLCellOn 2 (Dd e) (DdBd e))
    (hDdBd : ∀ e, Dd e ⊆ DvBd (ends e).1 ∩ DvBd (ends e).2)
    (hDddisj : ∀ e d, e ≠ d → Disjoint (Dd e) (Dd d)) :
    ∃ R : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
      (∀ w, IsPLHomeomorphInto 3 (R w) (src (.vertexBall w))) ∧
      (∀ w, R w '' src (.vertexBall w) = Dv w) ∧
      (∀ w, R w '' srcBd (.vertexBall w) = DvBd w) ∧
      ∀ w e, (w = (ends e).1 ∨ w = (ends e).2) →
        R w '' src (.splitDisk e) = Dd e := by
  obtain ⟨b, hb, hbBd, hbD⟩ := exists_section34_reference_sphere_maps
    hframe hprep hDv hDd hDdBd hDddisj
  have hext (w : Section34VertexIndex 𝒦 𝒦') :
      ∃ R : M₁ → M₂, IsPLHomeomorphInto 3 R (src (.vertexBall w)) ∧
        R '' src (.vertexBall w) = Dv w ∧ EqOn R (b w) (srcBd (.vertexBall w)) := by
    obtain ⟨A, r, u, hr, hu, hS, hSB⟩ := hframe.2.2.2.1 (.vertexBall w)
    obtain ⟨B, s, v, hs, hv, hT, hTB⟩ := hDv w
    have hbw := hb w
    have hbim := hbBd w
    rw [hSB] at hbw
    rw [hSB, hTB] at hbim
    have hext := exists_isPLHomeomorphInto_extension_of_cell
      (by decide : 0 < 3) hr hs hu hv hbw Subset.rfl hbim
    simpa only [hS, hSB, hT, section34Dim] using hext
  choose R hR hRim hRb using hext
  obtain ⟨-, -, -, -, -, -, -, -, hends, -⟩ := id hprep
  refine ⟨R, hR, hRim, fun w => (hRb w).image_eq.trans (hbBd w), ?_⟩
  intro w e he
  obtain ⟨-, hDB, -⟩ := section34_source_vertex_boundary_disks
    hframe (fun e => (hends e).2.2) w
  have hDsub : src (.splitDisk e) ⊆ srcBd (.vertexBall w) := hDB ⟨e, he⟩
  exact ((hRb w).mono hDsub).image_eq.trans (hbD w e he)

end DifferentialGeometry.Topology.PiecewiseLinear
