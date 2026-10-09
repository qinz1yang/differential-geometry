/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellBoundaryMarkedMap
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

theorem exists_section34_reference_sphere_maps
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends
      Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hDv : ∀ w, IsPLCellOn 3 (Dv w) (DvBd w))
    (hDd : ∀ e, IsPLCellOn 2 (Dd e) (DdBd e))
    (hDdBd : ∀ e, Dd e ⊆ DvBd (ends e).1 ∩ DvBd (ends e).2)
    (hDddisj : ∀ e d, e ≠ d → Disjoint (Dd e) (Dd d)) :
    ∃ b : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
      (∀ w, IsPLHomeomorphInto 3 (b w) (srcBd (.vertexBall w))) ∧
      (∀ w, b w '' srcBd (.vertexBall w) = DvBd w) ∧
      ∀ w e, (w = (ends e).1 ∨ w = (ends e).2) →
        b w '' src (.splitDisk e) = Dd e := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, hends, -⟩ := id hprep
  have hpoint (w : Section34VertexIndex 𝒦 𝒦') :
      ∃ b : M₁ → M₂,
        IsPLHomeomorphInto 3 b (srcBd (.vertexBall w)) ∧
        b '' srcBd (.vertexBall w) = DvBd w ∧
        ∀ e, (w = (ends e).1 ∨ w = (ends e).2) →
          b '' src (.splitDisk e) = Dd e := by
    let I := {e : Section34EdgeIndex 𝒦 𝒦' //
      w = (ends e).1 ∨ w = (ends e).2}
    have _ : Finite I := section34_incident_edges_finite (fun e => (hends e).2.1) w
    obtain ⟨e₀, he₀⟩ :=
      exists_section34Vertex_incident_edge hframe (fun e => (hends e).2.1) w
    let i₀ : I := ⟨e₀, he₀⟩
    obtain ⟨hsD, hsDB, hsdis⟩ :=
      section34_source_vertex_boundary_disks hframe (fun e => (hends e).2.2) w
    obtain ⟨htD, htDB, htdis⟩ :=
      section34_target_vertex_boundary_disks hDd hDdBd hDddisj w
    obtain ⟨b, hb, hbBd, hbD⟩ :=
      exists_isPLHomeomorphInto_boundary_disk_family
        (hframe.2.2.2.1 (.vertexBall w)) (hDv w)
        (fun i : I => hsD i) (fun i : I => htD i)
        (fun i : I => hsDB i) (fun i : I => htDB i)
        (fun i j hij => hsdis hij) (fun i j hij => htdis hij) i₀
    exact ⟨b, hb, hbBd, fun e he => hbD ⟨e, he⟩⟩
  choose b hb hbBd hbD using hpoint
  exact ⟨b, hb, hbBd, fun w e he => hbD w e he⟩

end DifferentialGeometry.Topology.PiecewiseLinear
