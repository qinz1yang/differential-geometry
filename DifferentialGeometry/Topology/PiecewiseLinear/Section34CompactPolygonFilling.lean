/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDiskLocalization
import DifferentialGeometry.Topology.PiecewiseLinear.TorusDisjointCircleFilling

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C V : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {H : Finset E3 → Set E3} {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}

theorem exists_vertex_disk_of_disjoint_face_trace
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (t : Section34CompactSimplexIndex K 3) (w : Section34CompactVertexIndex K K')
    (hwt : Section34Incident w.1 t.1) {J : Set E3} (hJ : IsPLSphere 1 J)
    (hJV : J ⊆ section34CompactVertexBallImage src f₁ w)
    (hJN : J ⊆ frontier (⋃ v, section34CompactVertexBallImage src f₁ v))
    (hJP : Disjoint J (fblBd t))
    (hJγ : ∀ e : Section34CompactEdgeIndex K K', Section34Incident e.1 t.1 →
      Disjoint J (section34CompactSplitDiskImage srcBd f₁ e)) :
    ∃ (D : Set E3) (q : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ q '' stdSimplexBoundary 2 = J ∧
        D ⊆ section34CompactVertexBallImage srcBd f₁ w ∧
        ∀ e : Section34CompactEdgeIndex K K', Section34Incident e.1 t.1 →
          Disjoint D (section34CompactSplitDiskImage src f₁ e) := by
  let T := section34CompactFaceTorus (section34CompactVertexBallImage src f₁) t
  have hVT : section34CompactVertexBallImage src f₁ w ⊆ T :=
    fun x hx => mem_iUnion₂.mpr ⟨⟨(t, w), hwt⟩, rfl, hx⟩
  have hTN : T ⊆ ⋃ v, section34CompactVertexBallImage src f₁ v := by
    intro x hx
    obtain ⟨a, -, hxa⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion.mpr ⟨a.1.2, hxa⟩
  have hJΘ : J ⊆ frontier T := fun x hx =>
    ⟨subset_closure (hVT (hJV hx)), fun hi => (hJN hx).2 (interior_mono hTN hi)⟩
  obtain ⟨-, hf₁, -, -, -, -, -, -, hnest, -⟩ := id hgraph
  obtain ⟨-, -, -, -, hT, -⟩ := hnest t
  obtain ⟨n, F, -, hF, hdis, -, htrace, hcarry, -⟩ :=
    exists_positive_finite_compact_trace_circles hcut hgraph hinv t
  have hFT : ∀ i, F i ⊆ frontier T := fun i x hx =>
    (htrace.symm.subset (mem_iUnion.mpr ⟨i, hx⟩)).2
  have hJF : ∀ i, Disjoint J (F i) := fun i => hJP.mono_right fun x hx =>
    (htrace.symm.subset (mem_iUnion.mpr ⟨i, hx⟩)).1
  have hnull := (hcut.isPLCellOn_vertexBallImage hf₁ w).isPLBall_three.nullhomotopic_inclusion
    hJV hVT
  obtain ⟨D, q, hq, hDT, hqJ⟩ := exists_disk_of_nullhomotopic_circle_disjoint_carrier
    hT hF hFT hdis hcarry hJ hJΘ hJF hnull
  obtain ⟨hDS, hDE⟩ := hcut.disk_subset_vertexBall_of_boundary_subset hgraph t w hwt hq hDT
    (by rwa [← hqJ]) (by simpa only [← hqJ] using hJγ)
  exact ⟨D, q, hq, hqJ.symm, hDS, hDE⟩

end DifferentialGeometry.Topology.PiecewiseLinear
