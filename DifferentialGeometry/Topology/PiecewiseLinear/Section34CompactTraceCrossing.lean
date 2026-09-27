/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVertexTrace

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {h f₁ : E3 → E3}
  {H : Finset E3 → Set E3} {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}

theorem Section34CompactFaceBallInvariants.curve_crossing_trace_circle
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (s : Section34CompactSimplexIndex K 3) {J : Set E3} (hJ : IsPLSphere 1 J)
    (hJT : J ⊆ fblBd s ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w))
    (e : Section34CompactEdgeIndex K K') {x : E3}
    (hx : x ∈ J ∩ section34CompactSplitDiskImage srcBd f₁ e) :
    HasPLCurveCrossingOnAt (frontier (⋃ w, section34CompactVertexBallImage src f₁ w))
      J (section34CompactSplitDiskImage srcBd f₁ e) x := by
  obtain ⟨ι, hι, F, hF, hdis, htrace, -⟩ :=
    exists_finite_trace_circles_of_crossings hcut hf₁ hinv s
  have : Finite ι := hι
  have hloc := eventually_trace_eq_circle hF hdis hJ (hJT.trans htrace.subset) hx.1
  rw [← htrace] at hloc
  obtain ⟨-, -, -, -, -, hc, -⟩ := id hinv
  have hc' : HasPLCurveCrossingOnAt
      (frontier (⋃ w, section34CompactVertexBallImage src f₁ w))
      (fblBd s ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w))
      (section34CompactSplitDiskImage srcBd f₁ e) x := hc s e x ⟨(hJT hx.1).1, hx.2⟩
  exact hc'.congr
    (Filter.Eventually.of_forall fun _ => Iff.rfl) hloc
    (Filter.Eventually.of_forall fun _ => Iff.rfl)

theorem Section34CompactFaceBallInvariants.eventually_frontier_face_torus_eq
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (s : Section34CompactSimplexIndex K 3) {x : E3} (hx : x ∈ fblBd s) :
    ∀ᶠ y in 𝓝 x, y ∈ frontier (⋃ w, section34CompactVertexBallImage src f₁ w) ↔
      y ∈ frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) := by
  have := finite_section34CompactGraphIndex hcut.2.2.1 (section34CompactGraphSkeleton K) 1
  let O := (⋃ w ∈ {w : Section34CompactVertexIndex K K' | ¬ Section34Incident w.1 s.1},
    section34CompactVertexBallImage src f₁ w)ᶜ
  have hO : IsOpen O := ((Set.toFinite _).isClosed_biUnion fun w _ =>
    (hcut.isPLCellOn_vertexBallImage hf₁ w).isCompact.isClosed).isOpen_compl
  have hxO : x ∈ O := by
    intro hbad
    obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.mp hbad
    exact Set.notMem_empty x (hinv.2.2.1 s w hw ▸ ⟨(hinv.1 s).boundary_subset hx, hxw⟩)
  have hNO : (⋃ w, section34CompactVertexBallImage src f₁ w) ∩ O =
      section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s ∩ O := by
    ext y
    constructor
    · rintro ⟨hy, hyO⟩
      obtain ⟨w, hyw⟩ := mem_iUnion.mp hy
      by_cases hw : Section34Incident w.1 s.1
      · exact ⟨mem_iUnion₂.mpr ⟨⟨(s, w), hw⟩, rfl, hyw⟩, hyO⟩
      · exact (hyO (mem_iUnion₂.mpr ⟨w, hw, hyw⟩)).elim
    · rintro ⟨hy, hyO⟩
      obtain ⟨a, -, hya⟩ := mem_iUnion₂.mp hy
      exact ⟨mem_iUnion.mpr ⟨a.1.2, hya⟩, hyO⟩
  have hfr : frontier (⋃ w, section34CompactVertexBallImage src f₁ w) ∩ O =
      frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) ∩ O := by
    rw [← frontier_inter_open_inter hO, hNO, frontier_inter_open_inter hO]
  filter_upwards [hO.mem_nhds hxO] with y hy
  exact ⟨fun h => (hfr.subset ⟨h, hy⟩).1, fun h => (hfr.symm.subset ⟨h, hy⟩).1⟩

theorem Section34CompactFaceBallInvariants.curve_crossing_on_face_torus
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (s : Section34CompactSimplexIndex K 3) {J : Set E3} (hJ : IsPLSphere 1 J)
    (hJT : J ⊆ fblBd s ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w))
    (e : Section34CompactEdgeIndex K K') {x : E3}
    (hx : x ∈ J ∩ section34CompactSplitDiskImage srcBd f₁ e) :
    HasPLCurveCrossingOnAt
      (frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s))
      J (section34CompactSplitDiskImage srcBd f₁ e) x := by
  exact (hinv.curve_crossing_trace_circle hcut hf₁ s hJ hJT e hx).congr
    (hinv.eventually_frontier_face_torus_eq hcut hf₁ s (hJT hx.1).1)
    (Filter.Eventually.of_forall fun _ => Iff.rfl) (Filter.Eventually.of_forall fun _ => Iff.rfl)

end DifferentialGeometry.Topology.PiecewiseLinear
