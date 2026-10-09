/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceDiskSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactMeridianSystem
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactSeparatingTrace

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C V : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {H : Finset E3 → Set E3} {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}

theorem Section34CompactCutFrame.disk_subset_vertexBall_of_boundary_subset
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (s : Section34CompactSimplexIndex K 3) (w : Section34CompactVertexIndex K K')
    (hw : Section34Incident w.1 s.1) {D : Set E3} {q : (Fin 3 → ℝ) → E3}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hDT : D ⊆ frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s))
    (hJV : q '' stdSimplexBoundary 2 ⊆ section34CompactVertexBallImage src f₁ w)
    (hJdisj : ∀ e : Section34CompactEdgeIndex K K', Section34Incident e.1 s.1 →
      Disjoint (q '' stdSimplexBoundary 2) (section34CompactSplitDiskImage srcBd f₁ e)) :
    D ⊆ section34CompactVertexBallImage srcBd f₁ w ∧
      ∀ e : Section34CompactEdgeIndex K K', Section34Incident e.1 s.1 →
        Disjoint D (section34CompactSplitDiskImage src f₁ e) := by
  obtain ⟨-, hf₁, -, -, -, -, -, -, hnest, -⟩ := id hgraph
  obtain ⟨-, -, -, -, hT, -⟩ := hnest s
  have hDE : ∀ e : Section34CompactEdgeIndex K K', Section34Incident e.1 s.1 →
      Disjoint D (section34CompactSplitDiskImage src f₁ e) := by
    intro e he
    have hcell := hcut.isPLCellOn_splitDiskImage hf₁ e
    have hmeet := (hcut.splitDiskImage_faceTorus_boundary hf₁ s e he).2.1
    have hBdT : section34CompactSplitDiskImage srcBd f₁ e ⊆
        frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) :=
      fun x hx => (hmeet.symm.subset hx).1
    have hdis := hT.isPLTorus_frontier.disjoint_disk_of_essential_circle hq hDT
      hcell.isPLSphere_one_of_two hBdT (hJdisj e he).symm
      (hcut.splitDiskBoundary_is_essential hf₁ s e he).2
    exact Set.disjoint_left.mpr fun x hxD hxE =>
      Set.disjoint_left.mp hdis hxD (hmeet.subset ⟨hDT hxD, hxE⟩)
  have hDV : D ⊆ section34CompactVertexBallImage src f₁ w := by
    classical
    obtain ⟨n, v, -, hv, hadj, hnext, -, -, hU⟩ :=
      exists_cycle_order_compact_face_vertex_balls hcut hf₁ s
    obtain ⟨i₀, hi₀⟩ := (hv w).mp hw
    let O := ⋃ j ∈ {j : Fin (n + 3) | j ≠ i₀}, section34CompactVertexBallImage src f₁ (v j)
    have hO : IsClosed O := (Set.toFinite _).isClosed_biUnion fun j _ =>
      (hcut.isPLCellOn_vertexBallImage hf₁ (v j)).isCompact.isClosed
    have hcover : D ⊆ section34CompactVertexBallImage src f₁ (v i₀) ∪ O := by
      intro x hx
      have hxT := hT.isPolyhedron.isClosed.frontier_subset (hDT hx)
      rw [← hU] at hxT
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hxT
      by_cases hji : j = i₀
      · exact Or.inl (hji ▸ hxj)
      · exact Or.inr (mem_iUnion₂.mpr ⟨j, hji, hxj⟩)
    have hinter : D ∩ (section34CompactVertexBallImage src f₁ (v i₀) ∩ O) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hxD, hx₀, hxO⟩
      obtain ⟨j, hji, hxj⟩ := mem_iUnion₂.mp hxO
      have hij := (hadj i₀ j hji.symm).mpr ⟨x, hx₀, hxj⟩
      obtain ⟨e, he, heq⟩ := hnext i₀ j hij
      exact Set.disjoint_left.mp (hDE e he) hxD (heq.symm.subset ⟨hx₀, hxj⟩)
    have hD : IsPLBall 2 D := ⟨q, hq⟩
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hD.isConnected.isPreconnected
        (section34CompactVertexBallImage src f₁ (v i₀)) O
        (hcut.isPLCellOn_vertexBallImage hf₁ (v i₀)).isCompact.isClosed hO hcover hinter with
      hd | hd
    · rwa [hi₀] at hd
    · obtain ⟨x, hx⟩ := hq.isPLSphere_image_stdSimplexBoundary.nonempty
      have hxD : x ∈ D := by
        obtain ⟨a, ha, rfl⟩ := hx
        exact hq.bijOn.mapsTo ha.1
      have hxV : x ∈ section34CompactVertexBallImage src f₁ (v i₀) := hi₀.symm ▸ hJV hx
      exact (Set.notMem_empty x (hinter ▸ ⟨hxD, hxV, hd hxD⟩)).elim
  refine ⟨?_, hDE⟩
  rw [(hcut.isPLCellOn_vertexBallImage hf₁ w).boundary_eq_frontier]
  have hVT : section34CompactVertexBallImage src f₁ w ⊆
      section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s :=
    fun x hx => mem_iUnion₂.mpr ⟨⟨(s, w), hw⟩, rfl, hx⟩
  exact fun x hx => ⟨subset_closure (hDV hx), fun hi => (hDT hx).2 (interior_mono hVT hi)⟩

theorem exists_vertex_disk_avoiding_other_face_seams
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    {s t : Section34CompactSimplexIndex K 3} (hst : s ≠ t)
    (w : Section34CompactVertexIndex K K') (hwt : Section34Incident w.1 t.1)
    {J : Set E3} (hJ : IsPLSphere 1 J) (hJP : J ⊆ fblBd s)
    (hJV : J ⊆ section34CompactVertexBallImage src f₁ w)
    (hJN : J ⊆ frontier (⋃ v, section34CompactVertexBallImage src f₁ v))
    (hJdisj : ∀ e : Section34CompactEdgeIndex K K', Section34Incident e.1 t.1 →
      Disjoint J (section34CompactSplitDiskImage srcBd f₁ e)) :
    ∃ (D : Set E3) (q : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ q '' stdSimplexBoundary 2 = J ∧
        D ⊆ section34CompactVertexBallImage srcBd f₁ w ∧
        ∀ e : Section34CompactEdgeIndex K K', Section34Incident e.1 t.1 →
          Disjoint D (section34CompactSplitDiskImage src f₁ e) := by
  have hsep := hinv.trace_circle_separates_other_face_torus hcut hgraph hst w hwt hJ hJP hJV hJN
  have hVT : section34CompactVertexBallImage src f₁ w ⊆
      section34CompactFaceTorus (section34CompactVertexBallImage src f₁) t :=
    fun x hx => mem_iUnion₂.mpr ⟨⟨(t, w), hwt⟩, rfl, hx⟩
  have hTN : section34CompactFaceTorus (section34CompactVertexBallImage src f₁) t ⊆
      ⋃ v, section34CompactVertexBallImage src f₁ v := by
    intro x hx
    obtain ⟨a, -, hxa⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion.mpr ⟨a.1.2, hxa⟩
  have hJΘ : J ⊆
      frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) t) :=
    fun x hx => ⟨subset_closure (hVT (hJV hx)), fun hi => (hJN hx).2 (interior_mono hTN hi)⟩
  obtain ⟨-, -, -, -, -, -, -, -, hnest, -⟩ := id hgraph
  obtain ⟨-, -, -, -, hT, -⟩ := hnest t
  obtain ⟨D, q, hq, hDT, hJq⟩ :=
    hT.isPLTorus_frontier.exists_isPLHomeomorphOn_disk_of_not_isPreconnected_sdiff hJ hJΘ hsep
  obtain ⟨hDV, hDE⟩ := hcut.disk_subset_vertexBall_of_boundary_subset hgraph t w hwt hq hDT
    (by rwa [← hJq]) (by simpa only [← hJq] using hJdisj)
  exact ⟨D, q, hq, hJq.symm, hDV, hDE⟩

end DifferentialGeometry.Topology.PiecewiseLinear
