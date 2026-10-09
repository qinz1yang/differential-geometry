/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CirclePartition
import DifferentialGeometry.Topology.PiecewiseLinear.CrossingBallSeam
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDiskLocalization

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem eventually_trace_eq_circle {ι : Type} [Finite ι] {F : ι → Set E3}
    (hF : ∀ i, IsPLSphere 1 (F i)) (hdis : Pairwise fun i j => Disjoint (F i) (F j))
    {J : Set E3} (hJ : IsPLSphere 1 J) (hJU : J ⊆ ⋃ i, F i) {x : E3} (hx : x ∈ J) :
    ∀ᶠ y in 𝓝 x, y ∈ ⋃ i, F i ↔ y ∈ J := by
  have hpair : (range F).PairwiseDisjoint id := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    exact hdis (fun hij => hne (congrArg F hij))
  have hmem : J ∈ range F :=
    (setOf_isPLSphere_one_subset_sUnion_eq (finite_range F)
      (by rintro _ ⟨i, rfl⟩; exact hF i) hpair).subset
        ⟨hJ, by simpa only [sUnion_range] using hJU⟩
  obtain ⟨k, hk⟩ := hmem
  let O := (⋃ i ∈ {i | i ≠ k}, F i)ᶜ
  have hO : IsOpen O :=
    ((Set.toFinite _).isClosed_biUnion fun i _ => (hF i).isPolyhedron.isClosed).isOpen_compl
  have hxO : x ∈ O := by
    intro hbad
    obtain ⟨i, hik, hxi⟩ := mem_iUnion₂.mp hbad
    exact Set.disjoint_left.mp (hdis hik) hxi (hk.symm ▸ hx)
  filter_upwards [hO.mem_nhds hxO] with y hyO
  constructor
  · intro hy
    obtain ⟨i, hyi⟩ := mem_iUnion.mp hy
    by_cases hik : i = k
    · exact hk ▸ hik ▸ hyi
    · exact (hyO (mem_iUnion₂.mpr ⟨i, hik, hyi⟩)).elim
  · intro hy
    exact mem_iUnion.mpr ⟨k, hk.symm ▸ hy⟩

variable {C V : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {H : Finset E3 → Set E3} {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}

theorem Section34CompactFaceBallInvariants.disjoint_splitDiskImage_of_circle_subset_vertexBall
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (s : Section34CompactSimplexIndex K 3) (w : Section34CompactVertexIndex K K')
    {J : Set E3} (hJ : IsPLSphere 1 J) (hJP : J ⊆ fblBd s)
    (hJV : J ⊆ section34CompactVertexBallImage src f₁ w)
    (hJN : J ⊆ frontier (⋃ v, section34CompactVertexBallImage src f₁ v))
    (e : Section34CompactEdgeIndex K K') :
    Disjoint J (section34CompactSplitDiskImage src f₁ e) := by
  have := finite_section34CompactGraphIndex hcut.2.2.1 (section34CompactGraphSkeleton K) 1
  have hV : ∀ v, IsPLBall 3 (section34CompactVertexBallImage src f₁ v) :=
    fun v => (hcut.isPLCellOn_vertexBallImage hf₁ v).isPLBall_three
  apply Set.disjoint_left.mpr
  intro x hxJ hxE
  have hxγ : x ∈ section34CompactSplitDiskImage srcBd f₁ e := by
    by_contra hnot
    exact (hJN hxJ).2 (hcut.splitDiskImage_sdiff_subset_interior hf₁ e ⟨hxE, hnot⟩)
  have hwe := hcut.subset_of_mem_splitDiskImage hf₁ hxE (hJV hxJ)
  obtain ⟨u, hwu, hends, heq⟩ : ∃ u : Section34CompactVertexIndex K K', w ≠ u ∧
      (e.1 : Set E3) = (w.1 : Set E3) ∪ (u.1 : Set E3) ∧
      section34CompactSplitDiskImage src f₁ e =
        section34CompactVertexBallImage src f₁ w ∩
          section34CompactVertexBallImage src f₁ u := by
    obtain ⟨a, b, hab, heab, heq⟩ := hcut.splitDiskImage_eq_inter hf₁ e
    rcases eq_or_eq_of_section34CompactVertexIndex_subset e heab hwe with rfl | rfl
    · exact ⟨b, hab, heab, heq⟩
    · exact ⟨a, hab.symm, heab.trans (union_comm _ _), heq.trans (inter_comm _ _)⟩
  have hlocal := eventually_mem_frontier_iUnion_iff_pair
    (fun v => (hV v).isPolyhedron.isClosed) (i := w) (j := u) (x := x) (by
      intro v hvw hvu hxv
      rcases eq_or_eq_of_section34CompactVertexIndex_subset e hends
        (hcut.subset_of_mem_splitDiskImage hf₁ hxE hxv) with hv | hv
      · exact hvw hv
      · exact hvu hv)
  obtain ⟨ι, hι, F, hF, hdis, htrace, -⟩ :=
    exists_finite_trace_circles_of_crossings hcut hf₁ hinv s
  have : Finite ι := hι
  have hJtrace : J ⊆ ⋃ i, F i := fun y hy => htrace.subset ⟨hJP hy, hJN hy⟩
  have hlocalJ := eventually_trace_eq_circle hF hdis hJ hJtrace hxJ
  rw [← htrace] at hlocalJ
  obtain ⟨-, -, -, -, -, hcross, -⟩ := id hinv
  have hc : HasPLCurveCrossingOnAt (frontier (⋃ v, section34CompactVertexBallImage src f₁ v))
      (fblBd s ∩ frontier (⋃ v, section34CompactVertexBallImage src f₁ v))
      (section34CompactSplitDiskImage srcBd f₁ e) x := hcross s e x ⟨hJP hxJ, hxγ⟩
  obtain ⟨q, hq, hqb⟩ := (hcut.isPLCellOn_splitDiskImage hf₁ e).exists_isPLHomeomorphOn_stdSimplex
  have hq' : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
      (section34CompactVertexBallImage src f₁ w ∩
        section34CompactVertexBallImage src f₁ u) := heq ▸ hq
  have hDU : section34CompactVertexBallImage src f₁ w ∩
      section34CompactVertexBallImage src f₁ u ⊆
        frontier (section34CompactVertexBallImage src f₁ u) := by
    have hD : IsPLBall 2 (section34CompactVertexBallImage src f₁ u ∩
        section34CompactVertexBallImage src f₁ w) := by
      rw [inter_comm]
      exact ⟨q, hq'⟩
    rw [inter_comm]
    exact (hV w).inter_subset_frontier_of_isPLBall hD (by decide)
  have hc' := hc.congr hlocal hlocalJ
    (Filter.Eventually.of_forall fun y => by rw [hqb])
  exact hc'.not_subset_of_ball_seam (hV w).isPolyhedron.isClosed
    (hV u).isPolyhedron.isClosed (hV u).isPLSphere_frontier hq' hDU hJV

theorem exists_vertex_disk_avoiding_other_face_split_disks
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    {s t : Section34CompactSimplexIndex K 3} (hst : s ≠ t)
    (w : Section34CompactVertexIndex K K') (hwt : Section34Incident w.1 t.1)
    {J : Set E3} (hJ : IsPLSphere 1 J) (hJP : J ⊆ fblBd s)
    (hJV : J ⊆ section34CompactVertexBallImage src f₁ w)
    (hJN : J ⊆ frontier (⋃ v, section34CompactVertexBallImage src f₁ v)) :
    ∃ (D : Set E3) (q : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ q '' stdSimplexBoundary 2 = J ∧
        D ⊆ section34CompactVertexBallImage srcBd f₁ w ∧
        ∀ e : Section34CompactEdgeIndex K K', Section34Incident e.1 t.1 →
          Disjoint D (section34CompactSplitDiskImage src f₁ e) := by
  exact exists_vertex_disk_avoiding_other_face_seams hinv hcut hgraph hst w hwt hJ hJP hJV hJN
    fun e _ => (hinv.disjoint_splitDiskImage_of_circle_subset_vertexBall hcut hgraph.2.1
      s w hJ hJP hJV hJN e).mono_right
        (hcut.isPLCellOn_splitDiskImage hgraph.2.1 e).boundary_subset

end DifferentialGeometry.Topology.PiecewiseLinear
