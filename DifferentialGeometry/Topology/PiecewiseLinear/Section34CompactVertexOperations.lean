/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocalInnermostDisk
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactMouthAvoidance

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C V : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {H : Finset E3 → Set E3} {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}

theorem Section34CompactCutFrame.frontier_eventually_eq_vertexBallBoundary
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (w : Section34CompactVertexIndex K K') {x : E3}
    (hxw : x ∈ section34CompactVertexBallImage src f₁ w)
    (hxE : ∀ e : Section34CompactEdgeIndex K K', x ∉ section34CompactSplitDiskImage src f₁ e) :
    ∀ᶠ y in 𝓝 x, y ∈ frontier (⋃ v, section34CompactVertexBallImage src f₁ v) ↔
      y ∈ section34CompactVertexBallImage srcBd f₁ w := by
  have := finite_section34CompactGraphIndex hcut.2.2.1 (section34CompactGraphSkeleton K) 1
  have hloc := eventually_mem_frontier_iUnion_iff_pair
    (fun v => (hcut.isPLCellOn_vertexBallImage hf₁ v).isCompact.isClosed)
    (i := w) (j := w) (x := x) (by
      intro v hvw _ hxv
      obtain ⟨e, hxe⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁ hvw hxv hxw
      exact hxE e hxe)
  simpa only [union_self, ← (hcut.isPLCellOn_vertexBallImage hf₁ w).boundary_eq_frontier] using hloc

theorem exists_compact_compression_of_vertex_trace_circle
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (s : Section34CompactSimplexIndex K 3) (w : Section34CompactVertexIndex K K')
    {J : Set E3} (hJ : IsPLSphere 1 J) (hJP : J ⊆ fblBd s)
    (hJV : J ⊆ section34CompactVertexBallImage src f₁ w)
    (hJN : J ⊆ frontier (⋃ v, section34CompactVertexBallImage src f₁ v)) :
    ∃ t : Section34CompactSimplexIndex K 3,
      Section34CompactCompression K K' (section34CompactVertexBallImage srcBd f₁)
        (section34CompactSplitDiskImage src f₁) fbl fblBd t := by
  classical
  have := finite_section34CompactSimplexIndex hcut.2.1 3
  have hf₁ := hgraph.2.1
  have hV := hcut.isPLCellOn_vertexBallImage hf₁ w
  have hS : IsPLSphere 2 (section34CompactVertexBallImage srcBd f₁ w) := by
    rw [hV.boundary_eq_frontier]
    exact hV.isPLBall_three.isPLSphere_frontier
  let T := frontier (⋃ v, section34CompactVertexBallImage src f₁ v)
  obtain ⟨D₀, q₀, hq₀, hq₀J, hD₀S, hD₀E⟩ :=
    exists_vertex_disk_avoiding_all_split_disks hinv hcut hgraph s w hJ hJP hJV hJN
  have hlocal : ∀ x ∈ D₀, ∀ᶠ y in 𝓝 x, y ∈ T ↔
      y ∈ section34CompactVertexBallImage srcBd f₁ w := by
    intro x hx
    exact hcut.frontier_eventually_eq_vertexBallBoundary hf₁ w (hV.boundary_subset (hD₀S hx))
      fun e hxe => Set.disjoint_left.mp (hD₀E e) hx hxe
  have hD₀T : D₀ ⊆ T := fun x hx => (hlocal x hx).self_of_nhds.mpr (hD₀S hx)
  have hfamily : ∀ t : Section34CompactSimplexIndex K 3,
      ∃ (n : ℕ) (F : Fin n → Set E3), (∀ i, IsPLSphere 1 (F i)) ∧
        (Pairwise fun i j => Disjoint (F i) (F j)) ∧ fblBd t ∩ T = ⋃ i, F i := by
    intro t
    obtain ⟨n, F, -, hF, hdis, htrace, -⟩ :=
      exists_positive_finite_compact_trace_circles hcut hgraph hinv t
    exact ⟨n, F, hF, hdis, htrace⟩
  choose r F hF hdis htrace using hfamily
  let I := Σ t : Section34CompactSimplexIndex K 3, Fin (r t)
  let G : I → Set E3 := fun i => F i.1 i.2
  have hG : ∀ i, IsPLSphere 1 (G i) := fun i => hF i.1 i.2
  have hGP : ∀ i, G i ⊆ fblBd i.1 := fun i x hx =>
    (htrace i.1).symm.subset (mem_iUnion.mpr ⟨i.2, hx⟩) |>.1
  have hGT : ∀ i, G i ⊆ T := fun i x hx =>
    (htrace i.1).symm.subset (mem_iUnion.mpr ⟨i.2, hx⟩) |>.2
  have hGdis : Pairwise fun i j => Disjoint (G i) (G j) := by
    rintro ⟨t, i⟩ ⟨u, j⟩ hne
    by_cases htu : t = u
    · subst u
      exact hdis t (fun hij => hne (by cases hij; rfl))
    · apply Set.disjoint_left.mpr
      intro x hxi hxj
      exact (hGT ⟨t, i⟩ hxi).2
        (hinv.2.2.2.1 t u htu
          ⟨(hinv.1 t).boundary_subset (hGP ⟨t, i⟩ hxi),
            (hinv.1 u).boundary_subset (hGP ⟨u, j⟩ hxj)⟩)
  have hJU : J ⊆ ⋃ i, G i := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp ((htrace s).subset ⟨hJP hx, hJN hx⟩)
    exact mem_iUnion.mpr ⟨⟨s, i⟩, hxi⟩
  have hpair : (range G).PairwiseDisjoint id := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    exact hGdis (fun hij => hne (congrArg G hij))
  have hmem : J ∈ range G :=
    (setOf_isPLSphere_one_subset_sUnion_eq (finite_range G)
      (by rintro _ ⟨i, rfl⟩; exact hG i) hpair).subset
        ⟨hJ, by simpa only [sUnion_range] using hJU⟩
  obtain ⟨i₀, hi₀⟩ := hmem
  obtain ⟨i, D, q, hq, hDD₀, hqG, hclean⟩ :=
    hS.exists_innermost_disk_subset_of_eventually_eq hq₀ hD₀S hlocal hG hGT hGdis i₀
      (hq₀J.trans hi₀.symm)
  have hDT : D ⊆ T := hDD₀.trans hD₀T
  have hGD : G i ⊆ D := by
    rw [← hqG, ← hq.image_eq]
    exact image_mono fun x hx => hx.1
  have hDG : D ∩ fblBd i.1 = G i := by
    apply Subset.antisymm
    · rintro x ⟨hxD, hxP⟩
      obtain ⟨j, hxj⟩ := mem_iUnion.mp ((htrace i.1).subset ⟨hxP, hDT hxD⟩)
      by_cases hji : (⟨i.1, j⟩ : I) = i
      · exact hji ▸ hxj
      · exact (Set.disjoint_left.mp (hclean ⟨i.1, j⟩ hji) hxD hxj).elim
    · exact fun x hx => ⟨hGD hx, hGP i hx⟩
  have hball : ∀ t : Section34CompactSimplexIndex K 3, t ≠ i.1 → Disjoint D (fbl t) := by
    intro t hti
    have hbd : Disjoint D (fblBd t) := by
      apply Set.disjoint_left.mpr
      intro x hxD hxP
      obtain ⟨j, hxj⟩ := mem_iUnion.mp ((htrace t).subset ⟨hxP, hDT hxD⟩)
      exact Set.disjoint_left.mp (hclean ⟨t, j⟩ (fun heq => hti (congrArg Sigma.fst heq))) hxD hxj
    have hfr : Disjoint D (frontier (fbl t)ᶜ) := by
      rw [frontier_compl, ← (hinv.1 t).boundary_eq_frontier]
      exact hbd
    obtain ⟨x, hx⟩ := (hG i).nonempty
    have hnot : x ∉ fbl t := fun hxt => (hGT i hx).2
      (hinv.2.2.2.1 i.1 t hti.symm ⟨(hinv.1 i.1).boundary_subset (hGP i hx), hxt⟩)
    have hsub : D ⊆ (fbl t)ᶜ := IsPreconnected.subset_of_disjoint_frontier
      (show IsPLBall 2 D from ⟨q, hq⟩).isConnected.isPreconnected ⟨x, hGD hx, hnot⟩ hfr
    exact Set.disjoint_left.mpr fun y hy hyt => hsub hy hyt
  refine ⟨i.1, w, D, G i, ?_, hDD₀.trans hD₀S, hGP i, hDG, ?_, ?_⟩
  · rw [← hqG]
    exact isPLCellOn_id_of_isPLBall hq
  · exact fun e => (hD₀E e).mono_left hDD₀
  · exact fun t hti => (hball t hti).mono_left sdiff_subset

theorem Section34CompactFaceBallInvariants.not_circle_subset_vertexBall_of_no_compression
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (hnc : ∀ t : Section34CompactSimplexIndex K 3,
      ¬ Section34CompactCompression K K' (section34CompactVertexBallImage srcBd f₁)
        (section34CompactSplitDiskImage src f₁) fbl fblBd t)
    (s : Section34CompactSimplexIndex K 3) (w : Section34CompactVertexIndex K K')
    {J : Set E3} (hJ : IsPLSphere 1 J) (hJP : J ⊆ fblBd s)
    (hJN : J ⊆ frontier (⋃ v, section34CompactVertexBallImage src f₁ v)) :
    ¬ J ⊆ section34CompactVertexBallImage src f₁ w := by
  intro hJV
  obtain ⟨t, ht⟩ := exists_compact_compression_of_vertex_trace_circle
    hinv hcut hgraph s w hJ hJP hJV hJN
  exact hnc t ht
end DifferentialGeometry.Topology.PiecewiseLinear
