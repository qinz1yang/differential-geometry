/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactSeparatingOperations
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTraceCarrying

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C V : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {H : Finset E3 → Set E3} {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}

theorem Section34CompactFaceBallInvariants.trace_circle_mem_components
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (s : Section34CompactSimplexIndex K 3) {J : Set E3} (hJ : IsPLSphere 1 J)
    (hJT : J ⊆ fblBd s ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w)) :
    J ∈ section34CompactTraceComponents (section34CompactVertexBallImage src f₁) fblBd s := by
  obtain ⟨ι, hι, F, hF, hdis, htrace, -⟩ :=
    exists_finite_trace_circles_of_crossings hcut hf₁ hinv s
  have : Finite ι := hι
  have hpair : (range F).PairwiseDisjoint id := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    exact hdis (fun hij => hne (congrArg F hij))
  have hJrange : J ∈ range F :=
    (setOf_isPLSphere_one_subset_sUnion_eq (finite_range F)
      (by rintro _ ⟨i, rfl⟩; exact hF i) hpair).subset
        ⟨hJ, by simpa only [sUnion_range] using hJT.trans htrace.subset⟩
  obtain ⟨x, hx⟩ := hJ.nonempty
  have hxT := hJT hx
  have hcover : connectedComponentIn
      (fblBd s ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w)) x ⊆
        ⋃₀ range F := by
    simpa only [sUnion_range, ← htrace] using connectedComponentIn_subset
      (fblBd s ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w)) x
  obtain ⟨A, ⟨hA, hsub⟩, -⟩ :=
    existsUnique_subset_of_isConnected_of_finite_closed_partition
      (isConnected_connectedComponentIn_iff.mpr hxT) (finite_range F)
      (by rintro _ ⟨i, rfl⟩; exact (hF i).isPolyhedron.isClosed) hpair hcover
  have hAJ : A = J := by
    by_contra hne
    exact Set.disjoint_left.mp (hpair hA hJrange hne)
      (hsub (mem_connectedComponentIn hxT)) hx
  refine ⟨x, hxT, Subset.antisymm ?_ ?_⟩
  · rwa [hAJ] at hsub
  · exact hJ.isConnected.isPreconnected.subset_connectedComponentIn hx hJT

theorem Section34CompactFaceBallInvariants.trace_circle_nonseparating_of_subset_of_no_operation
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (hnc : ∀ t, ¬ Section34CompactCompression K K'
      (section34CompactVertexBallImage srcBd f₁)
      (section34CompactSplitDiskImage src f₁) fbl fblBd t)
    (hnb : ∀ t, ¬ Section34CompactBigonSlide K K' (section34CompactVertexBallImage src f₁)
      (section34CompactVertexBallImage srcBd f₁) (section34CompactSplitDiskImage src f₁)
      (section34CompactSplitDiskImage srcBd f₁) fblBd t)
    (s : Section34CompactSimplexIndex K 3) {J : Set E3} (hJ : IsPLSphere 1 J)
    (hJT : J ⊆ fblBd s ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w)) :
    IsPreconnected
      (frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) \ J) := by
  exact hinv.trace_circle_nonseparating_of_no_operation hcut hgraph hnc hnb s hJ
    (hinv.trace_circle_mem_components hcut hgraph.2.1 s hJ hJT)

theorem Section34CompactFaceBallInvariants.trace_circle_homologyMap_ne_zero_of_no_operation
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (hnc : ∀ t, ¬ Section34CompactCompression K K'
      (section34CompactVertexBallImage srcBd f₁)
      (section34CompactSplitDiskImage src f₁) fbl fblBd t)
    (hnb : ∀ t, ¬ Section34CompactBigonSlide K K' (section34CompactVertexBallImage src f₁)
      (section34CompactVertexBallImage srcBd f₁) (section34CompactSplitDiskImage src f₁)
      (section34CompactSplitDiskImage srcBd f₁) fblBd t)
    (s : Section34CompactSimplexIndex K 3) {J : Set E3} (hJ : IsPLSphere 1 J)
    (hJT : J ⊆ fblBd s ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w))
    (hsub : J ⊆ section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) :
    integralSingularHomologyMap 1
      (⟨inclusion hsub, continuous_inclusion hsub⟩ :
        C(J, section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s)) ≠ 0 := by
  have hnonsep :=
    hinv.trace_circle_nonseparating_of_subset_of_no_operation hcut hgraph hnc hnb s hJ hJT
  obtain ⟨n, F, -, hF, hdis, hFN, hFΘ, hcarry, -⟩ :=
    exists_positive_finite_compact_trace_circles hcut hgraph hinv s
  have hpair : (range F).PairwiseDisjoint id := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    exact hdis (fun hij => hne (congrArg F hij))
  have hJrange : J ∈ range F :=
    (setOf_isPLSphere_one_subset_sUnion_eq (finite_range F)
      (by rintro _ ⟨i, rfl⟩; exact hF i) hpair).subset
        ⟨hJ, by simpa only [sUnion_range] using hJT.trans hFN.subset⟩
  obtain ⟨i, rfl⟩ := hJrange
  obtain ⟨-, -, -, -, -, -, -, -, hnest, -⟩ := id hgraph
  obtain ⟨-, -, -, -, hT, -⟩ := hnest s
  have hFsub : ∀ k, F k ⊆
      frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) := by
    intro k x hx
    exact (hFΘ.symm.subset (mem_iUnion.mpr ⟨k, hx⟩)).2
  intro hzero
  exact trace_circle_separates_of_zero_homology_image hT hF hFsub hdis hcarry i hsub hzero
    hnonsep

end DifferentialGeometry.Topology.PiecewiseLinear
