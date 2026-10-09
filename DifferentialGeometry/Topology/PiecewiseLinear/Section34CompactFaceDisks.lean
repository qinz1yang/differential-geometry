/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Homotopy
import DifferentialGeometry.Topology.PiecewiseLinear.BallHomotopy
import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.LabelledCellAssemblyWitness
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTraceArcs
import DifferentialGeometry.Topology.PiecewiseLinear.SphereInnermostDisk

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Leaves

variable {C V : Set (EuclideanSpace ℝ (Fin 3))}
  {h f₁ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {ε : ℝ}
  {K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {src srcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3))}
  {H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {env : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}

theorem exists_compactFaceDisks (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (htrace : Section34CompactTrace K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage srcBd f₁) fblBd) :
    ∃ (tgtD tgtDBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
      (tgtA tgtABd : Section34CompactArcIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
      (tgtP : Section34CompactMarkIndex K K' → Set (EuclideanSpace ℝ (Fin 3))),
      Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
        (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
        fblBd tgtD tgtDBd tgtA tgtABd tgtP := by
  classical
  obtain ⟨-, hf₁, -⟩ := id hgraph
  obtain ⟨-, -, hK'fin, -⟩ := id hcut
  have _ := finite_section34CompactGraphIndex hK'fin (section34CompactGraphSkeleton K) 1
  obtain ⟨hfcell, -, hfavoid, hfover, -⟩ := hinv
  obtain ⟨r, J, hr, hJs, hJd, hJU, -, hJe, hJh⟩ := htrace
  have hVc : ∀ u : Section34CompactVertexIndex K K',
      IsClosed (section34CompactVertexBallImage src f₁ u) :=
    fun u => (hcut.isPLCellOn_vertexBallImage hf₁ u).isCompact.isClosed
  have hUc : IsClosed (⋃ u, section34CompactVertexBallImage src f₁ u) :=
    isClosed_iUnion_of_finite hVc
  have hfsub : ∀ s, fblBd s ⊆ fbl s := fun s => (hfcell s).boundary_subset
  have hfsph : ∀ s, IsPLSphere 2 (fblBd s) := by
    intro s
    rw [(hfcell s).boundary_eq_frontier]
    exact (hfcell s).isPLBall_three.isPLSphere_frontier
  have hJS : ∀ s, ∀ i < r s,
      J s i ⊆ fblBd s ∩ frontier (⋃ u, section34CompactVertexBallImage src f₁ u) := by
    intro s i hi
    rw [hJU s]
    exact subset_iUnion₂ (s := fun i (_ : i < r s) => J s i) i hi
  have hTsub : ∀ (s : Section34CompactSimplexIndex K 3) (D : Set (EuclideanSpace ℝ (Fin 3))),
      D ⊆ fbl s → D ⊆ ⋃ u, section34CompactVertexBallImage src f₁ u →
      D ⊆ section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s := by
    intro s D hDf hDU x hx
    obtain ⟨u, hxu⟩ := mem_iUnion.mp (hDU hx)
    have hu : Section34Incident u.1 s.1 := by
      by_contra hn
      have hmem : x ∈ fbl s ∩ section34CompactVertexBallImage src f₁ u := ⟨hDf hx, hxu⟩
      rw [hfavoid s u hn] at hmem
      exact hmem
    exact mem_iUnion₂.mpr ⟨⟨(s, u), hu⟩, rfl, hxu⟩
  have hzero : ∀ s, ∀ i < r s, ∀ (D : Set (EuclideanSpace ℝ (Fin 3))) (n : ℕ), IsPLBall n D →
      J s i ⊆ D → D ⊆ section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s →
      False := by
    intro s i hi D n hD hJD hDT
    exact hJh s i hi (hJD.trans hDT)
      (integralSingularHomologyMap_nullhomotopic 1 one_ne_zero (hD.nullhomotopic_inclusion hJD hDT))
  have hdisk : ∀ s : Section34CompactSimplexIndex K 3, ∃ i < r s,
      ∃ D : Set (EuclideanSpace ℝ (Fin 3)), IsPLCellOn 2 D (J s i) ∧ D ⊆ fblBd s ∧
        D ∩ ⋃ u, section34CompactVertexBallImage src f₁ u = J s i := by
    intro s
    have _ : Nonempty (Fin (r s)) := ⟨⟨0, hr s⟩⟩
    obtain ⟨k, D, q, hq, hDS, hqJ, hDk⟩ := (hfsph s).exists_innermost_disk
      (J := fun k : Fin (r s) => J s k) (fun k => hJs s k k.2)
      (fun k => (hJS s k k.2).trans inter_subset_left)
      (fun k k' hkk' => hJd s k k.2 k' k'.2 fun h => hkk' (Fin.ext h))
    have hqJ' : q '' stdSimplexBoundary 2 = J s k := hqJ
    have hJD : J s k ⊆ D := by
      rw [← hqJ', ← hq.image_eq]
      exact image_mono fun x hx => hx.1
    have hpre : IsPreconnected (D \ J s k) := by
      have h1 : q '' openSimplex (stdVertices 1) = D \ q '' stdSimplexBoundary 2 :=
        IsPLHomeomorphOn.image_openSimplex_stdVertices hq
      have h2 : IsPreconnected (q '' openSimplex (stdVertices 1)) :=
        (convex_openSimplex _).isPreconnected.image q
          (hq.isPiecewiseAffineOn.continuousOn.mono openSimplex_stdVertices_subset_stdSimplex)
      rw [h1, hqJ'] at h2
      exact h2
    have hfr : Disjoint (D \ J s k)
        (frontier (⋃ u, section34CompactVertexBallImage src f₁ u)) := by
      refine Set.disjoint_left.mpr fun y hy hyU => ?_
      have hyJ : y ∈ ⋃ i < r s, J s i := by
        rw [← hJU s]
        exact ⟨hDS hy.1, hyU⟩
      obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hyJ
      by_cases hik : i = k
      · subst hik
        exact hy.2 hyi
      · exact Set.disjoint_left.mp (hDk ⟨i, hi⟩ fun h => hik (congrArg Fin.val h)) hy.1 hyi
    have hJU' : J s k ⊆ ⋃ u, section34CompactVertexBallImage src f₁ u :=
      ((hJS s k k.2).trans inter_subset_right).trans hUc.frontier_subset
    refine ⟨k, k.2, D, ?_, hDS, Subset.antisymm (fun y hy => ?_) (subset_inter hJD hJU')⟩
    · have hc : IsPLCellOn 2 D (q '' stdSimplexBoundary 2) := isPLCellOn_id_of_isPLBall hq
      rw [hqJ'] at hc
      exact hc
    · by_contra hyk
      have hDU : D \ J s k ⊆ ⋃ u, section34CompactVertexBallImage src f₁ u :=
        IsPreconnected.subset_of_disjoint_frontier hpre ⟨y, ⟨hy.1, hyk⟩, hy.2⟩ hfr
      have hDsub : D ⊆ ⋃ u, section34CompactVertexBallImage src f₁ u := fun z hz => by
        by_cases hzk : z ∈ J s k
        · exact hJU' hzk
        · exact hDU ⟨hz, hzk⟩
      exact hzero s k k.2 D 2 ⟨q, hq⟩ hJD (hTsub s D (hDS.trans (hfsub s)) hDsub)
  choose ι hι D hDcell hDS hDU using hdisk
  have harc : ∀ a : Section34CompactArcIndex K K',
      IsPLCellOn 1 (J a.1.1 (ι a.1.1) ∩ section34CompactVertexBallImage src f₁ a.1.2)
        (J a.1.1 (ι a.1.1) ∩ section34CompactVertexBallImage src f₁ a.1.2 ∩
          ⋃ e, section34CompactSplitDiskImage src f₁ e) := by
    intro a
    refine hcut.isPLCellOn_inter_vertexBallImage hf₁ (hJs _ _ (hι _))
      (((hJS _ _ (hι _)).trans inter_subset_left).trans (hfsub _)) (hfavoid a.1.1)
      ((hJS _ _ (hι _)).trans inter_subset_right) (hJe _ _ (hι _)) (fun u hu hJu => ?_) a.2
    exact hzero a.1.1 (ι a.1.1) (hι _) _ 3 (hcut.isPLCellOn_vertexBallImage hf₁ u).isPLBall_three
      hJu fun x hx => mem_iUnion₂.mpr ⟨⟨(a.1.1, u), hu⟩, rfl, hx⟩
  refine ⟨D, fun s => J s (ι s),
    fun a => J a.1.1 (ι a.1.1) ∩ section34CompactVertexBallImage src f₁ a.1.2,
    fun a => J a.1.1 (ι a.1.1) ∩ section34CompactVertexBallImage src f₁ a.1.2 ∩
      ⋃ e, section34CompactSplitDiskImage src f₁ e,
    fun p => J p.1.1 (ι p.1.1) ∩ section34CompactSplitDiskImage srcBd f₁ p.1.2,
    hDcell, hDS, hDU, fun s => (hJS s _ (hι s)).trans inter_subset_right, ?_, harc,
    fun _ => rfl, ?_, ?_, fun _ => rfl, ?_, fun _ => rfl⟩
  · intro s s' hss
    refine Set.disjoint_left.mpr fun y hy hy' => ?_
    have hyi : y ∈ interior (⋃ u, section34CompactVertexBallImage src f₁ u) :=
      hfover s s' hss ⟨hfsub s (hDS s hy), hfsub s' (hDS s' hy')⟩
    have hyJ : y ∈ J s (ι s) := by
      rw [← hDU s]
      exact ⟨hy, interior_subset hyi⟩
    exact Set.disjoint_left.mp disjoint_interior_frontier hyi
      (((hJS s _ (hι s)).trans inter_subset_right) hyJ)
  · intro s w hw
    refine eq_empty_of_subset_empty fun y hy => ?_
    rw [← hfavoid s w hw]
    exact ⟨hfsub s (hDS s hy.1), hy.2⟩
  · intro p
    obtain ⟨x, hx⟩ := hJe p.1.1 _ (hι p.1.1) p.1.2 p.2
    have hc : IsPLCellOn 0 ({x} : Set (EuclideanSpace ℝ (Fin 3)))
        ((fun _ : Fin 1 → ℝ => x) '' stdSimplexBoundary 0) :=
      isPLCellOn_id_of_isPLBall (isPLHomeomorphOn_const_stdSimplex_fin_one x)
    rw [stdSimplexBoundary_zero, image_empty] at hc
    change IsPLCellOn 0 (J p.1.1 (ι p.1.1) ∩ section34CompactSplitDiskImage srcBd f₁ p.1.2) ∅
    rw [hx]
    exact hc
  · intro s e he
    obtain ⟨a, b, -, hab, hEeq⟩ := hcut.splitDiskImage_eq_inter hf₁ e
    have hn : ¬ Section34Incident a.1 s.1 ∨ ¬ Section34Incident b.1 s.1 := by
      by_cases ha : Section34Incident a.1 s.1
      · refine Or.inr fun hb => he ?_
        change (e.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ convexHull ℝ (s.1 : Set _)
        rw [hab]
        exact union_subset ha hb
      · exact Or.inl ha
    refine eq_empty_of_subset_empty fun y hy => ?_
    have hyE : y ∈ section34CompactSplitDiskImage src f₁ e :=
      (hcut.isPLCellOn_splitDiskImage hf₁ e).boundary_subset hy.2
    rw [hEeq] at hyE
    have hyf : y ∈ fbl s := hfsub s (((hJS s _ (hι s)).trans inter_subset_left) hy.1)
    rcases hn with hn | hn
    · rw [← hfavoid s a hn]
      exact ⟨hyf, hyE.1⟩
    · rw [← hfavoid s b hn]
      exact ⟨hyf, hyE.2⟩

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
