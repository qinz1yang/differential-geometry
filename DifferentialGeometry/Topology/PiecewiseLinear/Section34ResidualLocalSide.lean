/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellChartLocalSide
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ResidualBall
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TerminalFaceBalls

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {H : Finset Ea → Set M₂} {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}
  {fbl fblBd tgtD tgtDBd : Section34SimplexIndex 𝒦 3 → Set M₂}
  {tgtA tgtABd : Section34ArcIndex 𝒦 𝒦' → Set M₂}
  {tgtP : Section34MarkIndex 𝒦 𝒦' → Set M₂}

omit [FiniteDimensional ℝ Ea] [MetricSpace M₂] [ChartedSpace E3 M₂] in
theorem Section34CutFrame.vertexBallImage_inter_inter_eq_empty
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : InjOn f₁ (section34CutNeighborhood src))
    {w₁ w₂ w₃ : Section34VertexIndex 𝒦 𝒦'} (h₁₂ : w₁ ≠ w₂) (h₁₃ : w₁ ≠ w₃)
    (h₂₃ : w₂ ≠ w₃) :
    section34VertexBallImage src f₁ w₁ ∩ section34VertexBallImage src f₁ w₂ ∩
      section34VertexBallImage src f₁ w₃ = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  obtain ⟨⟨hx₁, hx₂⟩, hx₃⟩ := hx
  obtain ⟨e, hxe⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁ h₁₂ hx₁ hx₂
  obtain ⟨a, b, -, habe, -⟩ := hcut.splitDiskImage_eq_inter hf₁ e
  have hw : ∀ w : Section34VertexIndex 𝒦 𝒦',
      x ∈ section34VertexBallImage src f₁ w → w = a ∨ w = b := fun w hxw =>
    eq_or_eq_of_section34VertexIndex_subset e habe
      (hcut.subset_of_mem_splitDiskImage hf₁ hxe hxw)
  rcases hw w₁ hx₁ with h1 | h1 <;> rcases hw w₂ hx₂ with h2 | h2 <;>
    rcases hw w₃ hx₃ with h3 | h3
  all_goals first
    | exact h₁₂ (h1.trans h2.symm)
    | exact h₁₃ (h1.trans h3.symm)
    | exact h₂₃ (h2.trans h3.symm)

omit [FiniteDimensional ℝ Ea] in
theorem Section34NormalPlus.exists_mem_nhds_frontier_subset_residual
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁
      (section34VertexBallImage src f₁) (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁) fbl fblBd)
    {t : Section34SimplexIndex 𝒦 4} {R W : Set M₂} (hR : IsPLCellOn 3 R (frontier R))
    (hfr : frontier R ⊆ (⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 t.1),
        section34VertexBallImage src f₁ w) ∪
      ⋃ (s : Section34SimplexIndex 𝒦 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : Disjoint (interior R) (⋃ (w : Section34VertexIndex 𝒦 𝒦')
      (_ : Section34Incident w.1 t.1), section34VertexBallImage src f₁ w))
    (hDc : ∀ s, IsClosed (tgtD s)) (hW : IsPLCellOn 3 W (frontier W))
    (hWt : W ⊆ ⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 t.1),
      section34VertexBallImage src f₁ w)
    {y : M₂} (hyR : y ∈ R) (hyW : y ∈ frontier W)
    (hyV : ∀ w : Section34VertexIndex 𝒦 𝒦', Section34Incident w.1 t.1 →
      y ∈ section34VertexBallImage src f₁ w → section34VertexBallImage src f₁ w ⊆ W)
    (hyD : ∀ s : Section34SimplexIndex 𝒦 3, Section34Incident s.1 t.1 → y ∉ tgtD s) :
    ∃ U ∈ 𝓝 y, U ∩ frontier W ⊆ R ∧ U \ W ⊆ interior R := by
  have hcut := hdata.1
  have hf₁ := hdata.2.2.1.2.2.1
  have hVfin := finite_setOf_section34Incident_graphIndex hcut.2.1 (graphSkeletonSpace 𝒦)
    1 t.2.1
  have hVc : ∀ u, IsClosed (section34VertexBallImage src f₁ u) := fun u =>
    (hcut.isPLCellOn_vertexBallImage hf₁ u).isCompact.isClosed
  have hfin : {u : Section34VertexIndex 𝒦 𝒦' |
      Section34Incident u.1 t.1 ∧ y ∉ section34VertexBallImage src f₁ u}.Finite :=
    hVfin.subset fun u hu => hu.1
  let F := (⋃ u ∈ {u : Section34VertexIndex 𝒦 𝒦' |
      Section34Incident u.1 t.1 ∧ y ∉ section34VertexBallImage src f₁ u},
        section34VertexBallImage src f₁ u) ∪
      ⋃ s ∈ {s : Section34SimplexIndex 𝒦 3 | Section34Incident s.1 t.1}, tgtD s
  have hFc : IsClosed F :=
    (hfin.isClosed_biUnion fun u _ => hVc u).union
      ((finite_setOf_section34Incident t).isClosed_biUnion fun s _ => hDc s)
  obtain ⟨chart, hchart, -, hVchart, -⟩ := hdata.exists_chart_tetrahedron t
  have hWsrc : W ⊆ chart.source := hWt.trans (iUnion₂_subset fun w hw => hVchart w hw)
  refine hW.exists_mem_nhds_of_inter_frontier_subset_in_chart hR hchart hWsrc
    hFc.isOpen_compl ?_ (hint.mono_right (interior_subset.trans hWt)) ?_ hyR hyW
  · rintro z ⟨hzF, hzR⟩
    rcases hfr hzR with hz | hz
    · obtain ⟨u, hu, hzu⟩ := mem_iUnion₂.mp hz
      by_cases hyu : y ∈ section34VertexBallImage src f₁ u
      · exact hyV u hu hyu hzu
      · exact (hzF (Or.inl (mem_iUnion₂.mpr ⟨u, ⟨hu, hyu⟩, hzu⟩))).elim
    · exact (hzF (Or.inr hz)).elim
  · rintro (hy | hy)
    · obtain ⟨u, ⟨-, hu⟩, hyu⟩ := mem_iUnion₂.mp hy
      exact hu hyu
    · obtain ⟨s, hs, hys⟩ := mem_iUnion₂.mp hy
      exact hyD s hs hys

end DifferentialGeometry.Topology.PiecewiseLinear
