/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CrossingInteriorClosure
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ImageLocalFiniteness

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ h : M₁ → M₂}
  {H : Finset Ea → Set M₂} {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}

omit [FiniteDimensional ℝ Ea] in
theorem section34FaceBall_inter_vertexUnion_subset_faceTorus
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd) (s : Section34SimplexIndex 𝒦 3) :
    fbl s ∩ (⋃ w, section34VertexBallImage src f₁ w) ⊆
      section34FaceTorus (section34VertexBallImage src f₁) s := by
  rintro x ⟨hxF, hxN⟩
  obtain ⟨w, hxw⟩ := mem_iUnion.mp hxN
  by_cases hws : Section34Incident w.1 s.1
  · exact mem_section34FaceTorus_iff.mpr ⟨w, hws, hxw⟩
  · have hbad := hinv.2.2.1 s w hws
    exact (show x ∈ (∅ : Set M₂) from hbad ▸ ⟨hxF, hxw⟩).elim

omit [FiniteDimensional ℝ Ea] in
theorem section34Trace_subset_faceTorus
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd) (s : Section34SimplexIndex 𝒦 3) :
    fblBd s ∩ frontier (⋃ w, section34VertexBallImage src f₁ w) ⊆
      section34FaceTorus (section34VertexBallImage src f₁) s := by
  let N := ⋃ w, section34VertexBallImage src f₁ w
  let T := section34FaceTorus (section34VertexBallImage src f₁) s
  have hTc : IsClosed T := isClosed_section34FaceTorus hcut.2.1
    (fun w => (hcut.isPLCellOn_vertexBallImage hf₁ w).isCompact.isClosed) s
  have hFT : fbl s ∩ N ⊆ T :=
    section34FaceBall_inter_vertexUnion_subset_faceTorus hinv s
  have hsub : frontier N ∩ interior (fbl s) ⊆ T := by
    rintro z ⟨hzN, hzF⟩
    by_contra hzT
    have hO : IsOpen (interior (fbl s) ∩ Tᶜ) := isOpen_interior.inter hTc.isOpen_compl
    obtain ⟨w, hwO, hwN⟩ := mem_closure_iff.mp (frontier_subset_closure hzN)
      _ hO ⟨hzF, hzT⟩
    exact hwO.2 (hFT ⟨interior_subset hwO.1, hwN⟩)
  intro y hy
  obtain ⟨c, -, hyc, hcross⟩ := hinv.2.2.2.2.1 s y hy
  have hcross' : HasPLCrossingAt (c '' (frontier N ∩ c.source))
      (c '' (frontier (fbl s) ∩ c.source)) (c y) := by
    rw [← (hinv.1 s).boundary_eq_frontier]
    exact hcross.symm
  have hcl := HasPLCrossingAt.mem_closure_inter_interior_of_chart hyc hcross'
    (hinv.1 s).isCompact.isClosed
    ((hinv.1 s).subset_closure_interior ((hinv.1 s).boundary_subset hy.1))
  exact closure_minimal hsub hTc hcl

open Classical in
omit [FiniteDimensional ℝ Ea] in
theorem eventually_mem_frontier_vertexUnion_iff_faceTorus
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd) (s : Section34SimplexIndex 𝒦 3)
    {y : M₂} (hy : y ∈ fbl s ∩ (⋃ w, section34VertexBallImage src f₁ w)) :
    ∀ᶠ z in 𝓝 y, z ∈ frontier (⋃ w, section34VertexBallImage src f₁ w) ↔
      z ∈ frontier (section34FaceTorus (section34VertexBallImage src f₁) s) := by
  let V := section34VertexBallImage src f₁
  let T := section34FaceTorus V s
  have hyimage : y ∈ f₁ '' section34CutNeighborhood src := by
    change y ∈ f₁ '' (⋃ w, src (.vertexBall w))
    rw [image_iUnion]
    exact hy.2
  obtain ⟨O, hO, hyO, hfin⟩ :=
    exists_section34VertexBallImage_finite_neighborhood hcut hf₁ hyimage
  let F : Set (Section34VertexIndex 𝒦 𝒦') :=
    {w | (V w ∩ O).Nonempty ∧ ¬ Section34Incident w.1 s.1}
  have hFfin : F.Finite := hfin.subset fun _ hw => hw.1
  have hclosed : IsClosed (⋃ w ∈ F, V w) := hFfin.isClosed_biUnion fun w _ =>
    (hcut.isPLCellOn_vertexBallImage hf₁ w).isCompact.isClosed
  let W := O ∩ (⋃ w ∈ F, V w)ᶜ
  have hW : IsOpen W := hO.inter hclosed.isOpen_compl
  have hyW : y ∈ W := by
    refine ⟨hyO, ?_⟩
    intro hybad
    obtain ⟨w, hwF, hyw⟩ := mem_iUnion₂.mp hybad
    have hbad := hinv.2.2.1 s w hwF.2
    exact (show y ∈ (∅ : Set M₂) from hbad ▸ ⟨hy.1, hyw⟩).elim
  have heq : (⋃ w, V w) ∩ W = T ∩ W := by
    ext z
    constructor
    · rintro ⟨hzN, hzW⟩
      obtain ⟨w, hzw⟩ := mem_iUnion.mp hzN
      refine ⟨?_, hzW⟩
      by_cases hws : Section34Incident w.1 s.1
      · exact mem_section34FaceTorus_iff.mpr ⟨w, hws, hzw⟩
      · exact (hzW.2 (mem_iUnion₂.mpr ⟨w, ⟨⟨z, hzw, hzW.1⟩, hws⟩, hzw⟩)).elim
    · rintro ⟨hzT, hzW⟩
      obtain ⟨w, -, hzw⟩ := mem_section34FaceTorus_iff.mp hzT
      exact ⟨mem_iUnion.mpr ⟨w, hzw⟩, hzW⟩
  have hfr : frontier (⋃ w, V w) ∩ W = frontier T ∩ W := by
    rw [← frontier_inter_open_inter hW, heq, frontier_inter_open_inter hW]
  filter_upwards [hW.mem_nhds hyW] with z hz
  exact ⟨fun h => (hfr.subset ⟨h, hz⟩).1, fun h => (hfr.symm.subset ⟨h, hz⟩).1⟩

omit [FiniteDimensional ℝ Ea] in
theorem section34Trace_eq_inter_frontier_faceTorus
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd) (s : Section34SimplexIndex 𝒦 3) :
    fblBd s ∩ frontier (⋃ w, section34VertexBallImage src f₁ w) =
      fblBd s ∩ frontier (section34FaceTorus (section34VertexBallImage src f₁) s) := by
  have hTc := isClosed_section34FaceTorus hcut.2.1
    (fun w => (hcut.isPLCellOn_vertexBallImage hf₁ w).isCompact.isClosed) s
  have hTN : section34FaceTorus (section34VertexBallImage src f₁) s ⊆
      ⋃ w, section34VertexBallImage src f₁ w := by
    intro z hz
    obtain ⟨w, -, hzw⟩ := mem_section34FaceTorus_iff.mp hz
    exact mem_iUnion.mpr ⟨w, hzw⟩
  ext y
  constructor
  · intro hy
    have hyT := section34Trace_subset_faceTorus hcut hf₁ hinv s hy
    have hlocal := eventually_mem_frontier_vertexUnion_iff_faceTorus hcut hf₁ hinv s
      ⟨(hinv.1 s).boundary_subset hy.1, hTN hyT⟩
    exact ⟨hy.1, (Filter.Eventually.self_of_nhds hlocal).mp hy.2⟩
  · intro hy
    have hlocal := eventually_mem_frontier_vertexUnion_iff_faceTorus hcut hf₁ hinv s
      ⟨(hinv.1 s).boundary_subset hy.1, hTN (hTc.frontier_subset hy.2)⟩
    exact ⟨hy.1, (Filter.Eventually.self_of_nhds hlocal).mpr hy.2⟩

end DifferentialGeometry.Topology.PiecewiseLinear
