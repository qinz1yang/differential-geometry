/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CrossingTraceCircles
import DifferentialGeometry.Topology.PiecewiseLinear.PLSphereLocallyPlanar
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTargetCells

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {h f₁ : E3 → E3}
  {H : Finset E3 → Set E3} {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}

private theorem mem_section34CompactFaceTorus_iff
    {tgtV : Section34CompactVertexIndex K K' → Set E3}
    {s : Section34CompactSimplexIndex K 3} {y : E3} :
    y ∈ section34CompactFaceTorus tgtV s ↔
      ∃ w, Section34Incident w.1 s.1 ∧ y ∈ tgtV w := by
  constructor
  · intro hy
    obtain ⟨a, ha, hya⟩ := mem_iUnion₂.mp hy
    refine ⟨a.1.2, ?_, hya⟩
    rw [← ha]
    exact a.2
  · rintro ⟨w, hw, hyw⟩
    exact mem_iUnion₂.mpr ⟨⟨(s, w), hw⟩, rfl, hyw⟩

theorem Section34CompactFaceBallInvariants.inter_frontier_faceTorus_eq
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src)) (s : Section34CompactSimplexIndex K 3) :
    fblBd s ∩ frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) =
      fblBd s ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w) := by
  classical
  have := finite_section34CompactGraphIndex hcut.2.2.1 (section34CompactGraphSkeleton K) 1
  let O := (⋃ w ∈ {w : Section34CompactVertexIndex K K' | ¬ Section34Incident w.1 s.1},
    section34CompactVertexBallImage src f₁ w)ᶜ
  have hO : IsOpen O :=
    ((Set.toFinite _).isClosed_biUnion fun w _ =>
      (hcut.isPLCellOn_vertexBallImage hf₁ w).isCompact.isClosed).isOpen_compl
  have hPO : fblBd s ⊆ O := by
    intro y hy hbad
    obtain ⟨w, hw, hyw⟩ := mem_iUnion₂.mp hbad
    have hyP := (hinv.1 s).boundary_subset hy
    exact Set.notMem_empty y (hinv.2.2.1 s w hw ▸ ⟨hyP, hyw⟩)
  have hNO : (⋃ w, section34CompactVertexBallImage src f₁ w) ∩ O =
      section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s ∩ O := by
    ext y
    constructor
    · rintro ⟨hy, hyO⟩
      obtain ⟨w, hyw⟩ := mem_iUnion.mp hy
      by_cases hw : Section34Incident w.1 s.1
      · exact ⟨mem_section34CompactFaceTorus_iff.mpr ⟨w, hw, hyw⟩, hyO⟩
      · exact (hyO (mem_iUnion₂.mpr ⟨w, hw, hyw⟩)).elim
    · rintro ⟨hy, hyO⟩
      obtain ⟨w, -, hyw⟩ := mem_section34CompactFaceTorus_iff.mp hy
      exact ⟨mem_iUnion.mpr ⟨w, hyw⟩, hyO⟩
  have hfront : frontier (⋃ w, section34CompactVertexBallImage src f₁ w) ∩ O =
      frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) ∩ O := by
    rw [← frontier_inter_open_inter hO, hNO, frontier_inter_open_inter hO]
  ext y
  constructor
  · rintro ⟨hyP, hyT⟩
    exact ⟨hyP, (hfront.symm.subset ⟨hyT, hPO hyP⟩).1⟩
  · rintro ⟨hyP, hyN⟩
    exact ⟨hyP, (hfront.subset ⟨hyN, hPO hyP⟩).1⟩

theorem exists_finite_trace_circles_of_crossings
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd) (s : Section34CompactSimplexIndex K 3) :
    ∃ (ι : Type) (_ : Finite ι) (J : ι → Set E3), (∀ i, IsPLSphere 1 (J i)) ∧
      (Pairwise fun i j => Disjoint (J i) (J j)) ∧
      fblBd s ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w) = ⋃ i, J i ∧
      fblBd s ∩ frontier
        (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) = ⋃ i, J i := by
  have := finite_section34CompactGraphIndex hcut.2.2.1 (section34CompactGraphSkeleton K) 1
  have hV : ∀ w, IsPLBall 3 (section34CompactVertexBallImage src f₁ w) :=
    fun w => (hcut.isPLCellOn_vertexBallImage hf₁ w).isPLBall_three
  have hN : IsPolyhedron (⋃ w, section34CompactVertexBallImage src f₁ w) :=
    IsPolyhedron.iUnion fun w => (hV w).isPolyhedron
  have hP : IsPLSphere 2 (fblBd s) := by
    rw [(hinv.1 s).boundary_eq_frontier]
    exact (hinv.1 s).isPLBall_three.isPLSphere_frontier
  have hreg : ∀ x ∈ frontier (⋃ w, section34CompactVertexBallImage src f₁ w),
      x ∈ closure (interior (⋃ w, section34CompactVertexBallImage src f₁ w)) := by
    intro x hx
    obtain ⟨w, hxw⟩ := mem_iUnion.mp (hN.isClosed.frontier_subset hx)
    have hxcl : x ∈ closure (interior (section34CompactVertexBallImage src f₁ w)) := by
      rw [(hV w).closure_interior]
      exact hxw
    exact closure_mono (interior_mono (subset_iUnion _ w)) hxcl
  obtain ⟨-, -, -, -, hcross, -⟩ := id hinv
  obtain ⟨ι, hι, J, hJ, hdisj, heq⟩ := exists_iUnion_isPLSphere_one_of_forall_lineChart
    (hP.isPolyhedron.inter hN.frontier) (hcross s) fun x hx =>
      (hcross s x hx).exists_lineChart hx.1 (hP.exists_isOpen_inter_homeomorph_of_two hx.1)
        hN.isClosed (hreg x hx.2)
  exact ⟨ι, hι, J, hJ, hdisj, heq, (hinv.inter_frontier_faceTorus_eq hcut hf₁ s).trans heq⟩

end DifferentialGeometry.Topology.PiecewiseLinear
