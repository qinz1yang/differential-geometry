/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.LocallyFiniteFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellPairFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ImageLocalFiniteness
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IncidentEdges
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexPairModel

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ : M₁ → M₂}

omit [FiniteDimensional ℝ Ea] in
theorem Section34CutFrame.frontier_eventually_eq_vertex_pair
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (a b : Section34VertexIndex 𝒦 𝒦') {x : M₂}
    (hx : x ∈ ⋃ w, section34VertexBallImage src f₁ w)
    (hother : ∀ w, w ≠ a → w ≠ b → x ∉ section34VertexBallImage src f₁ w) :
    ∀ᶠ y in 𝓝 x, y ∈ frontier (⋃ w, section34VertexBallImage src f₁ w) ↔
      y ∈ frontier (section34VertexBallImage src f₁ a ∪
        section34VertexBallImage src f₁ b) := by
  have hximage : x ∈ f₁ '' section34CutNeighborhood src := by
    change x ∈ f₁ '' (⋃ w, src (.vertexBall w))
    rw [image_iUnion]
    exact hx
  obtain ⟨O, hO, hxO, hfin⟩ :=
    exists_section34VertexBallImage_finite_neighborhood hcut hf₁ hximage
  exact eventually_mem_frontier_iUnion_iff_pair_of_finite_neighborhood
    (fun w => (hcut.isPLCellOn_vertexBallImage hf₁ w).isCompact.isClosed)
    hO hxO hfin a b hother

omit [FiniteDimensional ℝ Ea] in
theorem Section34CutFrame.frontier_eventually_eq_vertexBallBoundary
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (w : Section34VertexIndex 𝒦 𝒦') {x : M₂}
    (hxw : x ∈ section34VertexBallImage src f₁ w)
    (hxE : ∀ e : Section34EdgeIndex 𝒦 𝒦', x ∉ section34SplitDiskImage src f₁ e) :
    ∀ᶠ y in 𝓝 x, y ∈ frontier (⋃ v, section34VertexBallImage src f₁ v) ↔
      y ∈ section34VertexBallImage srcBd f₁ w := by
  have hlocal := hcut.frontier_eventually_eq_vertex_pair hf₁ w w
    (mem_iUnion.mpr ⟨w, hxw⟩) (by
      intro v hvw _ hxv
      obtain ⟨e, hxe⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁.injOn hvw hxv hxw
      exact hxE e hxe)
  simpa only [union_self, ← (hcut.isPLCellOn_vertexBallImage hf₁ w).boundary_eq_frontier]
    using hlocal

theorem Section34CutFrame.splitDiskBoundary_subset_frontier_vertexBallImages
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (e : Section34EdgeIndex 𝒦 𝒦') :
    section34SplitDiskImage srcBd f₁ e ⊆ frontier (⋃ w, section34VertexBallImage src f₁ w) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hends, -, -⟩ :=
    id hcut
  obtain ⟨a, b, -, heab, heq⟩ := hends e
  obtain ⟨Bd, hpair⟩ := hcut.exists_vertex_pair_cell hf₁ a b e heq.symm
  have hN (w : Section34VertexIndex 𝒦 𝒦') :
      src (.vertexBall w) ⊆ section34CutNeighborhood src :=
    subset_iUnion (fun w => src (.vertexBall w)) w
  have hinter : section34VertexBallImage src f₁ a ∩ section34VertexBallImage src f₁ b =
      section34SplitDiskImage src f₁ e := by
    change f₁ '' src (.vertexBall a) ∩ f₁ '' src (.vertexBall b) = f₁ '' src (.splitDisk e)
    rw [← hf₁.injOn.image_inter (hN a) (hN b), ← heq]
  have hD := hcut.isPLCellOn_splitDiskImage hf₁ e
  have hD' := hD
  rw [← hinter] at hD'
  have hfr := (hcut.isPLCellOn_vertexBallImage hf₁ a).boundary_subset_frontier_union_of_model
    (hcut.isPLCellOn_vertexBallImage hf₁ b) hD' hpair
  intro x hx
  have hxE := hD.boundary_subset hx
  have hxN : x ∈ ⋃ w, section34VertexBallImage src f₁ w :=
    mem_iUnion.mpr ⟨a, (hinter.symm.subset hxE).1⟩
  have hlocal := hcut.frontier_eventually_eq_vertex_pair hf₁ a b hxN (by
    intro w hwa hwb hxw
    rcases eq_or_eq_of_section34VertexIndex_subset e heab
        (hcut.subset_of_mem_splitDiskImage hf₁.injOn hxE hxw) with hw | hw
    · exact hwa hw
    · exact hwb hw)
  exact hlocal.self_of_nhds.mpr (hfr hx)

theorem Section34CutFrame.splitDiskImage_sdiff_subset_interior_vertexBallImages
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (e : Section34EdgeIndex 𝒦 𝒦') :
    section34SplitDiskImage src f₁ e \ section34SplitDiskImage srcBd f₁ e ⊆
      interior (⋃ w, section34VertexBallImage src f₁ w) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hends, -, -⟩ :=
    id hcut
  obtain ⟨a, b, -, -, heq⟩ := hends e
  obtain ⟨Bd, hpair⟩ := hcut.exists_vertex_pair_cell hf₁ a b e heq.symm
  have hN (w : Section34VertexIndex 𝒦 𝒦') :
      src (.vertexBall w) ⊆ section34CutNeighborhood src :=
    subset_iUnion (fun w => src (.vertexBall w)) w
  have hinter : section34VertexBallImage src f₁ a ∩ section34VertexBallImage src f₁ b =
      section34SplitDiskImage src f₁ e := by
    change f₁ '' src (.vertexBall a) ∩ f₁ '' src (.vertexBall b) = f₁ '' src (.splitDisk e)
    rw [← hf₁.injOn.image_inter (hN a) (hN b), ← heq]
  have hD := hcut.isPLCellOn_splitDiskImage hf₁ e
  rw [← hinter] at hD
  have hkey := (hcut.isPLCellOn_vertexBallImage hf₁ a).sdiff_subset_interior_union_of_model
    (hcut.isPLCellOn_vertexBallImage hf₁ b) hD hpair
  rw [hinter] at hkey
  exact hkey.trans (interior_mono (union_subset (subset_iUnion _ a) (subset_iUnion _ b)))

end DifferentialGeometry.Topology.PiecewiseLinear
