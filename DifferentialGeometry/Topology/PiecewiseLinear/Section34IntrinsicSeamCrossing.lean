/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CrossingCellSeam
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBallUpdate
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexFrontier

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ : M₁ → M₂}

omit [FiniteDimensional ℝ Ea] in
theorem Section34CutFrame.not_subset_vertexBall_of_splitDiskBoundary_crossing
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (w : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦')
    {J : Set M₂} {x : M₂} (c : OpenPartialHomeomorph M₂ E3) (hxc : x ∈ c.source)
    (hc : HasPLCurveCrossingOnAt
      (c '' (frontier (⋃ v, section34VertexBallImage src f₁ v) ∩ c.source))
      (c '' (J ∩ c.source)) (c '' (section34SplitDiskImage srcBd f₁ e ∩ c.source))
      (c x)) : ¬ J ⊆ section34VertexBallImage src f₁ w := by
  intro hJV
  have hx : x ∈ J ∩ section34SplitDiskImage srcBd f₁ e := by
    obtain ⟨O, V, φ, T, P, Q, -, -, -, -, hφx, -, -, -, -, -, -, hlocal⟩ := hc
    have hJ : c x ∈ c '' (J ∩ c.source) :=
      hlocal.self_of_nhds.2.1.mpr (hφx ▸ P.zero_mem)
    have hB : c x ∈ c '' (section34SplitDiskImage srcBd f₁ e ∩ c.source) :=
      hlocal.self_of_nhds.2.2.mpr (hφx ▸ Q.zero_mem)
    obtain ⟨y, hy, hyx⟩ := hJ
    obtain ⟨z, hz, hzx⟩ := hB
    exact ⟨c.injOn hy.2 hxc hyx ▸ hy.1, c.injOn hz.2 hxc hzx ▸ hz.1⟩
  have hxE := (hcut.isPLCellOn_splitDiskImage hf₁ e).boundary_subset hx.2
  have hwe := hcut.subset_of_mem_splitDiskImage hf₁.injOn hxE (hJV hx.1)
  obtain ⟨v, hends, heq⟩ : ∃ v : Section34VertexIndex 𝒦 𝒦',
      (e.1 : Set Ea) = (w.1 : Set Ea) ∪ (v.1 : Set Ea) ∧
      section34SplitDiskImage src f₁ e = section34VertexBallImage src f₁ w ∩
        section34VertexBallImage src f₁ v := by
    obtain ⟨a, b, -, heab, heq⟩ := hcut.splitDiskImage_eq_inter hf₁.injOn e
    rcases eq_or_eq_of_section34VertexIndex_subset e heab hwe with rfl | rfl
    · exact ⟨b, heab, heq⟩
    · exact ⟨a, heab.trans (union_comm _ _), heq.trans (inter_comm _ _)⟩
  have hlocal := hcut.frontier_eventually_eq_vertex_pair hf₁ w v
    (mem_iUnion.mpr ⟨w, hJV hx.1⟩) (by
      intro a haw hav hxa
      rcases eq_or_eq_of_section34VertexIndex_subset e hends
        (hcut.subset_of_mem_splitDiskImage hf₁.injOn hxE hxa) with ha | ha
      · exact haw ha
      · exact hav ha)
  obtain ⟨O, hOO, hO, hxO⟩ := _root_.mem_nhds_iff.mp hlocal
  have hOeq : frontier (⋃ a, section34VertexBallImage src f₁ a) ∩ O =
      frontier (section34VertexBallImage src f₁ w ∪ section34VertexBallImage src f₁ v) ∩
        O := by
    ext y
    exact and_congr_left fun hy => hOO hy
  have hc' := hc.congr (eventually_mem_image_inter_source_iff hO hOeq hxO hxc)
    (Filter.Eventually.of_forall fun _ => Iff.rfl)
    (Filter.Eventually.of_forall fun _ => Iff.rfl)
  have hD := hcut.isPLCellOn_splitDiskImage hf₁ e
  rw [heq] at hD
  exact HasPLCurveCrossingOnAt.not_subset_of_cell_seam_in_chart
    (hcut.isPLCellOn_vertexBallImage hf₁ w) (hcut.isPLCellOn_vertexBallImage hf₁ v)
    hD c hxc hc' hJV

end DifferentialGeometry.Topology.PiecewiseLinear
