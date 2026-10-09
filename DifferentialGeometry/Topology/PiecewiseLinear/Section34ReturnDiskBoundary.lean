/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellBoundaryDiskSeparation
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

theorem Section34CutFrame.inter_closure_frontier_sdiff_return_disk
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (w : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦')
    (hwe : w.1 ⊆ e.1) {D Db : Set M₂} (hD : IsPLCellOn 2 D Db)
    (hDloc : D ⊆ section34VertexBallImage srcBd f₁ w ∩
      frontier (⋃ v, section34VertexBallImage src f₁ v))
    (hother : ∀ d : Section34EdgeIndex 𝒦 𝒦', d ≠ e →
      Disjoint D (section34SplitDiskImage src f₁ d)) :
    D ∩ closure (frontier (⋃ v, section34VertexBallImage src f₁ v) \ D) = Db := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hends, -, -⟩ :=
    id hcut
  obtain ⟨v, hends, hinter⟩ : ∃ v : Section34VertexIndex 𝒦 𝒦',
      (e.1 : Set Ea) = (w.1 : Set Ea) ∪ (v.1 : Set Ea) ∧
      src (.vertexBall w) ∩ src (.vertexBall v) = src (.splitDisk e) := by
    obtain ⟨a, b, -, heab, heq⟩ := hends e
    rcases eq_or_eq_of_section34VertexIndex_subset e heab hwe with rfl | rfl
    · exact ⟨b, heab, heq.symm⟩
    · exact ⟨a, heab.trans (union_comm _ _), (inter_comm _ _).trans heq.symm⟩
  obtain ⟨S, hpair⟩ := hcut.exists_vertex_pair_cell hf₁ w v e hinter
  have hV := hcut.isPLCellOn_vertexBallImage hf₁ w
  have hlocal : ∀ x ∈ D, ∀ᶠ y in 𝓝 x,
      y ∈ frontier (⋃ z, section34VertexBallImage src f₁ z) ↔ y ∈ S := by
    intro x hx
    have hloc := hcut.frontier_eventually_eq_vertex_pair hf₁ w v
      (mem_iUnion.mpr ⟨w, hV.boundary_subset (hDloc hx).1⟩) (by
        intro z hzw hzv hxz
        obtain ⟨d, hxd⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁.injOn hzw hxz
          (hV.boundary_subset (hDloc hx).1)
        by_cases hde : d = e
        · rw [hde] at hxd
          rcases eq_or_eq_of_section34VertexIndex_subset e hends
              (hcut.subset_of_mem_splitDiskImage hf₁.injOn hxd hxz) with hz | hz
          · exact hzw hz
          · exact hzv hz
        · exact disjoint_left.mp (hother d hde) hx hxd)
    simpa only [hpair.boundary_eq_frontier] using hloc
  exact hpair.inter_closure_sdiff_of_eventually_eq hD
    (fun x hx => (hlocal x hx).self_of_nhds.mp (hDloc hx).2) hlocal

end DifferentialGeometry.Topology.PiecewiseLinear
