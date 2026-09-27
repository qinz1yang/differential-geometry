/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellBoundaryThinness

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace CompactSourceFaceProbe

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3}

private theorem compact_boundary_thin
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    {r l : Section34CompactLabelOf K K'} {n : ℕ}
    (hr : section34BoundedDim r = n) (hl : section34BoundedDim l = n + 2)
    (hrl : src r ⊆ srcBd l) :
    ∃ a b : Section34CompactLabelOf K K', a ≠ b ∧
      section34BoundedDim a = n + 1 ∧ section34BoundedDim b = n + 1 ∧
      src r ⊆ src a ∧ src a ⊆ srcBd l ∧ src r ⊆ src b ∧ src b ⊆ srcBd l ∧
      ∀ c : Section34CompactLabelOf K K', section34BoundedDim c = n + 1 →
        src r ⊆ src c → src c ⊆ srcBd l → c = a ∨ c = b := by
  obtain ⟨-, hK, hK', -, -, -, hcell, hboundary, hinter, hstrict, -⟩ := hcut
  let _ : Finite (Section34CompactLabelOf K K') := finite_section34CompactLabelOf hK hK'
  have hcelll : IsPLCellOn (n + 2) (src l) (srcBd l) := hl ▸ hcell l
  obtain ⟨q, hq, hqB⟩ := hcelll.exists_isPLHomeomorphOn_stdSimplex
  have hB : IsPLSphere (n + 1) (srcBd l) := hqB.symm ▸
    hq.isPLSphere_image_stdSimplexBoundary
  apply exists_pair_cofaces_of_finite_cell_decomposition
    (fun i => (hcell i).exists_isPLHomeomorphOn_stdSimplex) hboundary hinter hstrict hB ?_ hr hrl
  intro x hx
  rw [hboundary l] at hx
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
  refine ⟨i, ?_, hxi⟩
  rw [hboundary l]
  exact subset_iUnion₂_of_subset i hi subset_rfl

theorem split_disk_boundary_thin
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (e : Section34CompactEdgeIndex K K') (p : Section34CompactMarkIndex K K')
    (hp : src (.markedPoint p) ⊆ srcBd (.splitDisk e)) :
    ∃ a b : Section34CompactLabelOf K K', a ≠ b ∧
      section34BoundedDim a = 1 ∧ section34BoundedDim b = 1 ∧
      src (.markedPoint p) ⊆ src a ∧ src a ⊆ srcBd (.splitDisk e) ∧
      src (.markedPoint p) ⊆ src b ∧ src b ⊆ srcBd (.splitDisk e) ∧
      ∀ c : Section34CompactLabelOf K K', section34BoundedDim c = 1 →
        src (.markedPoint p) ⊆ src c → src c ⊆ srcBd (.splitDisk e) → c = a ∨ c = b := by
  exact compact_boundary_thin hcut (n := 0) rfl rfl hp

theorem vertex_ball_boundary_thin
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (w : Section34CompactVertexIndex K K') (r : Section34CompactLabelOf K K')
    (hr : section34BoundedDim r = 1) (hrw : src r ⊆ srcBd (.vertexBall w)) :
    ∃ a b : Section34CompactLabelOf K K', a ≠ b ∧
      section34BoundedDim a = 2 ∧ section34BoundedDim b = 2 ∧
      src r ⊆ src a ∧ src a ⊆ srcBd (.vertexBall w) ∧
      src r ⊆ src b ∧ src b ⊆ srcBd (.vertexBall w) ∧
      ∀ c : Section34CompactLabelOf K K', section34BoundedDim c = 2 →
        src r ⊆ src c → src c ⊆ srcBd (.vertexBall w) → c = a ∨ c = b := by
  exact compact_boundary_thin hcut hr rfl hrw

end CompactSourceFaceProbe

end DifferentialGeometry.Topology.PiecewiseLinear
