import DifferentialGeometry.Topology.Morse.Attachment.ManifoldHandle

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.Morse.CellAttachment
open DifferentialGeometry.Topology.Morse.ManifoldCellAttachment
open DifferentialGeometry.Topology.Handle

namespace DifferentialGeometry.Morse

variable {n k : ℕ} {H M : Type} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (MorseModel n) H}
  {f : M → ℝ} {c : ℝ} {hk : k ≤ n} (data : MorseChart n k hk c I f)


theorem cellEmbedding_value (z : ClosedCell k) :
    f (cellEmbedding hk c data z) = c - data.ε * ‖(z : EuclideanSpace ℝ (Fin k))‖ ^ 2 := by
  rw [cellEmbedding, data.normalForm_on _ (norm_cellMap_le hk data.ε data.R data.sqrt_two_epsilon_le_radius _ z.2),
    morseNormalForm_cellMap, Real.sq_sqrt (mul_nonneg (by norm_num) data.epsilon_pos.le)]
  ring

private theorem cellEmbedding_continuous : Continuous (cellEmbedding hk c data) := by
  apply continuousOn_univ.mp
  exact data.χ.continuousOn_toFun.comp (continuous_cellMap _).continuousOn
    (fun z _ ↦ data.closedBall_subset_source _ (norm_cellMap_le hk data.ε data.R data.sqrt_two_epsilon_le_radius _ z.2))

private theorem cellEmbedding_injective : Function.Injective (cellEmbedding hk c data) := by
  intro x y hxy
  apply cellMap_injective hk data.ε data.epsilon_pos
  exact data.χ.injOn
    (data.closedBall_subset_source _ (norm_cellMap_le hk data.ε data.R data.sqrt_two_epsilon_le_radius _ x.2))
    (data.closedBall_subset_source _ (norm_cellMap_le hk data.ε data.R data.sqrt_two_epsilon_le_radius _ y.2)) hxy

variable [T2Space M]

def cellAdjunctionHomeomorphLowerUnion (hf : Continuous f) :
    CellAdjunctionSpace k (cellAttachingMap hk c data) ≃ₜ
      {x : M // x ∈ sublevel f (c - data.ε) ∪ cellImage hk c data} := by
  apply cellAdjunctionHomeomorphUnionImage (φ := cellAttachingMap hk c data)
    (c := cellEmbedding hk c data) (fun _ ↦ rfl)
    (cellEmbedding_injective data) (cellEmbedding_continuous data)
  · rw [Set.disjoint_left]
    rintro x ⟨y, ⟨z, rfl⟩, rfl⟩ hx
    have he := cellEmbedding_value data (cellInteriorInclusion k z)
    have hz : ‖(z : EuclideanSpace ℝ (Fin k))‖ < 1 := z.2
    have hz0 : 0 ≤ ‖(z : EuclideanSpace ℝ (Fin k))‖ := norm_nonneg _
    change f (cellEmbedding hk c data (cellInteriorInclusion k z)) ≤ c - data.ε at hx
    change f (cellEmbedding hk c data (cellInteriorInclusion k z)) =
      c - data.ε * ‖(z : EuclideanSpace ℝ (Fin k))‖ ^ 2 at he
    have hsq : ‖(z : EuclideanSpace ℝ (Fin k))‖ ^ 2 < 1 := by nlinarith
    have hmul := mul_lt_mul_of_pos_left hsq data.epsilon_pos
    linarith
  · exact isClosed_Iic.preimage hf


@[simp]
theorem cellAdjunctionHomeomorphLowerUnion_lower (hf : Continuous f)
    (x : SublevelSpace f (c - data.ε)) :
    cellAdjunctionHomeomorphLowerUnion data hf
      (adjunctionLower (i := cellBoundaryInclusion k) (cellAttachingMap hk c data) x) =
      ⟨x.1, Or.inl x.2⟩ := by
  rfl


@[simp]
theorem cellAdjunctionHomeomorphLowerUnion_cell (hf : Continuous f) (x : ClosedCell k) :
    cellAdjunctionHomeomorphLowerUnion data hf
      (adjunctionCell (i := cellBoundaryInclusion k) (cellAttachingMap hk c data) x) =
      ⟨cellEmbedding hk c data x, Or.inr (mem_range_self x)⟩ := by
  rfl

end DifferentialGeometry.Morse
