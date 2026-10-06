import DifferentialGeometry.Topology.Surface.Recognition.EmbeddedFacePartitionBCF
import DifferentialGeometry.Topology.Attachment.Defs

/-!
# The disk parametrization of a whole edge fibre (lane S-BCF03b; BCF03 G7, P5)

A whole edge fibre `F ⊆ Wt` with `ed : F ≃ₜ ClosedCell 2` carrying the unit circle onto its rim `R`
(`SmoothDiskChartAt_BIFc.fibre_disk_rim`, `edge_fibre_BIFc`) is parametrized by the closed unit disk
`Disk 2` with `diskSphere 2 ↦ R`: the form of `disk_param` of `EmbeddedFacePartition_BCF`.

* `diskClosedCellHomeomorph_BCF`: `Disk 2 ≃ₜ ClosedCell 2`;
* `exists_diskParam_of_fibre_BCF`: `∃ h : Disk 2 → Wt`, continuous, injective, `range h = F`,
  `h '' diskSphere 2 = R`;
* `isCompact_of_homeomorph_closedCell_BCF`: such an `F` is compact (hence closed in a Hausdorff
  ambient space).
-/

set_option autoImplicit false

open Set Function Topology Metric

noncomputable section

namespace DifferentialGeometry.Topology.Surface

open DifferentialGeometry.Topology

/-- The closed unit disk and the closed cell of dimension `2` are homeomorphic (same set). -/
def diskClosedCellHomeomorph_BCF : Disk 2 ≃ₜ ClosedCell 2 where
  toFun x := ⟨x.1, mem_closedBall_zero_iff.mp x.2⟩
  invFun x := ⟨x.1, mem_closedBall_zero_iff.mpr x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val).subtype_mk _

variable {Wt : Type*} [TopologicalSpace Wt] {F R : Set Wt}

/-- **`disk_param` of a whole edge fibre.** -/
theorem exists_diskParam_of_fibre_BCF (ed : F ≃ₜ ClosedCell 2)
    (hR : Subtype.val '' (ed ⁻¹' {x : ClosedCell 2 | ‖x.1‖ = 1}) = R) :
    ∃ h : Disk 2 → Wt, Continuous h ∧ Injective h ∧ range h = F ∧ h '' diskSphere 2 = R := by
  let d := diskClosedCellHomeomorph_BCF
  refine ⟨fun x => ((ed.symm (d x) : F) : Wt), continuous_subtype_val.comp
    (ed.symm.continuous.comp d.continuous), ?_, ?_, ?_⟩
  · intro x x' hxx'
    exact d.injective (ed.symm.injective (Subtype.ext hxx'))
  · ext q
    constructor
    · rintro ⟨x, rfl⟩
      exact (ed.symm (d x)).2
    · intro hq
      exact ⟨d.symm (ed ⟨q, hq⟩), by simp⟩
  · rw [← hR]
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨ed.symm (d x), ?_, rfl⟩
      change ‖((ed (ed.symm (d x)) : ClosedCell 2) : EuclideanSpace ℝ (Fin 2))‖ = 1
      rw [ed.apply_symm_apply]
      exact mem_diskSphere.mp hx
    · rintro ⟨w, hw, rfl⟩
      refine ⟨d.symm (ed w), ?_, by simp⟩
      rw [mem_diskSphere]
      exact hw

/-- A subset homeomorphic to the closed `2`-cell is compact. -/
theorem isCompact_of_homeomorph_closedCell_BCF (ed : F ≃ₜ ClosedCell 2) : IsCompact F := by
  obtain ⟨h, hc, -, hr, -⟩ := exists_diskParam_of_fibre_BCF ed rfl
  have : CompactSpace (Disk 2) := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  rw [← hr]
  exact isCompact_range hc

end DifferentialGeometry.Topology.Surface
