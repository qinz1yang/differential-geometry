import DifferentialGeometry.Topology.Manifold.ClosedSolidTorusTwist
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CellAttachmentKernel

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold
attribute [local instance] finrank_real_complex_fact'

def closedDiskBoundary (z : Circle) : ClosedCell 2 :=
  cellBoundaryInclusion 2 (cellBoundaryTwoHomeomorphCircle.symm z)

theorem closedDiskBoundary_apply (z : Circle) :
    (closedDiskBoundary z).val = Complex.orthonormalBasisOneI.repr (z : ℂ) := rfl

@[simp] theorem closedDiskBoundary_norm (z : Circle) : ‖(closedDiskBoundary z).val‖ = 1 := by
  rw [closedDiskBoundary_apply, LinearIsometryEquiv.norm_map, Circle.norm_coe]

theorem closedDiskBoundary_contMDiff : ContMDiff (𝓡 1) (𝓡∂ 2) ∞ closedDiskBoundary := by
  have h : ContMDiff (𝓡 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
      (fun z : Circle => Complex.orthonormalBasisOneI.repr (z : ℂ)) :=
    Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.contDiff.contMDiff.comp
      contMDiff_coe_sphere
  apply (ContMDiff.iff_comp_isImmersion
    (isSmoothEmbedding_closedCell_inclusion 1).isImmersion).mpr
  exact ⟨h.continuous.subtype_mk _, h⟩

theorem closedDiskBoundary_injective : Function.Injective closedDiskBoundary := by
  intro z w h
  apply Subtype.ext
  exact Complex.orthonormalBasisOneI.repr.injective (congrArg Subtype.val h)

theorem range_closedDiskBoundary : Set.range closedDiskBoundary = {x | ‖x.val‖ = 1} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact closedDiskBoundary_norm z
  · intro hx
    refine ⟨cellBoundaryTwoHomeomorphCircle ⟨x.val, hx⟩, ?_⟩
    change cellBoundaryInclusion 2
      (cellBoundaryTwoHomeomorphCircle.symm (cellBoundaryTwoHomeomorphCircle ⟨x.val, hx⟩)) = x
    rw [Homeomorph.symm_apply_apply]
    rfl

@[simp] theorem closedDiskRotation_boundary (t z : Circle) :
    closedDiskRotation t (closedDiskBoundary z) = closedDiskBoundary (t * z) := by
  apply Subtype.ext
  simp only [closedDiskRotation_apply, closedDiskBoundary_apply,
    LinearIsometryEquiv.symm_apply_apply, Circle.coe_mul]

def closedSolidTorusBoundary (z : Circle × Circle) : ClosedCell 2 × Circle :=
  (closedDiskBoundary z.1, z.2)

theorem closedSolidTorusBoundary_contMDiff :
    ContMDiff ((𝓡 1).prod (𝓡 1)) ((𝓡∂ 2).prod (𝓡 1)) ∞ closedSolidTorusBoundary :=
  (closedDiskBoundary_contMDiff.comp contMDiff_fst).prodMk contMDiff_snd

theorem closedSolidTorusBoundary_isClosedEmbedding :
    Topology.IsClosedEmbedding closedSolidTorusBoundary :=
  closedSolidTorusBoundary_contMDiff.continuous.isClosedEmbedding (by
    intro z w h
    apply Prod.ext
    · exact closedDiskBoundary_injective (congrArg Prod.fst h)
    · exact congrArg (fun x : ClosedCell 2 × Circle => x.2) h)

theorem range_closedSolidTorusBoundary :
    Set.range closedSolidTorusBoundary = {x | ‖x.1.val‖ = 1} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact closedDiskBoundary_norm z.1
  · intro hx
    have hx' : x.1 ∈ Set.range closedDiskBoundary := by
      rw [range_closedDiskBoundary]
      exact hx
    obtain ⟨z, hz⟩ := hx'
    exact ⟨(z, x.2), Prod.ext hz rfl⟩

theorem closedSolidTorusAction_boundary (q p : ℤ) (t : Circle) (z : Circle × Circle) :
    closedSolidTorusAction q p t (closedSolidTorusBoundary z) =
      closedSolidTorusBoundary (Circle.slopeMap ![q, p] t * z) := by
  apply Prod.ext
  · exact closedDiskRotation_boundary (t ^ q) z.1
  · rfl

theorem closedSolidTorusTwist_boundary (k : ℤ) (z : Circle × Circle) :
    closedSolidTorusTwist k (closedSolidTorusBoundary z) =
      closedSolidTorusBoundary (Circle.matrixMap !![1, k; 0, 1] z) := by
  apply Prod.ext
  · change closedDiskRotation (z.2 ^ k) (closedDiskBoundary z.1) =
      closedDiskBoundary (z.1 ^ (1 : ℤ) * z.2 ^ k)
    rw [closedDiskRotation_boundary, zpow_one, mul_comm]
  · change z.2 = z.1 ^ (0 : ℤ) * z.2 ^ (1 : ℤ)
    simp

end DifferentialGeometry.Topology.Manifold
