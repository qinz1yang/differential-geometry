import DifferentialGeometry.Topology.Manifold.ClosedBall.Diffeomorph
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Geometry.Manifold.Instances.Sphere

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold
attribute [local instance] finrank_real_complex_fact'

private def diskRotationLinear (t : Circle) :
    EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (Complex.orthonormalBasisOneI.repr.symm.trans (rotation t)).trans
    Complex.orthonormalBasisOneI.repr

private theorem diskRotationLinear_closedBall (t : Circle) :
    diskRotationLinear t '' Metric.closedBall 0 1 = Metric.closedBall 0 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, (diskRotationLinear t).norm_map] using hx
  · intro hy
    refine ⟨(diskRotationLinear t).symm y, ?_, (diskRotationLinear t).apply_symm_apply y⟩
    simpa only [Metric.mem_closedBall, dist_zero_right,
      (diskRotationLinear t).symm.norm_map] using hy

def closedDiskRotation (t : Circle) :
    ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2 :=
  closedCellDiffeomorph (diskRotationLinear t).toContinuousLinearEquiv.toDiffeomorph
    (diskRotationLinear_closedBall t)

theorem closedDiskRotation_apply (t : Circle) (x : ClosedCell 2) :
    (closedDiskRotation t x).val = Complex.orthonormalBasisOneI.repr
      ((t : ℂ) * Complex.orthonormalBasisOneI.repr.symm x.val) := rfl

theorem closedDiskRotation_complex (t : Circle) (x : ClosedCell 2) :
    Complex.orthonormalBasisOneI.repr.symm (closedDiskRotation t x).val =
      (t : ℂ) * Complex.orthonormalBasisOneI.repr.symm x.val := by
  rw [closedDiskRotation_apply, LinearIsometryEquiv.symm_apply_apply]

@[simp] theorem closedDiskRotation_one (x : ClosedCell 2) : closedDiskRotation 1 x = x := by
  apply Subtype.ext
  apply Complex.orthonormalBasisOneI.repr.symm.injective
  simp only [closedDiskRotation_complex, Circle.coe_one, one_mul]

@[simp] theorem closedDiskRotation_mul (t s : Circle) (x : ClosedCell 2) :
    closedDiskRotation (t * s) x = closedDiskRotation t (closedDiskRotation s x) := by
  apply Subtype.ext
  apply Complex.orthonormalBasisOneI.repr.symm.injective
  simp only [closedDiskRotation_complex, Circle.coe_mul, mul_assoc]

@[simp] theorem closedDiskRotation_norm (t : Circle) (x : ClosedCell 2) :
    ‖(closedDiskRotation t x).val‖ = ‖x.val‖ :=
  (diskRotationLinear t).norm_map x.val

theorem closedDiskRotation_contMDiff :
    ContMDiff ((𝓡 1).prod (𝓡∂ 2)) (𝓡∂ 2) ∞
      (fun p : Circle × ClosedCell 2 => closedDiskRotation p.1 p.2) := by
  let e := Complex.orthonormalBasisOneI.repr
  have hc : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun z : Circle => (z : ℂ)) :=
    contMDiff_coe_sphere
  have hm : ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞
      (fun p : ℂ × ℂ => p.1 * p.2) := by
    rw [contMDiff_iff]
    exact ⟨continuous_mul, fun x y => contDiff_mul.contDiffOn⟩
  have h : ContMDiff ((𝓡 1).prod (𝓡∂ 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
      (fun p : Circle × ClosedCell 2 => e ((p.1 : ℂ) * e.symm p.2.val)) :=
    e.toContinuousLinearEquiv.contDiff.contMDiff.comp
      (hm.comp ((hc.comp contMDiff_fst).prodMk
        (e.symm.toContinuousLinearEquiv.contDiff.contMDiff.comp
          ((isSmoothEmbedding_closedCell_inclusion 1).contMDiff.comp contMDiff_snd))))
  apply (ContMDiff.iff_comp_isImmersion
    (isSmoothEmbedding_closedCell_inclusion 1).isImmersion).mpr
  exact ⟨h.continuous.subtype_mk _, h⟩

theorem closedDiskRotation_eq_self_iff (t : Circle) (x : ClosedCell 2) :
    closedDiskRotation t x = x ↔ t = 1 ∨ x.val = 0 := by
  constructor
  · intro h
    have he := congrArg (fun y : ClosedCell 2 =>
      Complex.orthonormalBasisOneI.repr.symm y.val) h
    rw [closedDiskRotation_complex] at he
    by_cases hx : Complex.orthonormalBasisOneI.repr.symm x.val = 0
    · exact Or.inr (Complex.orthonormalBasisOneI.repr.symm.injective
        (hx.trans (map_zero _).symm))
    · exact Or.inl (Subtype.ext ((mul_eq_right₀ hx).mp he))
  · rintro (rfl | hx)
    · exact closedDiskRotation_one x
    · apply Subtype.ext
      simp [closedDiskRotation_apply, hx]

end DifferentialGeometry.Topology.Manifold
