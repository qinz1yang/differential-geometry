import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.Diffeomorph
import DifferentialGeometry.Topology.Manifold.StereographicAntipodal

set_option autoImplicit false

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E V H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace H]
  (I : ModelWithCorners ℝ V H) (r : ℝ)
  [ChartedSpace H (Metric.closedBall (0 : E) r)]
  (h : IsImmersion I 𝓘(ℝ, E) ∞ (Subtype.val : Metric.closedBall (0 : E) r → E))

def closedBallLinearIsometryDiffeomorph (A : E ≃ₗᵢ[ℝ] E) :
    Metric.closedBall (0 : E) r ≃ₘ⟮I, I⟯ Metric.closedBall (0 : E) r where
  toFun x := ⟨A x.val, by simpa only [Metric.mem_closedBall, dist_zero_right, A.norm_map] using x.property⟩
  invFun x := ⟨A.symm x.val, by simpa only [Metric.mem_closedBall, dist_zero_right, A.symm.norm_map] using x.property⟩
  left_inv x := Subtype.ext (A.symm_apply_apply x.val)
  right_inv x := Subtype.ext (A.apply_symm_apply x.val)
  contMDiff_toFun := by
    apply (ContMDiff.iff_comp_isImmersion h).mpr
    exact ⟨(A.continuous.comp continuous_subtype_val).subtype_mk _,
      A.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff.comp h.contMDiff⟩
  contMDiff_invFun := by
    apply (ContMDiff.iff_comp_isImmersion h).mpr
    exact ⟨(A.symm.continuous.comp continuous_subtype_val).subtype_mk _,
      A.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff.comp h.contMDiff⟩

@[simp] theorem closedBallLinearIsometryDiffeomorph_apply (A : E ≃ₗᵢ[ℝ] E)
    (x : Metric.closedBall (0 : E) r) :
    (closedBallLinearIsometryDiffeomorph I r h A x).val = A x.val := rfl

@[simp] theorem closedBallLinearIsometryDiffeomorph_symm_apply (A : E ≃ₗᵢ[ℝ] E)
    (x : Metric.closedBall (0 : E) r) :
    ((closedBallLinearIsometryDiffeomorph I r h A).symm x).val = A.symm x.val := rfl

theorem mfderiv_closedBallLinearIsometryDiffeomorph_coe (A : E ≃ₗᵢ[ℝ] E)
    (x : Metric.closedBall (0 : E) r) :
    mfderiv I 𝓘(ℝ, E) (Subtype.val : Metric.closedBall (0 : E) r → E)
        (closedBallLinearIsometryDiffeomorph I r h A x) ∘L
      mfderiv I I (closedBallLinearIsometryDiffeomorph I r h A) x =
        A.toContinuousLinearEquiv.toContinuousLinearMap ∘L
          mfderiv I 𝓘(ℝ, E) (Subtype.val : Metric.closedBall (0 : E) r → E) x := by
  rw [← mfderiv_comp x (h.contMDiff.mdifferentiable (by simp) _)
    ((closedBallLinearIsometryDiffeomorph I r h A).contMDiff.mdifferentiable (by simp) _)]
  have heq : (Subtype.val : Metric.closedBall (0 : E) r → E) ∘
      closedBallLinearIsometryDiffeomorph I r h A =
      A.toContinuousLinearEquiv.toContinuousLinearMap ∘ (Subtype.val : Metric.closedBall (0 : E) r → E) := rfl
  rw [heq, mfderiv_comp x ((A.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff (n := ∞)).mdifferentiable (by simp) _)
    (h.contMDiff.mdifferentiable (by simp) _)]
  rw [mfderiv_eq_fderiv, A.toContinuousLinearEquiv.toContinuousLinearMap.fderiv]
  rfl

theorem closedBallLinearIsometryDiffeomorph_isometry (A : E ≃ₗᵢ[ℝ] E) :
    Isometry (closedBallLinearIsometryDiffeomorph I r h A) :=
  fun x y => A.toLinearIsometry.isometry x.val y.val

end DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Topology.Manifold

variable {E V H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace H]
  (I : ModelWithCorners ℝ V H)
  [ChartedSpace H (Metric.closedBall (0 : E) 1)]
  (h : IsImmersion I 𝓘(ℝ, E) ∞ (Subtype.val : Metric.closedBall (0 : E) 1 → E))
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

theorem closedBallLinearIsometryDiffeomorph_neg_sphere (z : Metric.sphere (0 : E) 1) :
    closedBallLinearIsometryDiffeomorph I 1 h (LinearIsometryEquiv.neg ℝ)
        (Set.inclusion Metric.sphere_subset_closedBall z) =
      Set.inclusion Metric.sphere_subset_closedBall (sphereAntipodalDiffeomorph (n := n) z) := by
  apply Subtype.ext
  rfl

end DifferentialGeometry.Topology.Manifold
