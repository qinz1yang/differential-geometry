import DifferentialGeometry.Geometry.Connection.Product
import DifferentialGeometry.Geometry.Metric.Cylinder
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Hessian

set_option autoImplicit false
noncomputable section
open Bundle Manifold DifferentialGeometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.VectorField
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Connection

private def standardLine : SmoothRiemannianMetric 𝓘(ℝ) ℝ where
  inner := (riemannianMetricVectorSpace ℝ).inner
  symm := (riemannianMetricVectorSpace ℝ).symm
  pos := (riemannianMetricVectorSpace ℝ).pos
  isVonNBounded := (riemannianMetricVectorSpace ℝ).isVonNBounded
  contMDiff := (riemannianMetricVectorSpace ℝ).contMDiff.of_le le_top

private def lineConst (c : ℝ) : ContMDiffSection 𝓘(ℝ) ℝ ∞ (TangentSpace 𝓘(ℝ) : ℝ → Type _) where
  toFun _ := c
  contMDiff_toFun := by
    apply (contMDiff_vectorSpace_iff_contDiff (𝕜 := ℝ)).mpr
    exact contDiff_const

private theorem lineConst_one_parallel (x v : ℝ) :
    leviCivitaConnectionOfMetric standardLine (lineConst 1) x v = 0 := by
  have h := (leviCivitaConnectionOfMetric_isMetricCompatible standardLine).mvfderiv_inner v
    ((lineConst 1).contMDiff.mdifferentiable (by simp) x)
    ((lineConst 1).contMDiff.mdifferentiable (by simp) x)
  let a : ℝ := by exact leviCivitaConnectionOfMetric standardLine (lineConst 1) x v
  change mvfderiv 𝓘(ℝ) (fun _ : ℝ => (1 : ℝ) * 1) x v = 1 * a + a * 1 at h
  simp only [mvfderiv_const, one_mul, mul_one] at h
  change (0 : ℝ) = a + a at h
  change a = 0
  linarith

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem leviCivita_cylinderAxis (g : SmoothRiemannianMetric I M) (x : M × ℝ)
    (v : TangentSpace (I.prod 𝓘(ℝ)) x) :
    leviCivitaConnectionOfMetric (cylinderMetric g) cylinderAxis x v = 0 := by
  have h := leviCivita_productVectorField_apply g standardLine
    (0 : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) (lineConst 1) x v
  have hemetric : g.prod standardLine = cylinderMetric g := rfl
  rw [hemetric] at h
  have hefield : (productVectorField
      (0 : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) (lineConst 1) :
      ∀ y, TangentSpace (I.prod 𝓘(ℝ)) y) = cylinderAxis := rfl
  rw [hefield] at h
  change leviCivitaConnectionOfMetric (cylinderMetric g) cylinderAxis x v =
    (leviCivitaConnectionOfMetric g (0 : ∀ y, TangentSpace I y) x.1 v.1,
      leviCivitaConnectionOfMetric standardLine (lineConst 1) x.2 v.2) at h
  rw [h, lineConst_one_parallel]
  have hzero := (LeviCivita g).zero
  change leviCivitaConnectionOfMetric g (0 : ∀ y, TangentSpace I y) = 0 at hzero
  rw [hzero]
  rfl

theorem hessFun_height_cylinderMetric [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M × ℝ)
    (v w : TangentSpace (I.prod 𝓘(ℝ)) x) :
    hessFun (cylinderMetric g) Prod.snd x v w = 0 := by
  rw [hessFun_eq_cov_grad _ contMDiff_snd]
  have hgrad : (fun y : M × ℝ => gradFun (cylinderMetric g) Prod.snd y) = cylinderAxis :=
    funext (gradFun_height_eq_cylinderAxis g)
  rw [hgrad]
  change (cylinderMetric g).inner x
    (leviCivitaConnectionOfMetric (cylinderMetric g) cylinderAxis x v) w = 0
  rw [leviCivita_cylinderAxis, map_zero, zero_apply]

end DifferentialGeometry.Geometry.Connection
