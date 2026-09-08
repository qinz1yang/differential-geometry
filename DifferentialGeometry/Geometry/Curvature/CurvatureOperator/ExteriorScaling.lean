import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorRepresentation
import DifferentialGeometry.Geometry.Curvature.Scaling
import DifferentialGeometry.Geometry.Curvature.AlgebraicTensorMetric

noncomputable section

namespace exteriorPower
open DifferentialGeometry.Geometry.Curvature
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem traceNormalizedCurvatureEndomorphism_smul
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d])) (c : ℝ) :
    traceNormalizedCurvatureEndomorphism (c • T) (hT.smul c) =
      c • traceNormalizedCurvatureEndomorphism T hT := by
  symm
  apply (eq_traceNormalizedCurvatureEndomorphism_iff _ _ _).mpr
  intro a b d e
  simp only [smul_apply, real_inner_smul_left,
    inner_traceNormalizedCurvatureEndomorphism_ιMulti, Matrix.cons_val_zero,
    Matrix.cons_val_one, smul_eq_mul]
  ring

theorem traceNormalizedCurvatureSelfAdjoint_smul
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d])) (c : ℝ) :
    traceNormalizedCurvatureSelfAdjoint (c • T) (hT.smul c) =
      c • traceNormalizedCurvatureSelfAdjoint T hT := by
  apply Subtype.ext
  exact traceNormalizedCurvatureEndomorphism_smul T hT c

end exteriorPower

namespace DifferentialGeometry.Geometry.Curvature
open Bundle
open scoped Manifold ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem traceNormalizedCurvatureEndomorphism_scaleMetric_pullback
    (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M)
    (e : F →L[ℝ] TangentSpace I x) :
    let T := metricRm04At g x
    let hT := mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule g x)
    let S := metricRm04At (scaleMetric c hc g) x
    let hS := mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule (scaleMetric c hc g) x)
    exteriorPower.traceNormalizedCurvatureEndomorphism
      (S.compContinuousLinearMap (fun _ => (Real.sqrt c)⁻¹ • e))
      (hS.compContinuousLinearMap ((Real.sqrt c)⁻¹ • e)) =
      c⁻¹ • exteriorPower.traceNormalizedCurvatureEndomorphism
        (T.compContinuousLinearMap (fun _ => e)) (hT.compContinuousLinearMap e) := by
  dsimp only
  have heq : (metricRm04At (scaleMetric c hc g) x).compContinuousLinearMap
      (fun _ => (Real.sqrt c)⁻¹ • e) =
      c⁻¹ • (metricRm04At g x).compContinuousLinearMap (fun _ => e) := by
    ext v
    exact metricRm04At_scaleMetric_inv_sqrt_smul c hc g x (fun i => e (v i))
  simp only [heq]
  exact exteriorPower.traceNormalizedCurvatureEndomorphism_smul _ _ _

theorem traceNormalizedCurvatureSelfAdjoint_scaleMetric_pullback
    (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M)
    (e : F →L[ℝ] TangentSpace I x) :
    let T := metricRm04At g x
    let hT := mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule g x)
    let S := metricRm04At (scaleMetric c hc g) x
    let hS := mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule (scaleMetric c hc g) x)
    exteriorPower.traceNormalizedCurvatureSelfAdjoint
      (S.compContinuousLinearMap (fun _ => (Real.sqrt c)⁻¹ • e))
      (hS.compContinuousLinearMap ((Real.sqrt c)⁻¹ • e)) =
      c⁻¹ • exteriorPower.traceNormalizedCurvatureSelfAdjoint
        (T.compContinuousLinearMap (fun _ => e)) (hT.compContinuousLinearMap e) := by
  apply Subtype.ext
  exact traceNormalizedCurvatureEndomorphism_scaleMetric_pullback c hc g x e

end DifferentialGeometry.Geometry.Curvature
