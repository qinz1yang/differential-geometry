import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorReaction

noncomputable section

open Bundle
open scoped Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem trace_traceNormalizedCurvatureEndomorphism_metricRm04At
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank ℝ (TangentSpace I x) = 3) :
    let T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ := metricRm04At g x
    let hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d]) := by
      exact mem_algebraicCurvatureTensorSubmodule.mp
        (metricRm04At_mem_algebraicCurvatureTensorSubmodule g x)
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI targetNorm : ∀ y : M, NormedAddCommGroup (TangentSpace I y) := fun y =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y
    letI : ∀ y : M, SeminormedAddCommGroup (TangentSpace I y) :=
      fun y => (targetNorm y).toSeminormedAddCommGroup
    letI : ∀ y : M, InnerProductSpace ℝ (TangentSpace I y) :=
      fun y => Bundle.instInnerProductSpaceReal y
    LinearMap.trace ℝ (⋀[ℝ]^2 (TangentSpace I x))
      (exteriorPower.traceNormalizedCurvatureEndomorphism T hT).toLinearMap =
      metricScalarAt g x := by
  intro T hT
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let targetNorm : ∀ y : M, NormedAddCommGroup (TangentSpace I y) := fun y =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y
  let _ : ∀ y : M, SeminormedAddCommGroup (TangentSpace I y) :=
    fun y => (targetNorm y).toSeminormedAddCommGroup
  let _ : ∀ y : M, InnerProductSpace ℝ (TangentSpace I y) :=
    fun y => Bundle.instInnerProductSpaceReal y
  let b := (stdOrthonormalBasis ℝ (TangentSpace I x)).reindex (finCongr hdim)
  have horth : OrthonormalBasisAt g x b.toBasis := by
    intro i j
    exact b.inner_eq_ite i j
  rw [LinearMap.trace_eq_matrix_trace ℝ (curvatureBivectorBasis b).toBasis,
    traceNormalizedCurvatureEndomorphism_toMatrix]
  exact traceNormalizedMetricCurvatureOperatorMatrixAt_trace_eq_metricScalarAt g x b.toBasis horth

end DifferentialGeometry.Geometry.Curvature.DimensionThree
