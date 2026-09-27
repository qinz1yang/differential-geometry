import DifferentialGeometry.Geometry.Exponential.MinimizingDomain.Topology
import DifferentialGeometry.Analysis.Integration.Measure.Polar.NullSets

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space (TangentBundle I M)]
  [RiemannianBundle (fun x : M => TangentSpace I x)]

private local instance tangentSpaceNormedAddCommGroup
    (x : M) : NormedAddCommGroup (TangentSpace I x) :=
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (E := fun y : M => TangentSpace I y) x

private local instance tangentSpaceInnerProductSpace
    (x : M) : InnerProductSpace ℝ (TangentSpace I x) :=
  Bundle.instInnerProductSpaceReal (E := fun y : M => TangentSpace I y) x

private local instance tangentSpaceNormedSpace
    (x : M) : NormedSpace ℝ (TangentSpace I x) := inferInstance

variable [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

variable [MeasurableSpace E] [BorelSpace E]

theorem measure_minimizingDomain_sdiff_extendibleMinimizingDomain
    (g : SmoothRiemannianMetric I M) (p : M)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    μ (minimizingDomain (I := I) g p \
      extendibleMinimizingDomain (I := I) g p) = 0 := by
  apply measure_mono_null ?_
    ((isSigmaCompact_minimizingDomain (I := I) g p).measure_setOf_forall_smul_notMem μ)
  rintro v ⟨hv, hvnot⟩
  exact ⟨hv, fun c hc hcv => hvnot ⟨c, hc, hcv⟩⟩

end DifferentialGeometry.Geometry.Riemannian.Exponential
