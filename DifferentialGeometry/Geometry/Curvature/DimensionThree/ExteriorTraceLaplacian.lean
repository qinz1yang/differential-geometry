import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorTracePullback
import DifferentialGeometry.Geometry.Connection.Laplacian.Trace
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorSmooth
import DifferentialGeometry.Geometry.Connection.LeviCivita.Pullback
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.ExteriorPower

noncomputable section
open Bundle
open scoped Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem trace_rawBundleEndomorphismConnLap_metric_pullback
    (g : SmoothRiemannianMetric I M)
    (ι : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun y => TotalSpace.mk' (F →L[ℝ] E) y (ι y).toContinuousLinearMap))
    (hmetric : ∀ x v w, g.inner x (ι x v) (ι x w) = ⟪v, w⟫)
    (hdim : Module.finrank ℝ F = 3) (x : M) :
    letI : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
    letI := Bundle.ExteriorPower.totalSpaceTopology F V 2
    letI := Bundle.ExteriorPower.fiberBundle F V 2
    letI := Bundle.ExteriorPower.vector_bundle F V 2
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
    let hι₁ := hι.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
    let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
      (fun y => (ι y).toLinearEquiv) hι₁.clm_bundle_map (LeviCivita g)
    let T := fun y => (metricRm04At g y).compContinuousLinearMap
      (fun _ => (ι y).toContinuousLinearMap)
    let hT := fun y => (mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule g y)).compContinuousLinearMap
      (ι y).toContinuousLinearMap
    let R := fun y => exteriorPower.traceNormalizedCurvatureEndomorphism (T y) (hT y)
    LinearMap.trace ℝ (⋀[ℝ]^2 (V x))
      (rawBundleEndomorphismConnLap g (cov.exteriorPower 2) R x).toLinearMap =
      laplacian (LeviCivita g) g (metricScalarAt g) x := by
  dsimp only
  let _ : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  let _ := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let _ := Bundle.ExteriorPower.fiberBundle F V 2
  let _ := Bundle.ExteriorPower.vector_bundle F V 2
  let _ := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  let _ := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
  let hι₁ := hι.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
  let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
    (fun y => (ι y).toLinearEquiv) hι₁.clm_bundle_map (LeviCivita g)
  let T := fun y => (metricRm04At g y).compContinuousLinearMap
    (fun _ => (ι y).toContinuousLinearMap)
  let hT : ∀ y, IsAlgCurvForm (fun a b c d => T y ![a,b,c,d]) := fun y =>
    (mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule g y)).compContinuousLinearMap
      (ι y).toContinuousLinearMap
  let R := fun y => exteriorPower.traceNormalizedCurvatureEndomorphism (T y) (hT y)
  have hTsmooth : ContMDiff I (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ)) ∞
      (fun y => TotalSpace.mk' (ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ)
        (E := Bundle.continuousMultilinearMap ℝ 4 F V) y (T y)) :=
    (metricRm04 g).contMDiff.multilinear_bundle_comp (fun _ => hι)
  have hRsmooth := Bundle.ExteriorPower.contMDiff_traceNormalizedCurvatureEndomorphism F V
    ∞ le_rfl T hT hTsmooth
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  have hιinv : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] F) y (ι y).symm.toContinuousLinearMap) := by
    simpa only [ContinuousLinearMap.inverse_equiv] using
      hι.clm_bundle_inverse (fun _ => ContinuousLinearMap.isInvertible_equiv)
  let _ : CovariantDerivative.ContMDiffCovariantDerivative cov ∞ :=
    CovariantDerivative.ContMDiffCovariantDerivative.pullbackFiberwiseLinearEquiv
      (fun y => (ι y).toLinearEquiv) hι.clm_bundle_map hιinv.clm_bundle_map (LeviCivita g)
  let _ := cov.exteriorPower_contMDiff 2
  have hc : cov.IsMetricCompatible :=
    CovariantDerivative.isMetricCompatible_pullback_leviCivita g ι hι₁ hmetric
  have htrace : (fun y => LinearMap.trace ℝ (⋀[ℝ]^2 (V y)) (R y).toLinearMap) = metricScalarAt g := by
    funext y
    exact trace_traceNormalizedCurvatureEndomorphism_metric_pullback g
      (RiemannianMetric.ofInnerProductSpace V) ι hmetric y
      ((VectorBundle.finrank_eq ℝ F V y).trans hdim)
  change LinearMap.trace ℝ _ (rawBundleEndomorphismConnLap g (cov.exteriorPower 2) R x).toLinearMap = _
  rw [trace_rawBundleEndomorphismConnLap_eq_laplacian_of_isMetricCompatible g
    (cov.exteriorPower 2) (hc.exteriorPower 2) inferInstance R hRsmooth x, htrace]

end DifferentialGeometry.Geometry.Curvature.DimensionThree
