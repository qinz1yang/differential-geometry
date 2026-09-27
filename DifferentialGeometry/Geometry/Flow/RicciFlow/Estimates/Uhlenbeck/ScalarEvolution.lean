import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.CurvatureOperatorEvolution
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorTraceLaplacian
import DifferentialGeometry.Analysis.Calculus.Trace

noncomputable section
open Bundle
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Curvature.DimensionThree
open scoped Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem metricScalarAt_hasDerivWithinAt_of_ricci_ode
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (t : D.RegularTime)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x) {J : Set ℝ} (ht : (t : ℝ) ∈ J)
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι t x).toContinuousLinearMap))
    (hmetric : ∀ s ∈ J, ∀ x v w, (S.family.metric s).inner x (ι s x v) (ι s x w) = ⟪v, w⟫)
    (x : M) (hdim : Module.finrank ℝ F = 3)
    (hode : ∀ v, HasDerivWithinAt (fun s => ι s x v)
      (ricciSharp (I := I) (S.family.metric t) x (ι t x v)) J t) :
    HasDerivWithinAt (fun s => metricScalarAt (S.family.metric s) x)
      (laplacian (LeviCivita (S.family.metric t)) (S.family.metric t)
        (metricScalarAt (S.family.metric t)) x +
        2 * Tensor0SBundle.normSq0S (S.family.metric t) x 2 (metricRicciAt (S.family.metric t) x)) J t := by
  let _ : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  let _ := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let _ := Bundle.ExteriorPower.fiberBundle F V 2
  let _ := Bundle.ExteriorPower.vector_bundle F V 2
  let _ := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  let hι₁ := hι.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
  let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
    (fun y => (ι t y).toLinearEquiv) hι₁.clm_bundle_map (LeviCivita (S.family.metric t))
  let T := fun s y => (metricRm04At (S.family.metric s) y).compContinuousLinearMap
    (fun _ => (ι s y).toContinuousLinearMap)
  let hT : ∀ s y, IsAlgCurvForm (fun a b c d => T s y ![a, b, c, d]) := fun s y =>
    (mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric s) y)).compContinuousLinearMap
      (ι s y).toContinuousLinearMap
  let R := fun s y => exteriorPower.traceNormalizedCurvatureEndomorphism (T s y) (hT s y)
  have hd := traceNormalizedCurvatureEndomorphism_pullback_hasDerivWithinAt_of_ricci_ode
    S hS t ι hι (hmetric t ht) x ((VectorBundle.finrank_eq ℝ F V x).trans hdim) hode
  change HasDerivWithinAt (fun s => R s x)
    (rawBundleEndomorphismConnLap (S.family.metric t) (cov.exteriorPower 2) (R t) x +
      (curvatureOperatorReactionEndomorphism3 (R t x).toLinearMap).toContinuousLinearMap) J t at hd
  have hdt := DifferentialGeometry.Analysis.hasDerivWithinAt_linearMap_trace hd
  have htrace (s : ℝ) (hs : s ∈ J) : LinearMap.trace ℝ (⋀[ℝ]^2 (V x)) (R s x).toLinearMap = metricScalarAt (S.family.metric s) x := by
    exact trace_traceNormalizedCurvatureEndomorphism_metric_pullback (S.family.metric s)
      (RiemannianMetric.ofInnerProductSpace V) (ι s) (hmetric s hs) x
      ((VectorBundle.finrank_eq ℝ F V x).trans hdim)
  have hlap := trace_rawBundleEndomorphismConnLap_metric_pullback (S.family.metric t)
    (ι t) hι (hmetric t ht) hdim x
  have hreact := trace_curvatureOperatorReactionEndomorphism3_metric_pullback (S.family.metric t)
    (RiemannianMetric.ofInnerProductSpace V) (ι t) (hmetric t ht) x
    ((VectorBundle.finrank_eq ℝ F V x).trans hdim)
  have hf : HasDerivWithinAt (fun s => metricScalarAt (S.family.metric s) x)
    (LinearMap.trace ℝ (⋀[ℝ]^2 (V x))
      (rawBundleEndomorphismConnLap (S.family.metric t) (cov.exteriorPower 2) (R t) x +
        (curvatureOperatorReactionEndomorphism3 (R t x).toLinearMap).toContinuousLinearMap).toLinearMap) J t := by
    exact hdt.congr (fun s hs => (htrace s hs).symm) (htrace t ht).symm
  apply hf.congr_deriv
  change LinearMap.trace ℝ _ ((rawBundleEndomorphismConnLap (S.family.metric t)
    (cov.exteriorPower 2) (R t) x).toLinearMap +
    curvatureOperatorReactionEndomorphism3 (R t x).toLinearMap) = _
  rw [map_add, hlap]
  exact congrArg (fun r => laplacian (LeviCivita (S.family.metric t)) (S.family.metric t)
    (metricScalarAt (S.family.metric t)) x + r) hreact

end DifferentialGeometry.PDE.RicciFlow
