import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PointedPinchingLimit
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.MetricExtension
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ReferenceChange
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCrossConvergence
import DifferentialGeometry.Geometry.Curvature.ModelChange
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.CurvatureOperator

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

private theorem curvatureOperator_nonnegative_of_metricCInf_admissible_pinching_of_innerProductSpace
    (G : ℕ → SmoothRiemannianMetric I M) (g r : SmoothRiemannianMetric I M)
    (hconv : MetricCInfConvergenceOnCompacts G g r)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (Q : ℕ → ℝ) (hQpos : ∀ i, 0 < Q i) (hQ : Tendsto Q atTop atTop)
    (hpinching : ∀ᶠ i in atTop, ∀ x : M, curvatureOperatorLowerBoundAt (G i) x
      (metricAlgebraicCurvatureTensorAt (G i) x)
      (rescalePinchingFunction (Q i) Phi (metricScalarAt (G i) x))) :
    ∀ x : M, metricAlgebraicCurvatureTensorAt g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) := by
  intro x
  let P : PointedRiemannianManifold I := {
    M := M, topology := inferInstance, charted := inferInstance, smooth := inferInstance,
    t2 := inferInstance, sigmaCompact := inferInstance, t2TangentBundle := inferInstance,
    basepoint := x, metric := g }
  let X : PointedRiemannianSeq I := ⟨fun i => { P with metric := G i }⟩
  let F : PointedRiemannianConvergenceMaps X P id := {
    partialDiffeomorph := fun _ => PartialDiffeomorph.refl M
    source_exhausts := ⟨fun _ => isOpen_univ, fun _ => subset_univ _,
      fun _ _ => ⟨0, fun _ _ => subset_univ _⟩⟩
    base_mem := fun _ => mem_univ _
    basepoint_map := fun _ => rfl }
  obtain ⟨C, hC, _⟩ := exists_canonicalMetricConvergenceData_of_metric_extension F G
    (hconv.change_reference g) (by
      intro K _
      refine Eventually.of_forall fun i =>
        ⟨univ, isOpen_univ, subset_univ _, subset_univ _, ?_⟩
      intro y _ v w
      change (G i).inner y v w =
        (G i).inner y (mfderiv I I id y v) (mfderiv I I id y w)
      rw [mfderiv_id]
      rfl)
  exact curvatureOperator_nonnegative_of_pointed_admissible_pinching_eventually
    C hC hPhi Q hQpos hQ hpinching x

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem curvatureOperator_nonnegative_of_metricCInf_admissible_pinching
    (G : ℕ → SmoothRiemannianMetric I M) (g r : SmoothRiemannianMetric I M)
    (hconv : MetricCInfConvergenceOnCompacts G g r)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (Q : ℕ → ℝ) (hQpos : ∀ i, 0 < Q i) (hQ : Tendsto Q atTop atTop)
    (hpinching : ∀ᶠ i in atTop, ∀ x : M, curvatureOperatorLowerBoundAt (G i) x
      (metricAlgebraicCurvatureTensorAt (G i) x)
      (rescalePinchingFunction (Q i) Phi (metricScalarAt (G i) x))) :
    ∀ x : M, metricAlgebraicCurvatureTensorAt g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (Fin (Module.finrank ℝ E)) ℝ).symm
  let J := I.transContinuousLinearEquiv e
  let f := ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e
  let G' : ℕ → SmoothRiemannianMetric J M := fun i => (G i).transContinuousLinearEquiv e
  let g' : SmoothRiemannianMetric J M := g.transContinuousLinearEquiv e
  let r' : SmoothRiemannianMetric J M := r.transContinuousLinearEquiv e
  have hconv' : MetricCInfConvergenceOnCompacts G' g' r' :=
    KappaSolutions.metricCInfConvOnCompacts_pullbackCross G g r f.symm hconv
  have hpinching' : ∀ᶠ i in atTop, ∀ x : M, curvatureOperatorLowerBoundAt (G' i) x
      (metricAlgebraicCurvatureTensorAt (G' i) x)
      (rescalePinchingFunction (Q i) Phi (metricScalarAt (G' i) x)) := by
    filter_upwards [hpinching] with i hi
    intro x
    change curvatureOperatorLowerBoundAt ((G i).transContinuousLinearEquiv e) x
      (metricAlgebraicCurvatureTensorAt ((G i).transContinuousLinearEquiv e) x)
      (rescalePinchingFunction (Q i) Phi
        (metricScalarAt ((G i).transContinuousLinearEquiv e) x))
    rw [metricScalarAt_transContinuousLinearEquiv]
    change curvatureOperatorLowerBoundAt (Diffeomorph.pullbackMetricCross (G i) f.symm) x
      (metricAlgebraicCurvatureTensorAt (Diffeomorph.pullbackMetricCross (G i) f.symm) x) _
    rw [Diffeomorph.pullbackMetricCross_eq_localPullMetric,
      curvatureOperatorLowerBoundAt_localPullMetric_iff]
    exact hi x
  have hnonneg :=
    curvatureOperator_nonnegative_of_metricCInf_admissible_pinching_of_innerProductSpace
      G' g' r' hconv' hPhi Q hQpos hQ hpinching'
  intro x
  have hzero : curvatureOperatorLowerBoundAt g' x (metricAlgebraicCurvatureTensorAt g' x) 0 := by
    simpa only [curvatureOperatorLowerBoundAt, zero_mul, add_zero,
      mem_algebraicCurvatureOperatorNonnegativeCone] using hnonneg x
  change curvatureOperatorLowerBoundAt (Diffeomorph.pullbackMetricCross g f.symm) x
    (metricAlgebraicCurvatureTensorAt (Diffeomorph.pullbackMetricCross g f.symm) x) 0 at hzero
  rw [Diffeomorph.pullbackMetricCross_eq_localPullMetric,
    curvatureOperatorLowerBoundAt_localPullMetric_iff] at hzero
  change curvatureOperatorLowerBoundAt g x (metricAlgebraicCurvatureTensorAt g x) 0 at hzero
  simpa only [curvatureOperatorLowerBoundAt, zero_mul, add_zero,
    mem_algebraicCurvatureOperatorNonnegativeCone] using hzero

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
