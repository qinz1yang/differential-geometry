import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PointedPinchingLimit
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.MetricExtension
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ReferenceChange

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Bundle Manifold Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology

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
