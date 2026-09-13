import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalAlternativeTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PositiveComponentModels

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle

universe u

private instance roundSphereFourFinrank :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

section ScaledEigenvalue

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem secLower_iff_eigenvalue_lower_bound (g : SmoothRiemannianMetric I3 M) (c : ℝ)
    (U : Set M) :
    SecLower g c U ↔ ∀ y ∈ U, c ≤ leastCurvatureOperatorEigenvalueAt (I := I3) g y
      (metricAlgebraicCurvatureTensorAt (I := I3) (M := M) g y) :=
  secLower_iff_le_leastCurvatureOperatorEigenvalueAt g (by simp [ThreeSpace]) c U

omit [SigmaCompactSpace M] in
theorem secLower_iff_scaled_eigenvalue_lower_bound {a c : ℝ} (ha : 0 < a)
    (g : SmoothRiemannianMetric I3 M) (U : Set M) :
    SecLower (scaleMetric (I := I3) a ha g) c U ↔
      ∀ y ∈ U, c ≤ leastCurvatureOperatorEigenvalueAt (I := I3)
        (scaleMetric (I := I3) a ha g) y
        (metricAlgebraicCurvatureTensorAt (I := I3) (M := M)
          (scaleMetric (I := I3) a ha g) y) :=
  secLower_iff_le_leastCurvatureOperatorEigenvalueAt (scaleMetric (I := I3) a ha g)
    (by simp [ThreeSpace]) c U

omit [SigmaCompactSpace M] in
theorem secLower_of_scaled_eigenvalue_lower_bound {a c : ℝ} (ha : 0 < a)
    (g : SmoothRiemannianMetric I3 M) {U : Set M}
    (h : ∀ y ∈ U, c ≤ leastCurvatureOperatorEigenvalueAt (I := I3)
      (scaleMetric (I := I3) a ha g) y
      (metricAlgebraicCurvatureTensorAt (I := I3) (M := M)
        (scaleMetric (I := I3) a ha g) y)) :
    SecLower g (c * a) U :=
  (secLower_scaleMetric_iff ha g U).mp ((secLower_iff_scaled_eigenvalue_lower_bound ha g U).mpr h)

theorem canonicalAlternative_transport_positive_of_scaled_eigenvalue_lower_bound
    {P : Type u} [TopologicalSpace P] [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P]
    [T2Space P] [SigmaCompactSpace P]
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    {x : M} {t : ℝ} {eps C : ℝ} {U : Set P}
    (data : PositiveComponent (M := P) U) (e : PartialDiffeomorph I3 I3 P M ∞)
    (he : U ⊆ e.source) (hwhole : e '' U = connectedComponent x)
    (hQ : 0 < S.scalar t x) {c : ℝ} (hc : C⁻¹ ≤ c)
    (h : ∀ y ∈ e '' U, c ≤ leastCurvatureOperatorEigenvalueAt (I := I3)
      (scaleMetric (I := I3) (S.scalar t x) hQ (S.base.metric t)) y
      (metricAlgebraicCurvatureTensorAt (I := I3) (M := M)
        (scaleMetric (I := I3) (S.scalar t x) hQ (S.base.metric t)) y)) :
    Nonempty (CanonicalAlternative S eps C x t (connectedComponent x)) :=
  canonicalAlternative_transport_positive data e he hwhole
    (secLower_of_scaleInvariant_lower_bound S hQ hc h)

end ScaledEigenvalue

theorem secLower_scaleMetric_roundMetricSphereThree {a : ℝ} (ha : 0 < a) :
    SecLower (M := Sphere 3)
      (scaleMetric (I := I3) a ha
        (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3))) a⁻¹ Set.univ :=
  (secLower_scaleMetric_iff ha (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3))
    Set.univ).mpr (by
      rw [inv_mul_cancel₀ ha.ne']
      exact secLower_roundMetricSphereThree)

theorem one_le_leastCurvatureOperatorEigenvalueAt_roundMetricSphereThree :
    ∀ y : Sphere 3, 1 ≤ leastCurvatureOperatorEigenvalueAt (I := I3)
      (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)) y
      (metricAlgebraicCurvatureTensorAt (I := I3) (M := Sphere 3)
        (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)) y) :=
  fun y => (secLower_iff_eigenvalue_lower_bound
      (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)) 1 Set.univ).mp
    secLower_roundMetricSphereThree y (Set.mem_univ y)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
