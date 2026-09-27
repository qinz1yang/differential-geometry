import DifferentialGeometry.Analysis.Calculus.MapConvergence.SmoothInverseOn


import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.Bounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Transition.Overlap
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalCoordinates.TransitionBounds
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Filter Topology

section HCGNormalTransition

open Bundle
open scoped Manifold ContDiff Bundle
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

universe u uE uH

section NormalTransitionCompactness

variable {E : Type uE} [NormedAddCommGroup E]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_normal_transition_subsequence
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (metricInput : NormalCoordMetricBounds (I := I) X)
    (x y : ∀ k : ℕ, (X.obj k).M)
    {U V Ua Va : Set E}
    (hU : IsOpen U) (hV : IsOpen V) (hUa : IsOpen Ua) (hVa : IsOpen Va)
    (hUanorm : ∃ Z : Real, ∀ z ∈ Ua, ‖z‖ ≤ Z)
    (hVanorm : ∃ Z : Real, ∀ z ∈ Va, ‖z‖ ≤ Z)
    (hUmetric : ∀ k, U ⊆ Metric.ball (0 : E) (metricInput.radius k (x k)))
    (hVmetric : ∀ k, V ⊆ Metric.ball (0 : E) (metricInput.radius k (y k)))
    (hUametric : ∀ k, Ua ⊆ Metric.ball (0 : E) (metricInput.radius k (x k)))
    (hVametric : ∀ k, Va ⊆ Metric.ball (0 : E) (metricInput.radius k (y k)))
    (hUexp : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      U ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj k).metric (x k)))
    (hVexp : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      V ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj k).metric (y k)))
    (hUaexp : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      Ua ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj k).metric (x k)))
    (hVaexp : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      Va ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj k).metric (y k)))
    (hJ : ∀ k, ContDiffOn Real (⊤ : ℕ∞)
      (normalTransition (I := I) (X.obj k) (x k) (y k)) U)
    (hJbar : ∀ k, ContDiffOn Real (⊤ : ℕ∞)
      (normalTransition (I := I) (X.obj k) (y k) (x k)) V)
    (hovlJ : ∀ k, NormalOverlapOn (I := I) (X.obj k) (x k) (y k) U)
    (hovlJbar : ∀ k, NormalOverlapOn (I := I) (X.obj k) (y k) (x k) V)
    (hmapJ : ∀ k, Set.MapsTo
      (normalTransition (I := I) (X.obj k) (x k) (y k)) U Va)
    (hmapJbar : ∀ k, Set.MapsTo
      (normalTransition (I := I) (X.obj k) (y k) (x k)) V Ua)
    (hLeft : ∀ k, ∀ z ∈ U,
      normalTransition (I := I) (X.obj k) (y k) (x k)
        (normalTransition (I := I) (X.obj k) (x k) (y k) z) = z)
    (hRight : ∀ k, ∀ w ∈ V,
      normalTransition (I := I) (X.obj k) (x k) (y k)
        (normalTransition (I := I) (X.obj k) (y k) (x k) w) = w) :
    ∃ (φ : ℕ → ℕ) (Jinf : E → E) (Jbarinf : E → E),
      StrictMono φ ∧ ContDiffOn ℝ (⊤ : ℕ∞) Jinf U ∧
        ContDiffOn ℝ (⊤ : ℕ∞) Jbarinf V ∧
        MapCInfConvergenceOnCompacts U
          (fun k => normalTransition (I := I) (X.obj (φ k))
            (x (φ k)) (y (φ k))) Jinf ∧
        MapCInfConvergenceOnCompacts V
          (fun k => normalTransition (I := I) (X.obj (φ k))
            (y (φ k)) (x (φ k))) Jbarinf ∧
        (∀ z ∈ U, Jinf z ∈ V → Jbarinf (Jinf z) = z) ∧
        (∀ w ∈ V, Jbarinf w ∈ U → Jinf (Jbarinf w) = w) := by
  apply exists_smooth_inverse_limit_subsequence_on hU hV
    (fun k => normalTransition (I := I) (X.obj k) (x k) (y k))
    (fun k => normalTransition (I := I) (X.obj k) (y k) (x k))
    hJ hJbar
  · exact MetricIsometry.normal_bounds_on (I := I) X metricInput x y U Va hU hVa
      hVanorm hUmetric hVametric hUexp hVaexp hJ hovlJ hmapJ
  · exact MetricIsometry.normal_bounds_on (I := I) X metricInput y x V Ua hV hUa
      hUanorm hVmetric hUametric hVexp hUaexp hJbar hovlJbar hmapJbar
  · exact hLeft
  · exact hRight

end NormalTransitionCompactness

end HCGNormalTransition

end CheegerGromovCompactness
end DifferentialGeometry
