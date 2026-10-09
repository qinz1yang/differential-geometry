import DifferentialGeometry.Geometry.Curvature.Bounds.PullbackSectionalPinching
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.RawRestriction

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Connection

universe uE uH uM uF uH' uN

theorem exists_pos_sectional_pinching_of_raw_pullback_derivatives
    {κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η) :
    ∃ δ > 0,
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] (H : Type uH) [TopologicalSpace H]
        (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type uM) [TopologicalSpace M] [ChartedSpace H M]
        [IsManifold I ∞ M] [T2Space M]
        (F : Type uF) [NormedAddCommGroup F] [NormedSpace ℝ F]
        [FiniteDimensional ℝ F] (H' : Type uH') [TopologicalSpace H']
        (J : ModelWithCorners ℝ F H') [J.Boundaryless]
        (N : Type uN) [TopologicalSpace N] [ChartedSpace H' N]
        [IsManifold J ∞ N] [T2Space N]
        (Φ : PartialDiffeomorph I J M N ∞)
        (G : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
        (c : ℝ) (hc : 0 < c) (p : M),
        p ∈ Φ.source →
        (∀ k : ℕ, k ≤ 2 →
          tensor0SFiberNorm G p (2 + k)
            (iteratedMetricCovariantDerivative G 2
              (fun y : M =>
                ((continuousMultilinearCurryFin1 ℝ (TangentSpace I y) ℝ).symm.toContinuousLinearMap.comp
                  (c • localPullInner h (Φ : M → N) y - G.inner y)).uncurryLeft) k p) ≤ δ) →
        (∀ v w : TangentSpace I p, LinearIndependent ℝ ![v, w] →
          sectionalCurvature G p v w = -κ) →
        SectionalBoundedBelowAt (scaleMetric c hc h) (Φ p) (-(κ + η)) ∧
          ∀ v w : TangentSpace J (Φ p), LinearIndependent ℝ ![v, w] →
            sectionalCurvature (scaleMetric c hc h) (Φ p) v w ≤ -(κ - η) := by
  obtain ⟨δ, hδ, hpinch⟩ :=
    exists_pos_sectional_pinching_of_pullback_metricDerivNorm_le.{uE, uH, uM, uF, uH', uN}
      hκ hη
  refine ⟨δ, hδ, ?_⟩
  intro E _ _ _ H _ I _ M _ _ _ _ F _ _ _ H' _ J _ N _ _ _ _ Φ G h c hc p hp hraw hsec
  let U : TopologicalSpace.Opens M := ⟨Φ.source, Φ.open_source⟩
  have hU : (U : Set M) ⊆ Φ.source := fun _ hx => hx
  let pU : U := ⟨p, hp⟩
  let hΦ := isLocalDiffeomorph_restrict_open (I := I) (J := J) U
    (fun y => Φ.isLocalDiffeomorphAt I J ∞ (hU y.property))
  apply hpinch E H I M F H' J N Φ U hU G (scaleMetric c hc h) pU
  · intro k hk
    rw [metricDerivNorm_scaled_localPullMetric_eq_raw G h (Φ : M → N) U hΦ c hc k pU]
    exact hraw k hk
  · exact hsec

end DifferentialGeometry.Geometry.Curvature
