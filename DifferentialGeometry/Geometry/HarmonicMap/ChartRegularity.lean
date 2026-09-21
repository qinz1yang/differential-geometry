import DifferentialGeometry.Analysis.Sobolev.Euclidean.MetricEnergy.GradientRegularity
import DifferentialGeometry.Geometry.Metric.Pullback.ConvexBounds
import DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.Locality

section

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter MeasureTheory Metric
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem exists_contDiffOn_one_of_chart_metric_minimality
    {m : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m)) {R a : ℝ} (hR : 0 < R) (ha : 0 < a)
    (hKsource : MapsTo L.symm (closedBall (0 : EuclideanSpace ℝ (Fin m)) a) Φ.source)
    {z : V → EuclideanSpace ℝ (Fin m)}
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (ball (0 : V) R))
    (hzc : ContinuousOn z (ball (0 : V) R)) (hz0 : z 0 = 0)
    (hzrange : MapsTo z (ball (0 : V) R) (closedBall (0 : EuclideanSpace ℝ (Fin m)) a))
    (hmin : let ψ := fun y => Φ (L.symm y)
      ∀ s : ℝ, 0 < s → s < R → ∀ q : V → EuclideanSpace ℝ (Fin m),
        ∀ hq : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => q x i) (ball (0 : V) s),
        (∀ i, DeGiorgi.MemW01p 2 (fun x => q x i - z x i) (ball (0 : V) s)) →
        (∀ᵐ x ∂volume.restrict (ball (0 : V) s), q x ∈ closedBall 0 a) →
        (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball (0 : V) s,
          pullbackMetricCoefficients g ψ (z x)
            (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))
            (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))) ≤
          (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball (0 : V) s,
            pullbackMetricCoefficients g ψ (q x)
              (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))
              (WithLp.toLp 2 (fun i => (hq i).weakGrad x j)))) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ ContDiffOn ℝ 1 z (ball (0 : V) r) ∧
      ∃ (G : Fin m → V → V) (C : Fin m → ℝ),
        (∀ i, 0 ≤ C i) ∧
        (∀ i, G i =ᵐ[volume.restrict (ball (0 : V) r)] (hz i).weakGrad) ∧
        (∀ i, ∀ x ∈ ball (0 : V) r, HasFDerivAt (fun y => z y i) (innerSL ℝ (G i x)) x) ∧
        ∀ i, ∀ x ∈ ball (0 : V) r, ∀ y ∈ ball (0 : V) r,
          ‖G i x - G i y‖ ≤ C i * ‖x - y‖ ^ ((1 : ℝ) / 8) := by
  let ψ := fun y => Φ (L.symm y)
  let B := pullbackMetricCoefficients g ψ
  have hK := isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) a
  obtain ⟨lam, C, hlam, hcoerce, hBLip⟩ := exists_pullback_metric_bounds_on_convex_chart
    g Φ L.symm hK (convex_closedBall 0 a) hKsource
  have hzK : ∀ᵐ x ∂volume.restrict (ball (0 : V) R), z x ∈ closedBall 0 a := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hzrange hx
  exact exists_contDiffOn_one_of_continuous_metric_minimizer hR ha hz hzc hz0 B hBLip
    (fun y _ v w => g.symm _ _ _) hlam hcoerce
    (fun c s hs hcs q hq hqz hqK =>
      quadratic_weakGrad_energy_le_on_subball_of_concentric_minimality
        hz hK hzK B hBLip.continuousOn hmin hs hcs q hq hqz hqK)

end DifferentialGeometry.Geometry

end

end
