import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionTimeZeroScalarBound

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

universe u

theorem exists_subseq_scalar_le_on_normalized_balls_of_forall_radius_positive_depth
    (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop)
    (htraced : ∀ A : ℝ, 0 < A → ∃ θ K : ℝ, 0 < θ ∧ 0 ≤ K ∧ ∀ᶠ n in atTop,
      (H n).isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (θ / R n) (K * R n))
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ)
    {t₀ : ℕ → ℝ} (hsliver : Tendsto (fun n => R n * (t n - t₀ n)) atTop (𝓝 0))
    (hnc : ∀ n (v : Icc (0 : ℝ) (H n).horizon) (p : ((H n).stageAt v).Carrier) (r : ℝ),
      (v : ℝ) < t₀ n → r ≤ ρ → (H n).isParabolicallyRmControlledBall v p r →
      ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt v).Carrier
          ((H n).stageMetric ((H n).activeStage v) v)
          (riemannianBallOf ((H n).stageMetric ((H n).activeStage v) v) p r))
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ n (v : Icc (0 : ℝ) (H n).horizon), (v : ℝ) ≤ t n →
      ∀ x : ((H n).stageAt v).Carrier,
        curvatureOperatorLowerBoundAt ((H n).stageMetric ((H n).activeStage v) v) x
          (metricAlgebraicCurvatureTensorAt ((H n).stageMetric ((H n).activeStage v) v) x)
          (Phi (metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) x)))
    {eps C1 C2 Cq : ℝ} (heps0 : 0 < eps) (heps : eps ≤ crossingNeckAccuracy.{u}) {qs : ℕ → ℝ}
    (hqs : ∀ n, qs n ≤ R n * Cq)
    (hwit : ∀ n (v : Icc (0 : ℝ) (H n).horizon), (v : ℝ) < t₀ n →
      (H n).time ((H n).activeStage v) < v → ∀ p : ((H n).stageAt v).Carrier,
        qs n < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) p →
        ∃ Wt : SpatialCanonicalWitness ((H n).stageMetric ((H n).activeStage v) v) eps C1 C2 p,
          Wt.capTubeHasNeckChart eps) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf ((H (ψ i)).stageMetric ((H (ψ i)).activeStage (t (ψ i)))
          (t (ψ i))) (y (ψ i)) (A / Real.sqrt (R (ψ i))),
        metricScalarAt ((H (ψ i)).stageMetric ((H (ψ i)).activeStage (t (ψ i))) (t (ψ i))) x ≤
          C₀ * R (ψ i) := by
  choose θ K hθ hK hev using fun k : ℕ => htraced ((k + 3 : ℕ) : ℝ) (by positivity)
  refine exists_subseq_scalar_le_on_normalized_balls_of_depth_schedule H t y R hR hRlim
    (fun k => min 1 (θ k)) (fun k => lt_min one_pos (hθ k)) (fun k => min_le_left _ _)
    (fun k => ⟨K k, hK k, (hev k).mono fun n hn => hn.mono_depth
      (div_pos (lt_min one_pos (hθ k)) (hR n))
      (div_le_div_of_nonneg_right (min_le_right _ _) (hR n).le)⟩)
    hκ hρ hsliver hnc hPhi hpinch heps0 heps hqs hwit

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
