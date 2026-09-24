import DifferentialGeometry.Geometry.Neck.BallVolume
import DifferentialGeometry.Geometry.Metric.Distance.LocalCompletion
import DifferentialGeometry.Geometry.Measure.BallMetricLocality
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.MetricLocality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EntropyBounds

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_complete_metric_extension_with_injectivity_of_normalizedNeck
    {K ρ : ℝ} (hρ : 0 < ρ) (hρpow : ρ ^ 4 * K ≤ 1) :
    ∃ η : ℝ, 0 < η ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M],
        ∀ {g : SmoothRiemannianMetric I3 M} {δ eps : ℝ} {k : ℕ}
          (N : NormalizedNeck g δ k), δ ≤ eps → eps < 1 / 11 → ⌈eps⁻¹⌉₊ ≤ k →
          ∀ {a R : ℝ}, 0 < a → 2*a + ρ < eps⁻¹ → a + ρ ≤ R →
          IsCompact (riemannianClosedBallOf (scaleMetric N.scale N.scale_pos g) N.center R) →
          (∀ x ∈ riemannianClosedBallOf (scaleMetric N.scale N.scale_pos g) N.center R,
            curvDerivNormSq 0 (scaleMetric N.scale N.scale_pos g) x ≤ K) →
          ∃ (g' : SmoothRiemannianMetric I3 M) (U : Set M),
            RiemannianMetricComplete g' ∧ IsOpen U ∧
            riemannianClosedBallOf (scaleMetric N.scale N.scale_pos g) N.center R ⊆ U ∧
            (∀ z ∈ U, g'.inner z = (scaleMetric N.scale N.scale_pos g).inner z) ∧
            (∀ z (v : TangentSpace I3 z),
              (scaleMetric N.scale N.scale_pos g).inner z v v ≤ g'.inner z v v) ∧
            (∀ m : ℕ, ∀ z ∈ U, curvDerivNorm m g' z =
              curvDerivNorm m (scaleMetric N.scale N.scale_pos g) z) ∧
            (∀ r : ℝ, 0 ≤ r → r < R →
              riemannianClosedBallOf g' N.center r =
                riemannianClosedBallOf (scaleMetric N.scale N.scale_pos g) N.center r) ∧
            ∀ x ∈ riemannianClosedBallOf g' N.center a,
              Set.InjOn (fun v : TangentSpace I3 x => Geometry.Riemannian.Exponential.expMap g' x v)
                {v | Real.sqrt (g'.inner x v v) < η} := by
  obtain ⟨v,hv,hvolume⟩ := exists_pos_le_normalizedNeck_ball_volume.{u} hρ
  let κ := v / ρ ^ 3
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  obtain ⟨ι,hι,hinj⟩ := local_metric_injectivity (I := I3) hκ
  refine ⟨ι*ρ, mul_pos hι hρ, ?_⟩
  intro M _ _ _ _ _ g δ eps k N hδ heps hk a R ha hfit hR hcompact hcurv
  let gn := scaleMetric N.scale N.scale_pos g
  obtain ⟨g',U,hcomplete,hU,hballU,heq,hle,_,_,hclosed,_⟩ :=
    Geometry.exists_complete_metric_extension_of_riemannianClosedBall gn N.center hcompact
  have hloc (z : M) (hz : z ∈ U) : ∀ᶠ y in 𝓝 z, ∀ v w : TangentSpace I3 y,
      g'.inner y v w = gn.inner y v w := by
    filter_upwards [hU.mem_nhds hz] with y hy
    intro v w
    exact congrArg (fun A => A v w) (heq y hy)
  refine ⟨g',U,hcomplete,hU,hballU,heq,hle,?_,hclosed,?_⟩
  · intro m z hz
    exact curvDerivNorm_eq_of_metric_eventuallyEq g' gn z (hloc z hz) m
  · intro x hx
    have haR : a < R := by linarith
    rw [hclosed a ha.le haR] at hx
    have hvol := hvolume N hδ heps hk ha (by linarith) x hx
    have hvoleq := Geometry.Measure.riemannianVolumeMeasure_ball_eq_of_eqOn_outer_closedBall
      gn g' ha.le hρ.le (by linarith : a+ρ ≤ R) hx
      (fun z hz => heq z (hballU hz)) hle
    have hvol' : ENNReal.ofReal (κ * ρ ^ Module.finrank ℝ ThreeSpace) ≤
        riemannianVolumeMeasure I3 M g' (riemannianBallOf g' x ρ) := by
      rw [hvoleq]
      have he : κ * ρ ^ Module.finrank ℝ ThreeSpace = v := by
        simp only [show Module.finrank ℝ ThreeSpace = 3 by simp [ThreeSpace], κ]
        field_simp
      rwa [he]
    have hcontrol : ∀ y ∈ riemannianBallOf g' x ρ,
        ρ^4 * Tensor0SBundle.normSq0S g' y 4 (metricRm04At g' y) ≤ 1 := by
      intro y hy
      rw [riemannianBallOf_eq_of_eqOn_outer_closedBall gn g' ha.le hρ.le
        (by linarith : a+ρ ≤ R) hx (fun z hz => heq z (hballU hz)) hle] at hy
      have hyR : y ∈ riemannianClosedBallOf gn N.center R :=
        riemannianClosedBallOf_subset_of_add_radius_le gn ha.le hρ.le
          hR hx (show riemannianEDistOf gn x y ≤ ENNReal.ofReal ρ from le_of_lt hy)
      have hnorm := curvDerivNormSq_eq_of_metric_eventuallyEq g' gn y (hloc y (hballU hyR)) 0
      have hh : Tensor0SBundle.normSq0S g' y 4 (metricRm04At g' y) ≤ K := by
        change curvDerivNormSq 0 g' y ≤ K
        rw [hnorm]
        exact hcurv y hyR
      exact (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ ρ^4)).trans hρpow
    exact hinj M g' hcomplete x ρ hρ hcontrol hvol'

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
