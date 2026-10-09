import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.LocalizedDistanceSmoothing
import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.CalibratedCoray
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness

/-!
# First-order control of localized distance smoothing

A smooth upper support of the distance and the global Lipschitz bound on the
smoothing error give differential control along both signs of a unit geodesic.
No differentiability of the distance at a cut point is required.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Collapse

private theorem derivative_le_of_right_increment {f : ℝ → ℝ} {v a : ℝ}
    (hf : HasDerivAt f v 0)
    (hinc : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t - f 0 ≤ a * t) : v ≤ a := by
  apply le_of_tendsto hf.tendsto_slope_zero_right
  filter_upwards [hinc, self_mem_nhdsWithin] with t ht hpos
  have ht0 : 0 < t := hpos
  simpa only [zero_add, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    (div_le_iff₀ ht0).mpr ht

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

private theorem smoothing_upper_support_derivative_le
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F ρ : M → ℝ} {Y : Set M} {x : M} {ε : ℝ} (hε : 0 ≤ ε)
    (hF : MDifferentiableAt I 𝓘(ℝ, ℝ) F x)
    (hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ x)
    (hval : ρ x = Metric.infDist x Y)
    (hupper : ∀ᶠ y in 𝓝 x, Metric.infDist y Y ≤ ρ y)
    (hdiff : ∀ y z, |(F y - Metric.infDist y Y) -
      (F z - Metric.infDist z Y)| ≤ ε * dist y z)
    (w : TangentSpace I x) (hw : g.inner x w w = 1) :
    mvfderiv (I := I) F x w - mvfderiv (I := I) ρ x w ≤ ε := by
  let γ := intrinsicGeodesic g hEnorm x w
  have hγ0 : γ 0 = x := intrinsicGeodesic_zero g hEnorm x w
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ := intrinsicGeodesic_contMDiff g hEnorm x w
  have hFl := hasDerivAt_comp_mfderiv_along I F γ 0
    (by simpa only [hγ0] using hF) (hγ.contMDiffAt.mdifferentiableAt (by simp))
  have hρl := hasDerivAt_comp_mfderiv_along I ρ γ 0
    (by simpa only [hγ0] using hρ) (hγ.contMDiffAt.mdifferentiableAt (by simp))
  have hspeed : mfderiv 𝓘(ℝ, ℝ) I γ 0 (realTangentOne 0) = w := by
    change mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) = w
    exact intrinsicGeodesic_mfderiv_zero g hEnorm x w
  have hline : HasDerivAt (fun t => F (γ t) - ρ (γ t))
      (mvfderiv (I := I) F x w - mvfderiv (I := I) ρ x w) 0 := by
    change HasDerivAt (fun t => F (γ t))
      (mvfderiv (I := I) F (γ 0)
        (mfderiv 𝓘(ℝ, ℝ) I γ 0 (realTangentOne 0))) 0 at hFl
    change HasDerivAt (fun t => ρ (γ t))
      (mvfderiv (I := I) ρ (γ 0)
        (mfderiv 𝓘(ℝ, ℝ) I γ 0 (realTangentOne 0))) 0 at hρl
    simp only [hspeed] at hFl hρl
    rw [hγ0] at hFl hρl
    exact hFl.sub hρl
  apply derivative_le_of_right_increment hline
  have hupperγ : ∀ᶠ t in 𝓝 (0 : ℝ), Metric.infDist (γ t) Y ≤ ρ (γ t) := by
    have hc : Tendsto γ (𝓝 0) (𝓝 x) := by
      have hc := hγ.continuous.tendsto 0
      rw [hγ0] at hc
      exact hc
    exact hc.eventually hupper
  filter_upwards [nhdsWithin_le_nhds hupperγ, self_mem_nhdsWithin] with t ht hpos
  have ht0 : 0 < t := hpos
  have hdist : dist (γ t) x ≤ t := by
    have hd := (lipschitzWith_one_intrinsicGeodesic g hEnorm x w hw).dist_le_mul t 0
    simpa only [γ, intrinsicGeodesic_zero, NNReal.coe_one, one_mul, Real.dist_eq,
      sub_zero, abs_of_pos ht0] using hd
  have hb := (abs_le.mp (hdiff (γ t) x)).2
  rw [hγ0, hval]
  calc F (γ t) - ρ (γ t) - (F x - Metric.infDist x Y)
      ≤ (F (γ t) - Metric.infDist (γ t) Y) - (F x - Metric.infDist x Y) := by
        linarith
    _ ≤ ε * dist (γ t) x := hb
    _ ≤ ε * t := mul_le_mul_of_nonneg_left hdist hε

theorem exists_minimizingDirection_smoothing_derivative_bound
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} {Y : Set M} {x : M} {ε : ℝ} (hε : 0 ≤ ε)
    (hY : IsClosed Y) (hYne : Y.Nonempty) (hx : 0 < Metric.infDist x Y)
    (hF : MDifferentiableAt I 𝓘(ℝ, ℝ) F x)
    (hdiff : ∀ y z, |(F y - Metric.infDist y Y) -
      (F z - Metric.infDist z Y)| ≤ ε * dist y z) :
    ∃ u ∈ minimizingDirectionsTo g hEnorm Y x,
      ∀ w : TangentSpace I x, g.inner x w w = 1 →
        |mvfderiv (I := I) F x w + g.inner x u w| ≤ ε := by
  obtain ⟨ρ, u, hρ, hval, hupper, hu, hgrad⟩ :=
    infDist_upper_support_of_isClosed g hEnorm hY hYne hx
  have hρd := hρ.mdifferentiableAt (by simp)
  have hder (w : TangentSpace I x) : mvfderiv (I := I) ρ x w = -g.inner x u w := by
    rw [← inner_gradientFun, hgrad, map_neg, neg_apply]
  refine ⟨u, hu, fun w hw => ?_⟩
  have hplus := smoothing_upper_support_derivative_le g hEnorm hε hF hρd
    hval hupper hdiff w hw
  have hminus := smoothing_upper_support_derivative_le g hEnorm hε hF hρd
    hval hupper hdiff (-w) (by simpa using hw)
  rw [hder] at hplus
  rw [hder, map_neg, map_neg] at hminus
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end DifferentialGeometry.Geometry.Collapse
