import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarBall
import DifferentialGeometry.Geometry.Metric.Scaling
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Scalar
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Bundle.FiberBundleHausdorff

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem terminal_scalar_limit_tendsto_atTop_of_endpoint_blowup
    (P : ℕ → OrientedThreeStage.{u}) (a s : ℕ → ℝ)
    (G : ∀ n, (P n).IncomingSlab (a n) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (Q : ℕ → ℝ) (hQ : ∀ n, 0 < Q n)
    (q : ℕ → ℝ) (qbar : ℝ) (hq : ∀ᶠ n in atTop, q n ≤ qbar * Q n)
    (C : ℝ≥0)
    (hgradient : ∀ n, ∀ x : (P n).Carrier, ∀ t ∈ Ioo (a n) (s n),
      q n < (G n).flow.scalar t x → ∀ v : TangentSpace ThreeModel x,
      |scalarDifferential (G n).flow t x v| ≤ C * (G n).flow.scalar t x *
        Real.sqrt ((G n).flow.scalar t x) * Real.sqrt (((G n).flow.base.metric t).inner x v v))
    (p : ∀ n, (G n).terminalRegularOpen)
    (hp : Tendsto (fun n => metricScalarAt (L n).metric (p n) / Q n) atTop atTop)
    (rho : ℝ) (ell : ℕ → ℝ) (hell : Tendsto ell atTop (𝓝 rho))
    (γ : ∀ n, Ico 0 rho → (G n).terminalRegularOpen)
    (hdist : ∀ t : Ico 0 rho, ∀ᶠ n in atTop,
      riemannianEDistOf (scaleMetric (Q n) (hQ n) (L n).metric) (γ n t) (p n) ≤
        ENNReal.ofReal (ell n - t))
    (f : Ico 0 rho → ℝ)
    (hscalar : ∀ t, Tendsto (fun n => metricScalarAt (L n).metric (γ n t) / Q n)
      atTop (𝓝 (f t))) :
    Tendsto f (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) atTop := by
  apply tendsto_atTop.mpr
  intro B
  let A := max qbar (max B 0) + 1
  have hA : 0 < A := by
    have hb : (0 : ℝ) ≤ max qbar (max B 0) := (le_max_right B 0).trans (le_max_right _ _)
    dsimp only [A]
    linarith
  have hqA : qbar ≤ A := by
    dsimp only [A]
    linarith [le_max_left qbar (max B 0)]
  have hBA : B < A := by
    dsimp only [A]
    linarith [(le_max_left B 0).trans (le_max_right qbar (max B 0))]
  let d := localPropagationRadius C / (2 * Real.sqrt (2 * A))
  have hd : 0 < d := div_pos (localPropagationRadius_pos C.coe_nonneg) (by positivity)
  have hgap : Tendsto (fun t : Ico 0 rho => rho - (t : ℝ))
      (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := rho)).sub
      (tendsto_comap : Tendsto (Subtype.val : Ico 0 rho → ℝ) _ (𝓝 rho))
  filter_upwards [hgap.eventually (Iio_mem_nhds hd)] with t ht
  by_contra hnot
  have hfB : f t < B := lt_of_not_ge hnot
  have hbound : ∀ᶠ n in atTop, metricScalarAt (L n).metric (γ n t) ≤ A * Q n := by
    filter_upwards [(hscalar t).eventually (Iio_mem_nhds (hfB.trans hBA))] with n hn
    exact (div_le_iff₀ (hQ n)).mp hn.le
  have hremain : ∀ᶠ n in atTop, ell n - (t : ℝ) < d :=
    (hell.sub_const (t : ℝ)).eventually (Iio_mem_nhds ht)
  have hhigh := hp.eventually_gt_atTop (6 * A)
  obtain ⟨n, hn, hr, hb, hlarge, hqn⟩ :=
    ((hdist t).and (hremain.and (hbound.and (hhigh.and hq)))).exists
  have hscaled : p n ∈ riemannianClosedBallOf
      (scaleMetric (Q n) (hQ n) (L n).metric) (γ n t) d :=
    hn.trans (ENNReal.ofReal_le_ofReal hr.le)
  have hradius : d = Real.sqrt (Q n) *
      (localPropagationRadius C / (2 * Real.sqrt (2 * (A * Q n)))) := by
    dsimp only [d]
    rw [show 2 * (A * Q n) = (2 * A) * Q n by ring,
      Real.sqrt_mul (by positivity : 0 ≤ 2 * A)]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr (hQ n)), ne_of_gt (Real.sqrt_pos.mpr (by positivity : 0 < 2 * A))]
  rw [hradius, DifferentialGeometry.riemannianClosedBallOf_scaleMetric] at hscaled
  have hlocal := (L n).scalar_le_on_small_ball_of_gradient_bound C (mul_pos hA (hQ n))
    (hqn.trans (mul_le_mul_of_nonneg_right hqA (hQ n).le))
    (hgradient n) (γ n t) hb (p n) hscaled
  have hquot : metricScalarAt (L n).metric (p n) / Q n ≤ 6 * A := by
    apply (div_le_iff₀ (hQ n)).mpr
    nlinarith only [hlocal]
  exact hlarge.not_ge hquot


attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    {G : P.IncomingSlab a s} : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

theorem terminal_pointed_scalar_tendsto_atTop_of_endpoint_blowup
    (P : ℕ → OrientedThreeStage.{u}) (a s : ℕ → ℝ)
    (G : ∀ n, (P n).IncomingSlab (a n) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (Q : ℕ → ℝ) (hQ : ∀ n, 0 < Q n)
    (q : ℕ → ℝ) (qbar : ℝ) (hq : ∀ᶠ n in atTop, q n ≤ qbar * Q n)
    (C : ℝ≥0)
    (hgradient : ∀ n, ∀ x : (P n).Carrier, ∀ t ∈ Ioo (a n) (s n),
      q n < (G n).flow.scalar t x → ∀ v : TangentSpace ThreeModel x,
      |scalarDifferential (G n).flow t x v| ≤ C * (G n).flow.scalar t x *
        Real.sqrt ((G n).flow.scalar t x) * Real.sqrt (((G n).flow.base.metric t).inner x v v))
    (basepoint p : ∀ n, (G n).terminalRegularOpen)
    (hp : Tendsto (fun n => metricScalarAt (L n).metric (p n) / Q n) atTop atTop)
    (rho : ℝ) (ell : ℕ → ℝ) (hell : Tendsto ell atTop (𝓝 rho))
    (γ : ∀ n, Ico 0 rho → (G n).terminalRegularOpen)
    (hdist : ∀ t : Ico 0 rho, ∀ᶠ n in atTop,
      riemannianEDistOf (scaleMetric (Q n) (hQ n) (L n).metric) (γ n t) (p n) ≤
        ENNReal.ofReal (ell n - t))
    (limit : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (maps : PointedRiemannianConvergenceMaps
      ({ obj := fun n =>
          { M := (G n).terminalRegularOpen
            topology := inferInstance
            charted := inferInstance
            smooth := inferInstance
            sigmaCompact := inferInstance
            t2 := inferInstance
            t2TangentBundle := inferInstance
            basepoint := basepoint n
            metric := scaleMetric (Q n) (hQ n) (L n).metric } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) limit id)
    (metricConvergence : MetricConvergenceData maps)
    (hcanonical : ∀ n, metricConvergence.domain n = CanonicalMetricCompactness.canonicalSourceData maps n)
    (curve : Ico 0 rho → limit.M)
    (hstay : ∀ t : Ico 0 rho, ∀ᶠ n in atTop, γ n t ∈ maps.target n)
    (hconv : ∀ t : Ico 0 rho, Tendsto (fun n => (maps.partialDiffeomorph n).symm (γ n t))
      atTop (𝓝 (curve t))) :
    Tendsto (fun t => metricScalarAt limit.metric (curve t))
      (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) atTop := by
  apply terminal_scalar_limit_tendsto_atTop_of_endpoint_blowup P a s G L Q hQ q qbar hq C
    hgradient p hp rho ell hell γ hdist
  intro t
  have ht := pointedScalar_tendsto_of_inverse_tendsto metricConvergence hcanonical
    (fun n => γ n t) (hstay t) (hconv t)
  convert ht using 1
  funext n
  change metricScalarAt (L n).metric (γ n t) / Q n =
    metricScalarAt (scaleMetric (Q n) (hQ n) (L n).metric) (γ n t)
  rw [metricScalarAt_scaleMetric]
  ring


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
