import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCurvatureEscape
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Curves
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.AmbientQuadraticControl
import DifferentialGeometry.Geometry.Metric.Scaling
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Scalar
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapInitialLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.MinimizingSegment

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

end

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

theorem exists_terminal_ray_cap_offset_exclusion_of_vanishing_age
    (N : ℕ) (D r eps : ℝ)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + 2 * eps⁻¹ + 1) < D)
    (hdepth : 2 * StandardCap.transitionEnd + 4000 < r / 2)
    (hN : ⌈eps⁻¹⌉₊ ≤ N) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ C : ℝ≥0,
      ∃ η ε₀ δ₀ : ℝ, 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ (rho : ℝ), 0 < rho → ∀ R : Ico 0 rho → ℝ,
      Tendsto R (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) atTop →
      ∀ᶠ tau : Ico 0 rho in comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho),
      ∀ (H : ℕ → ObservedHistory.{u}) (event : ∀ i, Fin (H i).eventCount)
        (last : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, (event i).succ ≤ last i)
        (time : ℕ → ℝ)
        (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (time i))
        (L : ∀ i, (G i).TerminalLimitMetric),
      (∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
      ∀ (parameters : ℕ → CutoffParameters)
        (records : ∀ i k, GeometricCutoffRecord (H i) k (parameters i))
        (boundary : ∀ i, ((H i).event (event i)).RetainedBoundaryIndex),
      let cap := fun i => (records i (event i)).static (boundary i)
      let q := fun i => (cap i).neck.scale
      let age := fun i => q i * (time i - (H i).time (event i).succ)
      (∀ i, (cap i).hasCanonicalWindow) →
      (∀ i, D + 1 ≤ (parameters i).modelRadius) →
      (∀ i, max ⌈eps⁻¹⌉₊ N + 2 ≤ (parameters i).modelOrder) →
      (∀ i, (parameters i).modelAccuracy ≤ ε₀) →
      Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0) →
      ∀ (q₀ a₀ : ℕ → ℝ), (∀ i, 0 < q₀ i) →
      (∀ i, q₀ i ≤ C₀ * q i) → (∀ i, 1 ≤ a₀ i * q i) →
      (∀ i x, InFixedHamiltonIveyRegion ((H i).initialMetric 0) (a₀ i) x) →
      (∀ i x, -3 / a₀ i ≤ metricScalarAt ((H i).initialMetric 0) x) →
      (∀ i k, (event i).succ ≤ k.castSucc → k.succ ≤ last i →
        ∀ b, (records i k).delta b ≤ δ₀) →
      (∀ i k, (event i).succ ≤ k.castSucc → k.succ ≤ last i →
        ∀ x : ((H i).stage k.castSucc).Carrier,
        ∀ t ∈ Ioo ((H i).time k.castSucc) ((H i).time k.succ),
          q₀ i < ((H i).event k).incoming.flow.scalar t x →
          |derivWithin (fun v => ((H i).event k).incoming.flow.scalar v x) (Iic t) t| ≤
            C * ((H i).event k).incoming.flow.scalar t x ^ 2) →
      (∀ i x, ∀ t ∈ Ioo ((H i).time (last i)) (time i), q₀ i < (G i).flow.scalar t x →
        |derivWithin (fun v => (G i).flow.scalar v x) (Iic t) t| ≤ C * (G i).flow.scalar t x ^ 2) →
      (∀ i, age i ≤ η) → Tendsto age atTop (𝓝 0) →
      ∀ (z : ℕ → ThreeBall) (y : ∀ i, (G i).terminalRegularOpen)
        (trace : ∀ i, BackwardPointTrace (H i) (event i).succ (last i) (hle i) (y i).val),
      (∀ i, (trace i).point (event i).succ le_rfl (hle i) =
        (cap i).inclusion ((cap i).witness.cap (z i))) →
      ∀ (Q radius : ℕ → ℝ) (hQ : ∀ i, 0 < Q i),
      ∀ (x : ∀ i, (G i).terminalRegularOpen),
      (∀ᶠ i in atTop, 0 < radius i ∧ q i < 4 * (16 / radius i ^ 2) ∧
        y i ∈ riemannianClosedBallOf (L i).metric (x i) (radius i / 2)) →
      ∀ (γ : ∀ i, ℝ → (G i).terminalRegularOpen) (ell : ℕ → ℝ),
      Tendsto ell atTop (𝓝 rho) →
      (∀ᶠ i in atTop, ∀ a ∈ Icc 0 (ell i), ∀ b ∈ Icc 0 (ell i),
        riemannianEDistOf (scaleMetric (Q i) (hQ i) (L i).metric)
          (γ i a) (γ i b) = ENNReal.ofReal |a - b|) →
      (∀ᶠ i in atTop, γ i tau = x i) →
      Tendsto (fun i => metricScalarAt (L i).metric (x i) / Q i) atTop (𝓝 (R tau)) →
      Tendsto (fun i => metricScalarAt (L i).metric (γ i (ell i)) / Q i) atTop atTop → False := by
  let r₁ := r + eps⁻¹ + 1
  have hepssmall' : eps < 1 / 11 := by linarith
  have hr₁ : StandardCap.transitionEnd + eps⁻¹ + 1 < r₁ := by
    dsimp [r₁]
    linarith [inv_pos.mpr heps]
  have hfit₁ : 64 * (r₁ + eps⁻¹) < D := by dsimp [r₁]; linarith
  have hfit' : r + eps⁻¹ + 1 ≤ D := by
    have hrpos : 0 < r := by linarith [StandardCap.transitionEnd_pos, inv_pos.mpr heps]
    linarith [inv_pos.mpr heps]
  obtain ⟨C₀, B, Cderiv, hC₀, _, _, hproducer⟩ :=
    exists_uniform_canonical_cap_window_convergence_and_uniform_scalar_derivative_bounds_at_vanishing_age
      N D r₁ eps heps hepssmall hr₁ hfit₁
  refine ⟨C₀, hC₀, fun C => ?_⟩
  obtain ⟨η, ε₀, δ₀, hη, hε₀, hεhalf, hδ₀, hmake⟩ := hproducer C
  refine ⟨η, ε₀, δ₀, hη, hε₀, hεhalf, hδ₀, ?_⟩
  intro rho hrho R hR
  filter_upwards [StandardCap.eventually_minimizing_segment_near_cap_core_exclusion_of_scalar_blowup
    D r eps heps hepssmall' hr hfit' hdepth rho hrho R hR] with tau hbad
  intro H event last hle time G L hinit parameters records boundary cap q age
    hcanonical hmargin hm herror herrorlim q₀ a₀ hq₀ hqcap hacap hfixed hlower hδ hderiv hfinal
    hage hagelim z y trace hbirth Q radius hQ x hnear γ ell hell hmin hpoint hmark hend
  obtain ⟨x₀, delta, order, datum, w, hwscalar, hwmetric, u, Ξ, hΞ, gflow, hmargin', hpos, S,
    hu, hucap, hΞsmooth, hΞbirth, hΞpoint, hslabs, hlast, hS, hgram, hjets, hbounds, hzero,
    hmetric, hterminal, hconvergence, hmarked, hcaps⟩ :=
    hmake H event last hle time G L hinit parameters records boundary hcanonical hmargin hm
      herror herrorlim q₀ a₀ hq₀ hqcap hacap hfixed hlower hδ hderiv hfinal hage hagelim z y trace hbirth
  let g := fun i => (S i).base.metric (age i)
  let h := fun i => scaleMetric (Q i) (hQ i) (L i).metric
  let qnorm := fun i => q i / Q i
  have hqnorm (i) : 0 < qnorm i := div_pos (cap i).neck.scale_pos (hQ i)
  let Φ := fun i => (H i).backwardSurvivorIncomingMap (event i).succ (last i) (hle i) (G i) ∘ Ξ i
  have hΦ (i) : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (Φ i) :=
    isLocalDiffeomorph_comp ((H i).backwardSurvivorIncomingMap_isLocalDiffeomorph
      (event i).succ (last i) (hle i) (G i)) (hΞ i)
  have hinj (i) : Function.Injective (Φ i) :=
    ((H i).backwardSurvivorIncomingMap_injective (event i).succ (last i) (hle i) (G i)).comp
      (hΞsmooth i).isEmbedding.injective
  have hmetric' (i) (z : standardCapWindow D) (v w : TangentSpace ThreeModel z) :
      (g i).inner z v w = qnorm i * (h i).inner (Φ i z)
        (mfderiv ThreeModel ThreeModel (Φ i) z v) (mfderiv ThreeModel ThreeModel (Φ i) z w) := by
    rw [show (g i).inner z v w = _ from hterminal i z v w]
    change q i * (L i).metric.inner (Φ i z)
        (mfderiv ThreeModel ThreeModel (Φ i) z v) (mfderiv ThreeModel ThreeModel (Φ i) z w) =
      (q i / Q i) * (Q i * (L i).metric.inner (Φ i z)
        (mfderiv ThreeModel ThreeModel (Φ i) z v) (mfderiv ThreeModel ThreeModel (Φ i) z w))
    rw [← mul_assoc, div_mul_cancel₀ _ (hQ i).ne']
  have hscaled (i) : scaleMetric (qnorm i) (hqnorm i) (h i) =
      scaleMetric (q i) (cap i).neck.scale_pos (L i).metric := by
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    simp only [scaleMetric_inner, h, qnorm]
    rw [← mul_assoc, div_mul_cancel₀ _ (hQ i).ne']
  have hnear' : ∀ᶠ i in atTop, riemannianEDistOf (scaleMetric (qnorm i) (hqnorm i) (h i))
      (x i) (Φ i (u i)) ≤ ENNReal.ofReal 4 := by
    filter_upwards [hnear] with i hi
    rw [hscaled i, show Φ i (u i) = y i from hΞpoint i]
    have hqr : (cap i).neck.scale * (radius i) ^ 2 < 64 := by
      have hqdiv : (cap i).neck.scale < 64 / (radius i) ^ 2 := by
        convert hi.2.1 using 1
        ring
      exact (lt_div_iff₀ (sq_pos_of_pos hi.1)).mp hqdiv
    have hroot : Real.sqrt ((cap i).neck.scale) * (radius i / 2) < 4 := by
      have hs : (Real.sqrt ((cap i).neck.scale) * radius i) ^ 2 < 8 ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (le_of_lt (cap i).neck.scale_pos)]
        norm_num only [Nat.reducePow]
        exact hqr
      have hn := mul_nonneg (Real.sqrt_nonneg ((cap i).neck.scale)) hi.1.le
      nlinarith
    rw [edistOf_scale]
    apply le_of_lt
    change ENNReal.ofReal (Real.sqrt ((cap i).neck.scale)) *
      riemannianEDistOf (L i).metric (x i) (y i) < ENNReal.ofReal 4
    calc
      _ ≤ ENNReal.ofReal (Real.sqrt ((cap i).neck.scale)) *
          ENNReal.ofReal (radius i / 2) := mul_le_mul' le_rfl hi.2.2
      _ = ENNReal.ofReal (Real.sqrt ((cap i).neck.scale) * (radius i / 2)) :=
        (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm
      _ < ENNReal.ofReal 4 :=
        (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 4)).mpr hroot
  have hscalar (i) (z : (G i).terminalRegularOpen) :
      metricScalarAt (h i) z = metricScalarAt (L i).metric z / Q i := by
    dsimp [h]
    rw [metricScalarAt_scaleMetric, inv_mul_eq_div]
  exact hbad N hN g (hconvergence (r + eps⁻¹) (by dsimp [r₁]; linarith))
    (fun i => (G i).terminalRegularOpen) h qnorm hqnorm Φ hΦ hinj hmetric' u
    (Eventually.of_forall hu) x hnear' γ ell hell hmin hpoint
    (by simpa only [hscalar] using hmark) (by simpa only [hscalar] using hend)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    {G : P.IncomingSlab a s} : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

theorem exists_isometric_terminal_scalar_blowup_curve_of_minimizing_segments
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
    (basepoint : ∀ n, (G n).terminalRegularOpen)
    (limit : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (maps : PointedRiemannianConvergenceMaps
      ({ obj := fun n =>
          { M := (G n).terminalRegularOpen
            basepoint := basepoint n
            metric := scaleMetric (Q n) (hQ n) (L n).metric } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) limit σ)
    (Mconv : MetricConvergenceData maps)
    (hcanonical : ∀ n, Mconv.domain n = CanonicalMetricCompactness.canonicalSourceData maps n)
    {rho : ℝ} (hrho : 0 < rho)
    (r ell : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hell : ∀ n, 0 ≤ ell n)
    (hrconv : Tendsto r atTop (𝓝 rho)) (hellconv : Tendsto ell atTop (𝓝 rho))
    (htarget : ∀ n, riemannianBallOf (scaleMetric (Q (σ n)) (hQ (σ n)) (L (σ n)).metric)
      (basepoint (σ n)) (r n) ⊆ maps.target n)
    (hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ x ∈ maps.source n, ∀ v : TangentSpace ThreeModel x,
        (1 - ε) * limit.metric.inner x v v ≤
          (scaleMetric (Q (σ n)) (hQ (σ n)) (L (σ n)).metric).inner (maps.partialDiffeomorph n x)
            (mfderiv ThreeModel ThreeModel (maps.partialDiffeomorph n) x v)
            (mfderiv ThreeModel ThreeModel (maps.partialDiffeomorph n) x v))
    (hcompact : ∀ R : ℝ, 0 ≤ R → R < rho →
      IsCompact (riemannianClosedBallOf limit.metric limit.basepoint R))
    (hradial : ∀ x : limit.M, riemannianEDistOf limit.metric limit.basepoint x < ENNReal.ofReal rho)
    (γ : ∀ n, ℝ → (G (σ n)).terminalRegularOpen)
    (hγ : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (γ n) (Icc 0 (ell n)))
    (hstart : ∀ n, γ n 0 = basepoint (σ n))
    (hmin : ∀ n, ∀ t ∈ Icc 0 (ell n), ∀ u ∈ Icc 0 (ell n),
      riemannianEDistOf (scaleMetric (Q (σ n)) (hQ (σ n)) (L (σ n)).metric)
        (γ n t) (γ n u) = ENNReal.ofReal |t - u|)
    (hhigh : Tendsto (fun n => metricScalarAt (L (σ n)).metric (γ n (ell n)) / Q (σ n)) atTop atTop) :
    let _ : EMetricSpace limit.M := limit.emetricSpace
    ∃ (φ : ℕ → ℕ) (g : C(Ico 0 rho, limit.M)), StrictMono φ ∧ Isometry g ∧
      g ⟨0, le_rfl, hrho⟩ = limit.basepoint ∧
      (∀ K : Set (Ico 0 rho), IsCompact K →
        TendstoUniformlyOn (fun n (t : Ico 0 rho) =>
          (maps.partialDiffeomorph (φ n)).symm (γ (φ n) t)) g atTop K) ∧
      (∀ t : Ico 0 rho, ∀ᶠ n in atTop, γ (φ n) t ∈ maps.target (φ n)) ∧
      (∀ t : Ico 0 rho, Tendsto (fun n => metricScalarAt (L (σ (φ n))).metric
        (γ (φ n) t) / Q (σ (φ n))) atTop (𝓝 (metricScalarAt limit.metric (g t)))) ∧
      Tendsto g (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) (cocompact limit.M) ∧
      (∀ x : limit.M, ¬ Tendsto g (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) (𝓝 x)) ∧
      Tendsto (fun t => metricScalarAt limit.metric (g t))
        (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) atTop := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hupper : ∀ K : Set limit.M, IsCompact K → ∀ D : ℝ, 1 < D → ∀ᶠ n in atTop,
      ∀ x ∈ K, ∀ v : TangentSpace ThreeModel x,
        (scaleMetric (Q (σ n)) (hQ (σ n)) (L (σ n)).metric).inner (maps.partialDiffeomorph n x)
          (mfderiv ThreeModel ThreeModel (maps.partialDiffeomorph n) x v)
          (mfderiv ThreeModel ThreeModel (maps.partialDiffeomorph n) x v) ≤
            D ^ 2 * limit.metric.inner x v v := by
    intro K hK D hD
    obtain ⟨N, hN⟩ := Perelman.KappaSolutions.exists_pointed_full_ambient_quadratic_control
      Mconv (fun n => by rw [hcanonical n]; rfl) K hK (D ^ 2 - 1) (by nlinarith)
    filter_upwards [eventually_ge_atTop N] with n hn
    intro x hx v
    have hh := (abs_le.mp ((hN n hn).2 x hx v)).2
    change (scaleMetric (Q (σ n)) (hQ (σ n)) (L (σ n)).metric).inner (maps.partialDiffeomorph n x)
      (mfderiv ThreeModel ThreeModel (maps.partialDiffeomorph n) x v)
      (mfderiv ThreeModel ThreeModel (maps.partialDiffeomorph n) x v) - limit.metric.inner x v v ≤
        (D ^ 2 - 1) * limit.metric.inner x v v at hh
    nlinarith
  let _ : EMetricSpace limit.M := limit.emetricSpace
  obtain ⟨φ, g, hφ, hg, hbase, hconv, hescape, hmissing⟩ :=
    maps.exists_isometric_segment_subseq_limit_with_missing_endpoint hrho r ell hr hell hrconv hellconv
      htarget hlower hupper hcompact hradial γ hγ hstart hmin
  have hstay (t : Ico 0 rho) : ∀ᶠ n in atTop, γ (φ n) t ∈ maps.target (φ n) := by
    filter_upwards [hφ.tendsto_atTop (hrconv.eventually_const_lt t.property.2),
      hφ.tendsto_atTop (hellconv.eventually_const_lt t.property.2)] with n hn hn'
    apply htarget (φ n)
    change riemannianEDistOf (scaleMetric (Q (σ (φ n))) (hQ (σ (φ n))) (L (σ (φ n))).metric)
      (basepoint (σ (φ n))) (γ (φ n) t) < ENNReal.ofReal (r (φ n))
    have hd := hmin (φ n) 0 ⟨le_rfl, t.property.1.trans hn'.le⟩ t ⟨t.property.1, hn'.le⟩
    rw [hstart] at hd
    simp only [zero_sub, abs_neg, abs_of_nonneg t.property.1] at hd
    rw [hd]
    exact (ENNReal.ofReal_lt_ofReal_iff (hr (φ n))).mpr hn
  let maps' := maps.compSubseq φ hφ
  have hcanonical' (n : ℕ) : (Mconv.compSubseq φ hφ).domain n =
      CanonicalMetricCompactness.canonicalSourceData maps' n := by
    change (Mconv.domain (φ n)).compSubseq φ hφ n = _
    rw [hcanonical (φ n)]
    rfl
  have hlimit (t : Ico 0 rho) : Tendsto (fun n => metricScalarAt (L (σ (φ n))).metric
      (γ (φ n) t) / Q (σ (φ n))) atTop (𝓝 (metricScalarAt limit.metric (g t))) := by
    have ht := pointedScalar_tendsto_of_inverse_tendsto (Mconv.compSubseq φ hφ) hcanonical'
      (fun n => γ (φ n) t) (hstay t)
      ((hconv {t} isCompact_singleton).tendsto_at (mem_singleton t))
    convert ht using 1
    funext n
    change metricScalarAt (L (σ (φ n))).metric (γ (φ n) t) / Q (σ (φ n)) =
      metricScalarAt (scaleMetric (Q (σ (φ n))) (hQ (σ (φ n))) (L (σ (φ n))).metric) (γ (φ n) t)
    rw [metricScalarAt_scaleMetric]
    ring
  have hdist (t : Ico 0 rho) : ∀ᶠ n in atTop,
      riemannianEDistOf (scaleMetric (Q (σ (φ n))) (hQ (σ (φ n))) (L (σ (φ n))).metric)
        (γ (φ n) t) (γ (φ n) (ell (φ n))) ≤ ENNReal.ofReal (ell (φ n) - t) := by
    filter_upwards [hφ.tendsto_atTop (hellconv.eventually_const_lt t.property.2)] with n hn
    change (t : ℝ) < ell (φ n) at hn
    have hd := hmin (φ n) t ⟨t.property.1, hn.le⟩ (ell (φ n)) ⟨hell (φ n), le_rfl⟩
    simpa only [abs_of_nonpos (sub_nonpos.mpr hn.le), neg_sub] using hd.le
  refine ⟨φ, g, hφ, hg, hbase, hconv, hstay, hlimit, hescape, hmissing, ?_⟩
  exact terminal_scalar_limit_tendsto_atTop_of_endpoint_blowup
    (fun n => P (σ (φ n))) (fun n => a (σ (φ n))) (fun n => s (σ (φ n)))
    (fun n => G (σ (φ n))) (fun n => L (σ (φ n)))
    (fun n => Q (σ (φ n))) (fun n => hQ (σ (φ n)))
    (fun n => q (σ (φ n))) qbar ((hσ.comp hφ).tendsto_atTop.eventually hq) C
    (fun n => hgradient (σ (φ n))) (fun n => γ (φ n) (ell (φ n)))
    (hhigh.comp hφ.tendsto_atTop) rho (ell ∘ φ) (hellconv.comp hφ.tendsto_atTop)
    (fun n t => γ (φ n) t) hdist (fun t => metricScalarAt limit.metric (g t)) hlimit

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    {G : P.IncomingSlab a s} : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

theorem exists_isometric_terminal_scalar_blowup_curve_of_scalar_escape
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
    (basepoint : ∀ n, (G n).terminalRegularOpen)
    (limit : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (maps : PointedRiemannianConvergenceMaps
      ({ obj := fun n =>
          { M := (G n).terminalRegularOpen
            basepoint := basepoint n
            metric := scaleMetric (Q n) (hQ n) (L n).metric } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) limit σ)
    (Mconv : MetricConvergenceData maps)
    (hcanonical : ∀ n, Mconv.domain n = CanonicalMetricCompactness.canonicalSourceData maps n)
    {rho : ℝ} (hrho : 0 < rho)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrconv : Tendsto r atTop (𝓝 rho))
    (htarget : ∀ n, riemannianBallOf (scaleMetric (Q (σ n)) (hQ (σ n)) (L (σ n)).metric)
      (basepoint (σ n)) (r n) ⊆ maps.target n)
    (hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ x ∈ maps.source n, ∀ v : TangentSpace ThreeModel x,
        (1 - ε) * limit.metric.inner x v v ≤
          (scaleMetric (Q (σ n)) (hQ (σ n)) (L (σ n)).metric).inner (maps.partialDiffeomorph n x)
            (mfderiv ThreeModel ThreeModel (maps.partialDiffeomorph n) x v)
            (mfderiv ThreeModel ThreeModel (maps.partialDiffeomorph n) x v))
    (hcompact : ∀ R : ℝ, 0 ≤ R → R < rho →
      IsCompact (riemannianClosedBallOf limit.metric limit.basepoint R))
    (hradial : ∀ x : limit.M, riemannianEDistOf limit.metric limit.basepoint x < ENNReal.ofReal rho)
    (D : ℕ → ℝ≥0)
    (htime : ∀ n, ∀ x : (P n).Carrier, ∀ t ∈ Ioo (a n) (s n), Q n < (G n).flow.scalar t x →
      |derivWithin (fun v => (G n).flow.scalar v x) (Iic t) t| ≤ D n * (G n).flow.scalar t x ^ 2)
    (hbaseScalar : ∀ n, metricScalarAt (L n).metric (basepoint n) ≤ Q n)
    (z : ∀ n, (G (σ n)).terminalRegularOpen)
    (hfinite : ∀ n, riemannianEDistOf (scaleMetric (Q (σ n)) (hQ (σ n)) (L (σ n)).metric)
      (basepoint (σ n)) (z n) ≠ ⊤)
    (hdist : Tendsto (fun n => (riemannianEDistOf
      (scaleMetric (Q (σ n)) (hQ (σ n)) (L (σ n)).metric) (basepoint (σ n)) (z n)).toReal)
      atTop (𝓝 rho))
    (hhigh : Tendsto (fun n => metricScalarAt (L (σ n)).metric (z n) / Q (σ n)) atTop atTop)
    (hinner : ∀ R : ℝ, 0 < R → R < rho → ∃ B : ℝ,
      ∀ᶠ n in atTop, ∀ y : (G (σ n)).terminalRegularOpen,
        riemannianEDistOf (scaleMetric (Q (σ n)) (hQ (σ n)) (L (σ n)).metric)
          (basepoint (σ n)) y < ENNReal.ofReal R →
            metricScalarAt (L (σ n)).metric y / Q (σ n) ≤ B) :
    let _ : EMetricSpace limit.M := limit.emetricSpace
    ∃ κ : ℕ → ℕ, StrictMono κ ∧
      ∃ (A ell : ℕ → ℝ) (y : ∀ n, (G (σ (κ n))).terminalRegularOpen)
        (γ : ∀ n, ℝ → (G (σ (κ n))).terminalRegularOpen),
        (∀ n, A n = min ((n : ℝ) + 2) (metricScalarAt (L (σ (κ n))).metric (z (κ n)) / Q (σ (κ n)))) ∧
        Tendsto A atTop atTop ∧ Tendsto ell atTop (𝓝 rho) ∧
        (∀ n, 0 < ell n) ∧
        (∀ n, metricScalarAt (L (σ (κ n))).metric (y n) / Q (σ (κ n)) = A n) ∧
        (∀ n, riemannianEDistOf (scaleMetric (Q (σ (κ n))) (hQ (σ (κ n))) (L (σ (κ n))).metric)
          (basepoint (σ (κ n))) (y n) = ENNReal.ofReal (ell n)) ∧
        (∀ n, ENNReal.ofReal (ell n) ≤ riemannianEDistOf
          (scaleMetric (Q (σ (κ n))) (hQ (σ (κ n))) (L (σ (κ n))).metric)
          (basepoint (σ (κ n))) (z (κ n))) ∧
        (∀ n, γ n 0 = basepoint (σ (κ n)) ∧ γ n (ell n) = y n) ∧
        (∀ n, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel ∞ (γ n) (Icc 0 (ell n))) ∧
        (∀ n, ∀ t ∈ Ico 0 (ell n), metricScalarAt (L (σ (κ n))).metric (γ n t) / Q (σ (κ n)) < A n) ∧
        (∀ n, ∀ t ∈ Icc 0 (ell n), metricScalarAt (L (σ (κ n))).metric (γ n t) / Q (σ (κ n)) ≤ A n) ∧
        (∀ n, ∀ t ∈ Icc 0 (ell n), ∀ u ∈ Icc 0 (ell n),
          riemannianEDistOf (scaleMetric (Q (σ (κ n))) (hQ (σ (κ n))) (L (σ (κ n))).metric)
            (γ n t) (γ n u) = ENNReal.ofReal |t - u|) ∧
        ∃ (φ : ℕ → ℕ) (g : C(Ico 0 rho, limit.M)), StrictMono φ ∧ Isometry g ∧
          g ⟨0, le_rfl, hrho⟩ = limit.basepoint ∧
          (∀ K : Set (Ico 0 rho), IsCompact K →
            TendstoUniformlyOn (fun n (t : Ico 0 rho) =>
              (maps.partialDiffeomorph (κ (φ n))).symm (γ (φ n) t)) g atTop K) ∧
          (∀ t : Ico 0 rho, ∀ᶠ n in atTop, γ (φ n) t ∈ maps.target (κ (φ n))) ∧
          (∀ t : Ico 0 rho, Tendsto (fun n => metricScalarAt (L (σ (κ (φ n)))).metric
            (γ (φ n) t) / Q (σ (κ (φ n)))) atTop (𝓝 (metricScalarAt limit.metric (g t)))) ∧
          Tendsto g (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) (cocompact limit.M) ∧
          (∀ x : limit.M, ¬ Tendsto g (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) (𝓝 x)) ∧
          Tendsto (fun t => metricScalarAt limit.metric (g t))
            (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) atTop := by
  obtain ⟨κ, hκ, A, ell, y, γ, hA, hAlim, helllim, hell, hy, hlength, hshort,
      hends, hγ, hbelow, hbound, hmin⟩ :=
    exists_terminal_minimizing_segments_at_scalar_escape_radius
      (fun n => P (σ n)) (fun n => a (σ n)) (fun n => s (σ n))
      (fun n => G (σ n)) (fun n => L (σ n)) (fun n => basepoint (σ n)) z
      (fun n => Q (σ n)) (fun n => hQ (σ n)) (fun n => D (σ n))
      (fun n => htime (σ n)) (fun n => hbaseScalar (σ n)) hfinite hrho hdist hhigh hinner
  let maps' := maps.compSubseq κ hκ
  have hcanonical' (n : ℕ) : (Mconv.compSubseq κ hκ).domain n =
      CanonicalMetricCompactness.canonicalSourceData maps' n := by
    change (Mconv.domain (κ n)).compSubseq κ hκ n = _
    rw [hcanonical (κ n)]
    rfl
  have hhigh' : Tendsto (fun n => metricScalarAt (L (σ (κ n))).metric (γ n (ell n)) / Q (σ (κ n)))
      atTop atTop := by
    simpa only [(hends _).2, hy] using hAlim
  let _ : EMetricSpace limit.M := limit.emetricSpace
  obtain ⟨φ, g, hφ, hg, hbase, hconv, hstay, hscalar, hescape, hmissing, hblowup⟩ :=
    exists_isometric_terminal_scalar_blowup_curve_of_minimizing_segments
      P a s G L Q hQ q qbar hq C hgradient basepoint limit (σ ∘ κ) (hσ.comp hκ)
      maps' (Mconv.compSubseq κ hκ) hcanonical' hrho (r ∘ κ) ell
      (fun n => hr (κ n)) (fun n => (hell n).le) (hrconv.comp hκ.tendsto_atTop) helllim
      (fun n => htarget (κ n))
      (fun ε hε => hκ.tendsto_atTop.eventually (hlower ε hε)) hcompact hradial
      γ (fun n => (hγ n).of_le (by simp)) (fun n => (hends n).1) hmin hhigh'
  exact ⟨κ, hκ, A, ell, y, γ, hA, hAlim, helllim, hell, hy, hlength, hshort,
    hends, hγ, hbelow, hbound, hmin, φ, g, hφ, hg, hbase, hconv, hstay, hscalar,
    hescape, hmissing, hblowup⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
