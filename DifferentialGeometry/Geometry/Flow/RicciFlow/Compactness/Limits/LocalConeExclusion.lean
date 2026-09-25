import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.PointedLocalFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.ConeExclusion
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Nonnegative

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

open Geometry.Curvature CheegerGromovCompactness
open Perelman Perelman.CanonicalNeighborhood.FiniteHorn
open Surgery.Topology

universe u


attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance pointedLimitRegular (P : PointedRiemannianManifold.{u, 0, 0} I3) :
    RegularSpace P.M := by
  let _ : LocallyCompactSpace P.M := ChartedSpace.locallyCompactSpace ThreeSpace P.M
  infer_instance

theorem pointed_local_flow_rescaled_cone_exclusion
    {X : PointedRiemannianSeq.{u, 0, 0} I3} {P : PointedRiemannianManifold.{u, 0, 0} I3}
    {f : ℕ → ℕ} (F : PointedRiemannianConvergenceMaps X P f) (C : MetricConvergenceData F)
    (hcanonical : ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (V : TopologicalSpace.Opens P.M) (hsource : ∀ n, (V : Set P.M) ⊆ (F.partialDiffeomorph n).source)
    {D : RealTimeInterval} (S : ℕ → SolutionOn (I := I3) (M := V) D)
    (hS : ∀ n, IsSolutionOn (S n))
    {tau : ℝ} (htau : 0 < tau) (hslab : Icc (-tau) 0 ⊆ D.carrier)
    (hreg : Ico (-tau) 0 ⊆ D.regular)
    (hterminal : ∀ n (x : V) (v w : TangentSpace I3 x),
      ((S n).base.metric 0).inner x v w = (X.obj (f n)).metric.inner (F.partialDiffeomorph n x)
        (mfderiv I3 I3 (F.partialDiffeomorph n) x v) (mfderiv I3 I3 (F.partialDiffeomorph n) x w))
    (hcurv : ∀ K : Set V, IsCompact K → ∀ m : ℕ,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop, ∀ t ∈ Icc (-tau) 0, ∀ x ∈ K,
        curvDerivNorm m ((S n).base.metric t) x ≤ B)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (Q : ℕ → ℝ) (hQpos : ∀ n, 0 < Q n) (hQ : Tendsto Q atTop atTop)
    (hpinching : ∀ t ∈ Icc (-tau) 0, ∀ᶠ n in atTop, ∀ x : V,
      curvatureOperatorLowerBoundAt ((S n).base.metric t) x
        (metricAlgebraicCurvatureTensorAt ((S n).base.metric t) x)
        (rescalePinchingFunction (Q n) Phi (metricScalarAt ((S n).base.metric t) x)))
    (hV : PathConnectedSpace V) :
    let _ : PathConnectedSpace V := hV
    let _ : PseudoMetricSpace V := (P.metric.restrictOpen V).toPseudoMetricSpace
    let _ : MetricSpace V := MetricSpace.ofT0PseudoMetricSpace V
    ∀ (p : V), metricScalarAt (P.metric.restrictOpen V) p ≠ 0 →
      ∀ {W : Type*} [MetricSpace W] {q : UniformSpace.Completion W} {d : ℝ},
      DifferentialGeometry.Toponogov.PuncturedConeApproximation q d →
      ∀ (x : ℕ → W) (maps : ℕ → V → W) (rho : ℕ → ℝ),
      (∀ n, 0 < rho n) → Tendsto rho atTop (𝓝 0) →
      (∀ n, maps n p = x n) →
      ∀ {R lower B : ℝ}, 0 < R → 0 < lower →
    IsCompact (Metric.closedBall p R) →
    (∀ᶠ n in atTop, dist (x n : UniformSpace.Completion W) q / rho n ∈ Icc lower B) →
    (∀ᶠ n in atTop, Metric.closedBall (x n) (R / 4 * rho n) ⊆ maps n '' Metric.closedBall p R) →
    (∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop,
      ∀ z ∈ Metric.closedBall p R, ∀ y ∈ Metric.closedBall p R,
        |dist (maps n z) (maps n y) / rho n - dist z y| < eps) → False := by
  let _ : PathConnectedSpace V := hV
  dsimp only
  let _ : PseudoMetricSpace V := (P.metric.restrictOpen V).toPseudoMetricSpace
  let _ : MetricSpace V := MetricSpace.ofT0PseudoMetricSpace V
  intro p hscalar W instW q d cone x maps rho hrho hrho0 hbase R lower B hR hlower
    hcompact hcenter hcover hdist
  let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I3 V.isOpen)
  obtain ⟨_, _, g, hzero, hsol, hnonneg, _⟩ :=
    exists_nonnegative_solution_subsequence_of_pointed_terminal_pullback F C hcanonical V hsource
      S hS (by linarith : -tau < 0) hslab hreg hterminal hcurv hPhi Q hQpos hQ hpinching
  let T : SolutionOn (I := I3) (M := V) (RealTimeInterval.closed (-tau) 0 (by linarith)) := {base.metric := g}
  have hsec : ∀ t ∈ Icc (-tau) 0, SecLower (T.base.metric t) 0 univ := by
    intro t ht z _ v w
    have h := (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional
      (g t) z (by simp [ThreeSpace])).mp (hnonneg t ht z) v w
    have hslots : (fun i => ![v, w, w, v] i) = vec4 (I := I3) v w w v := by
      funext i
      fin_cases i <;> rfl
    simpa only [T, zero_mul, metricRm04StandardAt_apply, hslots] using h
  have hmetric0 (z y : V) : edist z y = riemannianEDistOf (g 0) z y := by
    rw [hzero]
    rfl
  have hscalar0 : metricScalarAt (g 0) p ≠ 0 := by rw [hzero]; exact hscalar
  apply solution_not_rescaled_cone_limit (M := V) htau
    ({base.metric := g} : SolutionOn (I := I3) (M := V)
      (RealTimeInterval.closed (-tau) 0 (by linarith)))
    hsol hmetric0 hsec p hscalar0 cone x maps rho hrho hrho0 hbase hR hlower
    hcompact hcenter hcover hdist

theorem pointed_local_flow_on_rescaled_end_exclusion
    {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]
    [SigmaCompactSpace W]
    (gW : SmoothRiemannianMetric I3 W)
    (hWmetric : ∀ a b : W, edist a b = riemannianEDistOf gW a b)
    (x : ℕ → W) (A : ℕ → ℝ) (hA : ∀ n, 0 < A n) :
    let X : PointedRiemannianSeq.{u, 0, 0} I3 :=
      { obj := fun n => { M := W, basepoint := x n, metric := scaleMetric (A n) (hA n) gW } }
    ∀ (P : PointedRiemannianManifold.{u, 0, 0} I3) (f : ℕ → ℕ)
      (F : PointedRiemannianConvergenceMaps X P f) (C : MetricConvergenceData F),
      (∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F n) →
      ∀ (V : TopologicalSpace.Opens P.M) (hp : P.basepoint ∈ V),
      (∀ n, (V : Set P.M) ⊆ (F.partialDiffeomorph n).source) →
      ∀ (D : RealTimeInterval) (S : ℕ → SolutionOn (I := I3) (M := V) D),
      (∀ n, IsSolutionOn (S n)) → ∀ tau : ℝ, 0 < tau →
      Icc (-tau) 0 ⊆ D.carrier → Ico (-tau) 0 ⊆ D.regular →
      (∀ n (z : V) (v w : TangentSpace I3 z),
        ((S n).base.metric 0).inner z v w =
          (scaleMetric (A (f n)) (hA (f n)) gW).inner (F.partialDiffeomorph n z)
            (mfderiv I3 I3 (F.partialDiffeomorph n) z v)
            (mfderiv I3 I3 (F.partialDiffeomorph n) z w)) →
      (∀ K : Set V, IsCompact K → ∀ m : ℕ,
        ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop, ∀ t ∈ Icc (-tau) 0, ∀ z ∈ K,
          curvDerivNorm m ((S n).base.metric t) z ≤ B) →
      ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
      ∀ Q : ℕ → ℝ, (∀ n, 0 < Q n) → Tendsto Q atTop atTop →
      (∀ t ∈ Icc (-tau) 0, ∀ᶠ n in atTop, ∀ z : V,
        curvatureOperatorLowerBoundAt ((S n).base.metric t) z
          (metricAlgebraicCurvatureTensorAt ((S n).base.metric t) z)
          (rescalePinchingFunction (Q n) Phi (metricScalarAt ((S n).base.metric t) z))) →
      ∀ hV : PathConnectedSpace V,
      let _ : PathConnectedSpace V := hV
      let _ : PseudoMetricSpace V := (P.metric.restrictOpen V).toPseudoMetricSpace
      let _ : MetricSpace V := MetricSpace.ofT0PseudoMetricSpace V
      let p : V := ⟨P.basepoint, hp⟩
      metricScalarAt (P.metric.restrictOpen V) p ≠ 0 →
      ∀ (q : UniformSpace.Completion W) (d : ℝ),
      DifferentialGeometry.Toponogov.PuncturedConeApproximation q d →
      Tendsto (fun n => A (f n)) atTop atTop →
      ∀ r lower B : ℝ, 0 < r → 0 < lower → IsCompact (Metric.closedBall p r) →
      (∀ᶠ n in atTop, dist (x (f n) : UniformSpace.Completion W) q *
        Real.sqrt (A (f n)) ∈ Icc lower B) →
      (∀ᶠ n in atTop,
        riemannianClosedBallOf (scaleMetric (A (f n)) (hA (f n)) gW) (x (f n)) (r / 4) ⊆
          (fun z : V => F.partialDiffeomorph n z) '' Metric.closedBall p r) →
      (∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
        ∀ z ∈ Metric.closedBall p r, ∀ y ∈ Metric.closedBall p r,
          |metricDistance (scaleMetric (A (f n)) (hA (f n)) gW)
            (F.partialDiffeomorph n z) (F.partialDiffeomorph n y) - dist z y| < eta) → False := by
  dsimp only
  intro P f F C hcanonical V hp hsource D S hS tau htau hslab hreg hterminal hcurv
    Phi hPhi Q hQpos hQ hpinching hV
  let _ : PathConnectedSpace V := hV
  let _ : PseudoMetricSpace V := (P.metric.restrictOpen V).toPseudoMetricSpace
  let _ : MetricSpace V := MetricSpace.ofT0PseudoMetricSpace V
  let p : V := ⟨P.basepoint, hp⟩
  intro hscalar q d cone hAtop r lower B hr hlower hcompact hcenter hcapture hdist
  let rho := fun n => 1 / Real.sqrt (A (f n))
  have hrho (n : ℕ) : 0 < rho n := one_div_pos.mpr (Real.sqrt_pos.mpr (hA (f n)))
  have hrho0 : Tendsto rho atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hAtop)
  have hbase (n : ℕ) : F.partialDiffeomorph n p = x (f n) := F.basepoint_map n
  have hball (n : ℕ) :
      riemannianClosedBallOf (scaleMetric (A (f n)) (hA (f n)) gW) (x (f n)) (r / 4) =
        Metric.closedBall (x (f n)) (r / 4 * rho n) := by
    have hscale : r / 4 = Real.sqrt (A (f n)) * (r / 4 * rho n) := by
      dsimp only [rho]
      field_simp [(Real.sqrt_pos.mpr (hA (f n))).ne']
    conv_lhs => rw [hscale]
    rw [riemannianClosedBallOf_scaleMetric]
    ext y
    change riemannianEDistOf gW (x (f n)) y ≤ ENNReal.ofReal (r / 4 * rho n) ↔
      dist y (x (f n)) ≤ r / 4 * rho n
    rw [← hWmetric, edist_dist, ENNReal.ofReal_le_ofReal_iff (by positivity), dist_comm]
  have hdistScaled (n : ℕ) (z y : W) :
      metricDistance (scaleMetric (A (f n)) (hA (f n)) gW) z y = dist z y / rho n := by
    rw [metricDistance, edistOf_scale, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _), ← hWmetric, edist_dist,
      ENNReal.toReal_ofReal dist_nonneg]
    dsimp only [rho]
    rw [one_div, div_inv_eq_mul, mul_comm]
  apply pointed_local_flow_rescaled_cone_exclusion F C hcanonical V hsource S hS htau
    hslab hreg hterminal hcurv hPhi Q hQpos hQ hpinching hV p hscalar cone
    (fun n => x (f n)) (fun n z => F.partialDiffeomorph n z) rho hrho hrho0 hbase
    hr hlower hcompact
  · simpa only [rho, one_div, div_inv_eq_mul] using hcenter
  · filter_upwards [hcapture] with n hn
    rwa [hball n] at hn
  · intro eta heta
    filter_upwards [hdist eta heta] with n hn
    intro z hz y hy
    simpa only [hdistScaled] using hn z hz y hy

end DifferentialGeometry.PDE.RicciFlow
