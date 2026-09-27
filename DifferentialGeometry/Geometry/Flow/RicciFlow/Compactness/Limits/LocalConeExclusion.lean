import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.LocalMetricExtraction
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Distance
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Subsequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.TerminalBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.LocalEndComparison
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


theorem pointed_source_flow_rescaled_cone_exclusion_of_local_comparison
    {X : PointedRiemannianSeq.{u, 0, 0} I3} {P : PointedRiemannianManifold.{u, 0, 0} I3}
    {f : ℕ → ℕ} (F : PointedRiemannianConvergenceMaps X P f) (C : MetricConvergenceData F)
    (hcanonical : ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (V : TopologicalSpace.Opens P.M) (hp : P.basepoint ∈ V) [PathConnectedSpace V]
    (hsource : ∀ n, (V : Set P.M) ⊆ (F.partialDiffeomorph n).source)
    {D : RealTimeInterval} (S : ∀ n, SolutionOn (I := I3) (M := (X.obj (f n)).M) D)
    (hS : ∀ n, IsSolutionOn (S n))
    {tau : ℝ} (htau : 0 < tau) (hslab : Icc (-tau) 0 ⊆ D.carrier)
    (hreg : Ico (-tau) 0 ⊆ D.regular)
    (hterminal : ∀ n, (S n).base.metric 0 = (X.obj (f n)).metric)
    (hbaseOne : ∀ n, metricScalarAt (X.obj (f n)).metric (X.obj (f n)).basepoint = 1)
    (hcurv : ∀ K : Set V, IsCompact K → ∀ m : ℕ,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop, ∀ t ∈ Icc (-tau) 0, ∀ x ∈ K,
        curvDerivNorm m ((S n).base.metric t) (F.partialDiffeomorph n x) ≤ B)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (Q : ℕ → ℝ) (hQpos : ∀ n, 0 < Q n) (hQ : Tendsto Q atTop atTop)
    (hpinching : ∀ t ∈ Icc (-tau) 0, ∀ᶠ n in atTop, ∀ x : V,
      curvatureOperatorLowerBoundAt ((S n).base.metric t) (F.partialDiffeomorph n x)
        (metricAlgebraicCurvatureTensorAt ((S n).base.metric t) (F.partialDiffeomorph n x))
        (rescalePinchingFunction (Q n) Phi
          (metricScalarAt ((S n).base.metric t) (F.partialDiffeomorph n x))))
    {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]
    (gW : SmoothRiemannianMetric I3 W)
    (hWmetric : ∀ a b : W, edist a b = riemannianEDistOf gW a b)
    {q : UniformSpace.Completion W} {d : ℝ}
    (cone : DifferentialGeometry.Toponogov.PuncturedConeApproximation q d)
    (x : ℕ → W) (scale : ℕ → ℝ) (hscale : ∀ n, 0 < scale n)
    (hscaleTop : Tendsto scale atTop atTop)
    (Bmap : ∀ n, PartialDiffeomorph I3 I3 W (X.obj (f n)).M ∞)
    {R lower upper : ℝ} (hR : 0 < R) (hlower : 0 < lower)
    (hBsource : ∀ n, riemannianClosedBallOf (scaleMetric (scale n) (hscale n) gW) (x n) R ⊆ (Bmap n).source)
    (hBbase : ∀ n, Bmap n (x n) = (X.obj (f n)).basepoint)
    (hcapture : ∀ n, riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint (R/4) ⊆
      (Bmap n) '' riemannianClosedBallOf (scaleMetric (scale n) (hscale n) gW) (x n) R)
    (hBconv : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      ∀ y ∈ riemannianClosedBallOf (scaleMetric (scale n) (hscale n) gW) (x n) R,
      ∀ v : TangentSpace I3 y,
        (1-eta)*(scaleMetric (scale n) (hscale n) gW).inner y v v ≤
          (X.obj (f n)).metric.inner (Bmap n y) (mfderiv I3 I3 (Bmap n) y v) (mfderiv I3 I3 (Bmap n) y v) ∧
        (X.obj (f n)).metric.inner (Bmap n y) (mfderiv I3 I3 (Bmap n) y v) (mfderiv I3 I3 (Bmap n) y v) ≤
          (1+eta)*(scaleMetric (scale n) (hscale n) gW).inner y v v)
    (hcenter : ∀ᶠ n in atTop, dist (x n : UniformSpace.Completion W) q /
      (1 / Real.sqrt (scale n)) ∈ Icc lower upper) : False := by
  let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I3 V.isOpen)
  choose L hL hmetric using fun n => Perelman.KappaSolutions.exists_local_solution_of_partialDiffeomorph
    (S n) (hS n) (F.partialDiffeomorph n) V (hsource n)
  have hterm (n) (z : V) (v w : TangentSpace I3 z) :
      ((L n).base.metric 0).inner z v w = (X.obj (f n)).metric.inner (F.partialDiffeomorph n z)
        (mfderiv I3 I3 (F.partialDiffeomorph n) z v) (mfderiv I3 I3 (F.partialDiffeomorph n) z w) := by
    rw [hmetric,hterminal]
  have hjets : ∀ K : Set V, IsCompact K → ∀ m : ℕ,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop, ∀ t ∈ Icc (-tau) 0, ∀ z ∈ K,
        curvDerivNorm m ((L n).base.metric t) z ≤ B := by
    intro K hK m
    obtain ⟨B,hB,hbound⟩ := hcurv K hK m
    refine ⟨B,hB,hbound.mono ?_⟩
    intro n hn t ht z hz
    rw [curvDerivNorm_eq_of_partialDiffeomorph_restriction (F.partialDiffeomorph n) V
      (hsource n) ((L n).base.metric t) ((S n).base.metric t) (hmetric n t)]
    exact hn t ht z hz
  have hpin : ∀ t ∈ Icc (-tau) 0, ∀ᶠ n in atTop, ∀ z : V,
      curvatureOperatorLowerBoundAt ((L n).base.metric t) z
        (metricAlgebraicCurvatureTensorAt ((L n).base.metric t) z)
        (rescalePinchingFunction (Q n) Phi (metricScalarAt ((L n).base.metric t) z)) := by
    intro t ht
    filter_upwards [hpinching t ht] with n hn
    intro z
    have hsc := metricScalarAt_eq_of_partialDiffeomorph_restriction
      (F.partialDiffeomorph n) V (hsource n)
      ((L n).base.metric t) ((S n).base.metric t) (hmetric n t) z
    rw [hsc]
    exact curvatureOperatorLowerBoundAt_of_partialDiffeomorph_restriction
      (F.partialDiffeomorph n) V (hsource n) ((L n).base.metric t)
      ((S n).base.metric t) (hmetric n t) z _ (hn z)
  let inc := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3) V ⟨⟨P.basepoint,hp⟩⟩
  let compare := fun n => (inc.trans (F.partialDiffeomorph n)).trans (Bmap n).symm
  obtain ⟨ψ,hψ,g,hg0,hg,hcone,_,r,hr,hKr,hbase,hcap,hdist⟩ :=
    exists_nonnegative_local_flow_with_end_comparison F C hcanonical V hp hsource L hL
      (by linarith : -tau < 0) hslab hreg hterm hjets hPhi Q hQpos hQ hpin
      (fun n => scaleMetric (scale n) (hscale n) gW) x Bmap hR hBsource hBbase hcapture hBconv
  let _ : PseudoMetricSpace V := (P.metric.restrictOpen V).toPseudoMetricSpace
  let _ : MetricSpace V := MetricSpace.ofT0PseudoMetricSpace V
  let p : V := ⟨P.basepoint,hp⟩
  have hmetric0 (a b : V) : edist a b = riemannianEDistOf (g 0) a b := by rw [hg0]; rfl
  have hscalar : metricScalarAt (g 0) p = 1 := by
    rw [hg0,metricScalarAt_restrictOpen]
    exact Perelman.KappaSolutions.pointedScalar_base_eq_of_metricCG_canonical_domains C hcanonical hbaseOne
  have hsec : ∀ t ∈ Icc (-tau) 0, SecLower (g t) 0 univ := by
    intro t ht z _ v w
    have hn := (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional
      (g t) z (by simp [ThreeSpace])).mp (hcone t ht z) v w
    have hslots : (fun i => ![v,w,w,v] i) = vec4 (I := I3) v w w v := by
      funext i
      fin_cases i <;> rfl
    simpa only [SecLower,zero_mul,metricRm04StandardAt_apply,hslots] using hn
  let rho := fun n => 1 / Real.sqrt (scale n)
  have hrho (n) : 0 < rho n := one_div_pos.mpr (Real.sqrt_pos.mpr (hscale n))
  have hrho0 : Tendsto rho atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hscaleTop)
  have hball : riemannianClosedBallOf (g 0) p r = Metric.closedBall p r := by
    ext z
    change riemannianEDistOf (g 0) p z ≤ ENNReal.ofReal r ↔ dist z p ≤ r
    rw [← hmetric0,edist_dist,ENNReal.ofReal_le_ofReal_iff hr.le,dist_comm]
  have hscaledBall (n) : riemannianClosedBallOf (scaleMetric (scale n) (hscale n) gW) (x n) (r/4) =
      Metric.closedBall (x n) (r/4*rho n) := by
    have heq : r/4 = Real.sqrt (scale n) * (r/4*rho n) := by
      dsimp only [rho]
      field_simp [(Real.sqrt_pos.mpr (hscale n)).ne']
    conv_lhs => rw [heq]
    rw [riemannianClosedBallOf_scaleMetric]
    ext z
    change riemannianEDistOf gW (x n) z ≤ ENNReal.ofReal (r/4*rho n) ↔ dist z (x n) ≤ r/4*rho n
    rw [← hWmetric,edist_dist,ENNReal.ofReal_le_ofReal_iff (by positivity),dist_comm]
  have hdistScaled (n) (a b : W) : metricDistance (scaleMetric (scale n) (hscale n) gW) a b =
      dist a b / rho n := by
    rw [metricDistance,edistOf_scale,ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
      ← hWmetric,edist_dist,ENNReal.toReal_ofReal dist_nonneg]
    dsimp only [rho]
    rw [one_div,div_inv_eq_mul,mul_comm]
  have hdist0 (a b : V) : metricDistance (g 0) a b = dist a b := by
    rw [metricDistance,← hmetric0,edist_dist,ENNReal.toReal_ofReal dist_nonneg]
  apply solution_not_rescaled_cone_limit htau
    ({base.metric := g} : SolutionOn (I := I3) (M := V) (RealTimeInterval.closed (-tau) 0 (by linarith)))
    hg hmetric0 hsec p (by rw [hscalar]; norm_num) cone x
    (fun n z => compare n z) rho hrho hrho0 hbase hr hlower (hball ▸ hKr) hcenter
  · filter_upwards [hcap] with n hn
    have hh := hn.2
    change riemannianClosedBallOf (scaleMetric (scale n) (hscale n) gW) (x n) (r/4) ⊆
      (fun z => compare n z) '' riemannianClosedBallOf (g 0) p r at hh
    simpa only [hscaledBall,hball] using hh
  · intro eta heta
    filter_upwards [hdist eta heta] with n hn
    intro a ha b hb
    have hh := hn a (hball.symm ▸ ha) b (hball.symm ▸ hb)
    change |metricDistance (scaleMetric (scale n) (hscale n) gW) (compare n a) (compare n b) -
      metricDistance (g 0) a b| < eta at hh
    rwa [hdistScaled,hdist0] at hh



theorem pointed_source_flow_rescaled_cone_exclusion_of_curvature_bound
    {X : PointedRiemannianSeq.{u, 0, 0} I3} {P : PointedRiemannianManifold.{u, 0, 0} I3}
    {f : ℕ → ℕ} (F : PointedRiemannianConvergenceMaps X P f) (C : MetricConvergenceData F)
    (hcanonical : ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (V : TopologicalSpace.Opens P.M) (hp : P.basepoint ∈ V) [PathConnectedSpace V]
    (hsource : ∀ n, (V : Set P.M) ⊆ (F.partialDiffeomorph n).source)
    {D : RealTimeInterval} (S : ∀ n, SolutionOn (I := I3) (M := (X.obj (f n)).M) D)
    (hS : ∀ n, IsSolutionOn (S n))
    {tau : ℝ} (htau : 0 < tau) (hslab : Icc (-tau) 0 ⊆ D.carrier)
    (hreg : Ioo (-tau) 0 ⊆ D.regular)
    (hterminal : ∀ n, (S n).base.metric 0 = (X.obj (f n)).metric)
    (hbaseOne : ∀ n, metricScalarAt (X.obj (f n)).metric (X.obj (f n)).basepoint = 1)
    (K r : ℝ) (hK : 0 < K) (hr : 0 < r)
    (hcompact : ∀ n, IsCompact (riemannianClosedBallOf ((S n).base.metric 0) (X.obj (f n)).basepoint r))
    (hflowBound : ∀ n, ∀ t ∈ Icc (-tau) 0,
      ∀ x ∈ riemannianClosedBallOf ((S n).base.metric 0) (X.obj (f n)).basepoint r,
        curvDerivNormSq 0 ((S n).base.metric t) x ≤ K ^ 2)
    (himage : ∀ n, ∀ z : V, riemannianEDistOf ((S n).base.metric 0)
      (X.obj (f n)).basepoint (F.partialDiffeomorph n z) ≤ ENNReal.ofReal (r/4))
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (Q : ℕ → ℝ) (hQpos : ∀ n, 0 < Q n) (hQ : Tendsto Q atTop atTop)
    (hpinching : ∀ t ∈ Icc (-tau) 0, ∀ᶠ n in atTop, ∀ x : V,
      curvatureOperatorLowerBoundAt ((S n).base.metric t) (F.partialDiffeomorph n x)
        (metricAlgebraicCurvatureTensorAt ((S n).base.metric t) (F.partialDiffeomorph n x))
        (rescalePinchingFunction (Q n) Phi
          (metricScalarAt ((S n).base.metric t) (F.partialDiffeomorph n x))))
    {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]
    (gW : SmoothRiemannianMetric I3 W)
    (hWmetric : ∀ a b : W, edist a b = riemannianEDistOf gW a b)
    {q : UniformSpace.Completion W} {d : ℝ}
    (cone : DifferentialGeometry.Toponogov.PuncturedConeApproximation q d)
    (x : ℕ → W) (scale : ℕ → ℝ) (hscale : ∀ n, 0 < scale n)
    (hscaleTop : Tendsto scale atTop atTop)
    (Bmap : ∀ n, PartialDiffeomorph I3 I3 W (X.obj (f n)).M ∞)
    {R lower upper : ℝ} (hR : 0 < R) (hlower : 0 < lower)
    (hBsource : ∀ n, riemannianClosedBallOf (scaleMetric (scale n) (hscale n) gW) (x n) R ⊆ (Bmap n).source)
    (hBbase : ∀ n, Bmap n (x n) = (X.obj (f n)).basepoint)
    (hcapture : ∀ n, riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint (R/4) ⊆
      (Bmap n) '' riemannianClosedBallOf (scaleMetric (scale n) (hscale n) gW) (x n) R)
    (hBconv : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      ∀ y ∈ riemannianClosedBallOf (scaleMetric (scale n) (hscale n) gW) (x n) R,
      ∀ v : TangentSpace I3 y,
        (1-eta)*(scaleMetric (scale n) (hscale n) gW).inner y v v ≤
          (X.obj (f n)).metric.inner (Bmap n y) (mfderiv I3 I3 (Bmap n) y v) (mfderiv I3 I3 (Bmap n) y v) ∧
        (X.obj (f n)).metric.inner (Bmap n y) (mfderiv I3 I3 (Bmap n) y v) (mfderiv I3 I3 (Bmap n) y v) ≤
          (1+eta)*(scaleMetric (scale n) (hscale n) gW).inner y v v)
    (hcenter : ∀ᶠ n in atTop, dist (x n : UniformSpace.Completion W) q /
      (1 / Real.sqrt (scale n)) ∈ Icc lower upper) : False := by
  have hbound (n m : ℕ) (t : ℝ) (ht : t ∈ Icc (-(tau/2)) 0) (z : V) :
      curvDerivNorm m ((S n).base.metric t) (F.partialDiffeomorph n z) ≤
        shiLocalUniformBound 3 m (K * (tau/4))
          ((r / (4 * Real.exp (9*K*tau))) * Real.sqrt K /
            (4 * Real.exp (9*K*(tau/4)))) * K / Real.sqrt (tau/4)^m := by
    have hh := shi_curvDerivNorm_on_terminal_ball (S n) (hS n)
      (by linarith : -tau < 0) hK hr hslab hreg (X.obj (f n)).basepoint (hcompact n)
      (hflowBound n) m t (by simpa only [add_zero,neg_div] using ht)
      (F.partialDiffeomorph n z) (himage n z)
    simpa only [show Module.finrank ℝ ThreeSpace = 3 by simp [ThreeSpace],
      Nat.cast_ofNat,show (3:ℝ)^2=9 by norm_num,zero_sub,neg_neg] using hh
  apply pointed_source_flow_rescaled_cone_exclusion_of_local_comparison F C hcanonical V hp hsource
    S hS (tau := tau/2) (by positivity) (Icc_subset_Icc (by linarith) le_rfl |>.trans hslab)
    (fun t ht => hreg ⟨by linarith [ht.1],ht.2⟩) hterminal hbaseOne _ hPhi Q hQpos hQ
    (fun t ht => hpinching t ⟨by linarith [ht.1],ht.2⟩) gW hWmetric cone x scale hscale hscaleTop
    Bmap hR hlower hBsource hBbase hcapture hBconv hcenter
  intro L hL m
  refine ⟨shiLocalUniformBound 3 m (K * (tau/4))
    ((r / (4 * Real.exp (9*K*tau))) * Real.sqrt K / (4 * Real.exp (9*K*(tau/4)))) *
      K / Real.sqrt (tau/4)^m, ?_,Eventually.of_forall ?_⟩
  · exact div_nonneg (mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) hK.le) (by positivity)
  intro n t ht z hz
  exact hbound n m t ht z




theorem pointed_local_pullback_flow_rescaled_cone_exclusion
    {X : PointedRiemannianSeq.{u, 0, 0} I3} {P : PointedRiemannianManifold.{u, 0, 0} I3}
    {f : ℕ → ℕ} (F : PointedRiemannianConvergenceMaps X P f) (C : MetricConvergenceData F)
    (hcanonical : ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (V : TopologicalSpace.Opens P.M) (hp : P.basepoint ∈ V) [PathConnectedSpace V]
    (hsource : ∀ n, (V : Set P.M) ⊆ (F.partialDiffeomorph n).source)
    {D : RealTimeInterval} (S : ∀ n, SolutionOn (I := I3) (M := (X.obj (f n)).M) D)
    (hS : ∀ n, IsSolutionOn (S n))
    {tau : ℝ} (htau : 0 < tau) (hslab : Icc (-tau) 0 ⊆ D.carrier)
    (hreg : Ioo (-tau) 0 ⊆ D.regular)
    (hterminal : ∀ n, (S n).base.metric 0 = (X.obj (f n)).metric)
    (hbaseOne : ∀ n, metricScalarAt (X.obj (f n)).metric (X.obj (f n)).basepoint = 1)
    (K r : ℝ) (hK : 0 < K)
    (hcompact : ∀ n, IsCompact (riemannianClosedBallOf ((S n).base.metric 0) (X.obj (f n)).basepoint r))
    (hflowBound : ∀ n, ∀ t ∈ Icc (-tau) 0,
      ∀ x ∈ riemannianClosedBallOf ((S n).base.metric 0) (X.obj (f n)).basepoint r,
        curvDerivNormSq 0 ((S n).base.metric t) x ≤ K ^ 2)
    (himage : ∀ n, ∀ z : V, riemannianEDistOf ((S n).base.metric 0)
      (X.obj (f n)).basepoint (F.partialDiffeomorph n z) ≤ ENNReal.ofReal (r/4))
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (Q : ℕ → ℝ) (hQpos : ∀ n, 0 < Q n) (hQ : Tendsto Q atTop atTop)
    (hpinching : ∀ t ∈ Icc (-tau) 0, ∀ᶠ n in atTop, ∀ x : V,
      curvatureOperatorLowerBoundAt ((S n).base.metric t) (F.partialDiffeomorph n x)
        (metricAlgebraicCurvatureTensorAt ((S n).base.metric t) (F.partialDiffeomorph n x))
        (rescalePinchingFunction (Q n) Phi
          (metricScalarAt ((S n).base.metric t) (F.partialDiffeomorph n x))))
    {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]
    (gW : SmoothRiemannianMetric I3 W)
    (hWmetric : ∀ a b : W, edist a b = riemannianEDistOf gW a b)
    {q : UniformSpace.Completion W} {d : ℝ}
    (cone : DifferentialGeometry.Toponogov.PuncturedConeApproximation q d)
    (x : ℕ → W) (scale : ℕ → ℝ) (hscale : ∀ n, 0 < scale n)
    (hscaleTop : Tendsto scale atTop atTop)
    (N : ℕ → Type u) [∀ n, TopologicalSpace (N n)]
    [∀ n, ChartedSpace ThreeSpace (N n)] [∀ n, IsManifold I3 ∞ (N n)] [∀ n, T2Space (N n)]
    (gN : ∀ n, SmoothRiemannianMetric I3 (N n))
    (pi : ∀ n, (X.obj (f n)).M → N n)
    (hpi : ∀ n, IsLocalDiffeomorph I3 I3 ∞ (pi n)) (hipi : ∀ n, Function.Injective (pi n))
    (hmetric : ∀ n, (X.obj (f n)).metric = localPullMetric (gN n) (pi n) (hpi n))
    (hball : ∀ n, (pi n) '' riemannianBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint (r/4) =
      riemannianBallOf (gN n) (pi n (X.obj (f n)).basepoint) (r/4))
    (A : ∀ n, PartialDiffeomorph I3 I3 W (N n) ∞)
    {R lower upper : ℝ} (hR : 0 < R) (hRr : R ≤ r/4) (hlower : 0 < lower)
    (hAbase : ∀ n, A n (x n) = pi n (X.obj (f n)).basepoint)
    (hAcpt : ∀ n, IsCompact (riemannianClosedBallOf (scaleMetric (scale n) (hscale n) gW) (x n) R))
    (hAsource : ∀ n, riemannianClosedBallOf (scaleMetric (scale n) (hscale n) gW) (x n) R ⊆ (A n).source)
    (hAmetric : ∀ n,
      ∀ y ∈ riemannianClosedBallOf (scaleMetric (scale n) (hscale n) gW) (x n) R,
      ∀ v : TangentSpace I3 y,
        (1-1/((n:ℝ)+2))*(scaleMetric (scale n) (hscale n) gW).inner y v v ≤
          (gN n).inner (A n y) (mfderiv I3 I3 (A n) y v) (mfderiv I3 I3 (A n) y v) ∧
        (gN n).inner (A n y) (mfderiv I3 I3 (A n) y v) (mfderiv I3 I3 (A n) y v) ≤
          (1+1/((n:ℝ)+2))*(scaleMetric (scale n) (hscale n) gW).inner y v v)
    (hcenter : ∀ᶠ n in atTop, dist (x n : UniformSpace.Completion W) q /
      (1 / Real.sqrt (scale n)) ∈ Icc lower upper) : False := by
  have hr : 0 < r := by linarith
  have heps (n : ℕ) : 0 ≤ 1 / ((n:ℝ)+2) ∧ 1 / ((n:ℝ)+2) ≤ 1/2 := by
    refine ⟨by positivity,?_⟩
    apply one_div_le_one_div_of_le (by norm_num)
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hcoarse (n) : ∀ y ∈ riemannianClosedBallOf (scaleMetric (scale n) (hscale n) gW) (x n) R,
      ∀ v : TangentSpace I3 y,
      (1/2:ℝ)*(scaleMetric (scale n) (hscale n) gW).inner y v v ≤
        (gN n).inner (A n y) (mfderiv I3 I3 (A n) y v) (mfderiv I3 I3 (A n) y v) ∧
      (gN n).inner (A n y) (mfderiv I3 I3 (A n) y v) (mfderiv I3 I3 (A n) y v) ≤
        2*(scaleMetric (scale n) (hscale n) gW).inner y v v := by
    intro y hy v
    have hn := metric_inner_self_nonneg (scaleMetric (scale n) (hscale n) gW) y v
    have hc := hAmetric n y hy v
    have he := mul_le_mul_of_nonneg_right (heps n).2 hn
    constructor <;> nlinarith [mul_nonneg (heps n).1 hn]
  have hproduce (n : ℕ) := Geometry.Metric.exists_inverse_composition_of_localPullMetric
    (scaleMetric (scale n) (hscale n) gW) (gN n) (pi n) (hpi n) (hipi n)
    (X.obj (f n)).metric (hmetric n) (X.obj (f n)).basepoint (x n) hR hRr
    (hball n) (A n) (hAbase n) (hAcpt n) (hAsource n) (hcoarse n)
  choose B hBsource hBtarget hBpi hpiB hBsymm hDbase hDsource hDmetric hDcapture using hproduce
  let Dmap := fun n => (A n).trans (B n)
  have hDcmp : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      ∀ y ∈ riemannianClosedBallOf (scaleMetric (scale n) (hscale n) gW) (x n) (R/4),
      ∀ v : TangentSpace I3 y,
        (1-eta)*(scaleMetric (scale n) (hscale n) gW).inner y v v ≤
          (X.obj (f n)).metric.inner (Dmap n y) (mfderiv I3 I3 (Dmap n) y v) (mfderiv I3 I3 (Dmap n) y v) ∧
        (X.obj (f n)).metric.inner (Dmap n y) (mfderiv I3 I3 (Dmap n) y v) (mfderiv I3 I3 (Dmap n) y v) ≤
          (1+eta)*(scaleMetric (scale n) (hscale n) gW).inner y v v := by
    intro eta heta
    have hlim : Tendsto (fun n : ℕ => 1/((n:ℝ)+2)) atTop (𝓝 (0:ℝ)) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
    filter_upwards [hlim.eventually (Iio_mem_nhds heta)] with n hn
    intro y hy v
    rw [hDmetric n y hy]
    have hc := hAmetric n y (riemannianClosedBallOf_mono _ _ (by linarith : R/4 ≤ R) hy) v
    have hpos := metric_inner_self_nonneg (scaleMetric (scale n) (hscale n) gW) y v
    have he := mul_le_mul_of_nonneg_right hn.le hpos
    constructor <;> nlinarith
  exact pointed_source_flow_rescaled_cone_exclusion_of_curvature_bound F C hcanonical V hp hsource
    S hS htau hslab hreg hterminal hbaseOne K r hK hr hcompact hflowBound himage
    hPhi Q hQpos hQ hpinching gW hWmetric cone x scale hscale hscaleTop Dmap
    (by positivity : 0 < R/4) hlower hDsource hDbase
    (by simpa only [show R/4/4 = R/16 by ring] using hDcapture) hDcmp hcenter

theorem pointed_source_flow_rescaled_cone_exclusion_of_local_curvature
    {X : PointedRiemannianSeq.{u, 0, 0} I3} {P : PointedRiemannianManifold.{u, 0, 0} I3}
    {f : ℕ → ℕ} (F : PointedRiemannianConvergenceMaps X P f) (C : MetricConvergenceData F)
    (hcanonical : ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    {D : RealTimeInterval} (S : ∀ n, SolutionOn (I := I3) (M := (X.obj (f n)).M) D)
    (hS : ∀ n, IsSolutionOn (S n))
    {tau : ℝ} (htau : 0 < tau) (hslab : Icc (-tau) 0 ⊆ D.carrier)
    (hreg : Ioo (-tau) 0 ⊆ D.regular)
    (hterminal : ∀ n, (S n).base.metric 0 = (X.obj (f n)).metric)
    (hbaseOne : ∀ n, metricScalarAt (X.obj (f n)).metric (X.obj (f n)).basepoint = 1)
    (K r : ℝ) (hK : 0 < K) (hr : 0 < r)
    (hcompact : ∀ n, IsCompact (riemannianClosedBallOf ((S n).base.metric 0) (X.obj (f n)).basepoint r))
    (hflowBound : ∀ n, ∀ t ∈ Icc (-tau) 0,
      ∀ x ∈ riemannianClosedBallOf ((S n).base.metric 0) (X.obj (f n)).basepoint r,
        curvDerivNormSq 0 ((S n).base.metric t) x ≤ K ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (Q : ℕ → ℝ) (hQpos : ∀ n, 0 < Q n) (hQ : Tendsto Q atTop atTop)
    (hpinching : ∀ t ∈ Icc (-tau) 0, ∀ᶠ n in atTop,
      ∀ z ∈ riemannianClosedBallOf ((S n).base.metric 0) (X.obj (f n)).basepoint r,
        curvatureOperatorLowerBoundAt ((S n).base.metric t) z
          (metricAlgebraicCurvatureTensorAt ((S n).base.metric t) z)
          (rescalePinchingFunction (Q n) Phi (metricScalarAt ((S n).base.metric t) z)))
    {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]
    (gW : SmoothRiemannianMetric I3 W)
    (hWmetric : ∀ a b : W, edist a b = riemannianEDistOf gW a b)
    {q : UniformSpace.Completion W} {d : ℝ}
    (cone : DifferentialGeometry.Toponogov.PuncturedConeApproximation q d)
    (x : ℕ → W) (scale : ℕ → ℝ) (hscale : ∀ n, 0 < scale n)
    (hscaleTop : Tendsto scale atTop atTop)
    (Bmap : ∀ n, PartialDiffeomorph I3 I3 W (X.obj (f n)).M ∞)
    {R lower upper : ℝ} (hR : 0 < R) (hlower : 0 < lower)
    (hBsource : ∀ n, riemannianClosedBallOf (scaleMetric (scale n) (hscale n) gW) (x n) R ⊆ (Bmap n).source)
    (hBbase : ∀ n, Bmap n (x n) = (X.obj (f n)).basepoint)
    (hcapture : ∀ n, riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint (R/4) ⊆
      (Bmap n) '' riemannianClosedBallOf (scaleMetric (scale n) (hscale n) gW) (x n) R)
    (hBconv : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      ∀ y ∈ riemannianClosedBallOf (scaleMetric (scale n) (hscale n) gW) (x n) R,
      ∀ v : TangentSpace I3 y,
        (1-eta)*(scaleMetric (scale n) (hscale n) gW).inner y v v ≤
          (X.obj (f n)).metric.inner (Bmap n y) (mfderiv I3 I3 (Bmap n) y v) (mfderiv I3 I3 (Bmap n) y v) ∧
        (X.obj (f n)).metric.inner (Bmap n y) (mfderiv I3 I3 (Bmap n) y v) (mfderiv I3 I3 (Bmap n) y v) ≤
          (1+eta)*(scaleMetric (scale n) (hscale n) gW).inner y v v)
    (hcenter : ∀ᶠ n in atTop, dist (x n : UniformSpace.Completion W) q /
      (1 / Real.sqrt (scale n)) ∈ Icc lower upper) : False := by
  let _ : CompleteSpace ThreeSpace := FiniteDimensional.complete ℝ ThreeSpace
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have href : ∀ n, (C.domain n).referenceMetric = (C.domain n).limitMetric := by
    intro n
    rw [hcanonical]
    rfl
  obtain ⟨V, hp, hV, _, hevent⟩ :=
    F.exists_precompact_neighborhood_with_image_in_ball C href (by positivity : 0 < r / 4)
  let _ : PathConnectedSpace V := hV
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  let shift : ℕ → ℕ := fun n => n + N
  have hshift : StrictMono shift := fun _ _ h => Nat.add_lt_add_right h N
  let F' := F.compSubseq shift hshift
  let C' := C.compSubseq shift hshift
  have hcan : ∀ n, C'.domain n = CanonicalMetricCompactness.canonicalSourceData F' n := by
    intro n
    change MetricSourceData.compSubseq shift hshift n (C.domain (shift n)) = _
    rw [hcanonical]
    rfl
  have hsrc : ∀ n, (V : Set P.M) ⊆ (F'.partialDiffeomorph n).source :=
    fun n => subset_closure.trans (hN (shift n) (Nat.le_add_left N n)).1
  have himage : ∀ n, ∀ z : V, riemannianEDistOf ((S (shift n)).base.metric 0)
      (X.obj (f (shift n))).basepoint (F'.partialDiffeomorph n z) ≤ ENNReal.ofReal (r / 4) := by
    intro n z
    rw [hterminal]
    exact (hN (shift n) (Nat.le_add_left N n)).2 z z.property |>.le
  apply pointed_source_flow_rescaled_cone_exclusion_of_curvature_bound F' C' hcan V hp hsrc
    (fun n => S (shift n)) (fun n => hS (shift n)) htau hslab hreg
    (fun n => hterminal (shift n)) (fun n => hbaseOne (shift n)) K r hK hr
    (fun n => hcompact (shift n)) (fun n => hflowBound (shift n)) himage
    hPhi (Q ∘ shift) (fun n => hQpos (shift n)) (hQ.comp hshift.tendsto_atTop) _
    gW hWmetric cone (x ∘ shift) (scale ∘ shift) (fun n => hscale (shift n))
    (hscaleTop.comp hshift.tendsto_atTop) (fun n => Bmap (shift n)) hR hlower
    (fun n => hBsource (shift n)) (fun n => hBbase (shift n)) (fun n => hcapture (shift n))
    (fun eta heta => hshift.tendsto_atTop.eventually (hBconv eta heta))
    (hshift.tendsto_atTop.eventually hcenter)
  intro t ht
  filter_upwards [hshift.tendsto_atTop.eventually (hpinching t ht)] with n hn
  intro z
  exact hn (F'.partialDiffeomorph n z)
    ((himage n z).trans (ENNReal.ofReal_le_ofReal (by linarith : r / 4 ≤ r)))
theorem source_flow_rescaled_cone_exclusion_of_curvature_and_volume_lower_bounds
    (X : PointedRiemannianSeq.{u, 0, 0} I3)
    {D : RealTimeInterval} (S : ∀ n, SolutionOn (I := I3) (M := (X.obj n).M) D)
    (hS : ∀ n, IsSolutionOn (S n))
    {tau : ℝ} (htau : 0 < tau) (hslab : Icc (-tau) 0 ⊆ D.carrier)
    (hreg : Ioo (-tau) 0 ⊆ D.regular)
    (hterminal : ∀ n, (S n).base.metric 0 = (X.obj n).metric)
    (hbaseOne : ∀ n, metricScalarAt (X.obj n).metric (X.obj n).basepoint = 1)
    (K r : ℝ) (hK : 0 < K) (hr : 0 < r)
    (hcompact : ∀ n, IsCompact (riemannianClosedBallOf ((S n).base.metric 0) (X.obj n).basepoint r))
    (hflowBound : ∀ n, ∀ t ∈ Icc (-tau) 0,
      ∀ x ∈ riemannianClosedBallOf ((S n).base.metric 0) (X.obj n).basepoint r,
        curvDerivNormSq 0 ((S n).base.metric t) x ≤ K ^ 2)
    {a₀ κ : ℝ} (ha₀ : 0 < a₀) (hκ : 0 < κ)
    (hvolume : ∀ a : ℝ, 0 < a → a ≤ a₀ → ∀ᶠ n in atTop,
      ∀ z ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint (r / 4),
        ENNReal.ofReal (κ * a ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure I3 (X.obj n).M (X.obj n).metric
            (riemannianBallOf (X.obj n).metric z a))
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (Q : ℕ → ℝ) (hQpos : ∀ n, 0 < Q n) (hQ : Tendsto Q atTop atTop)
    (hpinching : ∀ t ∈ Icc (-tau) 0, ∀ᶠ n in atTop,
      ∀ z ∈ riemannianClosedBallOf ((S n).base.metric 0) (X.obj n).basepoint r,
        curvatureOperatorLowerBoundAt ((S n).base.metric t) z
          (metricAlgebraicCurvatureTensorAt ((S n).base.metric t) z)
          (rescalePinchingFunction (Q n) Phi (metricScalarAt ((S n).base.metric t) z)))
    {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]
    (gW : SmoothRiemannianMetric I3 W)
    (hWmetric : ∀ a b : W, edist a b = riemannianEDistOf gW a b)
    {q : UniformSpace.Completion W} {d : ℝ}
    (cone : DifferentialGeometry.Toponogov.PuncturedConeApproximation q d)
    (x : ℕ → W) (scale : ℕ → ℝ) (hscale : ∀ n, 0 < scale n)
    (hscaleTop : Tendsto scale atTop atTop)
    (Bmap : ∀ n, PartialDiffeomorph I3 I3 W (X.obj n).M ∞)
    {R lower upper : ℝ} (hR : 0 < R) (hlower : 0 < lower)
    (hBsource : ∀ n, riemannianClosedBallOf (scaleMetric (scale n) (hscale n) gW) (x n) R ⊆ (Bmap n).source)
    (hBbase : ∀ n, Bmap n (x n) = (X.obj n).basepoint)
    (hcapture : ∀ n, riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint (R/4) ⊆
      (Bmap n) '' riemannianClosedBallOf (scaleMetric (scale n) (hscale n) gW) (x n) R)
    (hBconv : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      ∀ y ∈ riemannianClosedBallOf (scaleMetric (scale n) (hscale n) gW) (x n) R,
      ∀ v : TangentSpace I3 y,
        (1-eta)*(scaleMetric (scale n) (hscale n) gW).inner y v v ≤
          (X.obj n).metric.inner (Bmap n y) (mfderiv I3 I3 (Bmap n) y v) (mfderiv I3 I3 (Bmap n) y v) ∧
        (X.obj n).metric.inner (Bmap n y) (mfderiv I3 I3 (Bmap n) y v) (mfderiv I3 I3 (Bmap n) y v) ≤
          (1+eta)*(scaleMetric (scale n) (hscale n) gW).inner y v v)
    (hcenter : ∀ᶠ n in atTop, dist (x n : UniformSpace.Completion W) q /
      (1 / Real.sqrt (scale n)) ∈ Icc lower upper) : False := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  obtain ⟨f, hf, r₀, _, _, P, F, C, hcanonical, _, _, _, _⟩ :=
    exists_pointed_terminal_metric_convergence_of_local_curvature_and_volume_lower_bound
      X S hS hr hK (by linarith : -tau < 0) hslab hreg hterminal
      (Eventually.of_forall fun n => by simpa only [hterminal] using hcompact n)
      (Eventually.of_forall fun n t ht z hz => hflowBound n t ht z (by simpa only [hterminal] using hz))
      ha₀ hκ (by simpa only [show Module.finrank ℝ ThreeSpace = 3 by simp [ThreeSpace]] using hvolume)
  let U := fun n => connectedComponentOpen (I := I3) (X.obj n).basepoint
  let hp := fun n => (mem_connectedComponent : (X.obj n).basepoint ∈ U n)
  let F' := F.liftTargetOpen U hp
  apply pointed_source_flow_rescaled_cone_exclusion_of_local_curvature F' C hcanonical
    (fun n => S (f n)) (fun n => hS (f n)) htau hslab hreg
    (fun n => hterminal (f n)) (fun n => hbaseOne (f n)) K r hK hr
    (fun n => hcompact (f n)) (fun n => hflowBound (f n)) hPhi (Q ∘ f)
    (fun n => hQpos (f n)) (hQ.comp hf.tendsto_atTop)
    (fun t ht => hf.tendsto_atTop.eventually (hpinching t ht)) gW hWmetric cone (x ∘ f)
    (scale ∘ f) (fun n => hscale (f n)) (hscaleTop.comp hf.tendsto_atTop)
    (fun n => Bmap (f n)) hR hlower (fun n => hBsource (f n)) (fun n => hBbase (f n))
    (fun n => hcapture (f n))
    (fun eta heta => hf.tendsto_atTop.eventually (hBconv eta heta))
    (hf.tendsto_atTop.eventually hcenter)
end DifferentialGeometry.PDE.RicciFlow
