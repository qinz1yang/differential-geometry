import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Bounds.ClosedInterval
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.AmbientQuadraticControl
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.BallImage
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullback

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

private theorem eventually_pointed_image_in_ball
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps X P phi)
    (C : MetricConvergenceData F)
    (href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric)
    (hcomplete : MetricComplete P) {A : ℝ} (hA : 0 ≤ A) :
    ∀ᶠ i in atTop, riemannianClosedBallOf P.metric P.basepoint A ⊆ F.source i ∧
      ∀ x ∈ riemannianClosedBallOf P.metric P.basepoint A,
        riemannianEDistOf (X.obj (phi i)).metric (X.obj (phi i)).basepoint (F.map i x) ≤
          ENNReal.ofReal (2 * A) := by
  filter_upwards [F.eventually_image_closed_ball_subset C href hcomplete P.basepoint
    hA (by norm_num : (1 : ℝ) < 2)] with i hi
  refine ⟨hi.1, fun x hx => ?_⟩
  have h := hi.2 ⟨x, hx, rfl⟩
  have hbase : F.map i P.basepoint = (X.obj (phi i)).basepoint := F.basepoint_map i
  change riemannianEDistOf (X.obj (phi i)).metric (F.map i P.basepoint)
    (F.map i x) ≤ ENNReal.ofReal (2 * A) at h
  rwa [hbase] at h


theorem exists_eventually_pointed_extension_curvature_bound
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (hphi : Tendsto phi atTop atTop)
    (F : PointedRiemannianConvergenceMaps (X.atZero (I := I)) P phi)
    (C : MetricConvergenceData F)
    (href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric)
    (hcomplete : MetricComplete P)
    (G : ℕ → ℝ → SmoothRiemannianMetric I P.M)
    (hG : ∀ K : Set P.M, IsCompact K → ∀ᶠ i in atTop,
      ∃ U : Set P.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ F.source i ∧
        ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (G i t).inner x v w = ((X.term (phi i)).S.base.metric t).inner (F.map i x)
            (mfderiv I I (F.map i) x v) (mfderiv I I (F.map i) x w))
    (times : Set ℝ) (p : ℕ)
    (hlocal : ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ i in atTop,
      ∀ t ∈ times, ∀ x : (X.term i).M,
        riemannianEDistOf ((X.term i).S.base.metric 0) (X.term i).basepoint x ≤
          ENNReal.ofReal A → curvDerivNorm p ((X.term i).S.base.metric t) x ≤ B)
    {A : ℝ} (hA : 0 ≤ A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ i in atTop, ∀ t ∈ times,
      ∀ x ∈ riemannianClosedBallOf P.metric P.basepoint A,
        curvDerivNorm p (G i t) x ≤ B := by
  have hmetricComplete : RiemannianMetricComplete (I := I) P.metric :=
    ⟨MetricComplete.complete P hcomplete⟩
  let K := riemannianClosedBallOf (I := I) P.metric P.basepoint A
  have hK : IsCompact K := hmetricComplete.closedEBall_isCompact P.basepoint A
  obtain ⟨B, hB, hb⟩ := hlocal (2 * A + 1) (by linarith)
  refine ⟨B, hB, ?_⟩
  filter_upwards [hG K hK, eventually_pointed_image_in_ball F C href hcomplete hA,
    hphi.eventually hb] with i hGi hFi hbi
  obtain ⟨U, hU, hKU, hUF, hpair⟩ := hGi
  intro t ht x hx
  have heq := curvDerivNorm_eq_of_local_pullback (G i t)
    ((X.term (phi i)).S.base.metric t) (F.partialDiffeomorph i) ⟨U, hU⟩
    hUF (hpair t) p ⟨x, hKU hx⟩
  change curvDerivNorm p (G i t) x =
    curvDerivNorm p ((X.term (phi i)).S.base.metric t) (F.map i x) at heq
  rw [heq]
  exact hbi t ht (F.map i x) ((hFi.2 x hx).trans (ENNReal.ofReal_le_ofReal (by linarith)))

theorem exists_eventually_pointed_extension_uniform_equivalence
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (hphi : Tendsto phi atTop atTop)
    (F : PointedRiemannianConvergenceMaps (X.atZero (I := I)) P phi)
    (C : MetricConvergenceData F)
    (href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric)
    (hcomplete : MetricComplete P)
    (G : ℕ → ℝ → SmoothRiemannianMetric I P.M)
    (hG : ∀ K : Set P.M, IsCompact K → ∀ᶠ i in atTop,
      ∃ U : Set P.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ F.source i ∧
        ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (G i t).inner x v w = ((X.term (phi i)).S.base.metric t).inner (F.map i x)
            (mfderiv I I (F.map i) x v) (mfderiv I I (F.map i) x w))
    {a b : ℝ} (hab : a < b) (hcarrier : Icc a b ⊆ X.D.carrier)
    (hregular : Ioo a b ⊆ X.D.regular) (hzero : (0 : ℝ) ∈ Icc a b)
    (hlocal : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 0 ≤ Q ∧ ∀ᶠ i in atTop,
      ∀ t ∈ Icc a b, ∀ x : (X.term i).M,
        riemannianEDistOf ((X.term i).S.base.metric 0) (X.term i).basepoint x ≤
          ENNReal.ofReal A → (X.term i).rmNormSq t x ≤ Q)
    {A : ℝ} (hA : 0 ≤ A) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ᶠ i in atTop, ∀ t ∈ Icc a b,
      MetricUniformEquivalentOn (riemannianClosedBallOf P.metric P.basepoint A)
        P.metric (G i t) B := by
  have hmetricComplete : RiemannianMetricComplete (I := I) P.metric :=
    ⟨MetricComplete.complete P hcomplete⟩
  let K := riemannianClosedBallOf (I := I) P.metric P.basepoint A
  have hK : IsCompact K := hmetricComplete.closedEBall_isCompact P.basepoint A
  obtain ⟨Q, _hQ, hQ⟩ := hlocal (2 * A + 1) (by linarith)
  obtain ⟨N, hN⟩ := exists_pointed_full_ambient_quadratic_control C href K hK
    (1 / 2) (by norm_num)
  let D : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt Q
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  let B₀ : ℝ := Real.exp (2 * D * (b - a))
  have hB₀ : 1 ≤ B₀ := Real.one_le_exp (by positivity)
  have hB₀pos : 0 < B₀ := Real.exp_pos _
  have hB : 1 ≤ 2 * B₀ := by linarith
  refine ⟨2 * B₀, hB, ?_⟩
  filter_upwards [hG K hK, eventually_pointed_image_in_ball F C href hcomplete hA,
    hphi.eventually hQ, eventually_ge_atTop N] with i hGi hFi hQi hi
  obtain ⟨U, _hU, hKU, _hUF, hpair⟩ := hGi
  let V := riemannianClosedBallOf (I := I) ((X.term (phi i)).S.base.metric 0)
    (X.term (phi i)).basepoint (2 * A + 1)
  have hquad := twoTensorQuadBound_of_solutions (fun _ => (X.term (phi i)).S)
    V a b Q (fun _ t ht x hx => hQi t ht x hx)
  have hEq := metric_uniform_equivalent_on_closed_interval_of_solution
    (X.term (phi i)).S (X.term (phi i)).isSolution hab hcarrier hregular hzero hD
    (fun t ht x hx v => hquad.2 0 t ht x hx v)
  have hEqB (t : ℝ) (ht : t ∈ Icc a b) :
      MetricUniformEquivalentOn V ((X.term (phi i)).S.base.metric 0)
        ((X.term (phi i)).S.base.metric t) B₀ := by
    apply metricUniformEquivalentOn_of_le (hEq 0 t ht)
    simp only [metricEquivalenceFactor, one_mul, sub_zero]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left
      (abs_le.mpr ⟨by linarith [ht.1, hzero.2], by linarith [ht.2, hzero.1]⟩)
      (mul_nonneg (by norm_num) hD)
  intro t ht
  refine ⟨hB, fun x hx v => ?_⟩
  have hxV : F.map i x ∈ V :=
    (hFi.2 x hx).trans (ENNReal.ofReal_le_ofReal (by linarith))
  have htime := (hEqB t ht).2 (F.map i x) hxV (mfderiv I I (F.map i) x v)
  have hclose := abs_le.mp ((hN i hi).2 x hx v)
  change -(1 / 2 * P.metric.inner x v v) ≤
    ((X.term (phi i)).S.base.metric 0).inner (F.map i x)
      (mfderiv I I (F.map i) x v) (mfderiv I I (F.map i) x v) -
        P.metric.inner x v v ∧
    ((X.term (phi i)).S.base.metric 0).inner (F.map i x)
      (mfderiv I I (F.map i) x v) (mfderiv I I (F.map i) x v) -
        P.metric.inner x v v ≤ 1 / 2 * P.metric.inner x v v at hclose
  have hnonneg : 0 ≤ P.metric.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (P.metric.pos x v hv).le
  rw [hpair t x (hKU hx) v v]
  have htimeLower := mul_le_mul_of_nonneg_left htime.1 hB₀pos.le
  rw [← mul_assoc, mul_inv_cancel₀ hB₀pos.ne', one_mul] at htimeLower
  have hmul : P.metric.inner x v v ≤ (2 * B₀) *
      ((X.term (phi i)).S.base.metric t).inner (F.map i x)
        (mfderiv I I (F.map i) x v) (mfderiv I I (F.map i) x v) := by
    nlinarith
  constructor
  · have hBpos : 0 < 2 * B₀ := by positivity
    calc
      _ ≤ (2 * B₀)⁻¹ * ((2 * B₀) *
          ((X.term (phi i)).S.base.metric t).inner (F.map i x)
            (mfderiv I I (F.map i) x v) (mfderiv I I (F.map i) x v)) :=
        mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hBpos.le)
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hBpos.ne', one_mul]
  · nlinarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
