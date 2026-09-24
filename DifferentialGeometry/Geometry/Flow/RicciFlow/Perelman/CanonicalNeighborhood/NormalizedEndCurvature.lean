import DifferentialGeometry.Topology.MetricSpace.CompactBall
import DifferentialGeometry.Geometry.Metric.Distance.Topology
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedCurvatureWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CrossModelDistanceTransfer
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2

private theorem eventually_source_ball_capture_near_completion_endpoint
    {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]
    (g : SmoothRiemannianMetric I3 W)
    (hmetric : ∀ x y : W, edist x y = riemannianEDistOf g x y)
    (X : FlowSequence.{u})
    (maps : ∀ i, PartialDiffeomorph I3 I3 W (X.term i).M ∞)
    (hsource : ∀ K : Set W, IsCompact K → ∀ᶠ i in atTop, K ⊆ (maps i).source)
    (hcomp : ∀ K : Set W, IsCompact K → ∀ᶠ i in atTop,
      ∀ y ∈ K, ∀ v : TangentSpace I3 y,
        g.inner y v v ≤ 4 * ((X.term i).S.base.metric 0).inner (maps i y)
          (mfderiv I3 I3 (maps i) y v) (mfderiv I3 I3 (maps i) y v) ∧
        ((X.term i).S.base.metric 0).inner (maps i y)
          (mfderiv I3 I3 (maps i) y v) (mfderiv I3 I3 (maps i) y v) ≤ 4 * g.inner y v v)
    {q : UniformSpace.Completion W} {r : ℝ} (hr : 0 < r)
    (hcompact : IsCompact (Metric.closedBall q r))
    (hcover : Metric.closedBall q r ⊆ insert q (range (fun x : W => (x : UniformSpace.Completion W))))
    {x : ℕ → W} (hx : Tendsto (fun n => (x n : UniformSpace.Completion W)) atTop (𝓝 q))
    {Q : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (hquant : ∀ᶠ n in atTop, (16 * a) ^ 2 < Q n * dist (x n : UniformSpace.Completion W) q ^ 2) :
    ∀ᶠ n in atTop, 0 < Q n ∧
      IsCompact (riemannianClosedBallOf g (x n) (8 * a / Real.sqrt (Q n))) ∧
      (∀ y ∈ riemannianClosedBallOf g (x n) (8 * a / Real.sqrt (Q n)),
        dist (x n : UniformSpace.Completion W) q / 2 < dist (y : UniformSpace.Completion W) q ∧
          dist (y : UniformSpace.Completion W) q < 3 * dist (x n : UniformSpace.Completion W) q / 2) ∧
      ∀ᶠ i in atTop,
        riemannianClosedBallOf ((X.term i).S.base.metric 0) (maps i (x n)) (2 * a / Real.sqrt (Q n)) ⊆
          (maps i) '' riemannianClosedBallOf g (x n) (8 * a / Real.sqrt (Q n)) ∧
        (maps i) '' riemannianClosedBallOf g (x n) (a / Real.sqrt (Q n)) ⊆
          riemannianClosedBallOf ((X.term i).S.base.metric 0) (maps i (x n)) (2 * a / Real.sqrt (Q n)) := by
  have heq (p : W) (R : ℝ) (hR : 0 ≤ R) : riemannianClosedBallOf g p R = Metric.closedBall p R := by
    ext y
    change riemannianEDistOf g p y ≤ ENNReal.ofReal R ↔ dist y p ≤ R
    rw [← hmetric, edist_dist, ENNReal.ofReal_le_ofReal_iff hR, dist_comm]
  have hballs := UniformSpace.Completion.coe_isometry.eventually_isCompact_scaled_closedBall
    hr hcompact hcover hx (show 0 < 8 * a by positivity)
    (by simpa only [show 2 * (8 * a) = 16 * a by ring] using hquant)
  filter_upwards [hballs] with n hn
  obtain ⟨hQ, hK, hrad⟩ := hn
  have hs : 0 < Real.sqrt (Q n) := Real.sqrt_pos.mpr hQ
  have hR : 0 < 8 * a / Real.sqrt (Q n) := by positivity
  have hsmall : 0 < a / Real.sqrt (Q n) := by positivity
  rw [← heq _ _ hR.le] at hK hrad
  refine ⟨hQ, hK, hrad, ?_⟩
  filter_upwards [hsource _ hK, hcomp _ hK] with i hsrc hcmp
  refine ⟨?_, ?_⟩
  · apply closedBall_subset_image_of_metric_lower_crossModel g ((X.term i).S.base.metric 0)
      (maps i) (x n) hR (by norm_num : 0 < (2 : ℝ))
      (show 2 * a / Real.sqrt (Q n) < (8 * a / Real.sqrt (Q n)) / 2 by
        simp only [div_eq_mul_inv] at hsmall ⊢
        nlinarith only [hsmall]) hK hsrc
    intro y hy v
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using (hcmp y hy v).1
  · rintro z ⟨y, hy, rfl⟩
    have hc : x n ∈ riemannianClosedBallOf g (x n) (a / Real.sqrt (Q n)) := by
      change riemannianEDistOf g (x n) (x n) ≤ _
      rw [riemannianEDistOf_self]
      exact bot_le
    have hd := crossModel_edist_le_of_metric_upper g ((X.term i).S.base.metric 0) (maps i) (x n)
      (by norm_num : 0 < (2 : ℝ)) hsmall.le
      (show 3 * (a / Real.sqrt (Q n)) < 8 * a / Real.sqrt (Q n) by
        simp only [div_eq_mul_inv] at hsmall ⊢
        nlinarith only [hsmall])
      hsrc (fun y hy v => by
        simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using (hcmp y hy v).2) hc hy
    change riemannianEDistOf ((X.term i).S.base.metric 0) (maps i (x n)) (maps i y) ≤ _
    calc
      _ ≤ ENNReal.ofReal 2 * riemannianEDistOf g (x n) y := hd
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (a / Real.sqrt (Q n)) := mul_le_mul' le_rfl hy
      _ = ENNReal.ofReal (2 * a / Real.sqrt (Q n)) := by
        rw [← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
        congr 1
        ring

private local instance pointedLimitRegular (L : PointedRiemannianManifold.{u, 0, 0} I3) :
    RegularSpace L.M := by
  let _ : EMetricSpace L.M := L.emetricSpace
  infer_instance

private theorem eventually_source_ball_capture_on_open_end
    (X : FlowSequence.{u}) (L : PointedRiemannianManifold.{u, 0, 0} I3) {f : ℕ → ℕ}
    (maps : PointedRiemannianConvergenceMaps (X.atTime 0) L f)
    (hcomp : ∀ eta : ℝ, 0 < eta → ∃ N : ℕ, ∀ i : ℕ, N ≤ i →
      ∀ y ∈ maps.source i, ∀ v : TangentSpace I3 y,
        (1 - eta) * L.metric.inner y v v ≤
          ((X.term (f i)).S.base.metric 0).inner (maps.partialDiffeomorph i y)
            (mfderiv I3 I3 (maps.partialDiffeomorph i) y v)
            (mfderiv I3 I3 (maps.partialDiffeomorph i) y v) ∧
        ((X.term (f i)).S.base.metric 0).inner (maps.partialDiffeomorph i y)
            (mfderiv I3 I3 (maps.partialDiffeomorph i) y v)
            (mfderiv I3 I3 (maps.partialDiffeomorph i) y v) ≤
          (1 + eta) * L.metric.inner y v v)
    (W : TopologicalSpace.Opens L.M) [PathConnectedSpace W] :
    let _ : PseudoMetricSpace W := (L.metric.restrictOpen W).toPseudoMetricSpace
    let _ : MetricSpace W := MetricSpace.ofT0PseudoMetricSpace W
    ∀ {q : UniformSpace.Completion W} {r : ℝ}, 0 < r →
      IsCompact (Metric.closedBall q r) →
      Metric.closedBall q r ⊆ insert q (range (fun x : W => (x : UniformSpace.Completion W))) →
      ∀ {x : ℕ → W}, Tendsto (fun n => (x n : UniformSpace.Completion W)) atTop (𝓝 q) →
      ∀ {Q : ℕ → ℝ} {a : ℝ}, 0 < a →
      (∀ᶠ n in atTop, (16 * a) ^ 2 < Q n * dist (x n : UniformSpace.Completion W) q ^ 2) →
      ∀ᶠ n in atTop, 0 < Q n ∧
        IsCompact (riemannianClosedBallOf (L.metric.restrictOpen W) (x n) (8 * a / Real.sqrt (Q n))) ∧
        (∀ y ∈ riemannianClosedBallOf (L.metric.restrictOpen W) (x n) (8 * a / Real.sqrt (Q n)),
          dist (x n : UniformSpace.Completion W) q / 2 < dist (y : UniformSpace.Completion W) q ∧
            dist (y : UniformSpace.Completion W) q < 3 * dist (x n : UniformSpace.Completion W) q / 2) ∧
        ∀ᶠ i in atTop,
          riemannianClosedBallOf (M := (X.term (f i)).M) ((X.term (f i)).S.base.metric 0)
              (maps.partialDiffeomorph i (x n : L.M)) (2 * a / Real.sqrt (Q n)) ⊆
            (fun y : W => maps.partialDiffeomorph i (y : L.M)) ''
              riemannianClosedBallOf (L.metric.restrictOpen W) (x n) (8 * a / Real.sqrt (Q n)) ∧
          (fun y : W => maps.partialDiffeomorph i (y : L.M)) ''
              riemannianClosedBallOf (L.metric.restrictOpen W) (x n) (a / Real.sqrt (Q n)) ⊆
            riemannianClosedBallOf (M := (X.term (f i)).M) ((X.term (f i)).S.base.metric 0)
              (maps.partialDiffeomorph i (x n : L.M)) (2 * a / Real.sqrt (Q n)) := by
  dsimp only
  let _ : PseudoMetricSpace W := (L.metric.restrictOpen W).toPseudoMetricSpace
  let _ : MetricSpace W := MetricSpace.ofT0PseudoMetricSpace W
  intro q r hr hcompact hcover x hx Q a ha hquant
  let inc := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3) W ⟨x 0⟩
  let F : ∀ i, PartialDiffeomorph I3 I3 W (X.term (f i)).M ∞ :=
    fun i => inc.trans (maps.partialDiffeomorph i)
  have hsrc (K : Set W) (hK : IsCompact K) : ∀ᶠ i in atTop, K ⊆ (F i).source := by
    obtain ⟨N, hN⟩ := maps.source_subset (hK.image continuous_subtype_val)
    filter_upwards [eventually_ge_atTop N] with i hi
    intro y hy
    change y ∈ (inc.trans (maps.partialDiffeomorph i)).source
    rw [PartialDiffeomorph.trans_source]
    exact ⟨mem_univ _, hN i hi ⟨y, hy, rfl⟩⟩
  have hcmp (K : Set W) (hK : IsCompact K) : ∀ᶠ i in atTop,
      ∀ y ∈ K, ∀ v : TangentSpace I3 y,
        (L.metric.restrictOpen W).inner y v v ≤
          4 * ((X.term (f i)).S.base.metric 0).inner (F i y)
            (mfderiv I3 I3 (F i) y v) (mfderiv I3 I3 (F i) y v) ∧
        ((X.term (f i)).S.base.metric 0).inner (F i y)
            (mfderiv I3 I3 (F i) y v) (mfderiv I3 I3 (F i) y v) ≤
          4 * (L.metric.restrictOpen W).inner y v v := by
    obtain ⟨N, hN⟩ := hcomp (1 / 2) (by norm_num)
    filter_upwards [hsrc K hK, eventually_ge_atTop N] with i hi hiN
    intro y hy v
    have hmem : (y : L.M) ∈ maps.source i := (hi hy).2
    have hderiv : mfderiv I3 I3 (F i) y v =
        mfderiv I3 I3 (maps.partialDiffeomorph i) (y : L.M) v := by
      have hd := mfderiv_comp y
        ((maps.partialDiffeomorph i).mdifferentiableAt (by simp) hmem)
        (hasMFDerivAt_subtype_val (I := I3) W y).mdifferentiableAt
      rw [mfderiv_subtype_val] at hd
      exact DFunLike.congr_fun hd v
    have hh := hN i hiN y hmem v
    have hval : F i y = maps.partialDiffeomorph i (y : L.M) := rfl
    rw [SmoothRiemannianMetric.restrictOpen_inner, hderiv, hval]
    constructor <;> linarith only [hh.1, hh.2]
  exact eventually_source_ball_capture_near_completion_endpoint (L.metric.restrictOpen W)
    (fun _ _ => rfl) ⟨X.interval ∘ f, fun i => X.term (f i)⟩ F hsrc hcmp
    hr hcompact hcover hx ha hquant

theorem exists_parabolic_curvature_bound_on_normalized_end {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar a tau C : ℝ, 0 < epsStar ∧ 0 < a ∧ a ≤ 1 / 2 ∧ 0 < tau ∧ 0 < C ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
          ∀ f : ℕ → ℕ, StrictMono f →
          ∀ L : PointedRiemannianManifold.{u, 0, 0} I3,
          ∀ maps : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) L f,
          ∀ conv : MetricConvergenceData maps,
          (∀ i, conv.domain i = CanonicalMetricCompactness.canonicalSourceData maps i) →
          (∀ eta : ℝ, 0 < eta → ∃ N : ℕ, ∀ i : ℕ, N ≤ i →
            ∀ y ∈ maps.source i, ∀ v : TangentSpace I3 y,
              (1 - eta) * L.metric.inner y v v ≤
                ((X.term (f i)).S.base.metric 0).inner (maps.partialDiffeomorph i y)
                  (mfderiv I3 I3 (maps.partialDiffeomorph i) y v)
                  (mfderiv I3 I3 (maps.partialDiffeomorph i) y v) ∧
              ((X.term (f i)).S.base.metric 0).inner (maps.partialDiffeomorph i y)
                  (mfderiv I3 I3 (maps.partialDiffeomorph i) y v)
                  (mfderiv I3 I3 (maps.partialDiffeomorph i) y v) ≤
                (1 + eta) * L.metric.inner y v v) →
          ∀ W : TopologicalSpace.Opens L.M, ∀ hW : PathConnectedSpace W,
          let _ : PathConnectedSpace W := hW
          let _ : PseudoMetricSpace W := (L.metric.restrictOpen W).toPseudoMetricSpace
          let _ : MetricSpace W := MetricSpace.ofT0PseudoMetricSpace W
          ∀ {q : UniformSpace.Completion W} {r : ℝ}, 0 < r →
            IsCompact (Metric.closedBall q r) →
            Metric.closedBall q r ⊆ insert q (range (fun x : W => (x : UniformSpace.Completion W))) →
            ∀ x : ℕ → W, Tendsto (fun n => (x n : UniformSpace.Completion W)) atTop (𝓝 q) →
            let Q : ℕ → ℝ := fun n => metricScalarAt L.metric (x n : L.M)
            Tendsto Q atTop atTop →
            (∀ᶠ n in atTop, 196 < Q n * dist (x n : UniformSpace.Completion W) q ^ 2) →
            ∀ᶠ n in atTop, 1 ≤ Q n ∧
              IsCompact (riemannianClosedBallOf (L.metric.restrictOpen W) (x n) (8 * a / Real.sqrt (Q n))) ∧
              (∀ y ∈ riemannianClosedBallOf (L.metric.restrictOpen W) (x n) (8 * a / Real.sqrt (Q n)),
                dist (x n : UniformSpace.Completion W) q / 2 < dist (y : UniformSpace.Completion W) q ∧
                  dist (y : UniformSpace.Completion W) q < 3 * dist (x n : UniformSpace.Completion W) q / 2) ∧
              ∀ᶠ i in atTop,
                (X.term (f i)).S.scalar 0 (maps.partialDiffeomorph i (x n : L.M)) ∈
                  Ioo (Q n / 2) (2 * Q n) ∧
                riemannianClosedBallOf (M := (X.term (f i)).M) ((X.term (f i)).S.base.metric 0)
                    (maps.partialDiffeomorph i (x n : L.M)) (2 * a / Real.sqrt (Q n)) ⊆
                  (fun y : W => maps.partialDiffeomorph i (y : L.M)) ''
                    riemannianClosedBallOf (L.metric.restrictOpen W) (x n) (8 * a / Real.sqrt (Q n)) ∧
                (fun y : W => maps.partialDiffeomorph i (y : L.M)) ''
                    riemannianClosedBallOf (L.metric.restrictOpen W) (x n) (a / Real.sqrt (Q n)) ⊆
                  riemannianClosedBallOf (M := (X.term (f i)).M) ((X.term (f i)).S.base.metric 0)
                    (maps.partialDiffeomorph i (x n : L.M)) (2 * a / Real.sqrt (Q n)) ∧
                Icc (-tau / Q n) 0 ⊆ (X.interval (f i)).carrier ∧
                ∀ t ∈ Icc (-tau / Q n) 0,
                  ∀ y ∈ riemannianClosedBallOf ((X.term (f i)).S.base.metric 0)
                    (maps.partialDiffeomorph i (x n : L.M)) (2 * a / Real.sqrt (Q n)),
                    Real.sqrt (FlowMetricBall.rmNormSq (X.term (f i)).S t y) ≤ C * Q n := by
  obtain ⟨epsStar, c, C, hepsStar, hc, hC, hprop⟩ :=
    exists_parabolic_curvature_bound_at_terminal_scalar_scale.{u} hkappa
  let a : ℝ := min (1 / 2) (c / 4)
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have ha1 : a ≤ 1 / 2 := min_le_left _ _
  have hac : a ≤ c / 4 := min_le_right _ _
  refine ⟨epsStar, a, c / 2, 2 * C, hepsStar, ha, ha1, by positivity, by positivity, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X f hf L maps conv hcanonical hcomp W hW
  let _ : PathConnectedSpace W := hW
  dsimp only
  let _ : PseudoMetricSpace W := (L.metric.restrictOpen W).toPseudoMetricSpace
  let _ : MetricSpace W := MetricSpace.ofT0PseudoMetricSpace W
  intro q r hr hcompact hcover x hx
  let Q : ℕ → ℝ := fun n => metricScalarAt L.metric (x n : L.M)
  change Tendsto Q atTop atTop → _
  intro hQ hquant
  have hquant' : ∀ᶠ n in atTop,
      (16 * a) ^ 2 < Q n * dist (x n : UniformSpace.Completion W) q ^ 2 := by
    filter_upwards [hquant] with n hn
    have hs : (16 * a) ^ 2 ≤ 64 := by nlinarith only [ha, ha1]
    linarith only [hs, hn]
  have hcapture := eventually_source_ball_capture_on_open_end
    X.toFlowSequence L maps hcomp W hr hcompact hcover hx ha hquant'
  have hwindow := hf.tendsto_atTop (hprop eps heps hle sigma hsigma Phi hPhi X)
  filter_upwards [hcapture, hQ.eventually_ge_atTop 1] with n hn hQn
  obtain ⟨hQpos, hK, hradial, hcap⟩ := hn
  refine ⟨hQn, hK, hradial, ?_⟩
  have hscalar := KappaSolutions.pointedScalar_tendsto_of_metricCG_canonical_domains
    conv hcanonical (x n : L.M)
  have hscalar' : ∀ᶠ i in atTop,
      (X.term (f i)).S.scalar 0 (maps.partialDiffeomorph i (x n : L.M)) ∈ Ioo (Q n / 2) (2 * Q n) :=
    hscalar.eventually (Ioo_mem_nhds (by dsimp only [Q]; linarith only [hQpos])
      (by dsimp only [Q]; linarith only [hQpos]))
  filter_upwards [hcap, hwindow, hscalar'] with i hcap_i hwin_i hscalar_i
  obtain ⟨hcarrier, hcurv⟩ := hwin_i (2 * Q n) (by linarith only [hQn])
    (maps.partialDiffeomorph i (x n : L.M)) hscalar_i.2.le
  have htime : -(c / 2) / Q n = -c / (2 * Q n) := by ring
  have hs : 0 < Real.sqrt (Q n) := Real.sqrt_pos.mpr hQpos
  have hrad : 2 * a / Real.sqrt (Q n) ≤ c / Real.sqrt (2 * Q n) := by
    apply (div_le_div_iff₀ hs (Real.sqrt_pos.mpr (by positivity))).mpr
    have hsqrt : Real.sqrt (2 * Q n) ≤ 2 * Real.sqrt (Q n) := by
      apply (Real.sqrt_le_iff).mpr
      exact ⟨by positivity, by nlinarith only [Real.sq_sqrt hQpos.le, hQpos]⟩
    nlinarith only [mul_le_mul_of_nonneg_left hsqrt (by positivity : 0 ≤ 2 * a),
      mul_le_mul_of_nonneg_right hac hs.le]
  refine ⟨hscalar_i, hcap_i.1, hcap_i.2, ?_, ?_⟩
  · simpa only [← htime, Q] using hcarrier
  · intro t ht y hy
    have hb := hcurv t (by
      change t ∈ Icc (-(c / 2) / Q n) 0 at ht
      simpa only [htime] using ht) y
      (hy.trans (ENNReal.ofReal_le_ofReal hrad))
    nlinarith only [hb]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
