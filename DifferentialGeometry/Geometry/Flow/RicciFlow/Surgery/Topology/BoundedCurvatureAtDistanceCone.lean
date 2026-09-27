import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedTerminalCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.LocalEndComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.ConeExclusion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncomingPinching
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.ScalarRescaling
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.QuadraticBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitness

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u v

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private local instance pointedLimitRegular (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel) :
    RegularSpace L.M := by
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  infer_instance

private theorem localPullMetric_restrict_inner {M N : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M]
    [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
    (g : SmoothRiemannianMetric ThreeModel N) (Φ : PartialDiffeomorph ThreeModel ThreeModel M N ∞)
    (V : TopologicalSpace.Opens M)
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : V => Φ z.val))
    (z : V) (v w : TangentSpace ThreeModel z) :
    (localPullMetric g (fun z : V => Φ z.val) hf).inner z v w =
      g.inner (Φ z) (mfderiv ThreeModel ThreeModel Φ z v)
        (mfderiv ThreeModel ThreeModel Φ z w) := by
  rw [localPullMetric_inner]
  have hd := DifferentialGeometry.mfderiv_restrict_open (I := ThreeModel) (J := ThreeModel) Φ V z
  rw [hd]
  rfl

private theorem isCompact_riemannianClosedBallOf_endpoint {P : OrientedThreeStage.{u}} {a b : ℝ}
    (A : P.ClosedSlab a b)
    (g : SmoothRiemannianMetric ThreeModel
      (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen)
    (p : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen) (r : ℝ) :
    IsCompact (riemannianClosedBallOf g p r) := by
  have hU : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularRegion = univ :=
    A.terminalRegularRegion_eq_univ P
  have : CompactSpace (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen :=
    isCompact_iff_compactSpace.mp (by
      change IsCompact (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularRegion
      rw [hU]
      exact isCompact_univ)
  exact (isClosed_le (Geometry.Riemannian.continuous_riemannianEDist g p)
    continuous_const).isCompact

private theorem scaleMetric_mul_eq {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (g : SmoothRiemannianMetric ThreeModel M) {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : c = a * b) :
    scaleMetric c hc g = scaleMetric a ha (scaleMetric b hb g) := by
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  simp only [scaleMetric_inner]
  rw [habc]
  ring

private theorem isCompact_closedBall_of_lt_dist_puncture {W : Type*} [MetricSpace W]
    {q : UniformSpace.Completion W} {d : ℝ} (hK : IsCompact (Metric.closedBall q d))
    (hcover : Metric.closedBall q d ⊆
      insert q (range (fun z : W => (z : UniformSpace.Completion W))))
    (x : W) {r : ℝ} (hr : r < dist (x : UniformSpace.Completion W) q)
    (hd : dist (x : UniformSpace.Completion W) q + r ≤ d) :
    IsCompact (Metric.closedBall x r) := by
  let K := Metric.closedBall (x : UniformSpace.Completion W) r
  have hKd : K ⊆ Metric.closedBall q d := by
    intro z hz
    have hz' : dist z (x : UniformSpace.Completion W) ≤ r := hz
    change dist z q ≤ d
    linarith [dist_triangle z (x : UniformSpace.Completion W) q]
  have hKc : IsCompact K := hK.of_isClosed_subset Metric.isClosed_closedBall hKd
  have hKr : K ⊆ range (fun z : W => (z : UniformSpace.Completion W)) := by
    intro z hz
    rcases hcover (hKd hz) with hzq | hzr
    · exfalso
      have hz' : dist z (x : UniformSpace.Completion W) ≤ r := hz
      rw [hzq, dist_comm] at hz'
      linarith
    · exact hzr
  have hpre : (fun z : W => (z : UniformSpace.Completion W)) ⁻¹' K = Metric.closedBall x r := by
    ext z
    simp only [K, mem_preimage, Metric.mem_closedBall, UniformSpace.Completion.dist_eq]
  rw [← hpre]
  exact ((UniformSpace.Completion.isUniformInducing_coe W).isInducing.isCompact_preimage_iff
    hKr).mpr hKc

theorem RetainedCoreHistory.normalized_terminal_ball_volume_lower_bound_of_scaled_tests
    (Phi : ℝ → ℝ) (hPhi : Perelman.AdmissiblePinchingFunction Phi) {C : ℝ≥0}
    (P : ℕ → OrientedThreeStage.{u}) (H : ∀ n, RetainedCoreHistory (P n))
    (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (hinit : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hs : ∀ n, (H n).horizon < s n)
    (x : ∀ n, (G n).terminalRegularOpen) (q Q : ℕ → ℝ)
    (hq : ∀ n, 0 < q n) (hqQ : ∀ n, q n ≤ Q n) (hQ : ∀ n, 1 ≤ Q n)
    (hderiv : ∀ n, ∀ j : Fin (H n).eventCount,
      ∀ y : ((H n).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      q n < ((H n).toHistory.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => ((H n).toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * ((H n).toHistory.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ n, ∀ y : ((H n).stage (Fin.last (H n).eventCount)).Carrier,
      ∀ t ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (s n), q n < (G n).flow.scalar t y →
      |derivWithin (fun v => (G n).flow.scalar v y) (Iic t) t| ≤ C * (G n).flow.scalar t y ^ 2)
    (hpinch : ∀ n, ∀ j : Fin (H n).eventCount,
      Perelman.PhiAlmostNonnegative ((H n).toHistory.event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ)) Phi)
    (hpinchFinal : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) Phi)
    {rho : ℝ}
    (hbuffer : ∀ R : ℝ, 0 < R → R < rho → ∃ r A θ : ℝ,
      0 < r ∧ R + r < rho ∧ 1 ≤ A ∧ 0 < θ ∧ 6 * C * (A * θ) ≤ 1 ∧
      ∀ᶠ n in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r)) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
          metricScalarAt (L n).metric y ≤ 2 * (A * Q n)) ∧
        ∃ first : Fin ((H n).eventCount + 1),
          (∀ y ∈ riemannianClosedBallOf
            (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
            Nonempty (BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
              (Fin.le_last first) y.val)) ∧
          (H n).time first ≤ s n - θ / Q n)
    {κ σ₀ : ℝ} (σ : ℕ → ℝ) (hκ : 0 < κ) (hσ₀ : 0 < σ₀)
    (hσQ : ∀ n, σ₀ ≤ σ n * Real.sqrt (Q n))
    (htested : ∀ n (t : ℝ) (ht : (H n).horizon < t) (hts : t < s n),
      let A := (H n).extendHorizon t ht.le
        ((G n).closedPrefix t ((H n).time_le_horizon.trans_lt ht) hts) (hinit n)
      let time : Icc (0 : ℝ) A.horizon := ⟨t, (H n).horizon_nonneg.trans ht.le, le_rfl⟩
      ∀ (y : (A.toHistory.stageAt time).Carrier) (b : ℝ), 0 < b → b ≤ σ n →
        A.toHistory.isParabolicallyRmControlledBall time y b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (A.toHistory.stageAt time).Carrier
              (A.toHistory.stageMetric (A.toHistory.activeStage time) time)
              (riemannianBallOf (A.toHistory.stageMetric (A.toHistory.activeStage time) time)
                y b)) :
    ∀ r R : ℝ, 0 < r → r < R → R < rho → ∀ J : ℝ, 0 ≤ J →
      ∃ a κ' : ℝ, 0 < a ∧ 0 < κ' ∧ r + a ≤ R ∧ a ^ 4 * J ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ y ∈ riemannianClosedBallOf
        (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) r,
        ENNReal.ofReal (κ' * a ^ 3) ≤ riemannianVolumeMeasure ThreeModel (G n).terminalRegularOpen
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric)
          (riemannianBallOf (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric)
            y a) := by
  intro r R hr hrR hRrho J hJ
  obtain ⟨b, A, θ0, hb, _, hA, hθ0, hbudget, hbuf⟩ := hbuffer r hr (hrR.trans hRrho)
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hsqrtA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hAp
  have hgap : 0 < R - r := sub_pos.mpr hrR
  let a0 := min (b / 2) (min (R - r) (min σ₀ (min 1 (1 / (J + 1)))))
  have ha0 : 0 < a0 := by dsimp [a0]; positivity
  have ha0b : a0 ≤ b / 2 := min_le_left _ _
  have ha0R : a0 ≤ R - r := (min_le_right _ _).trans (min_le_left _ _)
  have ha0σ : a0 ≤ σ₀ :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have ha01 : a0 ≤ 1 :=
    (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans
      (min_le_left _ _)
  have ha0J : a0 ≤ 1 / (J + 1) :=
    (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans
      (min_le_right _ _)
  let θ := min (A * θ0) ((a0 * Real.sqrt A) ^ 2)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθA : θ ≤ A * θ0 := min_le_left _ _
  obtain ⟨α, hα, _, hαθ, hball⟩ :=
    ObservedHistory.exists_uniform_parabolically_controlled_incoming_terminal_ball_radius hPhi hθ
  have hαa0 : α ≤ a0 * Real.sqrt A := by
    have hh : α ^ 2 ≤ (a0 * Real.sqrt A) ^ 2 := hαθ.trans (min_le_right _ _)
    nlinarith [mul_pos ha0 hsqrtA]
  let a := α / Real.sqrt A
  have ha : 0 < a := div_pos hα hsqrtA
  have haa0 : a ≤ a0 := (div_le_iff₀ hsqrtA).mpr hαa0
  have hab : a < b := (haa0.trans ha0b).trans_lt (by linarith)
  have haJ : a * (J + 1) ≤ 1 := (le_div_iff₀ (by positivity)).mp (haa0.trans ha0J)
  have ha1 : a ≤ 1 := haa0.trans ha01
  have hasmall : a ^ 4 * J ^ 2 ≤ 1 := by
    have h1 : a ^ 2 ≤ a := by nlinarith
    have h2 : a ^ 2 * J ≤ 1 :=
      (mul_le_mul_of_nonneg_right h1 hJ).trans (by linarith)
    have hh := pow_le_pow_left₀ (mul_nonneg (sq_nonneg a) hJ) h2 2
    nlinarith only [hh]
  refine ⟨a, κ, ha, hκ, by linarith [haa0.trans ha0R], hasmall, ?_⟩
  filter_upwards [hbuf] with n hn y hy
  obtain ⟨first, htrace, hstart⟩ := hn.2.2
  have hQp : 0 < Q n := zero_lt_one.trans_le (hQ n)
  have hAQ : 1 ≤ A * Q n := (hQ n).trans (le_mul_of_one_le_left hQp.le hA)
  have hsqrtQ : 0 < Real.sqrt (Q n) := Real.sqrt_pos.mpr hQp
  have hsub : riemannianClosedBallOf (L n).metric y (b / Real.sqrt (Q n)) ⊆
      riemannianClosedBallOf (scaleMetric (Q n) hQp (L n).metric) (x n) (r + b) := by
    have heq : riemannianClosedBallOf (L n).metric y (b / Real.sqrt (Q n)) =
        riemannianClosedBallOf (scaleMetric (Q n) hQp (L n).metric) y b := by
      rw [← riemannianClosedBallOf_scaleMetric (Q n) hQp]
      congr 1
      field_simp
    rw [heq]
    exact riemannianClosedBallOf_subset_of_add_radius_le _ hr.le hb.le le_rfl hy
  have hcompact : IsCompact (riemannianClosedBallOf (L n).metric y (b / Real.sqrt (Q n))) :=
    hn.1.of_isClosed_subset
      (isClosed_le (Geometry.Riemannian.continuous_riemannianEDist (L n).metric y)
        continuous_const) hsub
  have hradius : α / Real.sqrt (A * Q n) = a / Real.sqrt (Q n) := by
    rw [Real.sqrt_mul hAp.le]
    dsimp [a]
    field_simp
  have hstart' : (H n).time first ≤ s n - θ / (A * Q n) := by
    have hh : θ / (A * Q n) ≤ θ0 / Q n := by
      have hh := div_le_div_of_nonneg_right hθA (mul_pos hAp hQp).le
      have heq : A * θ0 / (A * Q n) = θ0 / Q n := by field_simp
      rwa [heq] at hh
    linarith
  have hbudget' : 6 * C * θ ≤ 1 :=
    (mul_le_mul_of_nonneg_left hθA (by positivity)).trans hbudget
  obtain ⟨p, S, _, _, _, _, hslabs, hlast, B, _, hBRadius, hB, _, himage, _, _⟩ :=
    hball (H n).toHistory first (Fin.last (H n).eventCount) (Fin.le_last first) (G n) (L n) y
      hAQ (hinit n) (div_pos hb hsqrtQ) hcompact (hq n)
      ((hqQ n).trans (le_mul_of_one_le_left hQp.le hA))
      (fun j _ _ => hderiv n j) (fun z _ => hfinal n z.val)
      (fun j _ _ => hpinch n j) (hpinchFinal n)
      (fun z hz => hn.2.1 z (hsub hz)) (fun z hz => htrace z (hsub hz)) hstart' hbudget'
      (by rw [hradius]; exact (div_lt_div_iff_of_pos_right hsqrtQ).mpr hab)
  have hBr : B.radius = a / Real.sqrt (Q n) := hBRadius.trans hradius
  have hBσ : B.radius ≤ σ n := by
    rw [hBr, div_le_iff₀ hsqrtQ]
    exact (haa0.trans ha0σ).trans (hσQ n)
  exact (H n).normalized_terminal_volume_ball_ge_of_tested_incomingFootprint_flow_ball
    (G n) (L n) (hinit n) (hs n) first
    (riemannianClosedBallOf (L n).metric y (b / Real.sqrt (Q n))) hstart'
    (sub_le_self _ (div_nonneg hθ.le (mul_pos hAp hQp).le)) S
    (fun j hf => hslabs j hf (Fin.le_last _)) hlast (x n) y hQp hr.le
    (by linarith [hab.le]) B hB hBr hn.1 hy (by simpa only [hBRadius] using himage) hBσ
    (htested n)

theorem RetainedCoreHistory.exists_normalized_terminal_pointed_convergence_of_scaled_tests
    (Phi : ℝ → ℝ) (hPhi : Perelman.AdmissiblePinchingFunction Phi) {C : ℝ≥0}
    (P₀ : ℕ → OrientedThreeStage.{u}) (H : ∀ n, RetainedCoreHistory (P₀ n))
    (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (hinit : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hs : ∀ n, (H n).horizon < s n)
    (x : ∀ n, (G n).terminalRegularOpen) (q Q : ℕ → ℝ)
    (hscale : ∀ n, Q n = metricScalarAt (L n).metric (x n))
    (hq : ∀ n, 0 < q n) (hqQ : ∀ n, q n ≤ Q n) (hQ : ∀ n, 1 ≤ Q n)
    (hderiv : ∀ n, ∀ j : Fin (H n).eventCount,
      ∀ y : ((H n).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      q n < ((H n).toHistory.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => ((H n).toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * ((H n).toHistory.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ n, ∀ y : ((H n).stage (Fin.last (H n).eventCount)).Carrier,
      ∀ t ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (s n), q n < (G n).flow.scalar t y →
      |derivWithin (fun v => (G n).flow.scalar v y) (Iic t) t| ≤ C * (G n).flow.scalar t y ^ 2)
    (hpinch : ∀ n, ∀ j : Fin (H n).eventCount,
      Perelman.PhiAlmostNonnegative ((H n).toHistory.event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ)) Phi)
    (hpinchFinal : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) Phi)
    {rho : ℝ} (hrho : 0 < rho)
    (hbuffer : ∀ R : ℝ, 0 < R → R < rho → ∃ r A θ : ℝ,
      0 < r ∧ R + r < rho ∧ 1 ≤ A ∧ 0 < θ ∧ 6 * C * (A * θ) ≤ 1 ∧
      ∀ᶠ n in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r)) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
          metricScalarAt (L n).metric y ≤ 2 * (A * Q n)) ∧
        ∃ first : Fin ((H n).eventCount + 1),
          (∀ y ∈ riemannianClosedBallOf
            (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
            Nonempty (BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
              (Fin.le_last first) y.val)) ∧
          (H n).time first ≤ s n - θ / Q n)
    {κ σ₀ : ℝ} (σ : ℕ → ℝ) (hκ : 0 < κ) (hσ₀ : 0 < σ₀)
    (hσQ : ∀ n, σ₀ ≤ σ n * Real.sqrt (Q n))
    (htested : ∀ n (t : ℝ) (ht : (H n).horizon < t) (hts : t < s n),
      let A := (H n).extendHorizon t ht.le
        ((G n).closedPrefix t ((H n).time_le_horizon.trans_lt ht) hts) (hinit n)
      let time : Icc (0 : ℝ) A.horizon := ⟨t, (H n).horizon_nonneg.trans ht.le, le_rfl⟩
      ∀ (y : (A.toHistory.stageAt time).Carrier) (b : ℝ), 0 < b → b ≤ σ n →
        A.toHistory.isParabolicallyRmControlledBall time y b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (A.toHistory.stageAt time).Carrier
              (A.toHistory.stageMetric (A.toHistory.activeStage time) time)
              (riemannianBallOf (A.toHistory.stageMetric (A.toHistory.activeStage time) time)
                y b)) :
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := (G n).terminalRegularOpen
            basepoint := x n
            metric := scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric } }
    ∃ (f : ℕ → ℕ), StrictMono f ∧
      ∃ (r : ℕ → ℝ), (∀ n, 0 < r n ∧ r n < rho) ∧ Tendsto r atTop (𝓝 rho) ∧
      ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (F : PointedRiemannianConvergenceMaps X.connectedComponent P f),
        let U := fun i => connectedComponentOpen (I := ThreeModel) (X.obj i).basepoint
        let hp := fun i => (mem_connectedComponent : (X.obj i).basepoint ∈ U i)
        let F' := F.liftTargetOpen U hp
        ∃ M : MetricConvergenceData F',
        metricScalarAt P.metric P.basepoint = 1 ∧
        (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F' n) ∧
        (∀ z : P.M, riemannianEDistOf P.metric P.basepoint z < ENNReal.ofReal rho) ∧
        (∀ R : ℝ, 0 ≤ R → R < rho →
          IsCompact (riemannianClosedBallOf P.metric P.basepoint R)) ∧
        (∀ n, riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint (r n) ⊆
          F'.target n) ∧
        ∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop, ∀ z ∈ F'.source n, ∀ v : TangentSpace ThreeModel z,
          (1 - eps) * P.metric.inner z v v ≤
            (X.obj (f n)).metric.inner (F'.map n z)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v) ∧
          (X.obj (f n)).metric.inner (F'.map n z)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v) ≤
            (1 + eps) * P.metric.inner z v v := by
  have hvol := RetainedCoreHistory.normalized_terminal_ball_volume_lower_bound_of_scaled_tests
    Phi hPhi P₀ H s G L hinit hs x q Q hq hqQ hQ hderiv hfinal hpinch hpinchFinal
      hbuffer σ hκ hσ₀ hσQ htested
  obtain ⟨f, hf, r, hr, hrlim, P, F, M, hM, hradial, hcompactP, hcapture, hbounds⟩ :=
    ObservedHistory.exists_terminal_pointed_convergence_of_buffered_backward_traces
      Phi hPhi (fun n => (H n).toHistory) (fun n => Fin.last (H n).eventCount) s G L hinit
      x q Q hq hqQ hQ (fun n j _ => hderiv n j) hfinal (fun n j _ => hpinch n j)
      hpinchFinal hrho (by
        intro R hR hRrho
        obtain ⟨r, A, θ, hr, hrrho, hA, hθ, hbudget, hb⟩ := hbuffer R hR hRrho
        refine ⟨r, A, θ, hr, hrrho, hA, hθ, hbudget, ?_⟩
        filter_upwards [hb] with n hn
        obtain ⟨first, htrace, hstart⟩ := hn.2.2
        exact ⟨hn.1, hn.2.1, first, Fin.le_last first, htrace, hstart⟩) hvol
  have hbase : metricScalarAt P.metric P.basepoint = 1 :=
    Perelman.KappaSolutions.pointedScalar_base_eq_of_metricCG_canonical_domains M hM (by
      intro n
      change metricScalarAt (scaleMetric (Q (f n)) (zero_lt_one.trans_le (hQ (f n)))
        (L (f n)).metric) (x (f n)) = 1
      rw [metricScalarAt_scaleMetric, ← hscale (f n), inv_mul_cancel₀]
      exact ne_of_gt (zero_lt_one.trans_le (hQ (f n))))
  exact ⟨f, hf, r, hr, hrlim, P, F, M, hbase, hM, hradial, hcompactP, hcapture, hbounds⟩

theorem RetainedCoreHistory.exists_nonnegative_local_flow_with_comparison_of_final_slab_window
    (P₀ : ℕ → OrientedThreeStage.{u}) (H : ∀ n, RetainedCoreHistory (P₀ n)) (s : ℕ → ℝ)
    (A : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).ClosedSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (hinit : ∀ n, (A n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (Ctime : ℝ≥0) (q : ℕ → ℝ) (hq : ∀ n, 0 < q n)
    (hderiv : ∀ n (j : Fin (H n).eventCount) (y : ((H n).stage j.castSucc).Carrier),
      ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
        q n < ((H n).toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H n).toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H n).toHistory.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ n y, ∀ t ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (s n),
      q n < (A n).flow.scalar t y →
      |derivWithin (fun v => (A n).flow.scalar v y) (Iic t) t| ≤
        Ctime * (A n).flow.scalar t y ^ 2)
    (x : ∀ n, ((A n).restrictIncoming le_rfl (A n).lt le_rfl).terminalRegularOpen)
    (Q : ℕ → ℝ) (hQ : ∀ n, 1 ≤ Q n) (hqQ : ∀ n, q n ≤ Q n)
    (hQlim : Tendsto Q atTop atTop)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ n j, Perelman.PhiAlmostNonnegative ((H n).toHistory.event j).incoming.flow
      (Ico ((H n).time j.castSucc) ((H n).time j.succ)) Phi)
    (hpinchFinal : ∀ n, Perelman.PhiAlmostNonnegative
      ((A n).restrictIncoming le_rfl (A n).lt le_rfl).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) Phi)
    (hbuffer : ∀ R : ℝ, 0 < R → R < 1 → ∃ r Amax θ : ℝ,
      0 < r ∧ R + r < 1 ∧ 1 ≤ Amax ∧ 0 < θ ∧ 6 * Ctime * (Amax * θ) ≤ 1 ∧
      ∀ᶠ n in atTop,
        IsCompact (riemannianClosedBallOf (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n))
          ((A n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))).metric)
          (x n) (R + r)) ∧
        (∀ z ∈ riemannianClosedBallOf (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n))
          ((A n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))).metric)
          (x n) (R + r), metricScalarAt
            ((A n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))).metric
            z ≤ 2 * (Amax * Q n)) ∧
        ∃ first : Fin ((H n).eventCount + 1),
          (∀ z ∈ riemannianClosedBallOf (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n))
            ((A n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))).metric)
            (x n) (R + r), Nonempty (BackwardPointTrace (H n).toHistory first
              (Fin.last (H n).eventCount) (Fin.le_last first) z.val)) ∧
          (H n).time first ≤ s n - θ / Q n)
    (hs : ∀ n, (H n).horizon < s n)
    (hscale : ∀ n, Q n = metricScalarAt
      ((A n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))).metric (x n))
    {κ σ₀ : ℝ} (σ : ℕ → ℝ) (hκ : 0 < κ) (hσ₀ : 0 < σ₀)
    (hσQ : ∀ n, σ₀ ≤ σ n * Real.sqrt (Q n))
    (htested : ∀ n (t : ℝ) (ht : (H n).horizon < t) (hts : t < s n),
      let B := (H n).extendHorizon t ht.le
        (((A n).restrictIncoming le_rfl (A n).lt le_rfl).closedPrefix t
          ((H n).time_le_horizon.trans_lt ht) hts) (hinit n)
      let tm : Icc (0 : ℝ) B.horizon := ⟨t, (H n).horizon_nonneg.trans ht.le, le_rfl⟩
      ∀ (y : (B.toHistory.stageAt tm).Carrier) (b : ℝ), 0 < b → b ≤ σ n →
        B.toHistory.isParabolicallyRmControlledBall tm y b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
              (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
              (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm) y b))
    {N : Type v} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
    [T2Space N] (Hn : ℕ → SmoothRiemannianMetric ThreeModel N) (xN : ℕ → N)
    (B : ∀ n, PartialDiffeomorph ThreeModel ThreeModel N
      ((A n).restrictIncoming le_rfl (A n).lt le_rfl).terminalRegularOpen ∞)
    {R : ℝ} (hR : 0 < R)
    (hBsource : ∀ n, riemannianClosedBallOf (Hn n) (xN n) R ⊆ (B n).source)
    (hBbase : ∀ n, B n (xN n) = x n)
    (hcapture : ∀ n, riemannianClosedBallOf (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n))
      ((A n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))).metric)
      (x n) (R / 4) ⊆ (B n) '' riemannianClosedBallOf (Hn n) (xN n) R)
    (hBconv : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      ∀ y ∈ riemannianClosedBallOf (Hn n) (xN n) R, ∀ v : TangentSpace ThreeModel y,
        (1 - eta) * (Hn n).inner y v v ≤ (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n))
          ((A n).endpointTerminalLimitMetric
            ((H n).stage (Fin.last (H n).eventCount))).metric).inner
            (B n y) (mfderiv ThreeModel ThreeModel (B n) y v)
            (mfderiv ThreeModel ThreeModel (B n) y v) ∧
        (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n))
          ((A n).endpointTerminalLimitMetric
            ((H n).stage (Fin.last (H n).eventCount))).metric).inner
            (B n y) (mfderiv ThreeModel ThreeModel (B n) y v)
            (mfderiv ThreeModel ThreeModel (B n) y v) ≤ (1 + eta) * (Hn n).inner y v v) :
    ∃ (j : ℕ → ℕ) (_ : StrictMono j) (P₂ : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
      (V : TopologicalSpace.Opens P₂.M)
      (hp : P₂.basepoint ∈ V) (_ : PathConnectedSpace V) (tau : ℝ) (htau : 0 < tau)
      (g : ℝ → SmoothRiemannianMetric ThreeModel V),
      g 0 = P₂.metric.restrictOpen V ∧ metricScalarAt P₂.metric P₂.basepoint = 1 ∧
      IsSolutionOn ({ base.metric := g } : SolutionOn (I := ThreeModel) (M := V)
        (RealTimeInterval.closed (-tau) 0 (by linarith))) ∧
      (∀ t ∈ Icc (-tau) 0, ∀ y : V, metricAlgebraicCurvatureTensorAt (g t) y ∈
        algebraicCurvatureOperatorNonnegativeCone (I := ThreeModel)) ∧
      ∃ C : ℕ → PartialDiffeomorph ThreeModel ThreeModel V N ∞,
        (∀ n, C n ⟨P₂.basepoint, hp⟩ = xN (j n)) ∧
        ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r) ∧
        (∀ᶠ n in atTop, riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r ⊆ (C n).source ∧
          riemannianClosedBallOf (Hn (j n)) (xN (j n)) (r / 4) ⊆
            (C n) '' riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r) ∧
        ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
          ∀ a ∈ riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r,
          ∀ b ∈ riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r,
            |(riemannianEDistOf (Hn (j n)) (C n a) (C n b)).toReal -
              (riemannianEDistOf (g 0) a b).toReal| < eta := by
  let G := fun n => (A n).restrictIncoming le_rfl (A n).lt le_rfl
  let L := fun n => (A n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))
  have hconv := RetainedCoreHistory.exists_normalized_terminal_pointed_convergence_of_scaled_tests
    Phi hPhi P₀ H s G L hinit hs x q Q hscale hq hqQ hQ hderiv hfinal hpinch hpinchFinal one_pos
    hbuffer σ hκ hσ₀ hσQ htested
  dsimp only at hconv
  obtain ⟨f₂, hf₂, _, _, _, P₂, F₂, M, hbase₂, hcanonical, hradial, hcompact, _, _⟩ := hconv
  let F := PointedRiemannianConvergenceMaps.liftTargetOpen
    (S := { obj := fun n =>
          { M := (G n).terminalRegularOpen
            basepoint := x n
            metric := scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric } })
    (fun i => connectedComponentOpen (I := ThreeModel) (x i))
    (fun i => (mem_connectedComponent : x i ∈ connectedComponentOpen (I := ThreeModel) (x i))) F₂
  let V : TopologicalSpace.Opens P₂.M := ⟨riemannianBallOf P₂.metric P₂.basepoint (1 / 2),
    isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ _) continuous_const⟩
  have hp : P₂.basepoint ∈ V := by
    change riemannianEDistOf P₂.metric P₂.basepoint P₂.basepoint < ENNReal.ofReal (1 / 2)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  have hpath : PathConnectedSpace V := isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_riemannianBallOf P₂.metric P₂.basepoint (by norm_num))
  have hVc : IsCompact (closure (V : Set P₂.M)) := by
    apply (hcompact (1 / 2) (by norm_num) (by norm_num)).of_isClosed_subset isClosed_closure
    refine closure_minimal (fun z (hz : riemannianEDistOf P₂.metric P₂.basepoint z <
      ENNReal.ofReal (1 / 2)) => (le_of_lt hz : riemannianEDistOf P₂.metric P₂.basepoint z ≤
        ENNReal.ofReal (1 / 2))) ?_
    exact isClosed_le (Geometry.Riemannian.continuous_riemannianEDist _ _) continuous_const
  have hupper : ∀ K : Set P₂.M, IsCompact K → ∀ C : ℝ, 1 < C → ∀ᶠ i in atTop,
      ∀ z ∈ K, ∀ v : TangentSpace ThreeModel z,
        (scaleMetric (Q (f₂ i)) (zero_lt_one.trans_le (hQ (f₂ i)))
          (L (f₂ i)).metric).inner (F.map i z)
          (mfderiv ThreeModel ThreeModel (F.map i) z v)
          (mfderiv ThreeModel ThreeModel (F.map i) z v) ≤ C ^ 2 * P₂.metric.inner z v v := by
    intro K hK C hC
    have hconv : metricSourceConvergesOn F
        (CanonicalMetricCompactness.canonicalSourceData F) K 0 := by
      have heq : M.domain = CanonicalMetricCompactness.canonicalSourceData F := funext hcanonical
      rw [← heq]
      exact M.converges K hK 0
    filter_upwards [pointed_metric_eventually_quadratic_bounds hK hconv
      (by nlinarith : 0 < C ^ 2 - 1)] with i hi
    intro z hz v
    simpa only [add_sub_cancel] using (hi.2 z hz v).2
  have hbuffer' : ∀ R : ℝ, 0 < R → R < 1 → ∃ r Amax θ : ℝ,
      0 < r ∧ R + r < 1 ∧ 1 ≤ Amax ∧ 0 < θ ∧ 6 * Ctime * (Amax * θ) ≤ 1 ∧ ∀ᶠ i in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q (f₂ i)) (zero_lt_one.trans_le (hQ (f₂ i))) (L (f₂ i)).metric)
          (x (f₂ i)) (R + r)) ∧
        (∀ z ∈ riemannianClosedBallOf
          (scaleMetric (Q (f₂ i)) (zero_lt_one.trans_le (hQ (f₂ i))) (L (f₂ i)).metric)
          (x (f₂ i)) (R + r), metricScalarAt (L (f₂ i)).metric z ≤ 2 * (Amax * Q (f₂ i))) ∧
        ∃ first : Fin ((H (f₂ i)).eventCount + 1),
          ∃ hle : first ≤ Fin.last (H (f₂ i)).eventCount,
          (∀ z ∈ riemannianClosedBallOf
            (scaleMetric (Q (f₂ i)) (zero_lt_one.trans_le (hQ (f₂ i))) (L (f₂ i)).metric)
            (x (f₂ i)) (R + r),
            Nonempty (BackwardPointTrace (H (f₂ i)).toHistory first
              (Fin.last (H (f₂ i)).eventCount) hle z.val)) ∧
          (H (f₂ i)).time first ≤ s (f₂ i) - θ / Q (f₂ i) := by
    intro R hR hR1
    obtain ⟨r, Amax, θ, hr, hRr, hA, hθ, hbud, hev⟩ := hbuffer R hR hR1
    refine ⟨r, Amax, θ, hr, hRr, hA, hθ, hbud, ?_⟩
    filter_upwards [hf₂.tendsto_atTop.eventually hev] with i hi
    obtain ⟨first, htr, hst⟩ := hi.2.2
    exact ⟨hi.1, hi.2.1, first, Fin.le_last first, htr, hst⟩
  open ObservedHistory in
  obtain ⟨Rr, rr, Amax, θ, hθ, Bd, _, _, _, _, _, hBd, hev⟩ :=
    exists_eventually_historical_solution_with_curvature_bounds_of_pointed_convergence
      (fun n => (H n).toHistory) (fun n => Fin.last (H n).eventCount) G x L hinit q Q hq hqQ hQ F
      one_pos hradial hcompact hupper Phi hPhi (fun n j _ => hderiv n j) hfinal
      (fun n j _ => hpinch n j) hpinchFinal hbuffer' V hVc
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  choose first hle Ψ hΨ hFv gflow S hsource _ _ _ hstart _ _ hS hzero hmetric hslabs hlast _
    hcurv using fun j : ℕ => hN (j + N) (Nat.le_add_left N j)
  have hsh : StrictMono (fun j : ℕ => j + N) := fun a b h => Nat.add_lt_add_right h N
  let F₃ := F.compSubseq (fun j => j + N) hsh
  let M₃ := M.compSubseq (fun j => j + N) hsh
  have hcan₃ (j : ℕ) : M₃.domain j = CanonicalMetricCompactness.canonicalSourceData F₃ j := by
    change (M.domain (j + N)).compSubseq _ hsh j = _
    rw [hcanonical (j + N)]
    rfl
  have hterm : ∀ j (z : V) (v w : TangentSpace ThreeModel z),
      ((S j).base.metric 0).inner z v w =
        (scaleMetric (Q (f₂ (j + N))) (zero_lt_one.trans_le (hQ (f₂ (j + N))))
          (L (f₂ (j + N))).metric).inner (F₃.partialDiffeomorph j z)
          (mfderiv ThreeModel ThreeModel (F₃.partialDiffeomorph j) z v)
          (mfderiv ThreeModel ThreeModel (F₃.partialDiffeomorph j) z w) := by
    intro j z v w
    refine (congrArg (fun g : SmoothRiemannianMetric ThreeModel V => g.inner z v w)
      (hzero j)).trans ?_
    exact localPullMetric_restrict_inner _ (F.partialDiffeomorph (j + N)) V (hFv j) z v w
  have hcurv' : ∀ K : Set V, IsCompact K → ∀ m : ℕ, ∃ B' : ℝ, 0 ≤ B' ∧ ∀ᶠ j in atTop,
      ∀ t ∈ Icc (-(θ / 2)) 0, ∀ z ∈ K, curvDerivNorm m ((S j).base.metric t) z ≤ B' :=
    fun _ _ m => ⟨Bd m, hBd m, Eventually.of_forall fun j t ht z _ => hcurv j m t ht z⟩
  have hpa (j : ℕ) : Perelman.PhiAlmostNonnegative (S j) (Icc (-θ) 0)
      (Perelman.rescalePinchingFunction (Q (f₂ (j + N))) Phi) :=
    ObservedHistory.phiAlmostNonnegative_parabolic_backwardSurvivorIncomingFootprint_localPullback
      (H (f₂ (j + N))).toHistory (first j) (Fin.last (H (f₂ (j + N))).eventCount)
      (hle j) (G (f₂ (j + N))) (L (f₂ (j + N)))
      (riemannianClosedBallOf (scaleMetric (Q (f₂ (j + N))) (zero_lt_one.trans_le (hQ _))
        (L (f₂ (j + N))).metric) (x (f₂ (j + N))) (Rr + rr))
      (gflow j) (hslabs j) (hlast j) hPhi.contDiff.continuous
      (fun jj _ _ => hpinch (f₂ (j + N)) jj) (hpinchFinal (f₂ (j + N)))
      (zero_lt_one.trans_le (hQ (f₂ (j + N)))) (hstart j) (Ψ j) (hΨ j) (S j)
      (fun v _ => hmetric j v)
  have hpinching : ∀ t ∈ Icc (-(θ / 2)) 0, ∀ᶠ j in atTop, ∀ z : V,
      curvatureOperatorLowerBoundAt ((S j).base.metric t) z
        (metricAlgebraicCurvatureTensorAt ((S j).base.metric t) z)
        (Perelman.rescalePinchingFunction (Q (f₂ (j + N))) Phi
          (metricScalarAt ((S j).base.metric t) z)) := by
    intro t ht
    exact Eventually.of_forall fun j z => hpa j t ⟨by linarith [ht.1], ht.2⟩ z
  have hBconv' : ∀ eta : ℝ, 0 < eta → ∀ᶠ j in atTop,
      ∀ y ∈ riemannianClosedBallOf (Hn (f₂ (j + N))) (xN (f₂ (j + N))) R,
      ∀ v : TangentSpace ThreeModel y,
        (1 - eta) * (Hn (f₂ (j + N))).inner y v v ≤
          (scaleMetric (Q (f₂ (j + N))) (zero_lt_one.trans_le (hQ (f₂ (j + N))))
            (L (f₂ (j + N))).metric).inner (B (f₂ (j + N)) y)
            (mfderiv ThreeModel ThreeModel (B (f₂ (j + N))) y v)
            (mfderiv ThreeModel ThreeModel (B (f₂ (j + N))) y v) ∧
        (scaleMetric (Q (f₂ (j + N))) (zero_lt_one.trans_le (hQ (f₂ (j + N))))
          (L (f₂ (j + N))).metric).inner (B (f₂ (j + N)) y)
          (mfderiv ThreeModel ThreeModel (B (f₂ (j + N))) y v)
          (mfderiv ThreeModel ThreeModel (B (f₂ (j + N))) y v) ≤
            (1 + eta) * (Hn (f₂ (j + N))).inner y v v :=
    fun eta heta => (hf₂.comp hsh).tendsto_atTop.eventually (hBconv eta heta)
  obtain ⟨_, _, g, hgb, hsol, hnonneg, _, r, hr, hcpt, hcenter, hcap, hdist⟩ :=
    DifferentialGeometry.PDE.RicciFlow.exists_nonnegative_local_flow_with_end_comparison
      F₃ M₃ hcan₃ V hp (fun j => hsource j) S hS (a := -(θ / 2)) (b := 0) (by linarith)
      (fun t ht => ⟨by linarith [ht.1], ht.2⟩) (fun t ht => ⟨by linarith [ht.1], ht.2⟩)
      hterm hcurv' hPhi (fun j => Q (f₂ (j + N))) (fun j => zero_lt_one.trans_le (hQ _))
      (hQlim.comp (hf₂.comp hsh).tendsto_atTop) hpinching
      (fun j => Hn (f₂ (j + N))) (fun j => xN (f₂ (j + N))) (fun j => B (f₂ (j + N))) hR
      (fun j => hBsource _) (fun j => hBbase _) (fun j => hcapture _) hBconv'
  exact ⟨fun j => f₂ (j + N), hf₂.comp hsh, P₂, V, hp, hpath, θ / 2, by positivity, g, hgb,
    hbase₂, hsol, hnonneg, _, hcenter, r, hr, hcpt, hcap, hdist⟩

theorem RetainedCoreHistory.final_slab_scalar_buffer_of_spatialCanonicalWitness
    (P₀ : ℕ → OrientedThreeStage.{u}) (H : ∀ m, RetainedCoreHistory (P₀ m)) (time : ℕ → ℝ)
    (A : ∀ m, ((H m).stage (Fin.last (H m).eventCount)).ClosedSlab
      ((H m).time (Fin.last (H m).eventCount)) (time m))
    (Ctime : ℝ≥0) (q : ℕ → ℝ)
    (y : ∀ m, ((A m).restrictIncoming le_rfl (A m).lt le_rfl).terminalRegularOpen)
    (Q₂ : ℕ → ℝ) (hQ₂ : ∀ m, 1 ≤ Q₂ m)
    (hQ₂y : ∀ m, Q₂ m = (A m).flow.scalar (time m) (y m).val)
    {eps C1 C2 : ℝ} (hC2 : 1 ≤ C2)
    (hW : ∀ m z, q m < (A m).flow.scalar (time m) z →
      ∃ W : SpatialCanonicalWitness ((A m).flow.base.metric (time m)) eps C1 C2 z,
        W.capTubeHasNeckChart eps)
    (hqy : ∀ᶠ m in atTop, q m < (A m).flow.scalar (time m) (y m).val)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (hwindow : ∀ m, (H m).time (Fin.last (H m).eventCount) ≤ time m - θ₀ / Q₂ m) :
    ∀ R : ℝ, 0 < R → R < 1 → ∃ r Amax θ : ℝ,
      0 < r ∧ R + r < 1 ∧ 1 ≤ Amax ∧ 0 < θ ∧ 6 * Ctime * (Amax * θ) ≤ 1 ∧
      ∀ᶠ m in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q₂ m) (zero_lt_one.trans_le (hQ₂ m))
            ((A m).endpointTerminalLimitMetric ((H m).stage (Fin.last (H m).eventCount))).metric)
          (y m) (R + r)) ∧
        (∀ z ∈ riemannianClosedBallOf
          (scaleMetric (Q₂ m) (zero_lt_one.trans_le (hQ₂ m))
            ((A m).endpointTerminalLimitMetric ((H m).stage (Fin.last (H m).eventCount))).metric)
          (y m) (R + r),
          metricScalarAt
            ((A m).endpointTerminalLimitMetric ((H m).stage (Fin.last (H m).eventCount))).metric z ≤
            2 * (Amax * Q₂ m)) ∧
        ∃ first : Fin ((H m).eventCount + 1),
          (∀ z ∈ riemannianClosedBallOf
            (scaleMetric (Q₂ m) (zero_lt_one.trans_le (hQ₂ m))
              ((A m).endpointTerminalLimitMetric ((H m).stage (Fin.last (H m).eventCount))).metric)
            (y m) (R + r),
            Nonempty (BackwardPointTrace (H m).toHistory first
              (Fin.last (H m).eventCount) (Fin.le_last first) z.val)) ∧
          (H m).time first ≤ time m - θ / Q₂ m := by
    intro R hR hR1
    let r := (1 - R) / 2
    have hr : 0 < r := by dsimp only [r]; linarith
    have hRr : R + r < 1 := by dsimp only [r]; linarith
    let θ := min θ₀ (1 / (6 * ((Ctime : ℝ) + 1) * C2))
    have hθ : 0 < θ := lt_min hθ₀ (by positivity)
    have hθθ₀ : θ ≤ θ₀ := min_le_left _ _
    have hθbudget : θ * (6 * ((Ctime : ℝ) + 1) * C2) ≤ 1 :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have hbudget : 6 * (Ctime : ℝ) * (C2 * θ) ≤ 1 := by
      have hC : (0 : ℝ) ≤ Ctime := Ctime.coe_nonneg
      nlinarith [mul_nonneg (zero_le_one.trans hC2) hθ.le]
    refine ⟨r, C2, θ, hr, hRr, hC2, hθ, hbudget, ?_⟩
    filter_upwards [hqy] with m hm
    refine ⟨isCompact_riemannianClosedBallOf_endpoint (A m) _ _ _, ?_,
      Fin.last (H m).eventCount, fun z _ =>
        ⟨BackwardPointTrace.singleton (H m).toHistory _ z.val⟩, ?_⟩
    · intro z hz
      obtain ⟨Wm, _⟩ := hW _ _ hm
      have hQ₂pos : 0 < Q₂ m := zero_lt_one.trans_le (hQ₂ m)
      have hz' := ((A m).mem_scaled_endpoint_closedBall_iff (Q₂ m) hQ₂pos (y m) z (R + r)).mp hz
      have hball : z.val ∈ riemannianBallOf ((A m).flow.base.metric (time m))
          (y m).val (Real.sqrt (metricScalarAt ((A m).flow.base.metric (time m))
            (y m).val))⁻¹ := by
        have hsq : 0 < Real.sqrt (Q₂ m) := Real.sqrt_pos.mpr hQ₂pos
        change riemannianEDistOf _ _ _ < _
        apply lt_of_le_of_lt hz'
        rw [ENNReal.ofReal_lt_ofReal_iff (by rw [inv_pos]; exact Real.sqrt_pos.mpr Wm.Q_pos)]
        change (R + r) / Real.sqrt (Q₂ m) < (Real.sqrt ((A m).flow.scalar (time m) (y m).val))⁻¹
        rw [← hQ₂y, div_lt_iff₀ hsq, inv_mul_cancel₀ hsq.ne']
        exact hRr
      have hb := (Wm.scalar_bounds _ (Wm.ball_inside
        (riemannianBallOf_mono _ _ Wm.radius_lower hball))).2
      have hLz : metricScalarAt
          ((A m).endpointTerminalLimitMetric ((H m).stage (Fin.last (H m).eventCount))).metric z =
          (A m).flow.scalar (time m) z.val :=
        metricScalarAt_restrictOpen _ _ _
      rw [hLz]
      have : (A m).flow.scalar (time m) z.val ≤ C2 * Q₂ m := by
        rw [hQ₂y]
        exact hb
      nlinarith [hQ₂pos]
    · have hdiv : θ / Q₂ m ≤ θ₀ / Q₂ m :=
        div_le_div_of_nonneg_right hθθ₀ (zero_le_one.trans (hQ₂ m))
      linarith [hwindow m]

theorem RetainedCoreHistory.exists_local_backward_limit_with_comparison_at_final_slab_end
    (P₀ : ℕ → OrientedThreeStage.{u}) (H : ∀ i, RetainedCoreHistory (P₀ i)) (time : ℕ → ℝ)
    (A : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).ClosedSlab
      ((H i).time (Fin.last (H i).eventCount)) (time i))
    (hinit : ∀ i, (A i).flow.base.metric ((H i).time (Fin.last (H i).eventCount)) =
      (H i).initialMetric (Fin.last (H i).eventCount))
    (hs : ∀ i, (H i).horizon < time i) (Ctime : ℝ≥0) (q : ℕ → ℝ) (hq : ∀ i, 0 < q i)
    (hderiv : ∀ i (j : Fin (H i).eventCount) (y : ((H i).stage j.castSucc).Carrier),
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q i < ((H i).toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).toHistory.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ i y, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      q i < (A i).flow.scalar t y →
      |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤
        Ctime * (A i).flow.scalar t y ^ 2)
    (x : ∀ i, ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (A i).flow.scalar (time i) (x i).val)
    (hqQ : ∀ i, q i ≤ (A i).flow.scalar (time i) (x i).val)
    (hqlim : Tendsto (fun i => q i / (A i).flow.scalar (time i) (x i).val) atTop (𝓝 0))
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (hwindow : ∀ i, (H i).time (Fin.last (H i).eventCount) ≤
      time i - θ₀ / (A i).flow.scalar (time i) (x i).val)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ i j, Perelman.PhiAlmostNonnegative ((H i).toHistory.event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ)) Phi)
    (hpinchFinal : ∀ i, Perelman.PhiAlmostNonnegative
      ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow
      (Ico ((H i).time (Fin.last (H i).eventCount)) (time i)) Phi)
    {κ σ₀ : ℝ} (σ : ℕ → ℝ) (hκ : 0 < κ) (hσ₀ : 0 < σ₀)
    (hσQ : ∀ i, σ₀ ≤ σ i * Real.sqrt ((A i).flow.scalar (time i) (x i).val))
    (htested : ∀ i (t : ℝ) (ht : (H i).horizon < t) (hts : t < time i),
      let B := (H i).extendHorizon t ht.le
        (((A i).restrictIncoming le_rfl (A i).lt le_rfl).closedPrefix t
          ((H i).time_le_horizon.trans_lt ht) hts) (hinit i)
      let tm : Icc (0 : ℝ) B.horizon := ⟨t, (H i).horizon_nonneg.trans ht.le, le_rfl⟩
      ∀ (y : (B.toHistory.stageAt tm).Carrier) (b : ℝ), 0 < b → b ≤ σ i →
        B.toHistory.isParabolicallyRmControlledBall tm y b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
              (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
              (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm) y b))
    {eps C1 C2 : ℝ}
    (hW : ∀ i y, q i < (A i).flow.scalar (time i) y →
      ∃ W : SpatialCanonicalWitness ((A i).flow.base.metric (time i)) eps C1 C2 y,
        W.capTubeHasNeckChart eps)
    {f : ℕ → ℕ} (hf : StrictMono f) (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (F : PointedRiemannianConvergenceMaps
      ({ obj := fun i =>
          { M := ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen
            basepoint := x i
            metric := scaleMetric ((A i).flow.scalar (time i) (x i).val)
              (zero_lt_one.trans_le (hQ i))
              ((A i).endpointTerminalLimitMetric
                ((H i).stage (Fin.last (H i).eventCount))).metric } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
    (M : MetricConvergenceData F)
    (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (W : TopologicalSpace.Opens Pl.M) (xW : ℕ → W) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hQW : ∀ n, 2 ≤ metricScalarAt Pl.metric (xW n : Pl.M))
    (hQWlim : Tendsto (fun n => metricScalarAt Pl.metric (xW n : Pl.M)) atTop atTop)
    (hcompactW : ∀ n, IsCompact (riemannianClosedBallOf (Pl.metric.restrictOpen W) (xW n)
      (4 * R₀ / Real.sqrt (metricScalarAt Pl.metric (xW n : Pl.M))))) :
    ∃ (j : ℕ → ℕ) (_ : StrictMono j) (A₂ : ℕ → ℝ) (hA₂ : ∀ n, 0 < A₂ n),
      Tendsto (fun n => A₂ n / metricScalarAt Pl.metric (xW (j n) : Pl.M)) atTop (𝓝 1) ∧
      ∃ (P₂ : PointedRiemannianManifold.{u, 0, 0} ThreeModel) (V : TopologicalSpace.Opens P₂.M)
        (hp : P₂.basepoint ∈ V) (_ : PathConnectedSpace V) (tau : ℝ) (htau : 0 < tau)
        (g : ℝ → SmoothRiemannianMetric ThreeModel V),
        g 0 = P₂.metric.restrictOpen V ∧
        IsSolutionOn ({ base.metric := g } : SolutionOn (I := ThreeModel) (M := V)
          (RealTimeInterval.closed (-tau) 0 (by linarith))) ∧
        (∀ t ∈ Icc (-tau) 0, ∀ y : V, metricAlgebraicCurvatureTensorAt (g t) y ∈
          algebraicCurvatureOperatorNonnegativeCone (I := ThreeModel)) ∧
        metricScalarAt P₂.metric P₂.basepoint = 1 ∧
        ∃ C : ℕ → PartialDiffeomorph ThreeModel ThreeModel V W ∞,
          (∀ n, C n ⟨P₂.basepoint, hp⟩ = xW (j n)) ∧
          ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r) ∧
          (∀ᶠ n in atTop, riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r ⊆ (C n).source ∧
            riemannianClosedBallOf (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
              (xW (j n)) (r / 4) ⊆ (C n) '' riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r) ∧
          ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
            ∀ a ∈ riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r,
            ∀ b ∈ riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r,
              |(riemannianEDistOf (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
                (C n a) (C n b)).toReal - (riemannianEDistOf (g 0) a b).toReal| < eta := by
  let G := fun i => (A i).restrictIncoming le_rfl (A i).lt le_rfl
  let L := fun i => (A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))
  let Q := fun i => (A i).flow.scalar (time i) (x i).val
  have hQpos : ∀ i, 0 < Q i := fun i => zero_lt_one.trans_le (hQ i)
  have hLscalar (i : ℕ) (y : (G i).terminalRegularOpen) :
      metricScalarAt (L i).metric y = (A i).flow.scalar (time i) y.val :=
    metricScalarAt_restrictOpen _ _ _
  obtain ⟨k, hk, hqk, hratio, hcmp⟩ :=
    CheegerGromovCompactness.exists_scalar_rescaled_source_comparison _ f Pl F M hcanonical W xW
      hR₀ hQW hcompactW
  let y : ∀ m, (G (f (k m))).terminalRegularOpen := fun m =>
    F.partialDiffeomorph (k m) (xW m : Pl.M)
  let qk : ℕ → ℝ := fun m => metricScalarAt
    (scaleMetric (Q (f (k m))) (hQpos _) (L (f (k m))).metric) (y m)
  let Q₂ : ℕ → ℝ := fun m => metricScalarAt (L (f (k m))).metric (y m)
  have hQ₂eq (m : ℕ) : Q₂ m = qk m * Q (f (k m)) := by
    change Q₂ m = metricScalarAt (scaleMetric (Q (f (k m))) (hQpos _) (L (f (k m))).metric)
      (y m) * Q (f (k m))
    rw [metricScalarAt_scaleMetric, mul_comm, ← mul_assoc, mul_inv_cancel₀ (hQpos _).ne',
      one_mul]
  have hqk1 (m : ℕ) : 1 ≤ qk m := hqk m
  have hQ₂ (m : ℕ) : 1 ≤ Q₂ m := by
    rw [hQ₂eq]
    nlinarith [hqk1 m, hQ (f (k m))]
  have hQQ₂ (m : ℕ) : Q (f (k m)) ≤ Q₂ m := by
    rw [hQ₂eq]
    nlinarith [hqk1 m, hQpos (f (k m))]
  have hqQ₂ (m : ℕ) : q (f (k m)) ≤ Q₂ m := (hqQ _).trans (hQQ₂ m)
  have hfk : StrictMono (fun m => f (k m)) := hf.comp hk
  have hqklim : Tendsto qk atTop atTop := by
    have hhalf : ∀ᶠ m in atTop, (1 / 2 : ℝ) < qk m / metricScalarAt Pl.metric (xW m : Pl.M) :=
      hratio.eventually (eventually_gt_nhds (by norm_num))
    apply tendsto_atTop_mono' atTop _ ((hQWlim.atTop_div_const (by norm_num : (0 : ℝ) < 2)))
    filter_upwards [hhalf] with m hm
    have hR := (by linarith [hQW m] : (0 : ℝ) < metricScalarAt Pl.metric (xW m : Pl.M))
    have := (lt_div_iff₀ hR).mp hm
    linarith
  have hQ₂lim : Tendsto Q₂ atTop atTop :=
    tendsto_atTop_mono (fun m =>
      (le_mul_of_one_le_right (by linarith [hqk1 m]) (hQ (f (k m)))).trans_eq
      (hQ₂eq m).symm) hqklim
  have hqy : ∀ᶠ m in atTop, q (f (k m)) < (A (f (k m))).flow.scalar (time (f (k m))) (y m).val := by
    filter_upwards [(hqlim.comp hfk.tendsto_atTop).eventually (eventually_lt_nhds one_pos)]
      with m hm
    have h1 : q (f (k m)) < Q (f (k m)) := by
      have := (div_lt_iff₀ (hQpos (f (k m)))).mp hm
      linarith
    rw [← hLscalar]
    exact h1.trans_le (hQQ₂ m)
  obtain ⟨m₀, hm₀⟩ := hqy.exists
  obtain ⟨W₀, _⟩ := hW _ _ hm₀
  have hC2 : 1 ≤ C2 := W₀.one_le_comparison_constant
  have hbuffer₂ := RetainedCoreHistory.final_slab_scalar_buffer_of_spatialCanonicalWitness
    (fun m => P₀ (f (k m))) (fun m => H (f (k m))) (fun m => time (f (k m)))
    (fun m => A (f (k m))) Ctime (fun m => q (f (k m))) y Q₂ hQ₂ (fun m => hLscalar _ _) hC2
    (fun m => hW (f (k m))) hqy hθ₀ (fun m => (hwindow (f (k m))).trans
      (sub_le_sub_left (div_le_div_of_nonneg_left hθ₀.le (hQpos _) (hQQ₂ m)) _))
  have hσpos (i : ℕ) : 0 < σ i := by
    by_contra hneg
    have h1 : σ i * Real.sqrt ((A i).flow.scalar (time i) (x i).val) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) (Real.sqrt_nonneg _)
    linarith [hσQ i]
  let inc := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := ThreeModel) W ⟨xW 0⟩
  let Fcmp := fun m => inc.trans (F.partialDiffeomorph (k m))
  let Gcmp := fun m => scaleMetric (qk m) (lt_of_lt_of_le zero_lt_one (hqk1 m))
    (Pl.metric.restrictOpen W)
  have hHeq (m : ℕ) := scaleMetric_mul_eq (L (f (k m))).metric
    (lt_of_lt_of_le zero_lt_one (hqk1 m)) (hQpos (f (k m))) (zero_lt_one.trans_le (hQ₂ m))
    (hQ₂eq m)
  have hcapture (m : ℕ) : riemannianClosedBallOf
      (scaleMetric (Q₂ m) (zero_lt_one.trans_le (hQ₂ m)) (L (f (k m))).metric) (y m) (R₀ / 4) ⊆
        (Fcmp m) '' riemannianClosedBallOf (Gcmp m) (xW m) R₀ := by
    rw [hHeq m]
    exact (hcmp m).2.2.2.1
  have hBconv : ∀ eta : ℝ, 0 < eta → ∀ᶠ m in atTop,
      ∀ z ∈ riemannianClosedBallOf (Gcmp m) (xW m) R₀, ∀ v : TangentSpace ThreeModel z,
        (1 - eta) * (Gcmp m).inner z v v ≤
          (scaleMetric (Q₂ m) (zero_lt_one.trans_le (hQ₂ m)) (L (f (k m))).metric).inner
            (Fcmp m z) (mfderiv ThreeModel ThreeModel (Fcmp m) z v)
            (mfderiv ThreeModel ThreeModel (Fcmp m) z v) ∧
        (scaleMetric (Q₂ m) (zero_lt_one.trans_le (hQ₂ m)) (L (f (k m))).metric).inner
            (Fcmp m z) (mfderiv ThreeModel ThreeModel (Fcmp m) z v)
            (mfderiv ThreeModel ThreeModel (Fcmp m) z v) ≤ (1 + eta) * (Gcmp m).inner z v v := by
    intro eta heta
    have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
    filter_upwards [hlim.eventually (eventually_lt_nhds heta)] with m hm
    intro z hz v
    rw [hHeq m]
    have hh := (hcmp m).2.2.1 z hz v
    have hg := metric_inner_self_nonneg (Gcmp m) z v
    exact ⟨(mul_le_mul_of_nonneg_right (by linarith : 1 - eta ≤ 1 - 1 / ((m : ℝ) + 2)) hg).trans
      hh.1, hh.2.trans (mul_le_mul_of_nonneg_right
        (by linarith : 1 + 1 / ((m : ℝ) + 2) ≤ 1 + eta) hg)⟩
  obtain ⟨j, hj, P₂, V, hp, hpath, tau, htau, g, hgb, hbase₂, hsol, hnonneg, C, hcenter, r, hr,
      hcpt, hcap, hdist⟩ :=
    RetainedCoreHistory.exists_nonnegative_local_flow_with_comparison_of_final_slab_window
      (fun m => P₀ (f (k m))) (fun m => H (f (k m))) (fun m => time (f (k m)))
      (fun m => A (f (k m))) (fun m => hinit _) Ctime (fun m => q (f (k m))) (fun m => hq _)
      (fun m => hderiv _) (fun m => hfinal _) y Q₂ hQ₂ hqQ₂ hQ₂lim hPhi (fun m => hpinch _)
      (fun m => hpinchFinal _) hbuffer₂ (fun m => hs _) (fun m => rfl) (fun m => σ (f (k m)))
      hκ hσ₀ (fun m => (hσQ (f (k m))).trans (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (hQQ₂ m)) (hσpos _).le)) (fun m => htested (f (k m)))
      Gcmp xW Fcmp hR₀ (fun m => (hcmp m).2.1) (fun m => rfl) hcapture hBconv
  exact ⟨j, hj, fun n => qk (j n), fun n => lt_of_lt_of_le zero_lt_one (hqk1 (j n)),
    hratio.comp hj.tendsto_atTop, P₂, V, hp, hpath, tau, htau, g, hgb, hsol, hnonneg, hbase₂, C,
    hcenter, r, hr, hcpt, hcap, hdist⟩

theorem RetainedCoreHistory.final_slab_punctured_cone_end_exclusion
    (P₀ : ℕ → OrientedThreeStage.{u}) (H : ∀ i, RetainedCoreHistory (P₀ i)) (time : ℕ → ℝ)
    (A : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).ClosedSlab
      ((H i).time (Fin.last (H i).eventCount)) (time i))
    (hinit : ∀ i, (A i).flow.base.metric ((H i).time (Fin.last (H i).eventCount)) =
      (H i).initialMetric (Fin.last (H i).eventCount))
    (hs : ∀ i, (H i).horizon < time i) (Ctime : ℝ≥0) (q : ℕ → ℝ) (hq : ∀ i, 0 < q i)
    (hderiv : ∀ i (j : Fin (H i).eventCount) (y : ((H i).stage j.castSucc).Carrier),
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q i < ((H i).toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).toHistory.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ i y, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      q i < (A i).flow.scalar t y →
      |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤
        Ctime * (A i).flow.scalar t y ^ 2)
    (x : ∀ i, ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (A i).flow.scalar (time i) (x i).val)
    (hqQ : ∀ i, q i ≤ (A i).flow.scalar (time i) (x i).val)
    (hqlim : Tendsto (fun i => q i / (A i).flow.scalar (time i) (x i).val) atTop (𝓝 0))
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (hwindow : ∀ i, (H i).time (Fin.last (H i).eventCount) ≤
      time i - θ₀ / (A i).flow.scalar (time i) (x i).val)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ i j, Perelman.PhiAlmostNonnegative ((H i).toHistory.event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ)) Phi)
    (hpinchFinal : ∀ i, Perelman.PhiAlmostNonnegative
      ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow
      (Ico ((H i).time (Fin.last (H i).eventCount)) (time i)) Phi)
    {κ σ₀ : ℝ} (σ : ℕ → ℝ) (hκ : 0 < κ) (hσ₀ : 0 < σ₀)
    (hσQ : ∀ i, σ₀ ≤ σ i * Real.sqrt ((A i).flow.scalar (time i) (x i).val))
    (htested : ∀ i (t : ℝ) (ht : (H i).horizon < t) (hts : t < time i),
      let B := (H i).extendHorizon t ht.le
        (((A i).restrictIncoming le_rfl (A i).lt le_rfl).closedPrefix t
          ((H i).time_le_horizon.trans_lt ht) hts) (hinit i)
      let tm : Icc (0 : ℝ) B.horizon := ⟨t, (H i).horizon_nonneg.trans ht.le, le_rfl⟩
      ∀ (y : (B.toHistory.stageAt tm).Carrier) (b : ℝ), 0 < b → b ≤ σ i →
        B.toHistory.isParabolicallyRmControlledBall tm y b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
              (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
              (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm) y b))
    {eps C1 C2 : ℝ}
    (hW : ∀ i y, q i < (A i).flow.scalar (time i) y →
      ∃ W : SpatialCanonicalWitness ((A i).flow.base.metric (time i)) eps C1 C2 y,
        W.capTubeHasNeckChart eps)
    {f : ℕ → ℕ} (hf : StrictMono f) (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (F : PointedRiemannianConvergenceMaps
      ({ obj := fun i =>
          { M := ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen
            basepoint := x i
            metric := scaleMetric ((A i).flow.scalar (time i) (x i).val)
              (zero_lt_one.trans_le (hQ i))
              ((A i).endpointTerminalLimitMetric
                ((H i).stage (Fin.last (H i).eventCount))).metric } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
    (M : MetricConvergenceData F)
    (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (W : TopologicalSpace.Opens Pl.M) (hWc : PathConnectedSpace W) :
    let _ : PathConnectedSpace W := hWc
    let _ : PseudoMetricSpace W := (Pl.metric.restrictOpen W).toPseudoMetricSpace
    let _ : MetricSpace W := MetricSpace.ofT0PseudoMetricSpace W
    ∀ (qW : UniformSpace.Completion W) (delta : ℝ), 0 < delta →
      IsCompact (Metric.closedBall qW delta) →
      Metric.closedBall qW delta ⊆
        insert qW (range (fun z : W => (z : UniformSpace.Completion W))) →
      Nonempty (DifferentialGeometry.Toponogov.PuncturedConeApproximation qW delta) →
      ∀ xW : ℕ → W, Tendsto (fun n => (xW n : UniformSpace.Completion W)) atTop (𝓝 qW) →
      Tendsto (fun n => metricScalarAt Pl.metric (xW n : Pl.M)) atTop atTop →
      ∀ c : ℝ, 0 < c →
      (∀ᶠ n in atTop, c ≤ metricScalarAt Pl.metric (xW n : Pl.M) *
        dist (xW n : UniformSpace.Completion W) qW ^ 2) →
      (∃ B : ℝ, ∀ᶠ n in atTop, metricScalarAt Pl.metric (xW n : Pl.M) *
        dist (xW n : UniformSpace.Completion W) qW ^ 2 ≤ B) → False := by
  intro instPath instPseudo instMetric
  let _ : PathConnectedSpace W := instPath
  let _ : PseudoMetricSpace W := instPseudo
  let _ : MetricSpace W := instMetric
  intro qW delta hdelta hK hcover hcone xW hx hQW c hc hlower hupper
  obtain ⟨B, hB⟩ := hupper
  have hd0 : Tendsto (fun n => dist (xW n : UniformSpace.Completion W) qW) atTop (𝓝 0) :=
    (tendsto_iff_dist_tendsto_zero).mp hx
  let R₀ := min 1 (Real.sqrt c / 8)
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hR₀ : 0 < R₀ := lt_min one_pos (by positivity)
  have hev : ∀ᶠ n in atTop, 2 ≤ metricScalarAt Pl.metric (xW n : Pl.M) ∧
      c ≤ metricScalarAt Pl.metric (xW n : Pl.M) * dist (xW n : UniformSpace.Completion W) qW ^ 2 ∧
      metricScalarAt Pl.metric (xW n : Pl.M) * dist (xW n : UniformSpace.Completion W) qW ^ 2 ≤ B ∧
      dist (xW n : UniformSpace.Completion W) qW < delta / 2 := by
    filter_upwards [hQW.eventually_ge_atTop 2, hlower, hB,
      hd0.eventually (eventually_lt_nhds (half_pos hdelta))] with n h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  let xW' : ℕ → W := fun n => xW (n + N)
  have hN' (n : ℕ) := hN (n + N) (Nat.le_add_left N n)
  have hcompactW : ∀ n, IsCompact (riemannianClosedBallOf (Pl.metric.restrictOpen W) (xW' n)
      (4 * R₀ / Real.sqrt (metricScalarAt Pl.metric (xW' n : Pl.M)))) := by
    intro n
    obtain ⟨h1, h2, _, h4⟩ := hN' n
    have hRn : 0 < metricScalarAt Pl.metric (xW' n : Pl.M) := by linarith
    have hsR := Real.sqrt_pos.mpr hRn
    have hdn : 0 < dist (xW' n : UniformSpace.Completion W) qW := by
      rcases (dist_nonneg (x := (xW' n : UniformSpace.Completion W)) (y := qW)).lt_or_eq
        with hlt | heq
      · exact hlt
      · exfalso
        change c ≤ metricScalarAt Pl.metric (xW' n : Pl.M) *
          dist (xW' n : UniformSpace.Completion W) qW ^ 2 at h2
        rw [← heq] at h2
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h2
        linarith
    have hcd : Real.sqrt c ≤ Real.sqrt (metricScalarAt Pl.metric (xW' n : Pl.M)) *
        dist (xW' n : UniformSpace.Completion W) qW := by
      rw [← Real.sqrt_sq hdn.le, ← Real.sqrt_mul hRn.le]
      exact Real.sqrt_le_sqrt h2
    have hrad : 4 * R₀ / Real.sqrt (metricScalarAt Pl.metric (xW' n : Pl.M)) ≤
        dist (xW' n : UniformSpace.Completion W) qW / 2 := by
      rw [div_le_iff₀ hsR]
      have hR8 : R₀ ≤ Real.sqrt c / 8 := min_le_right _ _
      nlinarith
    have hball : riemannianClosedBallOf (Pl.metric.restrictOpen W) (xW' n)
        (4 * R₀ / Real.sqrt (metricScalarAt Pl.metric (xW' n : Pl.M))) =
          Metric.closedBall (xW' n)
            (4 * R₀ / Real.sqrt (metricScalarAt Pl.metric (xW' n : Pl.M))) := by
      ext z
      change edist (xW' n) z ≤ ENNReal.ofReal _ ↔ dist z (xW' n) ≤ _
      rw [edist_dist, ENNReal.ofReal_le_ofReal_iff (by positivity), dist_comm]
    rw [hball]
    have h4' : dist (xW' n : UniformSpace.Completion W) qW < delta / 2 := h4
    exact isCompact_closedBall_of_lt_dist_puncture hK hcover (xW' n) (by linarith) (by linarith)
  have hQW' : Tendsto (fun n => metricScalarAt Pl.metric (xW' n : Pl.M)) atTop atTop :=
    hQW.comp (tendsto_add_atTop_nat N)
  obtain ⟨j, hj, A₂, hA₂, hratio, P₂, V, hp, hpath, tau, htau, g, hgb, hsol, hnonneg, hbase₂,
      C, hcenter, r, hr, hcpt, hcap, hdist⟩ :=
    RetainedCoreHistory.exists_local_backward_limit_with_comparison_at_final_slab_end P₀ H time A
      hinit hs Ctime q hq hderiv hfinal x hQ hqQ hqlim hθ₀ hwindow hPhi hpinch hpinchFinal σ hκ
      hσ₀ hσQ htested hW hf Pl F M hcanonical W xW' hR₀ (fun n => (hN' n).1) hQW' hcompactW
  let _ : PseudoMetricSpace V := (P₂.metric.restrictOpen V).toPseudoMetricSpace
  let _ : MetricSpace V := MetricSpace.ofT0PseudoMetricSpace V
  let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)
  let S : SolutionOn (I := ThreeModel) (M := V)
      (RealTimeInterval.closed (-tau) 0 (by linarith)) := { base.metric := g }
  have hsec : ∀ t ∈ Icc (-tau) 0, SecLower (S.base.metric t) 0 univ := by
    intro t ht z _ v w
    have h := (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional
      (g t) z (by simp [ThreeSpace])).mp (hnonneg t ht z) v w
    have hslots : (fun i => ![v, w, w, v] i) = vec4 (I := ThreeModel) v w w v := by
      funext i
      fin_cases i <;> rfl
    simpa only [S, zero_mul, metricRm04StandardAt_apply, hslots] using h
  have hmetric0 : ∀ a b : V, edist a b = riemannianEDistOf (S.base.metric 0) a b := by
    intro a b
    change edist a b = riemannianEDistOf (g 0) a b
    rw [hgb]
    rfl
  let p : V := ⟨P₂.basepoint, hp⟩
  have hscalar0 : metricScalarAt (S.base.metric 0) p ≠ 0 := by
    change metricScalarAt (g 0) p ≠ 0
    rw [hgb, metricScalarAt_restrictOpen, hbase₂]
    norm_num
  have hRj : Tendsto (fun n => metricScalarAt Pl.metric (xW' (j n) : Pl.M)) atTop atTop :=
    hQW'.comp hj.tendsto_atTop
  have hcmp : ∀ᶠ n in atTop, metricScalarAt Pl.metric (xW' (j n) : Pl.M) / 2 ≤ A₂ n ∧
      A₂ n ≤ 2 * metricScalarAt Pl.metric (xW' (j n) : Pl.M) := by
    filter_upwards [hratio.eventually (Ioo_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)
      (by norm_num : (1 : ℝ) < 2))] with n hn
    have hRpos : 0 < metricScalarAt Pl.metric (xW' (j n) : Pl.M) := by linarith [(hN' (j n)).1]
    have hl := (lt_div_iff₀ hRpos).mp hn.1
    have hu := (div_lt_iff₀ hRpos).mp hn.2
    exact ⟨by linarith, hu.le⟩
  have hAtop : Tendsto A₂ atTop atTop :=
    tendsto_atTop_mono' atTop (hcmp.mono fun _ h => h.1)
      (hRj.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  let rho := fun n => 1 / Real.sqrt (A₂ n)
  have hrho (n : ℕ) : 0 < rho n := one_div_pos.mpr (Real.sqrt_pos.mpr (hA₂ n))
  have hrho0 : Tendsto rho atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hAtop)
  have hballP : riemannianClosedBallOf (g 0) p r = Metric.closedBall p r := by
    rw [hgb]
    ext z
    change edist p z ≤ ENNReal.ofReal r ↔ dist z p ≤ r
    rw [edist_dist, ENNReal.ofReal_le_ofReal_iff hr.le, dist_comm]
  have hballH (n : ℕ) : riemannianClosedBallOf
      (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W)) (xW' (j n)) (r / 4) =
        Metric.closedBall (xW' (j n)) (r / 4 * rho n) := by
    have hscale : r / 4 = Real.sqrt (A₂ n) * (r / 4 * rho n) := by
      dsimp only [rho]
      field_simp [(Real.sqrt_pos.mpr (hA₂ n)).ne']
    conv_lhs => rw [hscale]
    rw [riemannianClosedBallOf_scaleMetric]
    ext z
    change edist (xW' (j n)) z ≤ ENNReal.ofReal (r / 4 * rho n) ↔ dist z (xW' (j n)) ≤ _
    rw [edist_dist, ENNReal.ofReal_le_ofReal_iff (by have := hrho n; positivity), dist_comm]
  have hdistH (n : ℕ) (a b : W) : (riemannianEDistOf
      (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W)) a b).toReal = dist a b / rho n := by
    rw [edistOf_scale, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    change Real.sqrt (A₂ n) * (edist a b).toReal = _
    rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg]
    dsimp only [rho]
    rw [one_div, div_inv_eq_mul, mul_comm]
  have hdistP (a b : V) : (riemannianEDistOf (g 0) a b).toReal = dist a b := by
    rw [hgb]
    change (edist a b).toReal = _
    rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  apply solution_not_rescaled_cone_limit (M := V) htau S hsol hmetric0 hsec p hscalar0
    hcone.some (fun n => xW' (j n)) (fun n z => C n z) rho hrho hrho0 hcenter hr
    (lower := Real.sqrt (c / 2)) (B := Real.sqrt (max 1 (2 * B)) + 1)
    (Real.sqrt_pos.mpr (half_pos hc)) (hballP ▸ hcpt)
  · filter_upwards [hcmp] with n hn
    obtain ⟨_, h2, h3, _⟩ := hN' (j n)
    set d := dist ((xW' (j n) : W) : UniformSpace.Completion W) qW
    have hd0 : 0 ≤ d := dist_nonneg
    have hdiv : d / rho n = Real.sqrt (A₂ n) * d := by
      dsimp only [rho]
      rw [one_div, div_inv_eq_mul, mul_comm]
    have hsq : (Real.sqrt (A₂ n) * d) ^ 2 = A₂ n * d ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (hA₂ n).le]
    have hz : 0 ≤ Real.sqrt (A₂ n) * d := mul_nonneg (Real.sqrt_nonneg _) hd0
    change c ≤ metricScalarAt Pl.metric (xW' (j n) : Pl.M) * d ^ 2 at h2
    change metricScalarAt Pl.metric (xW' (j n) : Pl.M) * d ^ 2 ≤ B at h3
    rw [hdiv]
    constructor
    · have hlow : c / 2 ≤ (Real.sqrt (A₂ n) * d) ^ 2 := by
        rw [hsq]
        have := mul_le_mul_of_nonneg_right hn.1 (sq_nonneg d)
        nlinarith
      calc Real.sqrt (c / 2) ≤ Real.sqrt ((Real.sqrt (A₂ n) * d) ^ 2) := Real.sqrt_le_sqrt hlow
        _ = Real.sqrt (A₂ n) * d := Real.sqrt_sq hz
    · have hup : (Real.sqrt (A₂ n) * d) ^ 2 ≤ max 1 (2 * B) := by
        rw [hsq]
        have := mul_le_mul_of_nonneg_right hn.2 (sq_nonneg d)
        exact (by nlinarith : A₂ n * d ^ 2 ≤ 2 * B).trans (le_max_right _ _)
      have := Real.le_sqrt_of_sq_le hup
      linarith
  · filter_upwards [hcap] with n hn
    rw [← hballH n, ← hballP]
    exact hn.2
  · intro eta heta
    filter_upwards [hdist eta heta] with n hn
    intro a ha b hb
    have h := hn a (hballP ▸ ha) b (hballP ▸ hb)
    rw [hdistH, hdistP] at h
    exact h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
