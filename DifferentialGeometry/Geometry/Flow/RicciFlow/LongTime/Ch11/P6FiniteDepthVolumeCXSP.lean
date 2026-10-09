import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceConeWindow_P6WA

set_option autoImplicit false

/-!
# CX-SPINE G3：固定正归一深度与固定正 κ尺度下的 terminal volume producer

源证明：Local/BoundedCurvatureAtDistanceConeWindow_P6WA:52–231。保留实际 tested κ、
trace buffer、窗口导数与 pinching；将深度趋无穷改为统一正下界 β。
内部 θ 同时受 Aβ/2 控制，重新取 controlled-ball 半径，输出真实 terminal volume 下界。
归一化 κ测试尺度只要求固定 σ₀>0，不要求趋无穷。
-/

noncomputable section

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

open ObservedHistory in
/-- 固定正深度与固定正归一 κ测试半径足以生产 compactness 所需的 terminal volume 界。 -/
theorem RetainedCoreHistory.normalized_terminal_volume_of_fixed_depth_CXSP
    (Phi : ℝ → ℝ) (hPhi : Perelman.AdmissiblePinchingFunction Phi) {C : ℝ≥0}
    (H : ℕ → RetainedCoreHistory.{u})
    (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (hinit : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hs : ∀ n, (H n).horizon < s n)
    (x : ∀ n, (G n).terminalRegularOpen) (q Q : ℕ → ℝ)
    (hq : ∀ n, 0 < q n) (hqQ : ∀ n, q n ≤ Q n) (hQ : ∀ n, 1 ≤ Q n)
    (U : ∀ n, Set ((H n).stage (Fin.last (H n).eventCount)).Carrier) (c : ℕ → ℝ)
    {β : ℝ} (hβ : 0 < β)
    (hdepth : ∀ᶠ n in atTop, β ≤ Q n * (s n - c n))
    (hderiv : ∀ n, ∀ j : Fin (H n).eventCount,
      ∀ (first : Fin ((H n).eventCount + 1)) (hf : first ≤ j.castSucc),
      ∀ z ∈ U n, ∀ A : BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
        (Fin.le_last first) z,
      ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ), c n ≤ t →
      q n < ((H n).toHistory.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun v => ((H n).toHistory.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (Fin.le_last _))) (Iic t) t| ≤
        C * ((H n).toHistory.event j).incoming.flow.scalar t
          (A.point j.castSucc hf (Fin.le_last _)) ^ 2)
    (hfinal : ∀ n, ∀ y ∈ U n,
      ∀ t ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (s n), c n ≤ t →
      q n < (G n).flow.scalar t y →
      |derivWithin (fun v => (G n).flow.scalar v y) (Iic t) t| ≤ C * (G n).flow.scalar t y ^ 2)
    (hpinch : ∀ n, ∀ j : Fin (H n).eventCount,
      Perelman.PhiAlmostNonnegative ((H n).toHistory.event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ) ∩ Ici (c n)) Phi)
    (hpinchFinal : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∩ Ici (c n)) Phi)
    {rho : ℝ}
    (hU : ∀ n, ∀ y ∈ riemannianBallOf
      (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) rho, y.val ∈ U n)
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
    (htested : ∀ n (t : ℝ) (ht : (H n).horizon < t) (hts : t < s n), c n ≤ t →
      let A := (H n).extendHorizon t ht.le
        ((G n).closedPrefix t ((H n).time_le_horizon.trans_lt ht) hts) (hinit n)
      let time : Icc (0 : ℝ) A.horizon := ⟨t, (H n).horizon_nonneg.trans ht.le, le_rfl⟩
      ∀ z ∈ U n, ∀ (y : (A.toHistory.stageAt time).Carrier), HEq y z →
      ∀ (b : ℝ), 0 < b → b ≤ σ n →
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
  obtain ⟨b, A, θ0, hb, hbr, hA, hθ0, hbudget, hbuf⟩ := hbuffer r hr (hrR.trans hRrho)
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
  let θ := min (A * θ0) (min ((a0 * Real.sqrt A) ^ 2) (A * β / 2))
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθA : θ ≤ A * θ0 := min_le_left _ _
  have hθsq : θ ≤ (a0 * Real.sqrt A) ^ 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hθβ : θ ≤ A * β / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hθdiv : θ / A ≤ β := by
    apply (div_le_iff₀ hAp).mpr
    nlinarith [mul_pos hAp hβ]
  obtain ⟨α, hα, _, hαθ, hball⟩ :=
    exists_uniform_parabolically_controlled_incoming_terminal_ball_radius_window_P6WA
      hPhi hθ
  have hαa0 : α ≤ a0 * Real.sqrt A := by
    have hh : α ^ 2 ≤ (a0 * Real.sqrt A) ^ 2 := hαθ.trans hθsq
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
  filter_upwards [hbuf, hdepth] with n hn hβn y hy
  have hcn : θ / A ≤ Q n * (s n - c n) := hθdiv.trans hβn
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
  have hrho : 0 < rho := hr.trans (hrR.trans hRrho)
  have hyU : ∀ z ∈ riemannianClosedBallOf (L n).metric y (b / Real.sqrt (Q n)), z.val ∈ U n :=
    fun z hz => hU n z (riemannianClosedBallOf_subset_riemannianBallOf_P6L _ _ hbr hrho (hsub hz))
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
  have hwn : c n ≤ s n - θ / (A * Q n) := by
    have h1 : θ ≤ Q n * (s n - c n) * A := (div_le_iff₀ hAp).mp hcn
    have h2 : θ / (A * Q n) ≤ s n - c n := by
      rw [div_le_iff₀ (mul_pos hAp hQp)]
      calc θ ≤ Q n * (s n - c n) * A := h1
        _ = (s n - c n) * (A * Q n) := by ring
    linarith
  have hIci : Ici (s n - θ / (A * Q n)) ⊆ Ici (c n) := Ici_subset_Ici.mpr hwn
  have hbudget' : 6 * C * θ ≤ 1 :=
    (mul_le_mul_of_nonneg_left hθA (by positivity)).trans hbudget
  obtain ⟨p, S, _, _, _, _, hslabs, hlast, B, _, hBRadius, hB, _, himage, _, _⟩ :=
    hball (H n).toHistory first (Fin.last (H n).eventCount) (Fin.le_last first) (G n) (L n) y
      hAQ (hinit n) (div_pos hb hsqrtQ) hcompact (U n) hyU (hq n)
      ((hqQ n).trans (le_mul_of_one_le_left hQp.le hA))
      (fun j hf _ z hz B t ht hct => hderiv n j first hf z hz B t ht (hwn.trans hct))
      (fun z hz t ht hct => hfinal n z.val (hyU z hz) t ht (hwn.trans hct))
      (fun j _ _ => RetainedCoreHistory.phiAlmostNonnegative_mono_P6N (hpinch n j)
        (inter_subset_inter_right _ hIci))
      (RetainedCoreHistory.phiAlmostNonnegative_mono_P6N (hpinchFinal n)
        (inter_subset_inter_right _ hIci))
      (fun z hz => hn.2.1 z (hsub hz)) (fun z hz => htrace z (hsub hz)) hstart' hbudget'
      (by rw [hradius]; exact (div_lt_div_iff_of_pos_right hsqrtQ).mpr hab)
  have hBr : B.radius = a / Real.sqrt (Q n) := hBRadius.trans hradius
  have hBσ : B.radius ≤ σ n := by
    rw [hBr, div_le_iff₀ hsqrtQ]
    exact (haa0.trans ha0σ).trans (hσQ n)
  exact (H n).normalized_terminal_volume_ball_ge_of_tested_incomingFootprint_flow_ball_window_P6WA
    (G n) (L n) (hinit n) (hs n) first
    (riemannianClosedBallOf (L n).metric y (b / Real.sqrt (Q n))) hstart'
    (sub_le_self _ (div_nonneg hθ.le (mul_pos hAp hQp).le)) S
    (fun j hf => hslabs j hf (Fin.le_last _)) hlast (U n) (x n) y
    (hU n y (riemannianClosedBallOf_subset_riemannianBallOf_P6L _ _ (hrR.trans hRrho) hrho hy))
    hQp hr.le
    (by linarith [hab.le]) B hB hBr hn.1 hy (by simpa only [hBRadius] using himage) hBσ
    (fun t ht hts hct => htested n t ht hts (hwn.trans hct))


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
