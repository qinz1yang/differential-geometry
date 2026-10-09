import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KSWGuardedTTCC11KX

/-!
# KSW-EXIT G6：叶 S1（Cone）证书（O-CH11-KSWEXIT，后缀 `_C11KX`）

G5 剩余 binder S1 = `GuardedConeLeaf_C11KX`（Cone:50 `…_scaled_tests_age_C11KS2` 的 guarded 形）。Cone 证明
里 U 侧数据只经两个树内叶：`hball`（`exists_uniform_parabolically_controlled_incoming_terminal_ball_radius_
window_P6WA`，hderiv / hfinal）与终端体积叶（htested）。两处都在 buffer 球（`R(L) ≤ 2·A·Q`）上、窗口
`[s − θ/(A·Q), s)`、`6·C·θ ≤ 1` ⇒ 把 `U` 缩成 `U′ := U ∩ {Rtop ≤ 2·A·Q}`，guard 由
`guardKX_of_ceiling_C11KX`（`C·(2AQ)·(θ/(AQ)) = 2·C·θ ≤ 1/3`）付；
event slab 上 `t < time j⁺ ≤ time last < s`。
* `guardedConeLeaf_C11KX : GuardedConeLeaf_C11KX`（**S1 PROVED**）；
* consumer `shortSLT_guarded_of_tc_C11KX`（PROVISIONAL[T4 TC]）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

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

open ObservedHistory in
/-- **叶 S1 证书（`_C11KX`，PROVED）**：guarded Cone ⇐ Cone:50 证明逐字；两个树内叶调用点
（`exists_uniform_parabolically_controlled_incoming_terminal_ball_radius_window_P6WA` 的 `hball` 与
`normalized_terminal_volume_ball_ge_of_tested_incomingFootprint_flow_ball_window_P6WA`）把 `U` 缩成
`U′ := U ∩ {Rtop ≤ 2·A·Q}`，guard 由 `6·C·θ ≤ 1`（深度 `θ/(A·Q)`、ceiling `2·A·Q`）付。 -/
theorem guardedConeLeaf_C11KX : GuardedConeLeaf_C11KX.{u} := by
  intro Phi hPhi C H s G L hinit hs x q Q Rtop hRtop hq hqQ hQ U c hQc hderiv hfinal hpinch
    hpinchFinal rho hU hbuffer κ σ₀ σ hκ hσ₀ hσQ htested r R hr hrR hRrho J hJ
  obtain ⟨β, hβ, hQcβ⟩ := hQc
  obtain ⟨b, A, θ1, hb, hbr, hA, hθ1, hbudget1, hbuf⟩ := hbuffer r hr (hrR.trans hRrho)
  obtain ⟨θ0, hθ0, hθ01, hθ0β⟩ : ∃ θ0 : ℝ, 0 < θ0 ∧ θ0 ≤ θ1 ∧ θ0 ≤ β :=
    ⟨min θ1 β, lt_min hθ1 hβ, min_le_left _ _, min_le_right _ _⟩
  have hbudget : 6 * C * (A * θ0) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hθ01 (zero_le_one.trans hA))
      (by positivity)).trans hbudget1
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
    exists_uniform_parabolically_controlled_incoming_terminal_ball_radius_window_P6WA
      hPhi hθ
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
  filter_upwards [hbuf, hQcβ] with n hn hcn y hy
  obtain ⟨first, htrace, hstart1⟩ := hn.2.2
  have hQp : 0 < Q n := zero_lt_one.trans_le (hQ n)
  have hstart : (H n).time first ≤ s n - θ0 / Q n :=
    hstart1.trans (by linarith [div_le_div_of_nonneg_right hθ01 hQp.le])
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
    have hθβ : θ / A ≤ β := (div_le_iff₀ hAp).mpr
      (hθA.trans ((mul_comm A θ0).trans_le (mul_le_mul_of_nonneg_right hθ0β hAp.le)))
    have h1 : θ ≤ Q n * (s n - c n) * A := (div_le_iff₀ hAp).mp (hθβ.trans hcn)
    have h2 : θ / (A * Q n) ≤ s n - c n := by
      rw [div_le_iff₀ (mul_pos hAp hQp)]
      calc θ ≤ Q n * (s n - c n) * A := h1
        _ = (s n - c n) * (A * Q n) := by ring
    linarith
  have hIci : Ici (s n - θ / (A * Q n)) ⊆ Ici (c n) := Ici_subset_Ici.mpr hwn
  have hbudget' : 6 * C * θ ≤ 1 :=
    (mul_le_mul_of_nonneg_left hθA (by positivity)).trans hbudget
  have hAQp : 0 < A * Q n := mul_pos hAp hQp
  have hMc : (C : ℝ) * (2 * (A * Q n)) * (θ / (A * Q n)) ≤ 1 / 2 := by
    have h1 : (C : ℝ) * (2 * (A * Q n)) * (θ / (A * Q n)) =
        2 * ((C : ℝ) * θ) * ((A * Q n) / (A * Q n)) := by ring
    rw [h1, div_self hAQp.ne', mul_one]
    nlinarith [hbudget']
  have hqM : q n ≤ 2 * (A * Q n) := by
    have := le_mul_of_one_le_left hQp.le hA
    linarith [hqQ n]
  let U' : Set ((H n).stage (Fin.last (H n).eventCount)).Carrier :=
    {z | z ∈ U n ∧ Rtop n z ≤ 2 * (A * Q n)}
  have hgd : ∀ z ∈ U', ∀ t, t ≤ s n → s n - θ / (A * Q n) ≤ t →
      GuardKX_C11KX (Rtop n) (q n) C (s n) t z :=
    fun z hz t hts hst => guardKX_of_ceiling_C11KX C.coe_nonneg hz.2 hqM hts hst hMc
  have hjs : ∀ j : Fin (H n).eventCount, (H n).time j.succ ≤ s n :=
    fun j => ((H n).time_strictMono.monotone (Fin.le_last j.succ)).trans (G n).lt.le
  have hyU' : ∀ z ∈ riemannianClosedBallOf (L n).metric y (b / Real.sqrt (Q n)),
      z.val ∈ U' := by
    intro z hz
    refine ⟨hyU z hz, ?_⟩
    rw [← hRtop n z]
    exact hn.2.1 z (hsub hz)
  obtain ⟨p, S, _, _, _, _, hslabs, hlast, B, _, hBRadius, hB, _, himage, _, _⟩ :=
    hball (H n).toHistory first (Fin.last (H n).eventCount) (Fin.le_last first) (G n) (L n) y
      hAQ (hinit n) (div_pos hb hsqrtQ) hcompact U' hyU' (hq n)
      ((hqQ n).trans (le_mul_of_one_le_left hQp.le hA))
      (fun j hf _ z hz B t ht hct hqt => hderiv n j first hf z hz.1 B t ht (hwn.trans hct) hqt
        (hgd z hz t (ht.2.le.trans (hjs j)) hct))
      (fun z hz t ht hct hqt => hfinal n z.val (hyU z hz) t ht (hwn.trans hct) hqt
        (hgd z.val (hyU' z hz) t ht.2.le hct))
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
    (fun j hf => hslabs j hf (Fin.le_last _)) hlast U' (x n) y
    (hyU' y (by
      change riemannianEDistOf (L n).metric y y ≤ ENNReal.ofReal (b / Real.sqrt (Q n))
      rw [riemannianEDistOf_self]
      exact bot_le))
    hQp hr.le
    (by linarith [hab.le]) B hB hBr hn.1 hy (by simpa only [hBRadius] using himage) hBσ
    (fun t ht hts hct => by
      intro _ _ z hz
      exact htested n t ht hts (hwn.trans hct) z hz.1 (hgd z hz t hts.le hct))

/-- **consumer（G6，PROVISIONAL[T4 TC]）**：S1 / S2 由证书付清，只剩 TC 叶 T4。 -/
theorem shortSLT_guarded_of_tc_C11KX (hT4 : GuardedTCLeaf_C11KX.{u}) {θ : ℝ} (hθ : 0 < θ) :
    ShortSLTGuarded_C11KX.{u} θ :=
  shortSLT_guarded_of_cone_tc_C11KX guardedConeLeaf_C11KX hT4 hθ

/-- consumer：T4 ⇒ K-SW（`0 < θ₀ ≤ 1/2`）。 -/
example (hT4 : GuardedTCLeaf_C11KX.{u}) {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hθ₀2 : θ₀ ≤ 1 / 2) :
    KSW_C11KS.{u} θ₀ :=
  ksw_of_shortSLT_C11KS hθ₀ hθ₀2
    (ShortSLTGuarded_C11KX.toShortSLT (shortSLT_guarded_of_tc_C11KX hT4 hθ₀))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
