import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.SliceDichotomyLateCg_P6LS3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HcenProducerP6HE
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarCurvature

/-!
# incoming-slab terminal localized BCD 的 K 层 kernel（O-CH11-BCDT G1a，后缀 `_P6BT`）

HFOOT 遗留 F2 `hlocBCD` 的两块 K 层零件（不含 tower / selected family）：
* **`RetainedCoreHistory.terminal_scalar_bound_P6BT`（terminal kernel）**：P6LS3
  `slice_scalar_bound_of_not_capWindowPoint_window_pinch_P6LS3`（P6WB 局部化 SLT 窗口 kernel 的 K 层单切片包装，
  常数 `∃ Q Λ Dcap Rrad ζ₀ Rad Bw` 在 history 之前）取 `A' = 2A`、`Cq' = 2Cq`，在 event `j` 的 incoming slab 上
  对 `t → s⁻`（`s = time j.succ`）的每个切片、基点 `w = x.1` 实例化，再取 terminal 极限：
  `TerminalLimitMetric.eventually_riemannianEDistOf_lt`（`B_ḡ(x, A/√R_k) ⊆ B_t(x, A/√R_k)`
  eventually）+
  `TerminalLimitMetric.tendsto_metricScalarAt`（`R(t, ·) → R_ḡ`）；`R_ḡ(x) = R_k` ⇒
  eventually `R_k/2 < R(t, x) < 2R_k`，故 `QA = 2Q`。U 侧 CN 只要求在 `B_t(x, 2·Rad/√R_k)` 上
  （eventually in `t`）。
  slab 导数 / 梯度用全局阈值 `qd ≤ q` 形（derivative supply），κ 用 slab 内 tested 形（κ supply），
  pinching 逐 event 全 slab（HI supply），records 为 late 形，`¬CWP` 为 late 展开形（eventually in `t`）。
* **`RetainedCoreHistory.eventually_witness_of_hwin_P6BT`（CN 局部化）**：selection 的 `hwin`
  （seed-trace 距离区域、阈值 `4R`）+ pre-surgery 种子距离余量 `hmargin`
  （`d_t(O⁻, p′) ≤ d_σ(O(σ), y) + L/(2√R)`，t → s⁻；来源 DIST `surgery_no_shortcut_C11D`）⇒
  eventually in `t`，`B_t(p′, r)`（`r ≤ L/(2√R)`）上阈值 `q ≥ 4R` 以上的 incoming-slab spatial witness。
  证明 = 三角不等式 + slab HEq 管线（照 `hcenE_history_P6HE` / `hW_of_selection_P6M`）。
* 小引理：`scalar_eq_of_heq_P6BT`（`σ = time i.succ` 处 `R(σ, y) = R⁺(q)`，HFOOT `_P6PF` 副本）、
  `witness_heq_P6BT`（witness 沿 stage / metric / 点 HEq 搬运）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn

/-- witness 沿 stage / metric / 点的 HEq 搬运。 -/
theorem witness_heq_P6BT {A B : OrientedThreeStage.{u}} (hAB : A = B) {gA : A.Metric}
    {gB : B.Metric} (hg : HEq gA gB) {a : A.Carrier} {b : B.Carrier} (hab : HEq a b)
    {ε C1 C2 : ℝ}
    (h : ∃ W : SpatialCanonicalWitness gA ε C1 C2 a, W.capTubeHasNeckChart ε) :
    ∃ W : SpatialCanonicalWitness gB ε C1 C2 b, W.capTubeHasNeckChart ε := by
  subst hAB
  cases eq_of_heq hg
  cases eq_of_heq hab
  exact h

namespace ObservedHistory

/-- `σ = time i.succ` 处 `R(σ, y) = R⁺(q)`（`HEq y q`；HFOOT `scalar_eq_of_heq_P6PF` 副本）。 -/
theorem scalar_eq_of_heq_P6BT (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    {σ : Icc (0 : ℝ) H.horizon} (hσ : (σ : ℝ) = H.time i.succ) {y : (H.stageAt σ).Carrier}
    {q : (H.stage i.succ).Carrier} (hq : HEq y q) :
    metricScalarAt (H.stageMetric (H.activeStage σ) σ) y =
      metricScalarAt (H.event i).outputMetric q := by
  obtain rfl : σ = H.stageTime i.succ := Subtype.ext hσ
  have hP : H.stageAt (H.stageTime i.succ) = H.stage i.succ :=
    congrArg H.stage (H.activeStage_stageTime i.succ)
  have hg : HEq (H.stageMetric (H.activeStage (H.stageTime i.succ)) (H.stageTime i.succ))
      (H.event i).outputMetric :=
    (ObservedHistory.stageMetric_heq_of_idx_P6S2 H (H.activeStage_stageTime i.succ) _).trans
      (heq_of_eq ((H.stageMetric_initial i.succ).trans (H.event_output i).symm))
  exact scalar_heq_P6ST2 hP hg hq

end ObservedHistory

namespace RetainedCoreHistory

/-- **CN 局部化（`_P6BT`）**：`hwin`（seed-trace 区域 CN，阈值 `4R`）+ pre-surgery 种子距离余量
`hmargin`（t → s⁻）⇒ eventually in `t`，incoming slab `B_t(p′, r)`（`r ≤ L/(2√R)`）上阈值 `q ≥ 4R`
以上的 spatial witness。 -/
theorem eventually_witness_of_hwin_P6BT (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {Tn aSeed σ : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn)
    {pT : (K.toHistory.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    (hsT : σ ≤ Tn) (has : aSeed ≤ σ) (hσ : (σ : ℝ) = K.time j.succ)
    (y : (K.toHistory.stageAt σ).Carrier) {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (haσ : (aSeed : ℝ) < σ)
    (hwin : ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ (2 : ℕ) / R ≤ (v : ℝ) →
      ∀ z : (K.toHistory.stageAt v).Carrier,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        4 * R ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v) z →
        K.toHistory.HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z)
    (h1 : K.toHistory.activeStage aSeed ≤ j.castSucc)
    (h2 : j.castSucc ≤ K.toHistory.activeStage Tn) (p' : (K.stage j.castSucc).Carrier)
    (hmargin : ∀ᶠ t in 𝓝[<] K.time j.succ,
      riemannianEDistOf (K.toHistory.stageMetric j.castSucc t) (seedTrace.point j.castSucc h1 h2)
          p' ≤
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
            (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
              (K.toHistory.activeStage_mono hsT)) y +
          ENNReal.ofReal (L / (2 * Real.sqrt R)))
    {r q : ℝ} (hr : r ≤ L / (2 * Real.sqrt R)) (hq : 4 * R ≤ q) :
    ∀ᶠ t in 𝓝[<] K.time j.succ, ∀ x' : (K.stage j.castSucc).Carrier,
      riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric t) p' x' <
          ENNReal.ofReal r →
      q < (K.toHistory.event j).incoming.flow.scalar t x' →
      ∃ W : SpatialCanonicalWitness ((K.toHistory.event j).incoming.flow.base.metric t)
        ε C1 C2 x', W.capTubeHasNeckChart ε := by
  have hs : K.time j.castSucc < K.time j.succ := K.time_strictMono Fin.castSucc_lt_succ
  have hLR : 0 < L ^ (2 : ℕ) / R := by positivity
  have haσ' : (aSeed : ℝ) < K.time j.succ := hσ ▸ haσ
  filter_upwards [hmargin, Ioo_mem_nhdsLT hs, Ioo_mem_nhdsLT haσ',
    Ioo_mem_nhdsLT (show K.time j.succ - L ^ (2 : ℕ) / R < K.time j.succ by linarith)]
    with t hmt ht1 ht2 ht3 x' hx' hqx
  have h0 : (0 : ℝ) ≤ t := (K.toHistory.time_nonneg _).trans ht1.1.le
  have hH : t ≤ K.toHistory.horizon :=
    ht1.2.le.trans (K.toHistory.time_le_horizon_at j.succ)
  let t' : Icc (0 : ℝ) K.toHistory.horizon := ⟨t, h0, hH⟩
  have hact : K.toHistory.activeStage t' = j.castSucc :=
    K.toHistory.activeStage_eq_castSucc_P6ST2 j t' ht1.1.le ht1.2
  have hav : aSeed ≤ t' := Subtype.coe_le_coe.mp ht2.1.le
  have hvs : t' ≤ σ := by
    change t ≤ (σ : ℝ)
    rw [hσ]
    exact ht3.2.le
  have hwinT : (σ : ℝ) - L ^ (2 : ℕ) / R ≤ (t' : ℝ) := by
    change (σ : ℝ) - L ^ (2 : ℕ) / R ≤ t
    rw [hσ]
    exact ht3.1.le
  let x'' : (K.toHistory.stageAt t').Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hact.symm) x'
  have hxx : HEq x'' x' := cast_heq _ _
  have hdeq : riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage t') t')
      (seedTrace.point (K.toHistory.activeStage t') (K.toHistory.activeStage_mono hav)
        (K.toHistory.activeStage_mono (hvs.trans hsT))) x'' =
      riemannianEDistOf (K.toHistory.stageMetric j.castSucc t)
        (seedTrace.point j.castSucc h1 h2) x' :=
    edist_heq_P6ST4 (congrArg K.toHistory.stage hact)
      (ObservedHistory.stageMetric_heq_of_idx_P6S2 K.toHistory hact t)
      (seedTrace.point_heq_P6HE hact _ _ _ _) hxx
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hhalf : L / (2 * Real.sqrt R) + L / (2 * Real.sqrt R) = L / Real.sqrt R := by
    field_simp
    ring
  have hLh : 0 ≤ L / (2 * Real.sqrt R) := by positivity
  have hx'' : riemannianEDistOf (K.toHistory.stageMetric j.castSucc t) p' x' <
      ENNReal.ofReal r := by
    rw [ObservedHistory.stageMetric_castSucc_apply]
    exact hx'
  have hdist : riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage t') t')
      (seedTrace.point (K.toHistory.activeStage t') (K.toHistory.activeStage_mono hav)
        (K.toHistory.activeStage_mono (hvs.trans hsT))) x'' ≤
      riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / Real.sqrt R) := by
    rw [hdeq]
    calc riemannianEDistOf (K.toHistory.stageMetric j.castSucc t)
          (seedTrace.point j.castSucc h1 h2) x'
        ≤ riemannianEDistOf (K.toHistory.stageMetric j.castSucc t)
            (seedTrace.point j.castSucc h1 h2) p' +
          riemannianEDistOf (K.toHistory.stageMetric j.castSucc t) p' x' :=
          riemannianEDistOf_triangle _ _ _ _
      _ ≤ (riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
            (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
              (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / (2 * Real.sqrt R))) + ENNReal.ofReal (L / (2 * Real.sqrt R)) :=
          add_le_add hmt (hx''.le.trans (ENNReal.ofReal_le_ofReal hr))
      _ = _ := by rw [add_assoc, ← ENNReal.ofReal_add hLh hLh, hhalf]
  have hsc : metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage t') t') x'' =
      (K.toHistory.event j).incoming.flow.scalar t x' :=
    scalar_heq_P6ST2 (congrArg K.toHistory.stage hact)
      (ObservedHistory.stageMetric_slab_heq_P6ST2 j (t := t') ht1.1.le ht1.2) hxx
  have hgood := hwin t' hav hvs hwinT x'' hdist (by rw [hsc]; linarith)
  exact witness_heq_P6BT (congrArg K.toHistory.stage hact)
    (ObservedHistory.stageMetric_slab_heq_P6ST2 j (t := t') ht1.1.le ht1.2) hxx hgood.1

/-- `√Rk ≤ 2√Rt`（`Rk ≤ 4Rt`）。 -/
private theorem sqrt_le_two_mul_sqrt_P6BT {a b : ℝ} (h : a ≤ 4 * b) :
    Real.sqrt a ≤ 2 * Real.sqrt b := by
  have h4 : Real.sqrt (4 * b) = 2 * Real.sqrt b := by
    rw [Real.sqrt_mul (by norm_num) b, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [← h4]
  exact Real.sqrt_le_sqrt h

/-- **terminal kernel（`_P6BT`）**：P6LS3 单切片 kernel（`A' = 2A`、`Cq' = 2Cq`）在 event `j` 的 incoming slab
上对 `t → s⁻` 实例化 + terminal 极限。常数 `∃ Q Λ Dcap Rrad ζ₀ Rad Bw` 在 history 之前；结论
`B_ḡ(x, A/√R_k)` 上 `R_ḡ ≤ 2Q·R_k`（`R_ḡ(x) = R_k`）。 -/
theorem terminal_scalar_bound_P6BT {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ)
    (hκ : 0 < κ) (Cder Cgrad : ℝ≥0) {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (A : ℝ) (hA : 0 < A) (Cq : ℝ) :
    ∃ Q Λ Dcap Rrad ζ₀ Rad Bw : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ 0 < ζ₀ ∧ 0 < Bw ∧
    ∀ (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount) {p : CutoffParameters} (T₀ : ℝ)
      (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ →
        GeometricCutoffRecord K.toHistory i p),
      (∀ i hT b, ((records i hT).static b).hasCanonicalWindow) →
      Rrad ≤ p.modelRadius → 2 ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
      (∀ i : Fin K.eventCount, Perelman.PhiAlmostNonnegative
        (K.toHistory.event i).incoming.flow (Ico (K.time i.castSucc) (K.time i.succ)) phi) →
    ∀ (x : (K.toHistory.event j).incoming.terminalRegularOpen) (Rk q qd ρ : ℝ),
      metricScalarAt (K.toHistory.event j).terminal.metric x = Rk → 0 < Rk →
      0 < q → q ≤ Cq * Rk → qd ≤ q →
      2 * Λ ≤ Rk → 4 * Λ ≤ Rk * K.time j.succ → 2 * Λ ≤ ρ * Real.sqrt Rk →
      T₀ ≤ K.time j.succ - 3 * Bw / Rk →
      K.EventSlabsDerivative Cder qd j.castSucc →
      (K.toHistory.event j).incoming.DerivativeBoundBefore Cder qd (K.time j.succ) →
      (K.toHistory.event j).incoming.GradientBoundBefore Cgrad qd (K.time j.succ) →
      (∀ (τ : Icc (0 : ℝ) K.toHistory.horizon),
        K.time j.castSucc < τ → (τ : ℝ) < K.time j.succ →
        ∀ (zz : (K.toHistory.stageAt τ).Carrier) (b : ℝ), 0 < b → b ≤ ρ →
          K.toHistory.isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
              (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
              (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b)) →
      (∀ᶠ t in 𝓝[<] K.time j.succ, ∀ x' : (K.stage j.castSucc).Carrier,
        riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric t) x.1 x' <
            ENNReal.ofReal (2 * Rad / Real.sqrt Rk) →
        q < (K.toHistory.event j).incoming.flow.scalar t x' →
        ∃ W : SpatialCanonicalWitness ((K.toHistory.event j).incoming.flow.base.metric t)
          ε C1 C2 x', W.capTubeHasNeckChart ε) →
      (∀ᶠ t in 𝓝[<] K.time j.succ, ¬ ∃ (i : Fin K.eventCount) (hT : T₀ ≤ K.time i.succ)
        (hl : i.succ ≤ j.castSucc) (B : BackwardPointTrace K.toHistory i.succ j.castSucc hl x.1)
        (b : (K.toHistory.event i).RetainedBoundaryIndex) (w : standardCapWindow p.modelRadius),
        B.point i.succ le_rfl hl = ((records i hT).static b).window w ∧ ‖w.val‖ < Dcap + 1 ∧
          t - K.time i.succ ≤ 1 / 2 * (((records i hT).static b).neck.scale)⁻¹) →
      ∀ z ∈ riemannianBallOf (K.toHistory.event j).terminal.metric x (A / Real.sqrt Rk),
        metricScalarAt (K.toHistory.event j).terminal.metric z ≤ 2 * Q * Rk := by
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, Bw, hQ, hΛ, -, -, hζ₀, hBw, hmain⟩ :=
    RetainedCoreHistory.slice_scalar_bound_of_not_capWindowPoint_window_pinch_P6LS3 hεle κ C1
      C2 hκ Cder Cgrad hphi (2 * A) (by positivity) (2 * Cq)
  refine ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, Bw, hQ, hΛ, hζ₀, hBw, ?_⟩
  intro K j p T₀ records hcan hRr hord hacc hpinch x Rk q qd ρ hRx hRk hq hqC hqd hΛR hΛt hΛρ
    hT₀ hslab hder hgrad hnc hW hnot z hz
  have hs : K.time j.castSucc < K.time j.succ := K.time_strictMono Fin.castSucc_lt_succ
  have hs0 : 0 < K.time j.succ := by
    by_contra hneg
    have : Rk * K.time j.succ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hRk.le (not_lt.mp hneg)
    linarith
  have hBR : 0 < Bw / Rk := div_pos hBw hRk
  have hxlim := (K.toHistory.event j).terminal.tendsto_metricScalarAt x
  rw [hRx] at hxlim
  have hxev := hxlim (Ioo_mem_nhds (show Rk / 2 < Rk by linarith) (show Rk < 2 * Rk by linarith))
  apply le_of_tendsto ((K.toHistory.event j).terminal.tendsto_metricScalarAt z)
  filter_upwards [Ioo_mem_nhdsLT hs,
    Ioo_mem_nhdsLT (show K.time j.succ / 2 < K.time j.succ by linarith),
    Ioo_mem_nhdsLT (show K.time j.succ - Bw / Rk < K.time j.succ by linarith), hxev,
    (K.toHistory.event j).terminal.eventually_riemannianEDistOf_lt x z hz, hW, hnot]
    with t ht1 ht2 ht3 hRt hdt hWt hnott
  have hRt' : Rk / 2 < (K.toHistory.event j).incoming.flow.scalar t x.1 ∧
      (K.toHistory.event j).incoming.flow.scalar t x.1 < 2 * Rk := hRt
  set Rt := (K.toHistory.event j).incoming.flow.scalar t x.1 with hRtdef
  have hRt0 : 0 < Rt := by linarith [hRt'.1]
  have hsRt : 0 < Real.sqrt Rt := Real.sqrt_pos.mpr hRt0
  have hsRk : 0 < Real.sqrt Rk := Real.sqrt_pos.mpr hRk
  have hkt : Real.sqrt Rk ≤ 2 * Real.sqrt Rt :=
    sqrt_le_two_mul_sqrt_P6BT (by linarith [hRt'.1])
  have htk : Real.sqrt Rt ≤ 2 * Real.sqrt Rk :=
    sqrt_le_two_mul_sqrt_P6BT (by linarith [hRt'.2])
  have hpinchW : ∀ i : Fin K.eventCount, Perelman.PhiAlmostNonnegative
      (K.toHistory.event i).incoming.flow
      (Ico (K.time i.castSucc) (K.time i.succ) ∩ Ici T₀) phi :=
    fun i t' ht' => hpinch i t' ht'.1
  have hBt : Bw / Rt ≤ 2 * Bw / Rk := by
    rw [div_le_div_iff₀ hRt0 hRk]
    nlinarith [hRt'.1]
  have hT₀t : T₀ ≤ t - Bw / Rt := by
    have : 3 * Bw / Rk = Bw / Rk + 2 * Bw / Rk := by ring
    linarith [ht3.1]
  have hCq : 0 ≤ Cq := by
    by_contra hneg
    have : Cq * Rk < 0 := mul_neg_of_neg_of_pos (not_le.mp hneg) hRk
    linarith
  have hqC' : q ≤ 2 * Cq * Rt := by
    nlinarith [mul_le_mul_of_nonneg_left hRt'.1.le hCq]
  have hΛt' : Λ ≤ Rt * t := by
    have h1 : Rk / 2 * (K.time j.succ / 2) ≤ Rt * t :=
      mul_le_mul hRt'.1.le ht2.1.le (by linarith) hRt0.le
    nlinarith
  have hρ0 : 0 < ρ := by
    by_contra hneg
    have : ρ * Real.sqrt Rk ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) hsRk.le
    linarith
  have hΛρ' : Λ ≤ ρ * Real.sqrt Rt := by
    have : ρ * Real.sqrt Rk ≤ ρ * (2 * Real.sqrt Rt) := mul_le_mul_of_nonneg_left hkt hρ0.le
    nlinarith
  have hU : ∀ w ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric t) x.1
      (Rad / Real.sqrt Rt), w ∈ riemannianBallOf
        ((K.toHistory.event j).incoming.flow.base.metric t) x.1 (2 * Rad / Real.sqrt Rk) := by
    intro w hw
    rcases le_or_gt 0 Rad with hRad | hRad
    · refine lt_of_lt_of_le hw (ENNReal.ofReal_le_ofReal ?_)
      rw [div_le_div_iff₀ hsRt hsRk]
      nlinarith [mul_le_mul_of_nonneg_left hkt hRad]
    · have h0 : ENNReal.ofReal (Rad / Real.sqrt Rt) = 0 :=
        ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg hRad.le hsRt.le)
      have hw' : riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric t) x.1 w <
          ENNReal.ofReal (Rad / Real.sqrt Rt) := hw
      rw [h0] at hw'
      exact absurd hw' (not_lt_zero)
  have hzt : z.1 ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric t) x.1
      (2 * A / Real.sqrt Rt) := by
    refine lt_of_lt_of_le hdt (ENNReal.ofReal_le_ofReal ?_)
    rw [div_le_div_iff₀ hsRk hsRt]
    nlinarith [mul_le_mul_of_nonneg_left htk hA.le]
  have hb := hmain K j T₀ records hcan hRr hord hacc hpinchW t ht1.1 ht1.2 x.1 q ρ hT₀t hq hqC'
    (by linarith [hRt'.1]) hΛt' hΛρ'
    (riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric t) x.1
      (2 * Rad / Real.sqrt Rk)) hU
    (fun w hw hqw => hWt w hw hqw) qd hqd hslab
    (fun y' t' ht' hqy' => hder y' t' ⟨ht'.1, ht'.2.trans ht1.2⟩ hqy')
    (fun w _ v' hv' _ hqw ξ => hgrad w v' ⟨hv'.1, hv'.2.trans ht1.2⟩ (lt_of_le_of_lt hqd hqw) ξ)
    (fun τ _ _ hτ1 hτ2 _ _ zz _ b hb0 hbρ hctrl => hnc τ hτ1 hτ2 zz b hb0 hbρ hctrl)
    hnott z.1 hzt
  change (K.toHistory.event j).incoming.flow.scalar t z.1 ≤ 2 * Q * Rk
  have hQ0 : 0 ≤ Q := by linarith
  calc (K.toHistory.event j).incoming.flow.scalar t z.1 ≤ Q * Rt := hb
    _ ≤ Q * (2 * Rk) := mul_le_mul_of_nonneg_left hRt'.2.le hQ0
    _ = 2 * Q * Rk := by ring

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
