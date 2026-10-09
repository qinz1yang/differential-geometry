import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6WBAdaptLocalP6WA2

/-!
# 固定 `c*` 收窄版（star）：`hWBlocStar` + SLT 核 / anchor star 孪生（O-CH11-WBADAPT G3，后缀 `_P6WA2`）

R-C11-19 Q4 "可收窄"：SLTLOCAL 的前 slab 局部合同 `hslabsLoc` 要求**每个固定 `c`**（`∀ Rad B c, ∀ᶠ n`），而一次
小时间 ODE 估计只覆盖受限制的 `c`。G1 的适配实际只用 `c* := 1/(2·max(Ctime, 1))`，故可另作消费者孪生，
只要求这个固定 `c*`。**两种要求分开写，不混写**：
* `hWBlocStar_of_shortSLT_guarded_P6WA2`（PROVED）：陈述 = `hWBloc` 类型把 `∃ … c` 去掉、guard 右端固定为
  `1 / (2 * max (Ctime : ℝ) 1)`（与 SLTPROD `hslabsLoc_cstar_of_hgood_P6SP` 的 `c⋆` 写法逐字一致）
  （生成器 `build-logs/scratch/O-CH11-WBADAPT/gen3.py` 从 `hWBloc` 文本逐处断言替换）；证明同 G1。
* `RetainedCoreHistory.eventually_scalar_bound_at_distance_window_local_star_P6WA2`（**PROVED**）：
  SLT 核局部孪生，前 slab 输入
  `hslabsLocStar : ∀ Rad B, ∀ᶠ n, … (t n − v)·max (q n) (R(t n, z)) ≤ c* → …`（`c*` 只依赖 `Ctime`）。
* `RetainedCoreHistory.hanchor0_lateW_local_star_P6WA2` /
  `ObservedHistory.hanchor0_eventSlab_local_star_P6WA2`（**PROVISIONAL[`hslabsLocStar`]**）：
  anchor 两层 star 孪生（kernel 帧 `c* = 1/(2·max(Ctime', 1))`）。
  producer 只需在固定深度 `c*/max(Cg·R, R(z))` 内给导数。
* consumer：star 孪生 ⇒ G2 的 `∀ c` 孪生（`hslabsLoc Rad B c*` 特化），即 star 的前提弱于 `∀ c` 版。
**不生产** `hslabsLocStar`；不声称 J10 已去。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- `c⋆` 两种写法：`ℝ≥0` 内取 max 再 coe（G1 适配内部）= `ℝ` 内取 max（star 陈述 / SLTPROD）。 -/
theorem coe_max_one_P6WA2 (C : ℝ≥0) : ((max C 1 : ℝ≥0) : ℝ) = max (C : ℝ) 1 := by
  rw [NNReal.coe_max, NNReal.coe_one]

/-- **`hWBlocStar` ⇐ guarded ShortSLT（`_P6WA2`，PROVED，无 binder）**：`hWBloc` 类型去掉存在量词 `c`，
前 slab guard 右端固定为 `c* = 1/(2·max(Ctime, 1))`。参数同 G1：`Ĉt := max Ctime 1`、`Bw := θ`。 -/
theorem hWBlocStar_of_shortSLT_guarded_P6WA2 :
    ∀ (ε : ℝ), ε ≤ coneAccuracy → ∀ (κ C1 C2 : ℝ), 0 < κ → ∀ (Ctime Cgrad : ℝ≥0)
      (phi : ℝ → ℝ), Perelman.AdmissiblePinchingFunction phi → ∀ (A : ℝ), 0 < A →
      ∀ (Cq θ : ℝ), 0 < θ →
      ∃ Q Λ Dcap Rrad ζ₀ Rad Bw : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧
      Dcap ≤ Rrad ∧ 0 < ζ₀ ∧ 0 < Bw ∧
      ∀ (H : RetainedCoreHistory.{u})
        (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
        (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount))
        {t : ℝ} (_ : H.time (Fin.last H.eventCount) < t) (_ : t < s)
          (y : (H.stage (Fin.last H.eventCount)).Carrier) (q ρ : ℝ),
        0 < q → q ≤ Cq * G.flow.scalar t y → Λ ≤ G.flow.scalar t y →
        Λ ≤ G.flow.scalar t y * t →
        ∀ {p : CutoffParameters} (T₀ : ℝ), T₀ ≤ t - Bw / G.flow.scalar t y →
        ∀ (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
          GeometricCutoffRecord H.toHistory i p),
        (∀ i hT b, ((records i hT).static b).hasCanonicalWindow) →
        Rrad ≤ p.modelRadius → 2 ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
        ∀ (U : Set (H.stage (Fin.last H.eventCount)).Carrier),
        (∀ w ∈ riemannianBallOf (G.flow.base.metric t) y (Rad / Real.sqrt (G.flow.scalar t y)),
          w ∈ U) →
        (∀ x ∈ U, q < G.flow.scalar t x →
          ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) ε C1 C2 x,
            W.capTubeHasNeckChart ε) →
        (∀ j : Fin H.eventCount,
          ∀ (first : Fin (H.eventCount + 1)) (hf : first ≤ j.castSucc),
          ∀ z ∈ U, ∀ B : BackwardPointTrace H.toHistory first (Fin.last H.eventCount)
            (Fin.le_last first) z,
          ∀ v ∈ Ioo (H.time j.castSucc) (H.time j.succ), t - Bw / G.flow.scalar t y ≤ v →
          (t - v) * max q (G.flow.scalar t z) ≤ 1 / (2 * max (Ctime : ℝ) 1) →
          q < (H.toHistory.event j).incoming.flow.scalar v
            (B.point j.castSucc hf (Fin.le_last _)) →
          |derivWithin (fun w => (H.toHistory.event j).incoming.flow.scalar w
            (B.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
            Ctime * (H.toHistory.event j).incoming.flow.scalar v
              (B.point j.castSucc hf (Fin.le_last _)) ^ 2) →
        (∀ x ∈ U, ∀ v ∈ Ioo (H.time (Fin.last H.eventCount)) t, t - Bw / G.flow.scalar t y ≤ v →
          q < G.flow.scalar v x →
          |derivWithin (fun w => G.flow.scalar w x) (Iic v) v| ≤ Ctime * G.flow.scalar v x ^ 2) →
        (∀ x ∈ U, ∀ v ∈ Ioo (H.time (Fin.last H.eventCount)) t, t - Bw / G.flow.scalar t y ≤ v →
          q < G.flow.scalar v x →
          ∀ w : TangentSpace ThreeModel x,
            |scalarDifferential G.flow v x w| ≤
              Cgrad * G.flow.scalar v x * Real.sqrt (G.flow.scalar v x) *
                Real.sqrt ((G.flow.base.metric v).inner x w w)) →
        (∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative (H.toHistory.event j).incoming.flow
          (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici (t - Bw / G.flow.scalar t y)) phi) →
        Perelman.PhiAlmostNonnegative G.flow
          (Ico (H.time (Fin.last H.eventCount)) s ∩ Ici (t - Bw / G.flow.scalar t y)) phi →
        (∀ (T : ℝ) (hT : H.time (Fin.last H.eventCount) < T) (hTs : T < s), T ≤ t →
          t - Bw / G.flow.scalar t y ≤ T →
          let B := H.extendHorizon T (hend ▸ hT.le) (G.closedPrefix T hT hTs) hG
          let tm : Icc (0 : ℝ) B.horizon := ⟨T, H.horizon_nonneg.trans (hend ▸ hT.le), le_rfl⟩
          ∀ z ∈ U, ∀ (yy : (B.toHistory.stageAt tm).Carrier), HEq yy z →
          ∀ (b : ℝ), 0 < b → b ≤ ρ →
            B.toHistory.isParabolicallyRmControlledBall tm yy b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                  (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                  (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                    yy b)) →
        Λ ≤ ρ * Real.sqrt (G.flow.scalar t y) →
        (¬ ∃ (j : Fin H.eventCount) (hT : T₀ ≤ H.time j.succ) (hl : j.succ ≤ Fin.last H.eventCount)
          (B : BackwardPointTrace H.toHistory j.succ (Fin.last H.eventCount) hl y)
          (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
          B.point j.succ le_rfl hl = ((records j hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
            t - H.time j.succ ≤ θ * (((records j hT).static b).neck.scale)⁻¹) →
        ∀ z ∈ riemannianBallOf (G.flow.base.metric t) y (A / Real.sqrt (G.flow.scalar t y)),
          G.flow.scalar t z ≤ Q * G.flow.scalar t y := by
  intro ε hεle κ C1 C2 hκ Ctime Cgrad phi hphi A hA Cq θ hθ
  have hC1 : (1 : ℝ) ≤ ((max Ctime 1 : ℝ≥0) : ℝ) := by exact_mod_cast le_max_right Ctime 1
  have hC0 : (0 : ℝ) < ((max Ctime 1 : ℝ≥0) : ℝ) := zero_lt_one.trans_le hC1
  have hS : ShortSLTGuarded_C11KX.{u} θ := shortSLT_guarded_C11KX hθ
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, hQ, hΛ, hD, hDR, hζ, hmain⟩ :=
    hS hεle κ C1 C2 hκ (max Ctime 1) Cgrad hphi A hA Cq
  refine ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, θ, hQ, hΛ, hD, hDR, hζ, hθ, ?_⟩
  intro H hend s G hG t ht hts y q ρ hq hqy hΛ1 hΛ2 p T₀ hT₀ records hcan hRrad hord hζ' U hUy hW
    hslabs hder hgrad hpinch hpinchG hnc hρ hnot
  refine hmain H hend G hG ht hts y q ρ hq hqy hΛ1 hΛ2 T₀ hT₀ records hcan hRrad hord hζ' U hUy hW
    ?_ ?_ ?_ hpinch hpinchG ?_ hρ hnot
  · intro j first hf z hz B v hv hvw hqv hg
    have hc := mul_max_le_cstar_of_guard_P6WA2 hC0 hg
    rw [coe_max_one_P6WA2] at hc
    exact abs_le_maxOne_mul_sq_P6WA2 (hslabs j first hf z hz B v hv hvw hc hqv)
  · intro x hx v hv hvw hqv _
    exact abs_le_maxOne_mul_sq_P6WA2 (hder x hx v hv hvw hqv)
  · intro x hx v hv hvw hqv _
    exact hgrad x hx v hv hvw hqv
  · intro T hT hTs hTt hTw _ _ z hz _
    exact hnc T hT hTs hTt hTw z hz

/-- **SLT 核局部孪生，固定 `c*`（`_P6WA2`，PROVED）**：`…_window_local_P6SL` 去掉 `hWBloc`，前 slab 输入
`hslabsLoc`（`∀ c`）收窄为 `hslabsLocStar`（只在 `c* = 1/(2·max(Ctime, 1))`）；
由 `hWBlocStar_of_shortSLT_guarded_P6WA2` 支付。证明 = SLTLOCAL 原证明逐字
（只换 obtain 来源与 `hslabsLoc Rad Bw c ↦ hslabsLocStar Rad Bw`）。 -/
theorem RetainedCoreHistory.eventually_scalar_bound_at_distance_window_local_star_P6WA2
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {Cq θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (H : ℕ → RetainedCoreHistory.{u})
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon) (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (hG : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (t : ℕ → ℝ) (ht : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n)
    (hts : ∀ n, t n < s n) (y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier)
    (q ρ : ℕ → ℝ) (hq : ∀ n, 0 < q n) (hqy : ∀ n, q n ≤ Cq * ((G n).flow.scalar (t n) (y n)))
    (hR : Tendsto (fun n => ((G n).flow.scalar (t n) (y n))) atTop atTop)
    (hRt : Tendsto (fun n => ((G n).flow.scalar (t n) (y n)) * t n) atTop atTop)
    {p : ℕ → CutoffParameters} (T₀ : ℕ → ℝ)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ t n - B / ((G n).flow.scalar (t n) (y n)))
    (records : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      GeometricCutoffRecord (H n).toHistory i (p n))
    (hcan : ∀ n i hT b, ((records n i hT).static b).hasCanonicalWindow)
    (hradius : Tendsto (fun n => (p n).modelRadius) atTop atTop)
    (horder : ∀ n, 2 ≤ (p n).modelOrder)
    (haccuracy : ∀ ζ : ℝ, 0 < ζ → ∀ᶠ n in atTop, (p n).modelAccuracy ≤ ζ)
    (hW : ∀ Rad : ℝ, ∀ᶠ n in atTop, ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
        (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))), q n < (G n).flow.scalar (t n) x →
      ∃ W : SpatialCanonicalWitness ((G n).flow.base.metric (t n)) ε C1 C2 x,
        W.capTubeHasNeckChart ε)
    (hslabsLocStar : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ j : Fin (H n).eventCount,
      ∀ (first : Fin ((H n).eventCount + 1)) (hf : first ≤ j.castSucc),
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
      ∀ Btr : BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
        (Fin.le_last first) z,
      ∀ v ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      t n - B / ((G n).flow.scalar (t n) (y n)) ≤ v →
      (t n - v) * max (q n) ((G n).flow.scalar (t n) z) ≤
        1 / (2 * max (Ctime : ℝ) 1) →
      q n < ((H n).toHistory.event j).incoming.flow.scalar v
        (Btr.point j.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun w => ((H n).toHistory.event j).incoming.flow.scalar w
        (Btr.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
        Ctime * ((H n).toHistory.event j).incoming.flow.scalar v
          (Btr.point j.castSucc hf (Fin.le_last _)) ^ 2)
    (hder : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
        (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
      ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
      t n - B / ((G n).flow.scalar (t n) (y n)) ≤ v →
      q n < (G n).flow.scalar v x →
      |derivWithin (fun w => (G n).flow.scalar w x) (Iic v) v| ≤
        Ctime * (G n).flow.scalar v x ^ 2)
    (hgrad : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
        (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
      ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
      t n - B / ((G n).flow.scalar (t n) (y n)) ≤ v →
      q n < (G n).flow.scalar v x → ∀ w : TangentSpace ThreeModel x,
        |scalarDifferential (G n).flow v x w| ≤
          Cgrad * (G n).flow.scalar v x * Real.sqrt ((G n).flow.scalar v x) *
            Real.sqrt (((G n).flow.base.metric v).inner x w w))
    (hpinch : ∀ B : ℝ, ∀ᶠ n in atTop, ∀ j : Fin (H n).eventCount,
      Perelman.PhiAlmostNonnegative ((H n).toHistory.event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ) ∩
          Ici (t n - B / ((G n).flow.scalar (t n) (y n)))) phi)
    (hpinchG : ∀ B : ℝ, ∀ᶠ n in atTop, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∩
        Ici (t n - B / ((G n).flow.scalar (t n) (y n)))) phi)
    (hnc : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ (T : ℝ)
      (hT : (H n).time (Fin.last (H n).eventCount) < T) (hTs : T < s n), T ≤ t n →
        t n - B / ((G n).flow.scalar (t n) (y n)) ≤ T →
        let Bh := (H n).extendHorizon T (hend n ▸ hT.le) ((G n).closedPrefix T hT hTs) (hG n)
        let tm : Icc (0 : ℝ) Bh.horizon :=
          ⟨T, (H n).horizon_nonneg.trans (hend n ▸ hT.le), le_rfl⟩
        ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
            (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        ∀ (yy : (Bh.toHistory.stageAt tm).Carrier), HEq yy z →
        ∀ (b : ℝ), 0 < b → b ≤ ρ n →
          Bh.toHistory.isParabolicallyRmControlledBall tm yy b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (Bh.toHistory.stageAt tm).Carrier
                (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                (riemannianBallOf (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                  yy b))
    (hρ : Tendsto (fun n => ρ n * Real.sqrt ((G n).flow.scalar (t n) (y n))) atTop atTop)
    (D θ : ℕ → ℝ) (hD : Tendsto D atTop atTop) (hθ : ∀ n, θ₀ ≤ θ n)
    (hnot : ∀ n, ¬ ∃ (j : Fin (H n).eventCount) (hT : T₀ n ≤ (H n).time j.succ)
      (hl : j.succ ≤ Fin.last (H n).eventCount)
      (Btr : BackwardPointTrace (H n).toHistory j.succ (Fin.last (H n).eventCount) hl (y n))
      (b : ((H n).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      Btr.point j.succ le_rfl hl = ((records n j hT).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - (H n).time j.succ ≤ θ n * (((records n j hT).static b).neck.scale)⁻¹) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 1 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        (G n).flow.scalar (t n) z ≤ Q * ((G n).flow.scalar (t n) (y n)) := by
  intro A hA
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, Bw, hQ, _, _, _, hζ₀, _, hmain⟩ :=
    hWBlocStar_of_shortSLT_guarded_P6WA2 ε hεle κ C1 C2 hκ Ctime Cgrad phi hphi A hA Cq θ₀ hθ₀
  refine ⟨Q, hQ, ?_⟩
  filter_upwards [hradius.eventually_ge_atTop Rrad, haccuracy ζ₀ hζ₀, hR.eventually_ge_atTop Λ,
    hRt.eventually_ge_atTop Λ, hρ.eventually_ge_atTop Λ, hD.eventually_ge_atTop Dcap, hT₀ Bw,
    hW Rad, hslabsLocStar Rad Bw, hder Rad Bw, hgrad Rad Bw, hpinch Bw, hpinchG Bw, hnc Rad Bw]
    with n hn1 hn2 hn3 hn4 hn5 hn6 hn7 hn8 hn9 hn10 hn11 hn12 hn13 hn14
  refine hmain (H n) (hend n) (G n) (hG n) (ht n) (hts n) (y n) (q n) (ρ n) (hq n) (hqy n) hn3
    hn4 (T₀ n) hn7 (records n) (hcan n) hn1 (horder n) hn2 _ (fun _ hw => hw) hn8 hn9 hn10 hn11
    hn12 hn13 hn14 hn5 ?_
  rintro ⟨j, hT, hl, Btr, b, x, h1, h2, h3⟩
  refine hnot n ⟨j, hT, hl, Btr, b, x, h1, by linarith, h3.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (hθ n)
    (inv_nonneg.mpr ((records n j hT).static b).neck.scale_pos.le)

/-- **anchor 局部孪生，固定 `c*`（`_P6WA2`，PROVISIONAL[`hslabsLocStar`]）**：`hanchor0_lateW_local_P6SL` 去掉
`hWBloc`，`hslabsLoc` 收窄为 `hslabsLocStar`；证明逐字（核调用换 star 版）。 -/
theorem RetainedCoreHistory.hanchor0_lateW_local_star_P6WA2
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {D θcap s t ρ T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters} {δb : ℕ → ℝ}
    {H : ℕ → RetainedCoreHistory.{u}}
    {records : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      GeometricCutoffRecord (H n).toHistory i (p n)}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hpinch : ∀ n, (∀ j : Fin (H n).eventCount, Perelman.PhiAlmostNonnegative
        ((H n).toHistory.event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ) ∩ Ici (T₀ n)) phi) ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∩ Ici (T₀ n)) phi)
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (hnot : ∀ n, ¬ ∃ (j : Fin (H n).eventCount) (hj : T₀ n ≤ (H n).time j.succ)
      (hl : j.succ ≤ Fin.last (H n).eventCount)
      (A : BackwardPointTrace (H n).toHistory j.succ (Fin.last (H n).eventCount) hl (y n))
      (b : ((H n).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point j.succ le_rfl hl = ((records n j hj).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - (H n).time j.succ ≤ θcap n * (((records n j hj).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ t n - B / ((G n).flow.scalar (t n) (y n)))
    (hRt : Tendsto (fun n => ((G n).flow.scalar (t n) (y n)) * t n) atTop atTop)
    (hR : Tendsto (fun n => ((G n).flow.scalar (t n) (y n))) atTop atTop)
    (hRpos : ∀ n, 0 < (G n).flow.scalar (t n) (y n))
    {Cq : ℝ} (q : ℕ → ℝ) (hq : ∀ n, 0 < q n)
    (hqC : ∀ n, q n ≤ Cq * ((G n).flow.scalar (t n) (y n)))
    (hslabsLocStar : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ j : Fin (H n).eventCount,
      ∀ (first : Fin ((H n).eventCount + 1)) (hf : first ≤ j.castSucc),
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
      ∀ Btr : BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
        (Fin.le_last first) z,
      ∀ v ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      t n - B / ((G n).flow.scalar (t n) (y n)) ≤ v →
      (t n - v) * max (q n) ((G n).flow.scalar (t n) z) ≤
        1 / (2 * max (Ctime : ℝ) 1) →
      q n < ((H n).toHistory.event j).incoming.flow.scalar v
        (Btr.point j.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun w => ((H n).toHistory.event j).incoming.flow.scalar w
        (Btr.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
        Ctime * ((H n).toHistory.event j).incoming.flow.scalar v
          (Btr.point j.castSucc hf (Fin.le_last _)) ^ 2)
    (hderSel : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n))
        (y n) (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
      ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
      t n - B / ((G n).flow.scalar (t n) (y n)) ≤ v →
      q n < (G n).flow.scalar v x →
      |derivWithin (fun w => (G n).flow.scalar w x) (Iic v) v| ≤
        Ctime * (G n).flow.scalar v x ^ 2)
    (hW : ∀ Rad : ℝ, ∀ᶠ n in atTop, ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
        (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))), q n < (G n).flow.scalar (t n) x →
      ∃ W : SpatialCanonicalWitness ((G n).flow.base.metric (t n)) ε C1 C2 x,
        W.capTubeHasNeckChart ε)
    (hgrad : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
        (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
      ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
      t n - B / ((G n).flow.scalar (t n) (y n)) ≤ v →
      q n < (G n).flow.scalar v x → ∀ w : TangentSpace ThreeModel x,
        |scalarDifferential (G n).flow v x w| ≤
          Cgrad * (G n).flow.scalar v x * Real.sqrt ((G n).flow.scalar v x) *
            Real.sqrt (((G n).flow.base.metric v).inner x w w))
    (hnc : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ (T : ℝ)
      (hT : (H n).time (Fin.last (H n).eventCount) < T) (hTs : T < s n), T ≤ t n →
        t n - B / ((G n).flow.scalar (t n) (y n)) ≤ T →
        let Bh := (H n).extendHorizon T (hend n ▸ hT.le) ((G n).closedPrefix T hT hTs) (hGi n)
        let tm : Icc (0 : ℝ) Bh.horizon :=
          ⟨T, (H n).horizon_nonneg.trans (hend n ▸ hT.le), le_rfl⟩
        ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
            (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        ∀ (yy : (Bh.toHistory.stageAt tm).Carrier), HEq yy z →
        ∀ (b : ℝ), 0 < b → b ≤ ρ n →
          Bh.toHistory.isParabolicallyRmControlledBall tm yy b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (Bh.toHistory.stageAt tm).Carrier
                (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                (riemannianBallOf (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                  yy b))
    (hρ : Tendsto (fun n => ρ n * Real.sqrt ((G n).flow.scalar (t n) (y n))) atTop atTop) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        (G n).flow.scalar (t n) z ≤ Q * ((G n).flow.scalar (t n) (y n)) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hradius : Tendsto (fun n => (p n).modelRadius) atTop atTop :=
    tendsto_atTop_mono (fun n => (hpar n).2.1.trans (hpar n).2.2.1) hnat
  have hDt : Tendsto D atTop atTop := tendsto_atTop_mono (fun n => (hpar n).2.1) hnat
  have hacc : ∀ ζ : ℝ, 0 < ζ → ∀ᶠ n in atTop, (p n).modelAccuracy ≤ ζ := by
    intro ζ hζ
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [h0.eventually (ge_mem_nhds hζ)] with n hn
    exact (hpar n).1.trans hn
  have hθ (n : ℕ) : (1 : ℝ) / 2 ≤ θcap n := by
    refine le_trans ?_ (hθcap n)
    have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith [n.cast_nonneg (α := ℝ)]
    have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
    linarith
  have hord (n : ℕ) : 2 ≤ (p n).modelOrder := le_trans (by omega) (hpar n).2.2.2.1
  intro A hA
  obtain ⟨Q, hQ, hev⟩ :=
    RetainedCoreHistory.eventually_scalar_bound_at_distance_window_local_star_P6WA2
    (Ctime := Ctime) (Cq := Cq) hεle hκ hphi (by norm_num : (0 : ℝ) < 1 / 2) H hend s G hGi t
    hat hts y q ρ hq hqC hR hRt T₀ hT₀
    records hcan hradius hord hacc hW hslabsLocStar hderSel hgrad
    (fun B => (hT₀ B).mono fun n hn j v hv w => (hpinch n).1 j v ⟨hv.1, hn.trans hv.2⟩ w)
    (fun B => (hT₀ B).mono fun n hn v hv w => (hpinch n).2 v ⟨hv.1, hn.trans hv.2⟩ w) hnc hρ D θcap
    hDt hθ
    hnot A hA
  refine ⟨max Q 2, le_max_right _ _, ?_⟩
  filter_upwards [hev] with n hn z hz
  refine (hn z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
  exact (hRpos n).le

namespace ObservedHistory

/-- **anchor 处的实际切换（kernel 帧），固定 `c*`（`_P6WA2`，PROVISIONAL[`hslabsLocStar`]）**：
`hanchor0_eventSlab_local_P6SL` 去掉 `hWBloc`，唯一非 kernel 前提收窄为 `hslabsLocStar`（K 帧 `q := Cg·R`，
`c* = 1/(2·max(Ctime', 1))`）；证明逐字（lateW 调用换 star 版）。 -/
theorem hanchor0_eventSlab_local_star_P6WA2
    {ε C1' C2' : ℝ} {Ctime' : ℝ≥0} (hεcone : ε ≤ coneAccuracy) (hC20 : 0 ≤ C2')
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {D θcap T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters} {δb : ℕ → ℝ}
    {records : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
      T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
      GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (p n)}
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
        Perelman.PhiAlmostNonnegative
          (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow
          (Ico (((K n).prefixAt (j n).castSucc).time i.castSucc)
            (((K n).prefixAt (j n).castSucc).time i.succ) ∩ Ici (T₀ n)) phi) ∧
      Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
        (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ) ∩ Ici (T₀ n)) phi)
    (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
      (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
      (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤
          θcap n * (((records n i hi).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRt : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) *
      t n) atTop atTop)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (hσ : ∀ n, (σ n : ℝ) = t n)
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRlt : ∀ n : ℕ, (n : ℝ) + 1 < R n)
    {κd : ℝ} (hκd : 0 < κd)
    (hvolK : ∀ D L B : ℝ, 0 < D → 0 < L → 0 < B → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - B / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
        ((Kh n).activeStage_mono hvt) x,
      ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ L →
        (Kh n).isParabolicallyRmControlledBall v
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
          (ϱ / Real.sqrt (R n)) →
        ENNReal.ofReal (κd * ϱ ^ 3) ≤
          Geometry.Collapse.ballVolume
            (scaleMetric (R n) (hRpos n) ((Kh n).stageMetric ((Kh n).activeStage v) v))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ϱ)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) {Cg : ℝ} (hCg : 2 ≤ Cg)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((Kh n).stageAt v).Carrier,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hdistW : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (Kh n).activeStage v = (Kh n).activeStage (σ n) →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)))
    (hslabsLocStar : ∀ Rad B : ℝ, ∀ᶠ n in atTop,
      ∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
      ∀ (first : Fin (((K n).prefixAt (j n).castSucc).eventCount + 1)) (hf : first ≤ i.castSucc),
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n)) (yG n)
          (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
      ∀ Btr : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory first
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) (Fin.le_last first) z,
      ∀ v ∈ Ioo (((K n).prefixAt (j n).castSucc).time i.castSucc)
        (((K n).prefixAt (j n).castSucc).time i.succ),
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ v →
      (t n - v) * max (Cg * R n) (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z) ≤
        1 / (2 * max (Ctime' : ℝ) 1) →
      Cg * R n < (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
        (Btr.point i.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun w =>
          (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar w
            (Btr.point i.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
        Ctime' * (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
          (Btr.point i.castSucc hf (Fin.le_last _)) ^ 2) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
          (yG n)
          (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
          Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hk := exists_tracedKappa_of_kseq_P6D2 hvolK
  obtain ⟨ρnc, hradii, hkappa⟩ := hk
  subst hKh
  have hnc := hnc_window_of_tracedKappa_P6M hjt htj σ hσ y yG hyG R hRpos hRn hκd ρnc hkappa
  have hρ : Tendsto (fun n => ρnc n *
      Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))) atTop atTop :=
    hradii.congr fun n => by rw [hRn n]
  have hW := hW_of_selection_Cg_P6M3 hjt htj σ hσ y yG hyG R hRpos hRn Tn aSeed haT hsT has pT
    seedTrace L hL hgood
  have hgrad := hgrad_of_selection_sameSlab_Cg_P6CD hC20 hjt htj σ hσ y yG hyG R hRpos hRn Tn
    aSeed haT hsT has pT seedTrace L hL hgood hwin hdistW
  have hder := hderSel_of_selection_sameSlab_Cg_P6JG3 hjt htj σ hσ y yG hyG R hRpos hRn Tn
    aSeed haT hsT has pT seedTrace L hL hgood hwin hdistW
  have hRlim : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
      atTop atTop :=
    tendsto_atTop_mono (fun n => (hRlt n).le.trans_eq (hRn n)) hnat
  have hR0 : ∀ n, 0 < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) :=
    fun n => (hRn n) ▸ hRpos n
  have hCg0 : ∀ n, 0 < Cg * R n := fun n => mul_pos (by linarith) (hRpos n)
  have hqC : ∀ n, Cg * R n ≤
      Cg * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) := fun n => by
    rw [hRn n]
  exact RetainedCoreHistory.hanchor0_lateW_local_star_P6WA2
    (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming)
    (s := fun n => (K n).time (j n).succ) (y := yG) (ρ := ρnc) hεcone hκd hphi
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) hcan hpar
    hθcap hpinch hjt htj hnot hT₀ hRt hRlim hR0 (Cq := Cg) (fun n => Cg * R n) hCg0 hqC
    hslabsLocStar
    hder hW hgrad hnc hρ

end ObservedHistory

/-- consumer（G3）：star 核孪生 ⇒ G2 的 `∀ c` 核孪生（`hslabsLoc` 特化到 `c*`）——star 前提更弱。 -/
example :
    type_of% @RetainedCoreHistory.eventually_scalar_bound_at_distance_window_local_P6WA2.{u} := by
  intro ε hεle κ C1 C2 hκ Ctime Cgrad phi hphi Cq θ₀ hθ₀ H hend s G hG t ht hts y q ρ hq hqy hR hRt
    p T₀ hT₀ records hcan hradius horder haccuracy hW hslabsLoc hder hgrad hpinch hpinchG hnc hρ D θ
    hD hθ hnot
  exact @RetainedCoreHistory.eventually_scalar_bound_at_distance_window_local_star_P6WA2.{u} ε hεle
    κ C1 C2 hκ Ctime Cgrad phi hphi Cq θ₀ hθ₀ H hend s G hG t ht hts y q ρ hq hqy hR hRt p T₀ hT₀
    records hcan hradius horder haccuracy hW (fun Rad B => hslabsLoc Rad B _) hder hgrad hpinch
    hpinchG hnc hρ D θ hD hθ hnot

/-- consumer（G3）：kernel 帧 star anchor ⇒ G2 的 `∀ c` anchor 孪生。 -/
example :
    type_of% @ObservedHistory.hanchor0_eventSlab_local_P6WA2.{u} := by
  intro ε C1' C2' Ctime' hεcone hC20 phi hphi K j t hjt htj D θcap T₀ p δb records yG hcan hpar
    hθcap hpinch hnot hT₀ hRt Kh hKh σ hσ y hyG R hRpos hRn hRlt κd hκd hvolK Tn aSeed haT hsT has
    pT seedTrace L hL Cg hCg hgood hwin hdistW hslabsLoc
  exact @ObservedHistory.hanchor0_eventSlab_local_star_P6WA2.{u} ε C1' C2' Ctime' hεcone hC20 phi
    hphi K j t hjt htj D θcap T₀ p δb records yG hcan hpar hθcap hpinch hnot hT₀ hRt Kh hKh σ hσ y
    hyG R hRpos hRn hRlt κd hκd hvolK Tn aSeed haT hsT has pT seedTrace L hL Cg hCg hgood hwin
    hdistW (fun Rad B => hslabsLoc Rad B _)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
