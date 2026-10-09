import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SLTLocalP6SL
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KSWGuardedCone3C11KX

/-!
# `shortSLT_guarded_C11KX ⇒ hWBloc` 直接适配（O-CH11-WBADAPT G1，后缀 `_P6WA2`）

R-C11-19 Q4 / D-19-4 新增裁定：SLTLOCAL G1（`P6SLTLocalP6SL.lean:100–169`）的 binder `hWBloc`
（SLT:249 窗口形 `…_terminal_window_P6WB` 的局部孪生陈述）可以由已交付的 guarded ShortSLT
`shortSLT_guarded_C11KX : 0 < θ → ShortSLTGuarded_C11KX θ`
（`P6KSWGuardedCone3C11KX.lean:659`，PROVED）
**直接适配**，不必先拆 TP / TL2 / TC 的分析叶（`hTPloc`，SLTLOCAL2-A/B）。
* **参数**（只依赖输入 `Ctime`、`θ`，在 history / records / 点 / 窗口之前选定）：
  `Ĉt := max Ctime 1`（`ℝ≥0`，处理 `Ctime = 0`）、`c* := 1 / (2·Ĉt)`、`Bw := θ`；以 `Ĉt` 与同一 `θ` 调 guarded
  ShortSLT，其输出 `Q, Λ, Dcap, Rrad, ζ₀, Rad` 原样填 `hWBloc` 的同名常数。
* **前 slab 导数**：guard `GuardKX_C11KX`（`2·Ĉt·max(R(t, z), q)·(t − v) ≤ 1`）⇒
  `(t − v)·max q R(t, z) ≤ c*`
  （`mul_max_le_cstar_of_guard_P6WA2`）= `hWBloc` 的局部导数前提 ⇒ `|∂ₜR| ≤ Ctime·R² ≤ Ĉt·R²`
  （`abs_le_maxOne_mul_sq_P6WA2`）。
* **final slab 导数 / 梯度 / κ**：`hWBloc` 给整个 `Bw`-窗口（`hnc`：整个 `U`）上的数据，限制到 guard 子集；
  时间导数常数 `Ctime → Ĉt`，梯度常数 `Cgrad` 与 κ 不变。
* **其余**：`Bw = θ` ⇒ records / `T₀` 窗口、Φ-pinching 窗口与 guarded 合同逐字一致；cap-window 年龄条件
  `θ · scale⁻¹` 是同一个 `θ`；`hW`（top 切片 witness）、终端 scalar bound 逐字。
* **结论逐字**：`hWBloc_of_shortSLT_guarded_P6WA2` 的陈述 = `P6SLTLocalP6SL.lean` 中 `hWBloc` binder 的类型
  （三处出现逐字相同，生成器 `build-logs/scratch/O-CH11-WBADAPT/gen1.py` 切文本并断言
  sha256 `4212f81a004cad179e319d3e112430ec3e3c488491f235acef2d0f747feeac5e`）。
**不生产** `hslabsLoc`（局部 producer，SLTPROD 车道）；**不声称 J10 已去**。
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

/-- **guard ⇒ `c*`（`_P6WA2`）**：`2·C·max(R_z, q)·(t − v) ≤ 1`（`GuardKX_C11KX` 的展开形）且 `0 < C`
⇒ `(t − v)·max(q, R_z) ≤ 1/(2·C)`
（`hWBloc` 前 slab 局部导数前提的形，`max` 两参数对调）。 -/
theorem mul_max_le_cstar_of_guard_P6WA2 {Rz q C t v : ℝ} (hC : 0 < C)
    (h : 2 * C * max Rz q * (t - v) ≤ 1) : (t - v) * max q Rz ≤ 1 / (2 * C) := by
  rw [le_div_iff₀ (by positivity), max_comm]
  have e : (t - v) * max Rz q * (2 * C) = 2 * C * max Rz q * (t - v) := by ring
  rw [e]
  exact h

/-- **时间导数常数放大（`_P6WA2`）**：`|d| ≤ C·R²` ⇒ `|d| ≤ max(C, 1)·R²`（`C : ℝ≥0`）。 -/
theorem abs_le_maxOne_mul_sq_P6WA2 {d R : ℝ} {C : ℝ≥0} (h : |d| ≤ C * R ^ 2) :
    |d| ≤ ((max C 1 : ℝ≥0) : ℝ) * R ^ 2 :=
  h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left C 1) (sq_nonneg R))

/-- **`hWBloc` ⇐ guarded ShortSLT（`_P6WA2`，PROVED，无 binder）**：结论逐字 = SLTLOCAL G1
`RetainedCoreHistory.eventually_scalar_bound_at_distance_window_local_P6SL` /
`RetainedCoreHistory.hanchor0_lateW_local_P6SL` / `ObservedHistory.hanchor0_eventSlab_local_P6SL`
的 binder `hWBloc` 的类型。取 `Ĉt := max Ctime 1`、`c := 1/(2·Ĉt)`、`Bw := θ`，
以 `Ĉt` 调 `shortSLT_guarded_C11KX`。 -/
theorem hWBloc_of_shortSLT_guarded_P6WA2 :
    ∀ (ε : ℝ), ε ≤ coneAccuracy → ∀ (κ C1 C2 : ℝ), 0 < κ → ∀ (Ctime Cgrad : ℝ≥0)
      (phi : ℝ → ℝ), Perelman.AdmissiblePinchingFunction phi → ∀ (A : ℝ), 0 < A →
      ∀ (Cq θ : ℝ), 0 < θ →
      ∃ Q Λ Dcap Rrad ζ₀ Rad Bw c : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧
      Dcap ≤ Rrad ∧ 0 < ζ₀ ∧ 0 < Bw ∧ 0 < c ∧
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
          (t - v) * max q (G.flow.scalar t z) ≤ c →
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
  refine ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, θ, 1 / (2 * ((max Ctime 1 : ℝ≥0) : ℝ)), hQ, hΛ, hD, hDR, hζ,
    hθ, by positivity, ?_⟩
  intro H hend s G hG t ht hts y q ρ hq hqy hΛ1 hΛ2 p T₀ hT₀ records hcan hRrad hord hζ' U hUy hW
    hslabs hder hgrad hpinch hpinchG hnc hρ hnot
  refine hmain H hend G hG ht hts y q ρ hq hqy hΛ1 hΛ2 T₀ hT₀ records hcan hRrad hord hζ' U hUy hW
    ?_ ?_ ?_ hpinch hpinchG ?_ hρ hnot
  · intro j first hf z hz B v hv hvw hqv hg
    exact abs_le_maxOne_mul_sq_P6WA2
      (hslabs j first hf z hz B v hv hvw (mul_max_le_cstar_of_guard_P6WA2 hC0 hg) hqv)
  · intro x hx v hv hvw hqv _
    exact abs_le_maxOne_mul_sq_P6WA2 (hder x hx v hv hvw hqv)
  · intro x hx v hv hvw hqv _
    exact hgrad x hx v hv hvw hqv
  · intro T hT hTs hTt hTw _ _ z hz _
    exact hnc T hT hTs hTt hTw z hz

/-- consumer（G1）：适配定理逐字喂 SLTLOCAL G1 的 SLT 核局部孪生 `hWBloc` 槽（类型检查 = binder 对齐）。 -/
example := @RetainedCoreHistory.eventually_scalar_bound_at_distance_window_local_P6SL.{u}
  hWBloc_of_shortSLT_guarded_P6WA2.{u}

/-- consumer（G1）：同一定理喂 anchor 两层孪生的 `hWBloc` 槽。 -/
example := @RetainedCoreHistory.hanchor0_lateW_local_P6SL.{u} hWBloc_of_shortSLT_guarded_P6WA2.{u}

/-- consumer（G1）：kernel 帧 anchor 切换的 `hWBloc` 槽。 -/
example := @ObservedHistory.hanchor0_eventSlab_local_P6SL.{u} hWBloc_of_shortSLT_guarded_P6WA2.{u}

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
