import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6WitnessConditionalP6M2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.SurgeryNoShortcutC11D

/-!
# 深度归纳期 4：R4 帧的 hgood / seed 数据中心搬运（O-CH11-DEPTH4D，后缀 `_P6DP4D`）

DEPTH4C 发现的帧错位：路 ii 主定理在选点 `(σ, y)` 跑 driver；KAPPA-ADAPT `hkappaC_tower_of_fresh_P6KA` 与
SLICE-BCBD2 G3②/G5 的形在 R4 中心 `(t ↑ σ, y′ ≍ p′)`、`R = R_k` 上。lead 裁定 (α)：在 R4 帧跑 driver。
本文件交 (α) 的新义务里**可证的部分**：
* **(T1)** `hgood_center_transport_P6DP4D`：selection 的 `hgood`（P6M2:38 binder 形，`4R` 阈值）从旧中心
  `(s, w)` 搬到新中心 `(t, y)`（同一 seed trace、同一 `R`），前提 = 距离可比 + 窗口包含 + `L + δ ≤ Λ`；
* **(T2)** `window_center_transport_P6DP4D`：`hwin` / `hT₀` / 半深度这类 `∀ T > 0, ∀ᶠ` 窗口前提的搬运；
* **(T1′)** `hgood_center_transport_seq_P6DP4D`：序列版，`L := Λ − 2`。
* **(T3 核)** `hcomp_event_of_noShortcut_P6DP4D`：seed trace 的 RegularCrossing 由 trace 字段免费给出，
  距离可比的 event 形 ⇐ `surgery_no_shortcut_C11D`（剩保护条件 / records / activeStage 桥）。
距离可比 (T3) 的来源 = `surgery_no_shortcut_C11D`（event 处 `∀ᶠ t ↑ τ` 的 no-shortcut），
其 RegularCrossing / 保护条件供给与 R4 对角取点 (T4) 见 state-O-CH11-DEPTH4D.md（精确剩余）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped NNReal Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- **(T1) hgood 中心搬运（逐点，`_P6DP4D`，PROVED）**：selection 的 `hgood`（中心 `(s, w)`、参数 `Λ`、`4R` 阈值，
P6M2:38 binder 形）+ 新中心 `(t, y)`（`t ≤ s`，同一 seed trace）处的距离可比
`d_t(seed(t), y) ≤ d_s(seed(s), w) + δ/√R` + 窗口包含 `s − Λ²/R ≤ t − L²/R` + `L + δ ≤ Λ`
⇒ 新中心处的 `hgood`（参数 `L`，同一 `R`、同一阈值 `4R`）。 -/
theorem hgood_center_transport_P6DP4D {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    (H : ObservedHistory.{u}) (Tn aSeed s t : Icc (0 : ℝ) H.horizon)
    (haT : aSeed ≤ Tn) (hsT : s ≤ Tn) (has : aSeed ≤ s) (hat : aSeed ≤ t) (hts : t ≤ s)
    (p : (H.stageAt Tn).Carrier)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) p)
    (w : (H.stageAt s).Carrier) (y : (H.stageAt t).Carrier) {R Λ L δ : ℝ}
    (hδ : 0 ≤ δ) (hL : 0 ≤ L)
    (hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ s),
      (s : ℝ) - Λ ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage s) s)
              (seedTrace.point (H.activeStage s) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) w +
            ENNReal.ofReal (Λ / Real.sqrt R) →
        4 * R ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hcomp : riemannianEDistOf (H.stageMetric (H.activeStage t) t)
        (seedTrace.point (H.activeStage t) (H.activeStage_mono hat)
          (H.activeStage_mono (hts.trans hsT))) y ≤
      riemannianEDistOf (H.stageMetric (H.activeStage s) s)
          (seedTrace.point (H.activeStage s) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) w +
        ENNReal.ofReal (δ / Real.sqrt R))
    (hwinL : (s : ℝ) - Λ ^ 2 / R ≤ (t : ℝ) - L ^ 2 / R) (hLδ : L + δ ≤ Λ) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
      (t : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvt.trans (hts.trans hsT)))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage t) t)
              (seedTrace.point (H.activeStage t) (H.activeStage_mono hat)
                (H.activeStage_mono (hts.trans hsT))) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        4 * R ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z := by
  intro v hav hvt hvw z hd hz
  refine hgood v hav (hvt.trans hts) (by linarith) z ?_ hz
  have hsum : ENNReal.ofReal (δ / Real.sqrt R) + ENNReal.ofReal (L / Real.sqrt R) ≤
      ENNReal.ofReal (Λ / Real.sqrt R) := by
    rw [← ENNReal.ofReal_add (div_nonneg hδ (Real.sqrt_nonneg R))
      (div_nonneg hL (Real.sqrt_nonneg R)), ← add_div]
    apply ENNReal.ofReal_le_ofReal
    exact div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg R)
  calc _ ≤ _ := hd
    _ ≤ (riemannianEDistOf (H.stageMetric (H.activeStage s) s)
          (seedTrace.point (H.activeStage s) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) w + ENNReal.ofReal (δ / Real.sqrt R)) +
          ENNReal.ofReal (L / Real.sqrt R) := add_le_add hcomp le_rfl
    _ = riemannianEDistOf (H.stageMetric (H.activeStage s) s)
          (seedTrace.point (H.activeStage s) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) w +
          (ENNReal.ofReal (δ / Real.sqrt R) + ENNReal.ofReal (L / Real.sqrt R)) := add_assoc _ _ _
    _ ≤ _ := add_le_add le_rfl hsum

/-- **(T2) 窗口型 eventually 前提的中心搬运（`_P6DP4D`，PROVED）**：`hwin` / `hT₀` / 半深度（selection 的
`hwin′`）这类 `∀ T > 0, ∀ᶠ n, f n ≤ s n − T/R n` 前提，在 `s n − t n ≤ 1/R n` 下搬到新中心 `t`（用 `T + 1`）。 -/
theorem window_center_transport_P6DP4D {f s t R : ℕ → ℝ}
    (hclose : ∀ n, s n - t n ≤ 1 / R n)
    (h : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, f n ≤ s n - T / R n) :
    ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, f n ≤ t n - T / R n := by
  intro T hT
  filter_upwards [h (T + 1) (by linarith)] with n hn
  have h1 : (T + 1) / R n = T / R n + 1 / R n := by
    rw [add_div]
  have h2 := hclose n
  linarith

/-- **(T1′) 序列版（`_P6DP4D`，PROVED）**：逐 `n` 的距离可比（`δ = 1`）+ `s n − t n ≤ 1/R n` + `2 ≤ Λ n`
⇒ 新中心 `(t n, y n)` 处的 hgood，参数 `L n := Λ n − 2`（`Λ → ∞` ⇒ `L → ∞`）。R4 帧里 `t_m` 是从
`∀ᶠ t ↑ σ` 集合里逐 `m` 取的，所以距离可比按 `∀ n` 给出。 -/
theorem hgood_center_transport_seq_P6DP4D {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    (H : ℕ → ObservedHistory.{u}) (Tn aSeed s t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, s n ≤ Tn n) (has : ∀ n, aSeed n ≤ s n)
    (hat : ∀ n, aSeed n ≤ t n) (hts : ∀ n, t n ≤ s n)
    (p : ∀ n, ((H n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (H n) ((H n).activeStage (aSeed n))
      ((H n).activeStage (Tn n)) ((H n).activeStage_mono (haT n)) (p n))
    (w : ∀ n, ((H n).stageAt (s n)).Carrier) (y : ∀ n, ((H n).stageAt (t n)).Carrier)
    {R Λ : ℕ → ℝ} (hR : ∀ n, 0 < R n) (hΛ : ∀ n, 2 ≤ Λ n)
    (hclose : ∀ n, (s n : ℝ) - t n ≤ 1 / R n)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (H n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ s n),
      (s n : ℝ) - Λ n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((H n).stageAt v).Carrier,
        riemannianEDistOf ((H n).stageMetric ((H n).activeStage v) v)
            ((seedTrace n).point ((H n).activeStage v) ((H n).activeStage_mono hav)
              ((H n).activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((H n).stageMetric ((H n).activeStage (s n)) (s n))
              ((seedTrace n).point ((H n).activeStage (s n)) ((H n).activeStage_mono (has n))
                ((H n).activeStage_mono (hsT n))) (w n) +
            ENNReal.ofReal (Λ n / Real.sqrt (R n)) →
        4 * R n ≤ metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) z →
        (H n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hcomp : ∀ n, riemannianEDistOf ((H n).stageMetric ((H n).activeStage (t n)) (t n))
        ((seedTrace n).point ((H n).activeStage (t n)) ((H n).activeStage_mono (hat n))
          ((H n).activeStage_mono ((hts n).trans (hsT n)))) (y n) ≤
      riemannianEDistOf ((H n).stageMetric ((H n).activeStage (s n)) (s n))
          ((seedTrace n).point ((H n).activeStage (s n)) ((H n).activeStage_mono (has n))
            ((H n).activeStage_mono (hsT n))) (w n) +
        ENNReal.ofReal (1 / Real.sqrt (R n))) :
    ∀ n, ∀ (v : Icc (0 : ℝ) (H n).horizon) (hav : aSeed n ≤ v) (hvt : v ≤ t n),
      (t n : ℝ) - (Λ n - 2) ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((H n).stageAt v).Carrier,
        riemannianEDistOf ((H n).stageMetric ((H n).activeStage v) v)
            ((seedTrace n).point ((H n).activeStage v) ((H n).activeStage_mono hav)
              ((H n).activeStage_mono (hvt.trans ((hts n).trans (hsT n))))) z ≤
          riemannianEDistOf ((H n).stageMetric ((H n).activeStage (t n)) (t n))
              ((seedTrace n).point ((H n).activeStage (t n)) ((H n).activeStage_mono (hat n))
                ((H n).activeStage_mono ((hts n).trans (hsT n)))) (y n) +
            ENNReal.ofReal ((Λ n - 2) / Real.sqrt (R n)) →
        4 * R n ≤ metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) z →
        (H n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z := by
  intro n
  have hΛn := hΛ n
  have hRn := hR n
  have hwinL : (s n : ℝ) - Λ n ^ 2 / R n ≤ (t n : ℝ) - (Λ n - 2) ^ 2 / R n := by
    have h1 : (Λ n - 2) ^ 2 / R n + 1 / R n ≤ Λ n ^ 2 / R n := by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ hRn.le
      nlinarith
    linarith [hclose n]
  exact hgood_center_transport_P6DP4D (H n) (Tn n) (aSeed n) (s n) (t n) (haT n) (hsT n) (has n)
    (hat n) (hts n) (p n) (seedTrace n) (w n) (y n) zero_le_one (by linarith) (hgood n)
    (hcomp n) hwinL (by linarith)

/-- **(T3 核) crossing 处的距离可比（event 形，`_P6DP4D`，PROVED）**：seed trace（任意 `BackwardPointTrace`）
在 event `e` 两侧的点之间的 RegularCrossing 由 trace 结构字段 `crossing` 免费给出；新中心点 `ym ↦ yp` 的
crossing + 两个保护条件 ⇒ `surgery_no_shortcut_C11D`：`∀ δ > 0, ∀ᶠ t ↑ time e⁺`，
`d_{e⁻,t}(seed, ym) ≤ d_{e⁺,τ}(seed, yp) + δ`。这正是 (T1) 的 `hcomp`（取 `δ := 1/√R`）在 event 形的来源；
剩余 = 保护条件（(SEP′) 型）、`S / hOld / hcan` ⇐ records（照 `hevent_of_records_C11D`）、activeStage 桥。 -/
theorem hcomp_event_of_noShortcut_P6DP4D (H : ObservedHistory.{u}) (e : Fin H.eventCount)
    {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {endpoint : (H.stage last).Carrier}
    (A : BackwardPointTrace H first last hle endpoint)
    (hf : first ≤ e.castSucc) (hl : e.succ ≤ last)
    {fixed : StaticCapScaffold} {Dc εc : ℝ} {mc : ℕ}
    (S : ∀ b : (H.event e).RetainedBoundaryIndex,
      (H.event e).PresentedStaticCap fixed Dc mc εc b)
    (hOld : (H.event e).old = (H.event e).transition.trace.retainedCore)
    (hcanonical : ∀ b, (S b).hasCanonicalWindow) (hε : εc ≤ 1 / 2)
    (hD : StandardCap.transitionEnd + 10 < Dc)
    {ym : (H.stage e.castSucc).Carrier} {yp : (H.stage e.succ).Carrier}
    (hy : (H.event e).RegularCrossing ym yp)
    (hseedprot : ∀ b, A.point e.succ (hf.trans (Fin.castSucc_lt_succ (i := e)).le) hl ∉
      (S b).window '' {x : standardCapWindow Dc | ‖x.val‖ ≤ StandardCap.transitionEnd + 10})
    (hyprot : ∀ b, yp ∉ (S b).window ''
      {x : standardCapWindow Dc | ‖x.val‖ ≤ StandardCap.transitionEnd + 10})
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ t in 𝓝[<] H.time e.succ,
      riemannianEDistOf (H.stageMetric e.castSucc t)
          (A.point e.castSucc hf ((Fin.castSucc_lt_succ (i := e)).le.trans hl)) ym ≤
        riemannianEDistOf (H.stageMetric e.succ (H.time e.succ))
            (A.point e.succ (hf.trans (Fin.castSucc_lt_succ (i := e)).le) hl) yp +
          ENNReal.ofReal δ :=
  H.surgery_no_shortcut_C11D e S hOld hcanonical hε hD (A.crossing e hf hl) hy hseedprot hyprot hδ

/-- **consumer（R4 中心的 Hdist ⇒ Hder）**：搬运后的 `hgood` / `hwin`（T1′ / T2）+ 新中心 `(σ, y)` 处的条件形
`hdistC`（P6M2:38 binder 逐字，`L := Λ − 2`）⇒ 新中心的 `hwitC` ∧ `hderivC`（P6M2:38 结论逐字）。 -/
example {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    (Kh : ℕ → ObservedHistory.{u}) (Tn aSeed s σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT₀ : ∀ n, s n ≤ Tn n) (has₀ : ∀ n, aSeed n ≤ s n)
    (has : ∀ n, aSeed n ≤ σ n) (hts : ∀ n, σ n ≤ s n) (hsT : ∀ n, σ n ≤ Tn n)
    (p : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (p n))
    (w : ∀ n, ((Kh n).stageAt (s n)).Carrier) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
    (R Λ L : ℕ → ℝ) (hLdef : L = fun n => Λ n - 2) (hR : ∀ n, 0 < R n) (hΛ : ∀ n, 2 ≤ Λ n)
    (hΛlim : Tendsto Λ atTop atTop) (hclose : ∀ n, (s n : ℝ) - σ n ≤ 1 / R n)
    (hgood₀ : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ s n),
      (s n : ℝ) - Λ n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((Kh n).stageAt v).Carrier,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT₀ n)))) z ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (s n)) (s n))
              ((seedTrace n).point ((Kh n).activeStage (s n)) ((Kh n).activeStage_mono (has₀ n))
                ((Kh n).activeStage_mono (hsT₀ n))) (w n) +
            ENNReal.ofReal (Λ n / Real.sqrt (R n)) →
        4 * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hcomp : ∀ n, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono ((hts n).trans (hsT₀ n)))) (y n) ≤
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (s n)) (s n))
          ((seedTrace n).point ((Kh n).activeStage (s n)) ((Kh n).activeStage_mono (has₀ n))
            ((Kh n).activeStage_mono (hsT₀ n))) (w n) +
        ENNReal.ofReal (1 / Real.sqrt (R n)))
    (hwin₀ : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ s n - T / R n)
    (hdistC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n))) :
    (∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
        ((Kh n).activeStage_mono hvt) x,
        4 * R n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
        ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) eps C1' C2'
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
          Wt.capTubeHasNeckChart eps) ∧
    (∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
        ((Kh n).activeStage_mono hvt) x,
        4 * R n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
        |derivWithin (fun v' => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v')
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
          (Iic (v : ℝ)) v| ≤
          Ctime' * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ^ 2) := by
  subst hLdef
  exact ObservedHistory.hwitC_hderivC_of_hdistC_P6M2 Kh Tn aSeed σ haT hsT has p seedTrace y R
    (fun n => Λ n - 2) hR
    ((tendsto_atTop_add_const_right _ (-2) hΛlim).congr fun n => (sub_eq_add_neg _ _).symm)
    (hgood_center_transport_seq_P6DP4D Kh Tn aSeed s σ haT hsT₀ has₀ has hts p seedTrace w y hR
      hΛ hclose hgood₀ hcomp)
    (window_center_transport_P6DP4D (f := fun n => (aSeed n : ℝ)) (s := fun n => (s n : ℝ))
      (t := fun n => (σ n : ℝ)) hclose hwin₀) hdistC

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
