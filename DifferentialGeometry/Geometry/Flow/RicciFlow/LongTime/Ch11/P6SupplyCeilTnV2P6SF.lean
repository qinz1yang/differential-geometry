import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SepRhoPlusFixV2P6SF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDSupplyP6SB3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SupplyRescaleP6HN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CwsUniformP6SN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J9LocSupplyP6KT2

/-!
# 先验供给 ⇒ 前缀 Dt，天花板统一在 `T_n`（O-CH11-SEPFIX G2，后缀 `_P6SF`）

R-C11-22 D-22-7：前缀 Dt 与 SEP 使用**同一 cutoff、同一 Q**（K 帧 `Q n = c n·ρ(c n·Tn n)⁻² = ρ̂(Tn)⁻²`）；
HNOT G5 `prefixDt_rescale_seq_P6HN`（阈值取在观测时刻 `t n = σ`）与 SLICE-BCBD3 `hpre_of_supply_tower_P6SB3`
（`ρs n (t n)`）改为 `T_n` ceiling 版：
* `ceilK_eq_P6SF`：`ρ̂(Tno/c)⁻² = c·ρ(Tno)⁻²`（K 帧天花板 = 原尺度天花板 ×c）。
* `prefixDt_rescale_seq_Tn_P6SF`：观测时刻 `t n ≤ Tn n`，阈值 `c n·ρ(c n·Tn n)⁻²`（供给 + `ρ` 反单调 + 阈值单调）。
  取 `t n := Tn n`（`Tn` 在 slab 内部时）即"前缀 Dt 到 Tn"本身。
* `hpre_of_supply_tower_Tn_P6SF`：G8″ / G9″ 的 `hpre1 / hpre2` 在 `ρs n := fun _ => ρ̂(Tn)` 处。
* consumer：KTRUNC2 L5（J9 截断，`Qs_loc`）与 G1 A4（J6）同一 `Qs_loc`；G8″ 全喂入（`hsepρ` ⇐ G1 A2、
  `hpre1 / hpre2` ⇐ 本文件，同一 `ρs`）。A5 短窗 guard（G8″ 结论里的 `(t − v)·max(…) ≤ 1/(2 max Ctime 1)`）原样保留。
-/

set_option autoImplicit false

/-! CX-WIRE 新文件修订：保留原件声明与证明，修复风格并保留冻结旧源。
原文“已登记 haccuracy”仅指已有条件接口；actual q₀ 的该条件仍待 C12-7′c。
本文件未生产全局 recenter 或 actual haccuracy；late adapter 另交新文件。
不要同时 import/register 原版与 V2，以免同名声明重复。 -/

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

/-- K 帧天花板（`_P6SF`）：`((q.rescale_P6N c).neckRadius (Tno/c))⁻² = c·(ρ(Tno)²)⁻¹`。 -/
theorem ceilK_eq_P6SF (q : CutoffParameters) {c : ℝ} (hc : 0 < c) (Tno : ℝ) :
    ((q.rescale_P6N c hc).neckRadius (Tno / c) ^ 2)⁻¹ = c * (q.neckRadius Tno ^ 2)⁻¹ := by
  change ((q.neckRadius (c * (Tno / c)) / Real.sqrt c) ^ 2)⁻¹ = _
  rw [mul_div_cancel₀ Tno hc.ne', div_pow, Real.sq_sqrt hc.le, inv_div, div_eq_mul_inv]

/-- **前缀 Dt，ceiling 在 `Tn`（`_P6SF`，PROVED）**：K 帧 `K n = (F.tower.history (ind n)).rescale_P6N (c
  n)`，
观测时刻 `t n ≤ Tn n`；阈值 `c n·(ρ(c n·Tn n)²)⁻¹`（与 KTRUNC `tK := Tn`、kernel `hscaleK` 同一 Q）。 -/
theorem prefixDt_rescale_seq_Tn_P6SF {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {C : ℝ≥0}
    (hTD : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius C)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) (ind : ℕ → ℕ) {c : ℕ → ℝ} (hc : ∀ n, 0 < c n)
    {j : ∀ n, Fin (F.tower.history (ind n)).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time (j n).castSucc < t n)
    (htj : ∀ n, t n < ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time (j n).succ)
    (Tn : ℕ → ℝ) (htT : ∀ n, t n ≤ Tn n) :
    (∀ n, ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).EventSlabsDerivative C
        (c n * (q.neckRadius (c n * Tn n) ^ 2)⁻¹) (j n).castSucc) ∧
    (∀ n, (((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).toHistory.event
        (j n)).incoming.DerivativeBoundBefore C (c n * (q.neckRadius (c n * Tn n) ^ 2)⁻¹) (t n))
          := by
  obtain ⟨h1, h2⟩ := prefixDt_rescale_seq_P6HN hTD hanti ind hc hjt htj
  have hle : ∀ n, c n * (q.neckRadius (c n * t n) ^ 2)⁻¹ ≤
      c n * (q.neckRadius (c n * Tn n) ^ 2)⁻¹ := fun n => by
    have ht0 : 0 ≤ t n :=
      ((((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).toHistory.time_nonneg
        (j n).castSucc)).trans (hjt n).le
    exact mul_le_mul_of_nonneg_left (inv_sq_neckRadius_le_P6HN hanti
      (mul_nonneg (hc n).le ht0) (mul_le_mul_of_nonneg_left (htT n) (hc n).le)) (hc n).le
  exact ⟨fun n e he => derivativeBoundBefore_mono_qcan_P6SN _ (hle n) (h1 n e he),
    fun n => derivativeBoundBefore_mono_qcan_P6SN _ (hle n) (h2 n)⟩

/-- **G8″ / G9″ 的 `hpre1 / hpre2`，ceiling 在 `Tn`（`_P6SF`，PROVED）**：`ρs n := fun _ => ρ(c n·Tn
  n)/√(c n)`
（时间常值）时阈值 `max (n+1) (ρs n (t n))⁻² = max (n+1) (c n·ρ(c n·Tn n)⁻²)`。SLICE-BCBD3
`hpre_of_supply_tower_P6SB3` 的 `T_n` 版。 -/
theorem hpre_of_supply_tower_Tn_P6SF {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {Ctime : ℝ≥0}
    (hTD : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) (ind : ℕ → ℕ) {c : ℕ → ℝ} (hc : ∀ n, 0 < c n)
    {j : ∀ n, Fin (F.tower.history (ind n)).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time (j n).castSucc < t n)
    (htj : ∀ n, t n < ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time (j n).succ)
    (Tn : ℕ → ℝ) (htT : ∀ n, t n ≤ Tn n) :
    (∀ n, ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).EventSlabsDerivative Ctime
        (max ((n : ℝ) + 1) ((q.neckRadius (c n * Tn n) / Real.sqrt (c n)) ^ 2)⁻¹) (j n).castSucc) ∧
    (∀ n, (((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).toHistory.event
        (j n)).incoming.DerivativeBoundBefore Ctime
          (max ((n : ℝ) + 1) ((q.neckRadius (c n * Tn n) / Real.sqrt (c n)) ^ 2)⁻¹) (t n)) := by
  obtain ⟨h1, h2⟩ := prefixDt_rescale_seq_Tn_P6SF hTD hanti ind hc hjt htj Tn htT
  have heq : ∀ n, ((q.neckRadius (c n * Tn n) / Real.sqrt (c n)) ^ 2)⁻¹ =
      c n * (q.neckRadius (c n * Tn n) ^ 2)⁻¹ := fun n => by
    rw [div_pow, Real.sq_sqrt (hc n).le, inv_div, div_eq_mul_inv]
  have hle : ∀ n, c n * (q.neckRadius (c n * Tn n) ^ 2)⁻¹ ≤
      max ((n : ℝ) + 1) ((q.neckRadius (c n * Tn n) / Real.sqrt (c n)) ^ 2)⁻¹ :=
    fun n => (heq n) ▸ le_max_right _ _
  exact ⟨fun n e he => derivativeBoundBefore_mono_qcan_P6SN _ (hle n) (h1 n e he),
    fun n => derivativeBoundBefore_mono_qcan_P6SN _ (hle n) (h2 n)⟩

/-- **consumer（`_P6SF`）：同一 `Qs_loc`**——KTRUNC2 L5 `hslabKT_of_supply_P6KT2`（J9 截断 Dt 到 `Tno`）与
G1 A4 `j6_of_accuracy_P6SF`（J6，∀ n）在同一 `Qs_loc n := max ((n+1)/c n) (ρ(Tno n)²)⁻¹` 上同时成立
（原尺度 Ho 帧；J6 由已登记 haccuracy 付，小 n 由前瞻 ∀k 形覆盖）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} {Ctime Ctime₀ : ℝ≥0}
    (hTD : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime) (hC : Ctime ≤ Ctime₀)
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (haccq : ∀ u : ℝ, 0 ≤ u →
      q.delta u ^ 2 * q.neckRadius u < q.neckRadius (2 * u) / (u + 1))
    (ind : ℕ → ℕ) {p : ℕ → CutoffParameters} {T₀ c σ L R Tno Tn : ℕ → ℝ}
    (recordsK : ∀ n (i : Fin (F.tower.history (ind n)).eventCount),
      max (T₀ n) (c n * (σ n - L n / R n)) ≤ (F.tower.history (ind n)).time i.succ →
        GeometricCutoffRecord (F.tower.history (ind n)).toHistory i (p n))
    (hc : ∀ n, 0 < c n) (hTn : ∀ n, Tn n = Tno n / c n) (h2 : ∀ n, 2 * c n < Tno n)
    (hNT : ∀ n : ℕ, (n : ℝ) + 1 ≤ Tno n) (hR1 : ∀ n, 1 ≤ R n)
    (hL : ∀ n, Tn n - 1 ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (hlink : ∀ n (t : ℝ), 0 ≤ t → (p n).delta t = q.delta t ∧ (p n).neckRadius t = q.neckRadius t)
    (hΛδ : ∀ n (i : Fin (F.tower.history (ind n)).eventCount),
      max (T₀ n) (c n * (σ n - L n / R n)) ≤ (F.tower.history (ind n)).time i.succ →
        (p n).recenterConstant * (p n).delta ((F.tower.history (ind n)).time i.succ) ≤ 1 / 2)
    (hρc : ∀ n : ℕ, q.neckRadius (Tno n) ^ 2 ≤ c n / ((n : ℝ) + 1)) :
    let Qs : ℕ → ℝ := fun n => max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹
    (∀ n (j : Fin (F.tower.history (ind n)).eventCount),
      ((F.tower.history (ind n)).toHistory.event j).incoming.DerivativeBoundBefore Ctime₀ (Qs n)
        (min ((F.tower.history (ind n)).time j.succ) (Tno n))) ∧
    (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
      ((recordsK n i hi).static b).neck.scale) := by
  intro Qs
  exact ⟨GC.LongTime.Ch11.hslabKT_of_supply_P6KT2 hTD hC hanti (fun t ht => q.neckRadius_pos t ht)
      ind Qs Tno (fun _ => le_max_right _ _),
    j6_of_accuracy_P6SF recordsK hc hTn h2 hNT hR1 hL hlink hanti haccq hΛδ hρc⟩

/-- **consumer（`_P6SF`）：G8″ `hslabs_of_sepRho_prefixDt_P6SB3` 喂入**——`ρs n := fun _ => ρ̂(Tn)`（时间常值），
`hsepρ` ⇐ G1 A2 `sepRhoPlusK_branch_of_accuracy_P6SF`（已登记 haccuracy），`hpre1 / hpre2` ⇐
`hpre_of_supply_tower_Tn_P6SF`（先验供给，同一 ceiling `Tn`）。K 帧 `K n = (F.tower.history (ind
  n)).rescale_P6N (c n)`，
records 参数 `p n = q.rescale_P6N (c n)`。G8″ 其余前提逐字（生成器 gen2.py 从源抽取）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} {Ctime : ℝ≥0}
    (hTD : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (haccq : ∀ u : ℝ, 0 ≤ u →
      q.delta u ^ 2 * q.neckRadius u < q.neckRadius (2 * u) / (u + 1))
    (ind : ℕ → ℕ) {c : ℕ → ℝ} (hc : ∀ n, 0 < c n) {eps C1' C2' : ℝ}
    {Cg : ℝ}
    (hC2 : 0 ≤ C2') (hCg : 1 ≤ Cg) {K : ℕ → RetainedCoreHistory.{u}}
    (hK : K = fun n => (F.tower.history (ind n)).rescale_P6N (c n) (hc n))
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ} (hjt : ∀ n, (K n).time (j n).castSucc < t n)
    (htj : ∀ n, t n < (K n).time (j n).succ) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (j n).castSucc).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) (hR1 : ∀ n, 1 ≤ R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((K n).toHistory.stageAt v).Carrier,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
          z →
        (K n).toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime v z)
    {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (a₀ : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a₀ n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage s) s)
        (a₀ n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (T₀X : ℕ → ℝ) (hT₀X : ∀ n, T₀X n ≤ aSeed n)
    (hOldX : ∀ n (e : Fin (K n).eventCount), T₀X n ≤ (K n).toHistory.time e.succ →
      ((K n).toHistory.event e).old = ((K n).toHistory.event e).transition.trace.retainedCore)
    (hdσ : ∀ n, riemannianEDistOf ((K n).toHistory.stageMetric
        ((K n).toHistory.activeStage (σ n)) (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) ≠ ⊤)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    (hp : p = fun n => q.rescale_P6N (c n) (hc n))
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    {θ₀ : ℝ}
    (Tno : ℕ → ℝ) (hθ₀ : 0 ≤ θ₀)
    (hTn : ∀ n, (Tn n : ℝ) = Tno n / c n) (h2 : ∀ n, 2 * c n < Tno n)
    (hNT : ∀ n : ℕ, (n : ℝ) + 1 ≤ Tno n)
    (hwinT : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - 1 ^ 2 / 2 ≤ t n - T / R n)
    (hΛδ : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (p n).recenterConstant * (p n).delta ((K n).time i.succ) ≤ 1 / 2)
    (hρ0 : ∀ᶠ n in atTop, 8 * θ₀ * (p n).neckRadius 0 ^ 2 ≤ (Tn n : ℝ))
    (habs : ∀ n : ℕ, (n : ℝ) + 1 ≤ ((p n).neckRadius (Tn n) ^ 2)⁻¹)
    (htT : ∀ n, t n ≤ (Tn n : ℝ)) :
    ∀ Rad B : ℝ, ∀ᶠ n in atTop,
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
        1 / (2 * max (Ctime : ℝ) 1) →
      Cg * R n < (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
        (Btr.point i.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun w =>
          (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar w
            (Btr.point i.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
        Ctime * (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
          (Btr.point i.castSucc hf (Fin.le_last _)) ^ 2 := by
  subst hK hp
  obtain ⟨hpre1, hpre2⟩ := hpre_of_supply_tower_Tn_P6SF hTD hanti ind hc hjt htj
    (fun n => (Tn n : ℝ)) htT
  exact ObservedHistory.hslabs_of_sepRho_prefixDt_P6SB3 hC2 hCg hjt htj σ hσ y yG hyG R hR hR1 hRn
    Tn aSeed haT hsT has pT seedTrace L hL hgood hr hsmall hclock a₀ ha₀ hpin hRa T₀X hT₀X hOldX hdσ
    hwin recordsK hcanK hacc hrad hord hT₀
    (fun n _ => q.neckRadius (c n * (Tn n : ℝ)) / Real.sqrt (c n))
    (sepRhoPlusK_branch_of_accuracy_P6SF recordsK hθ₀ hR hc hTn h2 hNT hwinT
      (fun n => anti_rescale_P6SF (hc n) hanti) (fun n => hacc_rescale_P6SF (hc n) haccq) hΛδ hρ0
        habs)
    hpre1 hpre2

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
