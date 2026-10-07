import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KdataRescaleNominalP6NI
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SepTnP6SN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LateKdataNominalP6NI

/-!
# 重标度 frame 的 at-Tn 小性 / (DLT) 搬运 + `hdistC` consumer（S-CH11-NOMID G3，后缀 `_P6NI`）

SEPTN G1（`P6SepTnP6SN`）已给 **frame-covariant 的 at-Tn 核** `sepWK_of_smallAtTn_P6SN`（`ρn : ℕ → ℝ`
逐 `n`、小性 / (DLT) 只在单个时刻 `Tn n` 的半窗上给出，不含 `Tn → ∞`），其 OPEN (i) / HANDOVER 第 1 项
是它在重标度 prefix 路线上的输入搬运。本文件只做这个差集，不重做核：
* `smallAtTn_rescale_P6NI`：原尺度 native `recent_cutoff_smallness` + 原尺度 `recordsK` 的 nominal 识别
  `hnomO` ⇒ 重标度 late records 的 at-Tn 小性，`ρn n := (N.params.rescale_P6N (c n)).neckRadius (Tn n)`
  （`= ρ(c Tn)/√c`；与 `nominal̃ = nominal/√c` 的因子抵消）。需要 `c n · Tn n → ∞`（P6SEL3 prefix
  `k + 1 ≤ Tno k` 给，`tendsto_mul_Tn_atTop_P6SN`）；**不需要** `Tn → ∞`；
* `deltaAtTn_rescale_P6NI`：共同 `δ / Λ`（`hpδ hprc`，`exists_lateKdata_…_nominal_P6NI` 的输出）+ 原尺度
  `delta_tendsto` ⇒ 重标度侧 (DLT) at-Tn（`rescale_P6N_eval`：`δ̃(t/c) = δ(t)`）；
* 文件末 `example`：G1 `exists_lateKdata_of_P5L_antitone_nominal_P6NI`（`q := N.params`、
  `recs := N.records`）的输出 ⇒ 上面的 `hnomO / hpδ / hprc`；
* consumer `hdistC_of_smallAtTn_rescale_P6NI`：重标度 history 上的条件形 `hdistC`，`hTn` 槽被 `hcT`
  （`c·Tn → ∞`）取代，`hδK / hnomId / 原尺度 native smallness` 全部经上面两条搬运；`d`（HDISTC 体积数据）
  只作为 `hdistC_of_sep_P6CD` 的输入，**不再**与 native `records / params` 绑定（lead：(A) 归 P6CGK）。
由 build-logs/scratch/S-CH11-NOMID/mk_d.py 生成。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **重标度侧 at-Tn 小性（`_P6NI`）**：`ρn n = (N.params.rescale_P6N (c n)).neckRadius (Tn n)`；
`c·Tn → ∞` 时，原时间窗 `[c Tn/2, c Tn]` 上取原尺度 native 小性，`nominal̃ = nominal/√c`。 -/
theorem smallAtTn_rescale_P6NI {Ko : ℕ → RetainedCoreHistory.{u}} {c : ℕ → ℝ}
    {hc : ∀ n, 0 < c n} {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    (recordsK : ∀ n (i : Fin (Ko n).eventCount), T₀ n ≤ (Ko n).time i.succ →
      GeometricCutoffRecord (Ko n).toHistory i (p n))
    (N : GC.LongTime.Ch11.Pre841NativeData_C11K (fun n => (Ko n).toHistory))
    (hnomO : ∀ n (i : Fin (Ko n).eventCount) (hi : T₀ n ≤ (Ko n).time i.succ) h,
      (recordsK n i hi).nominalRadius h = (N.records n i).nominalRadius h)
    {Tn : ℕ → ℝ} (hcT : Tendsto (fun n => c n * Tn n) atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ (i : Fin ((Ko n).rescale_P6N (c n) (hc n)).eventCount),
      ((Ko n).rescale_P6N (c n) (hc n)).time i.succ ∈ Icc (Tn n / 2) (Tn n) →
      ∀ (hi : max 1 (T₀ n / c n) ≤ ((Ko n).rescale_P6N (c n) (hc n)).time i.succ) h,
        ((Ko n).recordsKRescale_P6X3 (hc n) (recordsK n) i hi).nominalRadius h ≤
          ε * (N.params.rescale_P6N (c n) (hc n)).neckRadius (Tn n) := by
  intro ε hε
  obtain ⟨T, -, hT⟩ := N.recent_cutoff_smallness ε hε
  filter_upwards [hcT.eventually_ge_atTop T] with n hn i hti hi h
  have hcn : 0 < c n := hc n
  have hi0 : T₀ n ≤ (Ko n).time i.succ :=
    RetainedCoreHistory.le_time_of_rescale_P6X3 (hc n) (t := (Ko n).time i.succ) hi
  have hlo : c n * Tn n / 2 ≤ (Ko n).time i.succ := by
    have h0 : Tn n / 2 ≤ (Ko n).time i.succ / c n := hti.1
    have h1 := (le_div_iff₀ hcn).mp h0
    linarith [h1]
  have hhi : (Ko n).time i.succ ≤ c n * Tn n := by
    have h1 := hti.2
    change (Ko n).time i.succ / c n ≤ Tn n at h1
    rw [div_le_iff₀ hcn] at h1
    linarith
  have h1 := hT (c n * Tn n) hn n i ⟨hlo, hhi⟩ h
  change (recordsK n i hi0).nominalRadius h / Real.sqrt (c n) ≤
    ε * (N.params.neckRadius (c n * Tn n) / Real.sqrt (c n))
  rw [hnomO n i hi0 h, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right h1 (Real.sqrt_pos.mpr hcn).le

/-- **重标度侧 (DLT) at-Tn（`_P6NI`）**：late 参数与 native 共用 `δ / Λ`（`hpδ hprc`）、原尺度
`delta_tendsto`、`c·Tn → ∞` ⇒ 重标度侧半窗上 `Λ̃·δ̃ ≤ 1/2`（`rescale_P6N_eval`：`δ̃(t/c) = δ(t)`）。 -/
theorem deltaAtTn_rescale_P6NI {Ko : ℕ → RetainedCoreHistory.{u}} {c : ℕ → ℝ}
    {hc : ∀ n, 0 < c n} {p : ℕ → CutoffParameters}
    (N : GC.LongTime.Ch11.Pre841NativeData_C11K (fun n => (Ko n).toHistory))
    (hpδ : ∀ n, (p n).delta = N.params.delta)
    (hprc : ∀ n, (p n).recenterConstant = N.params.recenterConstant)
    {Tn : ℕ → ℝ} (hcT : Tendsto (fun n => c n * Tn n) atTop atTop) :
    ∀ᶠ n in atTop, ∀ (i : Fin ((Ko n).rescale_P6N (c n) (hc n)).eventCount),
      ((Ko n).rescale_P6N (c n) (hc n)).time i.succ ∈ Icc (Tn n / 2) (Tn n) →
      ((p n).rescale_P6N (c n) (hc n)).recenterConstant *
        ((p n).rescale_P6N (c n) (hc n)).delta
          (((Ko n).rescale_P6N (c n) (hc n)).time i.succ) ≤ 1 / 2 := by
  obtain ⟨Tδ, hδ⟩ := recenter_delta_tail_of_common_P6CD hpδ hprc N.delta_tendsto
  filter_upwards [hcT.eventually_ge_atTop (2 * Tδ)] with n hn i hti
  have hcn : 0 < c n := hc n
  have hlo : c n * Tn n / 2 ≤ (Ko n).time i.succ := by
    have h0 : Tn n / 2 ≤ (Ko n).time i.succ / c n := hti.1
    have h1 := (le_div_iff₀ hcn).mp h0
    linarith [h1]
  change (p n).recenterConstant *
    ((p n).rescale_P6N (c n) (hc n)).delta ((Ko n).time i.succ / c n) ≤ 1 / 2
  rw [((p n).rescale_P6N_eval (c n) (hc n) ((Ko n).time i.succ)).1]
  exact hδ n _ (by linarith)

/-- **consumer：重标度 history 上的条件形 `hdistC`，`hTn` 槽被 `c·Tn → ∞`（`hcT`）取代（`_P6NI`）**：
`hdistC_of_sep_P6CD` + SEPTN at-Tn 核 `sepWK_of_smallAtTn_P6SN`，核的输入 `hsm / hδ` 由
`smallAtTn_rescale_P6NI / deltaAtTn_rescale_P6NI` 从**原尺度**数据给（`N`、`hnomO`、`hpδ hprc`）；
`ρn n = (N.params.rescale_P6N (c n)).neckRadius (Tn n)`，`hsel4` 是 P6SEL3 G5 的 ④ 逐字（`q := N.params`）。
`d` 只供 HDISTC 体积数据。其余输入（`hcanK hacc hrad hord hT₀` 与 HDISTC 数据）同 G2 consumer。 -/
theorem hdistC_of_smallAtTn_rescale_P6NI (Ko : ℕ → RetainedCoreHistory.{u}) (c : ℕ → ℝ)
    (hc : ∀ n, 0 < c n) {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    (recordsK : ∀ n (i : Fin (Ko n).eventCount), T₀ n ≤ (Ko n).time i.succ →
      GeometricCutoffRecord (Ko n).toHistory i (p n))
    (N : GC.LongTime.Ch11.Pre841NativeData_C11K (fun n => (Ko n).toHistory))
    (hnomO : ∀ n (i : Fin (Ko n).eventCount) (hi : T₀ n ≤ (Ko n).time i.succ) h,
      (recordsK n i hi).nominalRadius h = (N.records n i).nominalRadius h)
    (hpδ : ∀ n, (p n).delta = N.params.delta)
    (hprc : ∀ n, (p n).recenterConstant = N.params.recenterConstant)
    {j : ∀ n, Fin ((Ko n).rescale_P6N (c n) (hc n)).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, ((Ko n).rescale_P6N (c n) (hc n)).time (j n).castSucc < t n) (htj : ∀ n, t n < ((Ko
      n).rescale_P6N (c n) (hc n)).time (j n).succ)
    (σ : ∀ n, Icc (0 : ℝ) ((Ko n).rescale_P6N (c n) (hc n)).toHistory.horizon) (y : ∀ n, (((Ko
      n).rescale_P6N (c n) (hc n)).toHistory.stageAt (σ
        n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hRpos : ∀ n, 0 < R n)
    (d : GC.LongTime.Ch11.Pre841Data_C11K (fun n => ((Ko n).rescale_P6N (c n) (hc n)).toHistory) σ
      y R
      hRpos)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) ((Ko n).rescale_P6N (c n) (hc n)).toHistory.horizon) (haT : ∀ n,
      aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, (((Ko n).rescale_P6N (c n) (hc n)).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace ((Ko n).rescale_P6N (c n) (hc n)).toHistory (((Ko
      n).rescale_P6N (c n) (hc n)).toHistory.activeStage (aSeed n))
      (((Ko n).rescale_P6N (c n) (hc n)).toHistory.activeStage (Tn n)) (((Ko n).rescale_P6N (c n)
        (hc n)).toHistory.activeStage_mono (haT n)) (pT n))
    (r L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (htime : ∀ n, 2 * r n ^ 2 < (Tn n : ℝ))
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature ((Ko n).rescale_P6N (c n) (hc
      n)).toHistory (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    (hcanK : ∀ n i hi b,
      (((Ko n).recordsKRescale_P6X3 (hc n) (recordsK n) i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, ((p n).rescale_P6N (c n) (hc n)).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ ((p n).rescale_P6N (c n) (hc n)).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ ((p n).rescale_P6N (c n) (hc n)).modelOrder)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, max 1 (T₀ n / c n) ≤ (σ n : ℝ) - B / R n)
    (hcT : Tendsto (fun n => c n * (Tn n : ℝ)) atTop atTop)
    (hsel4 : ∀ n,
      R n ≤ ((N.params.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹) :
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, ((Ko n).rescale_P6N (c n) (hc n)).toHistory.isTracedRegion (σ n) (y n)
        (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf (((Ko n).rescale_P6N (c n) (hc n)).toHistory.stageMetric (((Ko
        n).rescale_P6N (c n) (hc n)).toHistory.activeStage (σ n)) (σ
          n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) ((Ko n).rescale_P6N (c n) (hc n)).toHistory.horizon) (hav : aSeed n ≤ v)
        (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace ((Ko n).rescale_P6N (c n) (hc n)).toHistory (((Ko n).rescale_P6N (c
        n) (hc n)).toHistory.activeStage v) (((Ko n).rescale_P6N (c n) (hc
        n)).toHistory.activeStage (σ n))
          (((Ko n).rescale_P6N (c n) (hc n)).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf (((Ko n).rescale_P6N (c n) (hc n)).toHistory.stageMetric (((Ko
          n).rescale_P6N (c n) (hc n)).toHistory.activeStage v) v)
            ((seedTrace n).point (((Ko n).rescale_P6N (c n) (hc n)).toHistory.activeStage v) (((Ko
              n).rescale_P6N (c n) (hc n)).toHistory.activeStage_mono
                hav)
              (((Ko n).rescale_P6N (c n) (hc n)).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point (((Ko n).rescale_P6N (c n) (hc n)).toHistory.activeStage v) le_rfl (((Ko
              n).rescale_P6N (c n) (hc n)).toHistory.activeStage_mono
                hvs)) ≤
          riemannianEDistOf (((Ko n).rescale_P6N (c n) (hc n)).toHistory.stageMetric (((Ko
            n).rescale_P6N (c n) (hc n)).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point (((Ko n).rescale_P6N (c n) (hc n)).toHistory.activeStage (σ n))
                (((Ko n).rescale_P6N (c n) (hc n)).toHistory.activeStage_mono (has n))
                (((Ko n).rescale_P6N (c n) (hc n)).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)) := by
  have hhalf : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ) := fun n => by
    have : 0 ≤ L n ^ 2 / R n := div_nonneg (sq_nonneg _) (hRpos n).le
    linarith [hroom n]
  have htT : ∀ n, t n ≤ (Tn n : ℝ) := fun n => by
    rw [← hσ n]
    exact hsT n
  exact hdistC_of_sep_P6CD hjt htj rfl σ y R hσ hRpos d Tn aSeed haT hsT has pT seedTrace r L hL
    hroom htime hsmall hclock hRr
    (T₀ := fun n => max 1 (T₀ n / c n)) (p := fun n => (p n).rescale_P6N (c n) (hc n))
    (fun n => (Ko n).recordsKRescale_P6X3 (hc n) (recordsK n)) hcanK hacc hrad hord hT₀
    (sepWK_of_smallAtTn_P6SN (K := fun n => (Ko n).rescale_P6N (c n) (hc n))
      (fun n => (Ko n).recordsKRescale_P6X3 (hc n) (recordsK n))
      (s := fun n => (σ n : ℝ)) (Tn := fun n => (Tn n : ℝ))
      (ρn := fun n => (N.params.rescale_P6N (c n) (hc n)).neckRadius (Tn n))
      hjt htT hhalf htime hRpos hRr hsel4
      (deltaAtTn_rescale_P6NI N hpδ hprc hcT) (smallAtTn_rescale_P6NI recordsK N hnomO hcT))

/-- 接线：G1 的输出（`q := N.params`、`recs := N.records`）⇒ 本文件的 `hnomO / hpδ / hprc`。 -/
example {Ko : ℕ → RetainedCoreHistory.{u}}
    (N : GC.LongTime.Ch11.Pre841NativeData_C11K (fun n => (Ko n).toHistory))
    (Q : ℕ → ℝ)
    (hP5L : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T : ℝ, ∀ n, ∃ p : CutoffParameters,
      p.delta = N.params.delta ∧ p.neckRadius = N.params.neckRadius ∧
      p.fixed = N.params.fixed ∧ p.recenterConstant = N.params.recenterConstant ∧
      D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
      ∃ records : ∀ i : Fin (Ko n).eventCount, T ≤ (Ko n).time i.succ →
        GeometricCutoffRecord (Ko n).toHistory i p,
      (∀ i hi b, GC.LongTime.Ch11.linkedCanonicalWindow_C11E ((records i hi).static b)) ∧
      ∀ i hi, (records i hi).nominalRadius =
          (N.records n i).nominalRadius ∧
        (records i hi).delta =
          (N.records n i).delta ∧
        (records i hi).order =
          (N.records n i).order ∧
        (∀ α, HEq ((records i hi).neck α) ((N.records n i).neck α)) ∧
        (∀ b, ((records i hi).static b).neck.scale =
          ((N.records n i).static b).neck.scale) ∧
        ∀ (b) (z : ThreeBall),
          ((records i hi).static b).inclusion
              (((records i hi).static b).witness.cap z) =
            ((N.records n i).static b).inclusion
              (((N.records n i).static b).witness.cap z)) :
    ∃ (T₀ : ℕ → ℝ) (p : ℕ → CutoffParameters)
      (recordsK : ∀ n (i : Fin (Ko n).eventCount), T₀ n ≤ (Ko n).time i.succ →
        GeometricCutoffRecord (Ko n).toHistory i (p n)),
      (∀ n (i : Fin (Ko n).eventCount) (hi : T₀ n ≤ (Ko n).time i.succ) h,
        (recordsK n i hi).nominalRadius h = (N.records n i).nominalRadius h) ∧
      (∀ n, (p n).delta = N.params.delta) ∧
      ∀ n, (p n).recenterConstant = N.params.recenterConstant := by
  obtain ⟨T₀, p, recordsK, -, -, -, -, -, -, hpδ, hprc, hrp⟩ :=
    RetainedCoreHistory.exists_lateKdata_of_P5L_antitone_nominal_P6NI Q N.records hP5L
      N.delta_tendsto N.radius_antitone
  exact ⟨T₀, p, recordsK, fun n i hi h => congrFun (hrp n i hi).1 h, hpδ, hprc⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
