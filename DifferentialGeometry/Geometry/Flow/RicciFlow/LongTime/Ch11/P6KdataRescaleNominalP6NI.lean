import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KdataRescaleP6X3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SepNeckP6CD

/-!
# 重标度下的 reparameterization / nominal 识别（S-CH11-NOMID G2，后缀 `_P6NI`）

`KdataRescale_P6X3` 把原尺度 K 层数据搬到重标度 history `K̃ = Ko.rescale_P6N c`，late records 取
`recordsKRescale_P6X3`（`GeometricCutoffRecord.rescale_P6M`）。本文件：识别在重标度下的保持——
lead R-C11-8 裁定 (2)：**关系带因子**，不是无因子 equality：
* `nominalRadius̃ = nominalRadius_native / √c`；
* tube `neck.scalẽ = c · neck.scale_native`、static `neck.scalẽ = c · static.neck.scale_native`；
* `delta`、`order` 不变。
（`rescale_P6M`：`nominalRadius h := R.nominalRadius h / √μ`；`rescale_P6M_scale`：`scale ↦ μ · scale`。）
内容：
* `recordsKRescale_factor_P6NI`：原尺度 reparameterization 合取（`P6LateKdataNominalP6NI` 的输出形，
  inline）⇒ 上述五条因子关系（对参考 records `recs`）；
* `KdataRescale_nominal_P6NI`：`KdataRescale_P6X3` 的原结论 ∧ 因子关系（多一个原尺度前提
  `hrp`；参考族取 `recordsF`，它本来就是该定理的前提）；
* `hnomId_rescale_P6NI`：`hdistC_of_native_P6CD` 的 `hnomId` 槽在 `K̃` 上的来源——native 重标度数据
  `recsN`（`d.native.records`）与原尺度参考族 `recsO` 的关系**也按因子形** `nominal_N = nominal_O / √c` 给；
* consumer `hdistC_of_native_rescale_P6NI`：`hdistC_of_native_P6CD` 在 `K := Ko.rescale_P6N c`、
  `recordsK := recordsKRescale_P6X3`、`T₀ := max 1 (T₀/c)`、`p := p.rescale_P6N c` 上，`hnomId` 由上面给，
  其余输入（`hT₀ hTn hsel4 hδK` 与 `HDISTC` 数据）逐字保留。
**不在本文件解决**：`hTn : Tn̂ → ∞` 与 `d.native.params` 的 `n` 无关（rescaled 参数
`q.rescale_P6N (c n)` 随 `n` 变，P6SEL3 G5 S3 BLOCKED）——见 DELIVERIES G2 块的 repair 说明。
由 build-logs/scratch/S-CH11-NOMID/mk_b.py 生成。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

/-- **重标度的因子关系（`_P6NI`）**：原尺度 reparameterization 合取（`recordsK` 对参考 `recs`）⇒
重标度 late record 对**原尺度** `recs` 的带因子关系：`nominal̃ = nominal / √c`、tube / static
`neck.scalẽ = c · neck.scale`、`delta / order` 不变。 -/
theorem recordsKRescale_factor_P6NI (K : RetainedCoreHistory.{u}) {c : ℝ} (hc : 0 < c)
    {p q : CutoffParameters} {T₀ : ℝ}
    (recordsK : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ →
      GeometricCutoffRecord K.toHistory i p)
    (recs : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i q)
    (hrp : ∀ (i : Fin K.eventCount) (hi : T₀ ≤ K.time i.succ),
      (recordsK i hi).nominalRadius =
        (recs i).nominalRadius ∧
      (recordsK i hi).delta =
        (recs i).delta ∧
      (recordsK i hi).order =
        (recs i).order ∧
      (∀ α, HEq ((recordsK i hi).neck α) ((recs i).neck α)) ∧
      (∀ b, ((recordsK i hi).static b).neck.scale =
        ((recs i).static b).neck.scale) ∧
      ∀ (b) (z : ThreeBall),
        ((recordsK i hi).static b).inclusion
            (((recordsK i hi).static b).witness.cap z) =
          ((recs i).static b).inclusion
            (((recs i).static b).witness.cap z))
    (i : Fin (K.rescale_P6N c hc).eventCount)
    (hi : max 1 (T₀ / c) ≤ (K.rescale_P6N c hc).time i.succ) :
    (∀ h, (K.recordsKRescale_P6X3 hc recordsK i hi).nominalRadius h =
      (recs i).nominalRadius h / Real.sqrt c) ∧
    (K.recordsKRescale_P6X3 hc recordsK i hi).delta = (recs i).delta ∧
    (K.recordsKRescale_P6X3 hc recordsK i hi).order = (recs i).order ∧
    (∀ α, ((K.recordsKRescale_P6X3 hc recordsK i hi).neck α).scale =
      c * ((recs i).neck α).scale) ∧
    (∀ b, ((K.recordsKRescale_P6X3 hc recordsK i hi).static b).neck.scale =
      c * ((recs i).static b).neck.scale) := by
  have hi0 : T₀ ≤ K.time i.succ := le_time_of_rescale_P6X3 hc (t := K.time i.succ) hi
  obtain ⟨hnom, hdel, hord, -, hsc, -⟩ := hrp i hi0
  refine ⟨fun h => ?_, hdel, hord, fun α => ?_, fun b => ?_⟩
  · exact congrArg (fun z => z / Real.sqrt c) (congrFun hnom h)
  · have hn : (K.recordsKRescale_P6X3 hc recordsK i hi).nominalRadius ⟨α⟩ =
        (recs i).nominalRadius ⟨α⟩ / Real.sqrt c :=
      congrArg (fun z => z / Real.sqrt c) (congrFun hnom ⟨α⟩)
    rw [(K.recordsKRescale_P6X3 hc recordsK i hi).scale_eq α, (recs i).scale_eq α, hn, div_pow,
      Real.sq_sqrt hc.le, inv_div, div_eq_mul_inv]
  · have h1 := ((recordsK i hi0).static b).rescale_P6M_scale c hc
    exact h1.trans (congrArg (fun z => c * z) (hsc b))

end RetainedCoreHistory

/-- **`hnomId` 槽在重标度 history 上（`_P6NI`）**：late `recordsKRescale` 的 nominal 半径等于 native 重标度
records `recsN` 的，条件：原尺度 reparameterization 合取（`recordsK` 对 `recsO`）+ **因子形**的
`nominal_N = nominal_O / √c`（不是无因子 equality）。 -/
theorem hnomId_rescale_P6NI {Ko : ℕ → RetainedCoreHistory.{u}} {c : ℕ → ℝ} {hc : ∀ n, 0 < c n}
    {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters} {q q' : CutoffParameters}
    (recordsK : ∀ n (i : Fin (Ko n).eventCount), T₀ n ≤ (Ko n).time i.succ →
      GeometricCutoffRecord (Ko n).toHistory i (p n))
    (recsO : ∀ n (i : Fin (Ko n).eventCount), GeometricCutoffRecord (Ko n).toHistory i q)
    (hrp : ∀ n (i : Fin (Ko n).eventCount) (hi : T₀ n ≤ (Ko n).time i.succ),
      (recordsK n i hi).nominalRadius =
        (recsO n i).nominalRadius ∧
      (recordsK n i hi).delta =
        (recsO n i).delta ∧
      (recordsK n i hi).order =
        (recsO n i).order ∧
      (∀ α, HEq ((recordsK n i hi).neck α) ((recsO n i).neck α)) ∧
      (∀ b, ((recordsK n i hi).static b).neck.scale =
        ((recsO n i).static b).neck.scale) ∧
      ∀ (b) (z : ThreeBall),
        ((recordsK n i hi).static b).inclusion
            (((recordsK n i hi).static b).witness.cap z) =
          ((recsO n i).static b).inclusion
            (((recsO n i).static b).witness.cap z))
    (recsN : ∀ n (i : Fin ((Ko n).rescale_P6N (c n) (hc n)).eventCount),
      GeometricCutoffRecord ((Ko n).rescale_P6N (c n) (hc n)).toHistory i q')
    (hrecsN : ∀ n (i : Fin ((Ko n).rescale_P6N (c n) (hc n)).eventCount) h,
      (recsN n i).nominalRadius h = (recsO n i).nominalRadius h / Real.sqrt (c n)) :
    ∀ n (i : Fin ((Ko n).rescale_P6N (c n) (hc n)).eventCount)
      (hi : max 1 (T₀ n / c n) ≤ ((Ko n).rescale_P6N (c n) (hc n)).time i.succ) h,
      ((Ko n).recordsKRescale_P6X3 (hc n) (recordsK n) i hi).nominalRadius h =
        (recsN n i).nominalRadius h := fun n i hi h =>
  ((Ko n).recordsKRescale_factor_P6NI (hc n) (recordsK n) (recsO n) (hrp n) i hi).1 h |>.trans
    (hrecsN n i h).symm

/-- **`KdataRescale_P6X3` ∧ 因子关系（`_P6NI`）**：多一个原尺度前提——`recordsK` 是参考族 `recordsF` 的
reparameterization 合取；多一个结论——重标度 late records 对**原尺度** `recordsF` 的带因子关系
（`nominal̃ = nominal/√c`、tube / static `neck.scalẽ = c · neck.scale`、`delta / order` 不变）。 -/
theorem KdataRescale_nominal_P6NI :
    ∃ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi ∧
    ∀ (Ko : ℕ → RetainedCoreHistory.{u}) (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
      (Ctime₀ : ℝ≥0) (Q T₀ : ℕ → ℝ) (p pF : ℕ → CutoffParameters)
      (recordsK : ∀ n (i : Fin (Ko n).eventCount), T₀ n ≤ (Ko n).time i.succ →
        GeometricCutoffRecord (Ko n).toHistory i (p n))
      (a₀ : ℕ → ℝ),
      (recordsF : ∀ n i, GeometricCutoffRecord (Ko n).toHistory i (pF n)) →
      (∀ n, 0 < a₀ n) →
      (∀ n x, InFixedHamiltonIveyRegion ((Ko n).initialMetric 0) (a₀ n) x ∧
        -3 / a₀ n ≤ metricScalarAt ((Ko n).initialMetric 0) x) →
      (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n (i : Fin (Ko n).eventCount), T₀ n ≤ (Ko n).time i.succ →
        (pF n).delta ((Ko n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) →
      (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Q n) ≤
        ((recordsK n i hi).static b).neck.scale) →
      (∀ᶠ n in atTop, ∀ i hi b, 1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale) →
      (∀ n, (Ko n).EventSlabsDerivative Ctime₀ (Q n) (Fin.last (Ko n).eventCount)) →
      (∀ n (i : Fin (Ko n).eventCount) (hi : T₀ n ≤ (Ko n).time i.succ),
        (recordsK n i hi).nominalRadius =
          (recordsF n i).nominalRadius ∧
        (recordsK n i hi).delta =
          (recordsF n i).delta ∧
        (recordsK n i hi).order =
          (recordsF n i).order ∧
        (∀ α, HEq ((recordsK n i hi).neck α) ((recordsF n i).neck α)) ∧
        (∀ b, ((recordsK n i hi).static b).neck.scale =
          ((recordsF n i).static b).neck.scale) ∧
        ∀ (b) (z : ThreeBall),
          ((recordsK n i hi).static b).inclusion
              (((recordsK n i hi).static b).witness.cap z) =
            ((recordsF n i).static b).inclusion
              (((recordsF n i).static b).witness.cap z)) →
      (∀ n x, InFixedHamiltonIveyRegion (((Ko n).rescale_P6N (c n) (hc n)).initialMetric 0)
          (a₀ n / c n) x ∧
        -3 / (a₀ n / c n) ≤
          metricScalarAt (((Ko n).rescale_P6N (c n) (hc n)).initialMetric 0) x) ∧
      (∀ n i hi b,
        (((Ko n).recordsKRescale_P6X3 (hc n) (recordsK n) i hi).static b).hasCanonicalWindow) ∧
      (∀ n (i : Fin ((Ko n).rescale_P6N (c n) (hc n)).eventCount),
        max 1 (T₀ n / c n) ≤ ((Ko n).rescale_P6N (c n) (hc n)).time i.succ →
        ((pF n).rescale_P6N (c n) (hc n)).delta (((Ko n).rescale_P6N (c n) (hc n)).time i.succ) ≤
          1 / ((n : ℝ) + 1)) ∧
      (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (c n * Q n) ≤
        (((Ko n).recordsKRescale_P6X3 (hc n) (recordsK n) i hi).static b).neck.scale) ∧
      (∀ᶠ n in atTop, ∀ i hi b, 1 ≤ a₀ n / c n *
        (((Ko n).recordsKRescale_P6X3 (hc n) (recordsK n) i hi).static b).neck.scale) ∧
      (∀ n (i : Fin ((Ko n).rescale_P6N (c n) (hc n)).eventCount), Perelman.PhiAlmostNonnegative
        (((Ko n).rescale_P6N (c n) (hc n)).toHistory.event i).incoming.flow
        (Ico (((Ko n).rescale_P6N (c n) (hc n)).time i.castSucc)
          (((Ko n).rescale_P6N (c n) (hc n)).time i.succ) ∩ Ici (max 1 (T₀ n / c n))) phi) ∧
      (∀ n, ((Ko n).rescale_P6N (c n) (hc n)).EventSlabsDerivative Ctime₀ (c n * Q n)
        (Fin.last ((Ko n).rescale_P6N (c n) (hc n)).eventCount)) ∧
      (∀ n (i : Fin ((Ko n).rescale_P6N (c n) (hc n)).eventCount)
        (hi : max 1 (T₀ n / c n) ≤ ((Ko n).rescale_P6N (c n) (hc n)).time i.succ),
        (∀ h, ((Ko n).recordsKRescale_P6X3 (hc n) (recordsK n) i hi).nominalRadius h =
          (recordsF n i).nominalRadius h / Real.sqrt (c n)) ∧
        ((Ko n).recordsKRescale_P6X3 (hc n) (recordsK n) i hi).delta = (recordsF n i).delta ∧
        ((Ko n).recordsKRescale_P6X3 (hc n) (recordsK n) i hi).order = (recordsF n i).order ∧
        (∀ α, (((Ko n).recordsKRescale_P6X3 (hc n) (recordsK n) i hi).neck α).scale =
          c n * ((recordsF n i).neck α).scale) ∧
        (∀ b, (((Ko n).recordsKRescale_P6X3 (hc n) (recordsK n) i hi).static b).neck.scale =
          c n * ((recordsF n i).static b).neck.scale)) := by
  obtain ⟨Phi, hPhi, H⟩ := KdataRescale_P6X3.{u}
  refine ⟨Phi, hPhi, ?_⟩
  intro Ko c hc Ctime₀ Q T₀ p pF recordsK a₀ recordsF ha₀ hHI hcanK hδF hscaleK hbirthA hslabK hrp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    H Ko c hc Ctime₀ Q T₀ p pF recordsK a₀ recordsF ha₀ hHI hcanK hδF hscaleK hbirthA hslabK
  exact ⟨h1, h2, h3, h4, h5, h6, h7,
    fun n i hi => (Ko n).recordsKRescale_factor_P6NI (hc n) (recordsK n) (recordsF n) (hrp n) i hi⟩

/-- **consumer：`hdistC_of_native_P6CD` 在重标度 history 上（`_P6NI`）**：`K := Ko.rescale_P6N c`、
`recordsK := recordsKRescale_P6X3`、`T₀ := max 1 (T₀/c)`、`p := p.rescale_P6N c`；`hnomId` 由
`hnomId_rescale_P6NI` 给（原尺度 reparameterization 合取 + 因子形 `hdS`），其余输入
（`hcanK hacc hrad hord hT₀ hTn hsel4 hδK` 与 `HDISTC` 数据）逐字（`hT₀ hδK` 写在重标度侧）。 -/
theorem hdistC_of_native_rescale_P6NI (Ko : ℕ → RetainedCoreHistory.{u}) (c : ℕ → ℝ)
    (hc : ∀ n, 0 < c n) {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters} {q : CutoffParameters}
    (recordsK : ∀ n (i : Fin (Ko n).eventCount), T₀ n ≤ (Ko n).time i.succ →
      GeometricCutoffRecord (Ko n).toHistory i (p n))
    (recsO : ∀ n (i : Fin (Ko n).eventCount), GeometricCutoffRecord (Ko n).toHistory i q)
    (hrp : ∀ n (i : Fin (Ko n).eventCount) (hi : T₀ n ≤ (Ko n).time i.succ),
      (recordsK n i hi).nominalRadius =
          (recsO n i).nominalRadius ∧
        (recordsK n i hi).delta =
          (recsO n i).delta ∧
        (recordsK n i hi).order =
          (recsO n i).order ∧
        (∀ α, HEq ((recordsK n i hi).neck α) ((recsO n i).neck α)) ∧
        (∀ b, ((recordsK n i hi).static b).neck.scale =
          ((recsO n i).static b).neck.scale) ∧
        ∀ (b) (z : ThreeBall),
          ((recordsK n i hi).static b).inclusion
              (((recordsK n i hi).static b).witness.cap z) =
            ((recsO n i).static b).inclusion
              (((recsO n i).static b).witness.cap z))
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
    (hTn : Tendsto (fun n => (Tn n : ℝ)) atTop atTop)
    (hsel4 : ∀ n, R n ≤ (d.native.params.neckRadius (Tn n) ^ 2)⁻¹)
    (hδK : ∃ Tδ : ℝ, ∀ (n : ℕ) (τ : ℝ), Tδ ≤ τ →
      ((p n).rescale_P6N (c n) (hc n)).recenterConstant *
        ((p n).rescale_P6N (c n) (hc n)).delta τ ≤ 1 / 2)
    (hdS : ∀ n (i : Fin ((Ko n).rescale_P6N (c n) (hc n)).eventCount) h,
      (d.native.records n i).nominalRadius h = (recsO n i).nominalRadius h / Real.sqrt (c n)) :
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
  exact hdistC_of_native_P6CD (K := fun n => (Ko n).rescale_P6N (c n) (hc n)) hjt htj σ y R hσ
    hRpos d Tn aSeed haT hsT has pT seedTrace r L hL hroom htime hsmall hclock hRr
    (T₀ := fun n => max 1 (T₀ n / c n)) (p := fun n => (p n).rescale_P6N (c n) (hc n))
    (fun n => (Ko n).recordsKRescale_P6X3 (hc n) (recordsK n))
    hcanK hacc hrad hord hT₀ hTn hsel4 hδK
    (hnomId_rescale_P6NI recordsK recsO hrp (fun n i => d.native.records n i) hdS)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
