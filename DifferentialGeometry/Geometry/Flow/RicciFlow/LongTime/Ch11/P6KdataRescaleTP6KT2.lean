import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DbbMinRescaleP6KT

/-!
# KdataRescale 截断孪生（O-CH11-KTRUNC2b (P1)，后缀 `_P6KT2`）

Joint / RerunEvent8 族（P6JointNoJ10P6JB :491 等）经 `KdataRescale_P6X3` 把 hgap 元组的原尺度数据搬到 K 帧。
截断后 hgap J9 是 `DerivativeBoundBefore … (min (time j.succ) Tno)`，
故 KdataRescale 的 hslab 进 / 出都换截断形；
最后一个合取用 KTRUNC1 的 `eventSlabsDerivT_rescale_P6KT`。
生成器 `build-logs/scratch/O-CH11-KTRUNC2/gen/gen_p1.py`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **(P1) `KdataRescale_P6X3` 的截断孪生（`_P6KT2`）**：hslab 输入改截断形（原尺度终点
`min (time j.succ) (tK n)`），输出改截断形（K 帧阈值 `c·Q`、终点 `min (time j.succ) (tK n / c n)`，
经 KTRUNC1 `eventSlabsDerivT_rescale_P6KT`）；其余五个合取与证明逐字。新增全称量 `tK` 紧随 `Q T₀`。 -/
theorem KdataRescaleT_P6KT2 :
    ∃ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi ∧
    ∀ (Ko : ℕ → RetainedCoreHistory.{u}) (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
      (Ctime₀ : ℝ≥0) (Q T₀ tK : ℕ → ℝ) (p pF : ℕ → CutoffParameters)
      (recordsK : ∀ n (i : Fin (Ko n).eventCount), T₀ n ≤ (Ko n).time i.succ →
        GeometricCutoffRecord (Ko n).toHistory i (p n))
      (a₀ : ℕ → ℝ),
      (∀ n i, GeometricCutoffRecord (Ko n).toHistory i (pF n)) →
      (∀ n, 0 < a₀ n) →
      (∀ n x, InFixedHamiltonIveyRegion ((Ko n).initialMetric 0) (a₀ n) x ∧
        -3 / a₀ n ≤ metricScalarAt ((Ko n).initialMetric 0) x) →
      (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n (i : Fin (Ko n).eventCount), T₀ n ≤ (Ko n).time i.succ →
        (pF n).delta ((Ko n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) →
      (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Q n) ≤
        ((recordsK n i hi).static b).neck.scale) →
      (∀ᶠ n in atTop, ∀ i hi b, 1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale) →
      (∀ n (j : Fin (Ko n).eventCount),
        ((Ko n).toHistory.event j).incoming.DerivativeBoundBefore Ctime₀ (Q n)
          (min ((Ko n).time j.succ) (tK n))) →
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
      (∀ n (j : Fin ((Ko n).rescale_P6N (c n) (hc n)).eventCount),
        (((Ko n).rescale_P6N (c n) (hc n)).toHistory.event j).incoming.DerivativeBoundBefore
          Ctime₀ (c n * Q n)
          (min (((Ko n).rescale_P6N (c n) (hc n)).time j.succ) (tK n / c n))) := by
  obtain ⟨Phi, hPhi, hpinch⟩ := hpinchK0_rescale_P6X2.{u}
  refine ⟨Phi, hPhi, ?_⟩
  intro Ko c hc Ctime₀ Q T₀ tK p pF recordsK a₀ recordsF ha₀ hHI hcanK hδF hscaleK hbirthA
    hslabK
  refine ⟨fun n => (Ko n).hHI_rescale_P6X3 (hc n) (hHI n),
    fun n => (Ko n).hcanK_rescale_P6X3 (hc n) (recordsK n) (hcanK n),
    fun n => (Ko n).hδF_rescale_P6X3 (hc n) (hδF n),
    fun n => (Ko n).hscaleK_rescale_P6X3 (hc n) (recordsK n) (hscaleK n),
    hbirthA.mono fun n hn => (Ko n).hbirthA_rescale_P6X3 (hc n) (recordsK n) hn,
    fun n i => hpinch (Ko n) (c n) (hc n) (pF n) (recordsF n) (a₀ n) (ha₀ n) (hHI n) _
      (le_max_left _ _) i,
    fun n => (Ko n).eventSlabsDerivT_rescale_P6KT (hc n) (hslabK n)⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
