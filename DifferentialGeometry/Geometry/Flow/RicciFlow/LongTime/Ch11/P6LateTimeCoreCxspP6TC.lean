import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LateTimeCoreP6TC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LateGoodCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedGoodWindowCXSP

/-!
# 时间版 late core 与 ch12 CXSP 的对接（O-CH11-P6TIME G3，后缀 `_P6TC`）

* `lateGoodAt_of_timeCore_P6TC`：`CanonicalLateTimeCore_P6X` 在单个 `A > 0` 处的结论**逐字**就是
  `lateGoodAt_of_selected_CXSP`（P6LateGoodCXSP.lean L78–85）的结论形——ch12 用到该结论处可直接换成
  时间版，不再需要其 `hP6`。
* **`seedGoodWindow_of_timeCore_P6TC`**（consumer）：时间版在 `A' = 51200·e⁵⁷·A` 处取 `K₁ T`，直接喂
  ch12 `seedGoodWindow_of_lateGood_CXSP` 的 `hgood`（P6SeedGoodWindowCXSP.lean：其头注要求的上游"保留完整 Good
  的 producer"），输出 seed 半深窗口上的完整 Good。
* `canonicalLateTimeCore_of_selected_P6TC`：反向，CXSP 的条件 producer（原尺度 selected 形 `hP6`，binder 与
  `canonicalLateCore_of_selected_P6X` 逐字相同）⇒ 时间版（`lateGoodAt_of_selected_CXSP` + `A` 单调）。
`hP6` 形状差异（非同形，故不写 `example` 互推）：CXSP / `_P6X` 的 `hP6` 是**原尺度** selected 序列
（种子 `Tn pT r` 于 `F.tower.history (ind k)`、`k+1 ≤ R·r²`、窗口含 `r k`）；jointD 链的 `hPN`（G2a）是
**重标度**（`c = r²`、`r̃ = 1`）normalized-prefix 形，多 `T₀ Qt` 迟度、`Qt k < R k`、`R ≤ ρ̃(T̃n)⁻²`、`hroom`、
ball `(A+1)·1`、`hdistσ` 与原尺度种子 `hsmall hvol`。两条 producer 都落到同一 `CanonicalLateTimeCore_P6X`。
陈述由 build-logs/scratch/O-CH11-P6TIME/mk_g3.py 从 `P6LateCoreP6X.lean`（sha256 1d39d44b84a90d06…）与
`P6SeedGoodWindowCXSP.lean`（sha256 524092a403cf767b…）逐字抽取生成。
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Collapse Set Filter
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace GC.LongTime.Ch11

universe u

/-- 时间版在单个 `A > 0` 处 = `lateGoodAt_of_selected_CXSP` 的结论形（无 `hP6`）。 -/
theorem lateGoodAt_of_timeCore_P6TC {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (h : CanonicalLateTimeCore_P6X F ε C1 C2 Ctime) {A : ℝ} (hA : 0 < A) :
    ∃ K₁ T : ℝ, 0 < K₁ ∧ 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
          K₁ * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) y →
          H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime t y :=
  h A hA

/-- **consumer（ch12）**：时间版 ⇒ `seedGoodWindow_of_lateGood_CXSP` 的输出（`hgood` 由时间版在
`A' = 51200·e⁵⁷·A` 处付清；`KG TG` 即该处的 `K₁ T`）。 -/
theorem seedGoodWindow_of_timeCore_P6TC {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (h : CanonicalLateTimeCore_P6X F ε C1 C2 Ctime) {A : ℝ} (hA : 0 < A) :
    ∃ KG TG : ℝ, 0 < KG ∧ 0 < TG ∧
      ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          2 * TG ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
            (H.activeStage_mono haT) p,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
        ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (A * r),
          (10000 * KG) * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) y →
          H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime v y := by
  obtain ⟨KG, TG, hKG, hTG, hB⟩ := h (51200 * Real.exp 57 * A) (by positivity)
  exact ⟨KG, TG, hKG, hTG, seedGoodWindow_of_lateGood_CXSP hA hB⟩

/-- **CXSP 条件 producer ⇒ 时间版**（binder 与 `canonicalLateCore_of_selected_P6X` 逐字相同；
`A ≤ 2` 借 `max A 2`）。 -/
theorem canonicalLateTimeCore_of_selected_P6TC {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hcan : HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hder : TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hP6 : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
      let Kh : ℕ → ObservedHistory.{u} := fun k => (F.tower.history (ind k)).toHistory
      ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier)
        (r : ℕ → ℝ), (∀ k, 0 < r k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tn k : ℝ)) →
        (∀ k, 2 * r k ^ 2 < (Tn k : ℝ)) →
        (∀ k, hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) (r k)) →
        (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤
          ballVolume ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k)) (pT k) (r k)) →
      ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
        (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - r k ^ 2) →
      ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
          ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
        (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
        (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
        (∀ k, R k = metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
        (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k * r k ^ 2) →
        Tendsto L atTop atTop →
        (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
        (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
          (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
          ∀ z : ((Kh k).stageAt v).Carrier,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                  ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k))
                    ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal (L k / Real.sqrt (R k)) →
            4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
            (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - r k ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
        Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - r k ^ 2 / 2))) atTop atTop →
        Tendsto (fun k => r k / 200 * Real.sqrt (R k)) atTop atTop → False) :
    CanonicalLateTimeCore_P6X F ε C1 C2 Ctime := by
  intro A hA
  have hA2 : 1 < max A 2 := lt_of_lt_of_le one_lt_two (le_max_right _ _)
  exact lateTimeCoreAt_mono_P6TC (lateGoodAt_of_selected_CXSP hanti hcan hder hA2 (hP6 _ hA2)) hA
    (le_max_left _ _)

/-- 投影回旧形：`canonicalLateTimeCore_of_selected_P6TC` ⇒ `canonicalLateCore_of_selected_P6X` 的结论。 -/
example : type_of% @canonicalLateCore_of_selected_P6X.{u} := by
  intro P g F q ε C1 C2 Ctime hanti hcan hder hP6
  exact canonicalLateCore_of_timeCore_P6TC
    (canonicalLateTimeCore_of_selected_P6TC hanti hcan hder hP6)

end GC.LongTime.Ch11
