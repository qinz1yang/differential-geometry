import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6BoundaryCasesP6S
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TowerInductionStep
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPartition

/-!
# P6 反证顶层：坏点序列 ⇒ selection 输出（O-CH11-P6SEL G1，后缀 `_P6X`）

P6 收口主形（`false_of_selection_eventSlab_Kdata_supplied_P6D`）的 selection 组 binder
`σ y R hRpos Tn aSeed haT hsT has pT seedTrace L hL hgood hwin hsel` 由坏点序列 + 树内 selector
`exists_localized_canonical_time_control_point_selection` 给出（本文件），event 内部类的
`j t yG hjt htj hσ hyG hRn` 由位置识别给出，`hqR` 的 `n+1` 部分由子列重索引给出：

* `selection_step_P6X`：单点 selector，`L := √(R₀ r²)/4`（恰满足 selector 的 `htime / hspace`）；
* `selection_of_bad_sequence_P6X`：逐 `n` 取 selection ⇒ 主形逐字形的 `hgood / hsel`、
  `hwin`（`σ − aSeed ≥ r²/2 + L²/R`，`L → ∞` ⇒ 尺度不变的 `∀ T, ∀ᶠ n, aSeed ≤ σ − T/R`），
  外加 κ 线 `pre841Data_of_three_C11KD` 要的 `t − r²/2 ≤ σ − T/R` 与 `r√R/200 → ∞`；
  前提只有 `R(x) r² → ∞`（**不要求 `R → ∞`**：见发现 F1）；
* `exists_strictMono_succ_lt_or_bdd_P6X`：`R` 要么有子列 `n+1 < R(ψ n)`（`hqR` 的 `n+1` 部分），
  要么沿尾有界（(Bd) 支，主形不覆盖）；
* `eventInterior_data_P6X`：event 内部类 ⇒ `j yG`、`activeStage σ = j.castSucc`、
  `HEq y yG`、`R = incoming scalar`（主形 `hjt htj hyG hRn` 逐字）。

显式缺口（不在本文件）：K 层数据（P6LATE late 形）、Pre841 `d`（κ 线）、`hdist`（P6ANCH2 条件形
hdistC + (α)）、`hslice`（P6ANCH2 G3 切片二分）、`hnotK` 的 "CWP ⇒ Good" 生产者、final slab /
边界类（P6BND、P6ANCH2 设计段 (H)(S)）、(Bd) 支（`R` 有界、`t → ∞` 的 age regime）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

/-- `L := √(R₀ r²)/4` 满足 selector 的时间条件 `2L²/R₀ ≤ r²/2`。 -/
theorem selection_htime_P6X {R0 r : ℝ} (hR0 : 0 < R0) :
    2 * (Real.sqrt (R0 * r ^ 2) / 4) ^ 2 / R0 ≤ r ^ 2 / 2 := by
  rw [div_pow, Real.sq_sqrt (by positivity)]
  rw [div_le_div_iff₀ hR0 (by norm_num)]
  nlinarith [sq_nonneg r]

/-- `√(R₀ r²) = √R₀ · r`（`r > 0`）。 -/
theorem sqrt_mul_sq_P6X {R0 r : ℝ} (hR0 : 0 ≤ R0) (hr : 0 < r) :
    Real.sqrt (R0 * r ^ 2) = Real.sqrt R0 * r := by
  rw [Real.sqrt_mul hR0, Real.sqrt_sq hr.le]

/-- `L := √(R₀ r²)/4` 满足 selector 的空间条件 `2L/√R₀ ≤ r/2`。 -/
theorem selection_hspace_P6X {R0 r : ℝ} (hR0 : 0 < R0) (hr : 0 < r) :
    2 * (Real.sqrt (R0 * r ^ 2) / 4) / Real.sqrt R0 ≤ r / 2 := by
  rw [sqrt_mul_sq_P6X hR0.le hr]
  have hs : 0 < Real.sqrt R0 := Real.sqrt_pos.mpr hR0
  rw [div_le_div_iff₀ hs (by norm_num)]
  nlinarith

/-- **单点 selection（`_P6X`）**：树内 selector 取 `L := √(R₀ r²)/4`。输出只留主形要的分量：
坏、`0 < Q`、`R₀ ≤ Q`、`Q ≤ ρ(T)⁻²`、窗口 `T − r²/2 ≤ s − L²/Q`、Good 区（阈值 `4Q`）。 -/
theorem selection_step_P6X (H : ObservedHistory.{u}) (q : CutoffParameters)
    {eps C1 C2 C1' C2' : ℝ} (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2')
    {Ctime Ctime' : ℝ≥0} (hCtime : Ctime ≤ Ctime')
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hcanonical : ∀ (v : Icc (0 : ℝ) H.horizon) (z : (H.stageAt v).Carrier),
      (q.neckRadius v ^ 2)⁻¹ < metricScalarAt (H.stageMetric (H.activeStage v) v) z →
      ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage v) v) eps C1 C2 z,
        W.capTubeHasNeckChart eps)
    (hderivative : ∀ (v : Icc (0 : ℝ) H.horizon) (z : (H.stageAt v).Carrier),
      H.time (H.activeStage v) < (v : ℝ) → (v : ℝ) < H.horizon →
      (q.neckRadius v ^ 2)⁻¹ < metricScalarAt (H.stageMetric (H.activeStage v) v) z →
      |derivWithin (fun t => metricScalarAt (H.stageMetric (H.activeStage v) t) z)
        (Iic (v : ℝ)) v| ≤
        Ctime * metricScalarAt (H.stageMetric (H.activeStage v) v) z ^ 2)
    (T : Icc (0 : ℝ) H.horizon) (p : (H.stageAt T).Carrier) (r A : ℝ) (hr : 0 < r) (hA : 0 < A)
    (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ T)
    (haSeed : (aSeed : ℝ) = (T : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (x : (H.stageAt T).Carrier)
    (hx : x ∈ riemannianBallOf (H.stageMetric (H.activeStage T) T) p (A * r))
    (hR : 0 < metricScalarAt (H.stageMetric (H.activeStage T) T) x)
    (hbad : ¬ H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' T x) :
    ∃ (s : Icc (0 : ℝ) H.horizon) (has : aSeed ≤ s) (hsT : s ≤ T)
      (y : (H.stageAt s).Carrier),
    (¬ H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' s y) ∧
    0 < metricScalarAt (H.stageMetric (H.activeStage s) s) y ∧
    metricScalarAt (H.stageMetric (H.activeStage T) T) x ≤
      metricScalarAt (H.stageMetric (H.activeStage s) s) y ∧
    metricScalarAt (H.stageMetric (H.activeStage s) s) y ≤ (q.neckRadius T ^ 2)⁻¹ ∧
    (T : ℝ) - r ^ 2 / 2 ≤ (s : ℝ) -
      (Real.sqrt (metricScalarAt (H.stageMetric (H.activeStage T) T) x * r ^ 2) / 4) ^ 2 /
        metricScalarAt (H.stageMetric (H.activeStage s) s) y ∧
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ s),
      (s : ℝ) -
        (Real.sqrt (metricScalarAt (H.stageMetric (H.activeStage T) T) x * r ^ 2) / 4) ^ 2 /
          metricScalarAt (H.stageMetric (H.activeStage s) s) y ≤ (v : ℝ) →
    ∀ z : (H.stageAt v).Carrier,
      riemannianEDistOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
            (H.activeStage_mono (hvs.trans hsT))) z ≤
        riemannianEDistOf (H.stageMetric (H.activeStage s) s)
            (seedTrace.point (H.activeStage s) (H.activeStage_mono has)
              (H.activeStage_mono hsT)) y +
          ENNReal.ofReal
            ((Real.sqrt (metricScalarAt (H.stageMetric (H.activeStage T) T) x * r ^ 2) / 4) /
              Real.sqrt (metricScalarAt (H.stageMetric (H.activeStage s) s) y)) →
      4 * metricScalarAt (H.stageMetric (H.activeStage s) s) y ≤
        metricScalarAt (H.stageMetric (H.activeStage v) v) z →
      H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z := by
  have hL : 0 < Real.sqrt (metricScalarAt (H.stageMetric (H.activeStage T) T) x * r ^ 2) / 4 :=
    div_pos (Real.sqrt_pos.mpr (by positivity)) (by norm_num)
  have hsel := H.exists_localized_canonical_time_control_point_selection q hC1 hC2 hCtime hanti
    hcanonical hderivative T p r A _ hr hA hL aSeed haT haSeed seedTrace x hx hR hbad
    (selection_htime_P6X hR) (selection_hspace_P6X hR hr)
  obtain ⟨s, has, hsT, y, hbad', hQ, hRQ, hQρ, -, hwin, -, -, hgood⟩ := hsel
  exact ⟨s, has, hsT, y, hbad', hQ, hRQ, hQρ, hwin, hgood⟩

/-- `L` 与 `r√R/200` 的发散：`R(x) r² → ∞` ⇒ `√(R(x) r²)/c → ∞`。 -/
theorem tendsto_sqrt_div_P6X {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n => Real.sqrt (f n) / c) atTop atTop :=
  (Real.tendsto_sqrt_atTop.comp hf).atTop_div_const hc

/-- 窗口不等式：`T − r²/2 ≤ s − L²/Q`、`L ≥ max 1 T'` ⇒ `T − r²/2 ≤ s − T'/Q`。 -/
theorem window_of_large_L_P6X {Tn s L Q r T' : ℝ} (hQ : 0 < Q)
    (hw : Tn - r ^ 2 / 2 ≤ s - L ^ 2 / Q) (hL : max 1 T' ≤ L) :
    Tn - r ^ 2 / 2 ≤ s - T' / Q := by
  have h1 : 1 ≤ L := (le_max_left _ _).trans hL
  have h2 : T' ≤ L := (le_max_right _ _).trans hL
  have hL2 : T' ≤ L ^ 2 := by nlinarith
  have : T' / Q ≤ L ^ 2 / Q := div_le_div_of_nonneg_right hL2 hQ.le
  linarith

/-- window-room（R-C11-5 D-10）：`T − r²/2 ≤ s − L²/Q` ⇒ `L² ≤ Q·(s − (T − r²/2))`。 -/
theorem window_room_P6X {Tn s L Q r : ℝ} (hQ : 0 < Q) (hw : Tn - r ^ 2 / 2 ≤ s - L ^ 2 / Q) :
    L * L ≤ Q * (s - (Tn - r ^ 2 / 2)) := by
  have h : L ^ 2 / Q ≤ s - (Tn - r ^ 2 / 2) := by linarith
  rw [div_le_iff₀ hQ] at h
  nlinarith

/-- **坏点序列 ⇒ selection 输出（G1 主定理，`_P6X`）**。逐 `n` 用 `selection_step_P6X`；
输出与主形 `false_of_selection_eventSlab_Kdata_supplied_P6D` 的 selection 组 binder 逐字同形
（`R n` 记为选出点的标量），外加 `R(x n) ≤ R n`、`R n ≤ ρ(Tn n)⁻²`、κ 线窗口与 `hradii`。
唯一的发散前提是 `R(x n) · r n² → ∞`（尺度不变量）。 -/
theorem selection_of_bad_sequence_P6X {Kh : ℕ → ObservedHistory.{u}} (q : ℕ → CutoffParameters)
    {eps C1 C2 C1' C2' : ℝ} (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2')
    {Ctime Ctime' : ℝ≥0} (hCtime : Ctime ≤ Ctime')
    (hanti : ∀ n, AntitoneOn (q n).neckRadius (Ici 0))
    (hcanonical : ∀ n (v : Icc (0 : ℝ) (Kh n).horizon) (z : ((Kh n).stageAt v).Carrier),
      ((q n).neckRadius v ^ 2)⁻¹ < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
      ∃ W : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) eps C1 C2 z,
        W.capTubeHasNeckChart eps)
    (hderivative : ∀ n (v : Icc (0 : ℝ) (Kh n).horizon) (z : ((Kh n).stageAt v).Carrier),
      (Kh n).time ((Kh n).activeStage v) < (v : ℝ) → (v : ℝ) < (Kh n).horizon →
      ((q n).neckRadius v ^ 2)⁻¹ < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
      |derivWithin (fun t => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) t) z)
        (Iic (v : ℝ)) v| ≤
        Ctime * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z ^ 2)
    (Tn : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (r : ℕ → ℝ) (A : ℝ) (hr : ∀ n, 0 < r n) (hA : 0 < A)
    (aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (haSeed : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (x : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (hx : ∀ n, x n ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n))
      (pT n) (A * r n))
    (hR : ∀ n, 0 < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (x n))
    (hbad : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' (Tn n) (x n))
    (hdiv : Tendsto (fun n => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (Tn n))
      (Tn n)) (x n) * r n ^ 2) atTop atTop) :
    ∃ (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
      (R : ℕ → ℝ) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n) (L : ℕ → ℝ),
      (∀ n, R n = metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)) ∧
      (∀ n, 0 < R n) ∧
      (∀ n, metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (x n) ≤
        R n) ∧
      (∀ n, R n ≤ ((q n).neckRadius (Tn n) ^ 2)⁻¹) ∧
      Tendsto L atTop atTop ∧
      (∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' (σ n) (y n)) ∧
      (∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
        ∀ z : ((Kh n).stageAt v).Carrier,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) →
          4 * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
          (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z) ∧
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) ∧
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ) - T / R n) ∧
      Tendsto (fun n => R n * ((σ n : ℝ) - ((Tn n : ℝ) - r n ^ 2 / 2))) atTop atTop ∧
      Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop := by
  have key := fun n => selection_step_P6X (Kh n) (q n) hC1 hC2 hCtime (hanti n) (hcanonical n)
    (hderivative n) (Tn n) (pT n) (r n) A (hr n) hA (aSeed n) (haT n) (haSeed n) (seedTrace n)
    (x n) (hx n) (hR n) (hbad n)
  choose σ has hsT y hsel hQ hRQ hQρ hwin hgood using key
  set R0 : ℕ → ℝ := fun n =>
    metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (x n) with hR0def
  have hL : Tendsto (fun n => Real.sqrt (R0 n * r n ^ 2) / 4) atTop atTop :=
    tendsto_sqrt_div_P6X hdiv (by norm_num)
  have hwin' : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ) - T /
      metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n) := by
    intro T hT
    filter_upwards [hL.eventually_ge_atTop (max 1 T)] with n hn
    exact window_of_large_L_P6X (hQ n) (hwin n) hn
  refine ⟨σ, y, fun n => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
    (y n), hsT, has, fun n => Real.sqrt (R0 n * r n ^ 2) / 4, fun _ => rfl, hQ, hRQ, hQρ, hL,
    hsel, hgood, ?_, hwin', ?_, ?_⟩
  · intro T hT
    filter_upwards [hwin' T hT] with n hn
    have h2 : (0 : ℝ) ≤ r n ^ 2 := sq_nonneg _
    rw [haSeed n]
    linarith
  · refine tendsto_atTop_mono (fun n => ?_) (hL.atTop_mul_atTop₀ hL)
    exact window_room_P6X (hQ n) (hwin n)
  · have h200 : Tendsto (fun n => Real.sqrt (R0 n * r n ^ 2) / 200) atTop atTop :=
      tendsto_sqrt_div_P6X hdiv (by norm_num)
    refine tendsto_atTop_mono (fun n => ?_) h200
    have hs : Real.sqrt (R0 n) ≤ Real.sqrt
        (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)) :=
      Real.sqrt_le_sqrt (hRQ n)
    rw [sqrt_mul_sq_P6X (hR n).le (hr n)]
    have := (hr n).le
    nlinarith [Real.sqrt_nonneg (R0 n)]

/-- **`hqR` 的 `n+1` 部分 / (Bd) 支**：任意实序列要么有严格单调子列 `n+1 < R(ψ n)`，要么沿尾有界。 -/
theorem exists_strictMono_succ_lt_or_bdd_P6X (R : ℕ → ℝ) :
    (∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ n : ℕ, (n : ℝ) + 1 < R (ψ n)) ∨
      ∃ M : ℝ, ∀ᶠ k in atTop, R k ≤ M := by
  by_cases h : ∀ M : ℝ, ∃ᶠ k in atTop, M < R k
  · exact Or.inl (extraction_forall_of_frequently fun n => h ((n : ℝ) + 1))
  · simp only [not_forall, Filter.not_frequently, not_lt] at h
    exact Or.inr h

end ObservedHistory

namespace RetainedCoreHistory

/-- slab 内部时刻的 `activeStage`（`P6AnchorSelectionP6M` 的 private 版在本文件复写）。 -/
theorem activeStage_eq_of_mem_slab_P6X (K : RetainedCoreHistory.{u})
    (j : Fin K.eventCount) (τ : Icc (0 : ℝ) K.toHistory.horizon)
    (h1 : K.time j.castSucc ≤ τ) (h2 : (τ : ℝ) < K.time j.succ) :
    K.toHistory.activeStage τ = j.castSucc :=
  (K.toHistory.mem_stageDomain_iff τ j.castSucc).mp (by
    simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
      (show (τ : ℝ) ∈ Ico (K.time j.castSucc) (K.time j.succ) from ⟨h1, h2⟩))

/-- 标量 `stageMetric m` ↔ incoming（`m = j.castSucc`）。 -/
theorem scalar_of_incoming_P6X (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
    {m : Fin (K.eventCount + 1)} (hm : j.castSucc = m) (v : ℝ)
    (z : (K.stage j.castSucc).Carrier) (x : (K.stage m).Carrier) (hx : HEq x z) :
    metricScalarAt (K.toHistory.stageMetric m v) x =
      (K.toHistory.event j).incoming.flow.scalar v z := by
  subst hm
  obtain rfl := eq_of_heq hx
  rw [ObservedHistory.stageMetric_castSucc_apply]
  rfl

/-- **event 内部类的位置识别（`_P6X`）**：子列整条落在 event slab 内部时，给出主形的
`j yG hjt htj hyG hRn`（`t := σ`，`hσ := rfl`）。 -/
theorem eventInterior_data_P6X {K : ℕ → RetainedCoreHistory.{u}}
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (hpos : ∀ n, ∃ j : Fin (K n).toHistory.eventCount,
      (K n).toHistory.time j.castSucc < (σ n : ℝ) ∧ (σ n : ℝ) < (K n).toHistory.time j.succ) :
    ∃ (j : ∀ n, Fin (K n).eventCount) (yG : ∀ n, ((K n).stage (j n).castSucc).Carrier),
      (∀ n, (K n).time (j n).castSucc < (σ n : ℝ)) ∧
      (∀ n, (σ n : ℝ) < (K n).time (j n).succ) ∧
      (∀ n, HEq (y n) (yG n)) ∧
      ∀ n, metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) =
        ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n) (yG n) := by
  choose j hj1 hj2 using hpos
  have hact : ∀ n, (K n).toHistory.activeStage (σ n) = (j n).castSucc := fun n =>
    (K n).activeStage_eq_of_mem_slab_P6X (j n) (σ n) (hj1 n).le (hj2 n)
  refine ⟨j, fun n => cast (congrArg (fun m => ((K n).stage m).Carrier) (hact n)) (y n),
    hj1, hj2, fun n => (cast_heq _ _).symm, fun n => ?_⟩
  exact (K n).scalar_of_incoming_P6X (j n) (hact n).symm (σ n) _ (y n) (cast_heq _ _).symm

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
