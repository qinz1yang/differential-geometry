import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LeftBadLocalizationCXST

/-!
# Localized bad-point sequence 与实际 history 消费（CX-STAGE）

从已显式给定的 localization 规格，选择同一批 points，同时支付 scaled-time limit、
curvature-ratio limit、seed-distance 与 rerun window。弱层只能支付第一个 limit，见前文件。
`localized_bad_rerun_geometry_CXST` 用实际 history 的 scalar 与 seed distances，调用已有
`leftShift_params_P6S2` / `rerun_dist_le_P6S2`；它不生产 localization、κ 或 witness transfer。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v

/-- 同一 diagonal choice 保留两个 limits 与每个 n 的 rerun 数值条件。
`h` 仍是独立 geometric obligation，不能由 `LeftBadAt_CXST` 反向取得。 -/
theorem localized_left_bad_sequence_CXST {T : ℕ → Type u} {X : ∀ n, T n → Type v}
    {time : ∀ n, T n → ℝ} {Bad : ∀ n t, X n t → Prop}
    {scalar : ∀ n t, X n t → ℝ} {seedDistance : ∀ n t, X n t → ℝ≥0∞}
    {a σ R L : ℕ → ℝ} {D0 : ℕ → ℝ≥0∞}
    (h : ∀ n, LeftLocalizedBadAt_CXST (time n) (Bad n) (scalar n) (seedDistance n)
      (σ n) (R n) (L n) (D0 n))
    (ha : ∀ n, a n < σ n) (hR : ∀ n, 0 < R n) (hL : ∀ n, 0 < L n) :
    ∃ (t : ∀ n, T n) (z : ∀ n, X n (t n)),
      (∀ n, a n < time n (t n) ∧ time n (t n) < σ n ∧ Bad n (t n) (z n) ∧
        R n / 2 ≤ scalar n (t n) (z n) ∧
        σ n - time n (t n) ≤ L n ^ 2 / (2 * R n) ∧
        seedDistance n (t n) (z n) ≤
          D0 n + ENNReal.ofReal (L n / (4 * Real.sqrt (R n)))) ∧
      Tendsto (fun n => R n * (σ n - time n (t n))) atTop (𝓝 0) ∧
      Tendsto (fun n => scalar n (t n) (z n) / R n) atTop (𝓝 1) := by
  have key (n : ℕ) : ∃ (t : T n) (z : X n t),
      a n < time n t ∧ time n t < σ n ∧ Bad n t z ∧
      R n / 2 ≤ scalar n t z ∧ σ n - time n t ≤ L n ^ 2 / (2 * R n) ∧
      seedDistance n t z ≤ D0 n + ENNReal.ofReal (L n / (4 * Real.sqrt (R n))) ∧
      R n * (σ n - time n t) ≤ 1 / ((n : ℝ) + 1) ∧
      |scalar n t z / R n - 1| ≤ 1 / ((n : ℝ) + 1) := by
    have hr := hR n
    have hl := hL n
    let δ := min (σ n - a n)
      (min (L n ^ 2 / (2 * R n)) ((1 / ((n : ℝ) + 1)) / R n))
    have hδ : 0 < δ := lt_min (sub_pos.mpr (ha n)) (lt_min (by positivity) (by positivity))
    have hε : 0 < min (1 / 2 : ℝ) (1 / ((n : ℝ) + 1)) := lt_min (by norm_num) (by positivity)
    obtain ⟨t, z, ht, hs, hb, hq, hd⟩ := h n δ hδ _ hε
    have hd1 : δ ≤ σ n - a n := min_le_left _ _
    have hd2 : δ ≤ L n ^ 2 / (2 * R n) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hd3 : δ ≤ (1 / ((n : ℝ) + 1)) / R n :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hq1 := hq.trans_le (min_le_left _ _)
    have hq2 := hq.le.trans (min_le_right _ _)
    have hhalf : (1 / 2 : ℝ) < scalar n t z / R n := by
      have := (abs_lt.mp hq1).1
      linarith
    have hh := (lt_div_iff₀ hr).mp hhalf
    have hgap : σ n - time n t < (1 / ((n : ℝ) + 1)) / R n := by linarith
    have hbudget := (lt_div_iff₀ hr).mp hgap
    exact ⟨t, z, by linarith, hs, hb, by linarith, by linarith, hd,
      by nlinarith, hq2⟩
  choose t z ht hs hb hhalf hwin hd hbudget hratio using key
  refine ⟨t, z, fun n => ⟨ht n, hs n, hb n, hhalf n, hwin n, hd n⟩, ?_, ?_⟩
  · exact squeeze_zero (fun n => mul_nonneg (hR n).le (sub_nonneg.mpr (hs n).le))
      hbudget tendsto_one_div_add_atTop_nhds_zero_nat
  · have habs := squeeze_zero (fun n => abs_nonneg _) hratio
      tendsto_one_div_add_atTop_nhds_zero_nat
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [habs.eventually (eventually_lt_nhds hε)] with n hn
    rwa [Real.dist_eq]

namespace ObservedHistory

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

/-- 原 `stage_class_left_bad_P6S2` 的直接 consumer：保留同一 `hcapW` / 未闭合 `hstab`，
把时间预算改成 `1 / ((n + 1) Qₙ)`，得到任意指定正尺度 Q 的 scaled-time limit。
没有从这些旧假设推出 curvature ratio 或 seed-distance control。 -/
theorem scaled_left_bad_of_stage_class_CXST {Kh : ℕ → ObservedHistory.{u}}
    {eps C1 C2 : ℝ} {Ctime : ℝ≥0} {i : ∀ n, Fin (Kh n).eventCount} {pp : ℕ → CutoffParameters}
    (R : ∀ n, GeometricCutoffRecord (Kh n) (i n) (pp n))
    (hcapW : ∀ n (b : ((Kh n).event (i n)).RetainedBoundaryIndex) (x : ThreeBall),
      ∃ W : SpatialCanonicalWitness ((Kh n).event (i n)).outputMetric eps C1 C2
        (((R n).static b).inclusion (((R n).static b).witness.cap x)), W.capTubeHasNeckChart eps)
    (hstab : ∀ n (p' : ((Kh n).stage (i n).castSucc).Carrier)
      (q : ((Kh n).stage (i n).succ).Carrier), ((Kh n).event (i n)).RegularCrossing p' q →
      (∃ δ : ℝ, 0 < δ ∧ ∀ v : Icc (0 : ℝ) (Kh n).horizon, (Kh n).time (i n).succ - δ < v →
        (v : ℝ) < (Kh n).time (i n).succ → ∀ z : ((Kh n).stageAt v).Carrier,
          (Kh n).HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z) →
      ∃ W : SpatialCanonicalWitness ((Kh n).event (i n)).outputMetric eps C1 C2 q,
        W.capTubeHasNeckChart eps)
    (y : ∀ n, ((Kh n).stageAt ((Kh n).stageTime (i n).succ)).Carrier)
    (hsel : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl eps C1 C2 Ctime
      ((Kh n).stageTime (i n).succ) (y n)) {Q : ℕ → ℝ} (hQ : ∀ n, 0 < Q n) :
    ∃ (v : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (z : ∀ n, ((Kh n).stageAt (v n)).Carrier),
      (∀ n, (Kh n).time (i n).castSucc < (v n : ℝ) ∧
        (v n : ℝ) < (Kh n).time (i n).succ ∧
        ¬ (Kh n).HasSpatialCanonicalTimeControl eps C1 C2 Ctime (v n) (z n)) ∧
      Tendsto (fun n => Q n * ((Kh n).time (i n).succ - (v n : ℝ))) atTop (𝓝 0) := by
  have h (n : ℕ) : LeftBadAt_CXST (fun v : Icc (0 : ℝ) (Kh n).horizon => (v : ℝ))
      (fun v z => ¬ (Kh n).HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z)
      ((Kh n).time (i n).succ) := by
    intro δ hδ
    obtain ⟨v, h1, h2, z, hz⟩ :=
      (R n).stage_class_left_bad_P6S2 (hcapW n) (hstab n) (hsel n) δ hδ
    exact ⟨v, z, h1, h2, hz⟩
  exact scaled_left_bad_sequence_CXST h
    (fun n => (Kh n).time_strictMono (Fin.castSucc_lt_succ (i := i n))) hQ

/-- 实际 history consumer：localized 坏点给出 `leftShift_rerun_P6S2` 的三个几何输入，
并验证窗口、阈值与距离域的 inclusion。`seed` 可实例化为已有 seed trace 的逐时刻点；
这里不把任意 seed family 当作已证明存在的 trace。 -/
theorem localized_bad_rerun_geometry_CXST {H : ObservedHistory.{u}}
    {eps C1 C2 : ℝ} {Ctime : ℝ≥0} {a σ : Icc (0 : ℝ) H.horizon}
    (seed : ∀ t : Icc (0 : ℝ) H.horizon, (H.stageAt t).Carrier)
    (y : (H.stageAt σ).Carrier) {R L : ℝ} (ha : a < σ) (hR : 0 < R) (hL : 0 < L)
    (h : LeftLocalizedBadAt_CXST (fun t : Icc (0 : ℝ) H.horizon => (t : ℝ))
      (fun t z => ¬ H.HasSpatialCanonicalTimeControl eps C1 C2 Ctime t z)
      (fun t z => metricScalarAt (H.stageMetric (H.activeStage t) t) z)
      (fun t z => riemannianEDistOf (H.stageMetric (H.activeStage t) t) (seed t) z)
      σ R L (riemannianEDistOf (H.stageMetric (H.activeStage σ) σ) (seed σ) y)) :
    ∃ (t : Icc (0 : ℝ) H.horizon) (z : (H.stageAt t).Carrier), a < t ∧ t < σ ∧
      ¬ H.HasSpatialCanonicalTimeControl eps C1 C2 Ctime t z ∧
      R / 2 ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) z ∧
      (σ : ℝ) - t ≤ L ^ 2 / (2 * R) ∧
      4 * R ≤ 8 * metricScalarAt (H.stageMetric (H.activeStage t) t) z ∧
      (σ : ℝ) - L ^ 2 / R ≤
        (t : ℝ) - (L / 2) ^ 2 / metricScalarAt (H.stageMetric (H.activeStage t) t) z ∧
      ∀ d : ℝ≥0∞,
        d ≤ riemannianEDistOf (H.stageMetric (H.activeStage t) t) (seed t) z +
          ENNReal.ofReal ((L / 2) /
            Real.sqrt (metricScalarAt (H.stageMetric (H.activeStage t) t) z)) →
        d ≤ riemannianEDistOf (H.stageMetric (H.activeStage σ) σ) (seed σ) y +
          ENNReal.ofReal (L / Real.sqrt R) := by
  obtain ⟨t, z, ht, hs, hb, hh, hwin, hd⟩ :=
    h.exists_rerun_parameters (a := (a : ℝ)) ha hR hL
  obtain ⟨hfour, hwindow, -⟩ := leftShift_params_P6S2 hR hh hL.le hwin
  exact ⟨t, z, ht, hs, hb, hh, hwin, hfour, hwindow,
    fun d hdist => rerun_dist_le_P6S2 hR hL.le hh hd hdist⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
