import DifferentialGeometry.Geometry.Hyperbolic.HG06AdapterBasicHGA

/-!
# HG06 → ch12 消费形状的 adapter：主定理（S-HG-ADAPT G4，后缀 `_HGA`）

输入 = donor `hyperbolic_stability_of_cusp_count_le`（裸 `(M, g)`，`endCount M ≤ endCount N`，
**一对** `∃ ξ n`，结论 `sSup (dist (e p) (f p)) < η`，`isMetricApproximationOnBall` 假设，
`e : M ≃ᵢ N`）。输出 = ch12 消费的形状：

* `hg06_S0_HGA`（= ch12 `hps02_Ck_isometry_O19` 的 `hHG06` binder，sheet S0，`ckErr_O19` 换成
  `ckErr_HGA`）：固定 `ξ = 1/(n+1)`，hypothesis `ckErr < ξ/3`（`k ≤ n+1`，闭球 `ξ⁻¹`），
  结论 `e : H ≃ H'` 光滑、逆光滑、保度量，`riemannianEDistOf H'.metric (e p) (f p) < ofReal η`
  逐点（`sSup` → 逐点经紧性给出 `BddAbove`）。
* `hg06_S0_endCount_HGA`：同上但 cusp 数假设写成 `endCount H.Carrier ≤ endCount H'.Carrier`
  （不要 HG03 的 `HyperbolicTruncation`）。
* `hg06_allSmallDelta_endCount_HGA` / `hg06_adapter_HGA`：D-R3-19 的 all-small-δ 形状，
  `δ₀ ≤ min {ξ/2, 1/(2N), ξ/(2 max(1, S_N))}`，`N = n+1`，`S_N = Σ_{a ≤ N} 1/a!`；
  阈值只依赖 `(H, o, η)`，**不**依赖 `k`（固定阶量词 `∀ m η, 0 < η → ∃ threshold`）；
  `∀ δ ≤ δ₀, ∀ k ≥ ⌈δ⁻¹⌉`，近似半径 `δ⁻¹`、阶 `k`、误差 `δ`。

范数换算（D-R3-19 "norm comparison constants"）：donor 的 `metricCkErrorOn` 是加权和
`Σ_{a ≤ N} (a!)⁻¹ sup |∇^a err|`，`metricDerivNorm` 与 ch12 `ckErr` 逐点相等（树里的
`metricDerivNorm_eq_raw_on_open`），所以唯一的常数是 `S_N`；`S_N < e < 3` 给 S0 的 `ξ/3`；
`S_N ≥ 2` 给 `δ ≤ ξ/(2 max(1,S_N)) ≤ ξ/4 < ξ/3`，所以 all-small-δ 由 S0 推出。
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Hyperbolic

universe u v

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **`sSup` → 逐点。** donor 结论 `sSup (dist (a p) (f p)) < η`（`a : H ≃ᵢ H'`）经紧性（`BddAbove`）
和 G3 变成 ch12 的逐点 `riemannianEDistOf` 估计，同时给出光滑保度量同构。 -/
theorem hg06_pointwise_of_sSup_HGA
    (H : FiniteVolumeHyperbolicModel.{u}) (H' : FiniteVolumeHyperbolicModel.{v})
    (o : H.Carrier) {η : ℝ} (hη : 0 < η)
    (U : Opens H.Carrier) (f : H.Carrier → H'.Carrier)
    (hUη : riemannianClosedBallOf H.metric o η⁻¹ ⊆ U)
    (hcm : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U) :
    letI : TopologicalSpace.MetrizableSpace H.Carrier := Manifold.metrizableSpace (𝓡 3) H.Carrier
    letI : PseudoMetricSpace H.Carrier := H.metric.toPseudoMetricSpace
    letI : MetricSpace H.Carrier := MetricSpace.ofT0PseudoMetricSpace H.Carrier
    letI : TopologicalSpace.MetrizableSpace H'.Carrier :=
      Manifold.metrizableSpace (𝓡 3) H'.Carrier
    letI : PseudoMetricSpace H'.Carrier := H'.metric.toPseudoMetricSpace
    letI : MetricSpace H'.Carrier := MetricSpace.ofT0PseudoMetricSpace H'.Carrier
    (∃ a : H.Carrier ≃ᵢ H'.Carrier,
        sSup ((fun p : (U : Set H.Carrier) => dist (a p) (f p)) ''
          (Subtype.val ⁻¹' Metric.closedBall o η⁻¹)) < η) →
      ∃ e : H.Carrier ≃ H'.Carrier, ContMDiff (𝓡 3) (𝓡 3) ∞ e ∧ ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm ∧
        (∀ p, localPullInner H'.metric e p = H.metric.inner p) ∧
        ∀ p ∈ riemannianClosedBallOf H.metric o η⁻¹,
          riemannianEDistOf H'.metric (e p) (f p) < ENNReal.ofReal η := by
  let _ : TopologicalSpace.MetrizableSpace H.Carrier := Manifold.metrizableSpace (𝓡 3) H.Carrier
  let _ : PseudoMetricSpace H.Carrier := H.metric.toPseudoMetricSpace
  let _ : MetricSpace H.Carrier := MetricSpace.ofT0PseudoMetricSpace H.Carrier
  let _ : TopologicalSpace.MetrizableSpace H'.Carrier := Manifold.metrizableSpace (𝓡 3) H'.Carrier
  let _ : PseudoMetricSpace H'.Carrier := H'.metric.toPseudoMetricSpace
  let _ : MetricSpace H'.Carrier := MetricSpace.ofT0PseudoMetricSpace H'.Carrier
  rintro ⟨a, ha⟩
  obtain ⟨e, hea, hinner⟩ := riemannian_isometry_of_dist_isometry_HGA H H' a
  have hr : 0 < η⁻¹ := inv_pos.mpr hη
  have hclosed : riemannianClosedBallOf H.metric o η⁻¹ = Metric.closedBall o η⁻¹ := by
    ext y
    change edist o y ≤ ENNReal.ofReal η⁻¹ ↔ dist y o ≤ η⁻¹
    rw [edist_dist, dist_comm, ENNReal.ofReal_le_ofReal_iff hr.le]
  have hK : IsCompact (riemannianClosedBallOf H.metric o η⁻¹) :=
    DifferentialGeometry.RiemannianMetricComplete.closedEBall_isCompact H.complete o η⁻¹
  have hcont : ContinuousOn (fun p : H.Carrier => dist (a p) (f p))
      (riemannianClosedBallOf H.metric o η⁻¹) :=
    continuous_dist.comp_continuousOn
      (a.continuous.continuousOn.prodMk (hcm.continuousOn.mono hUη))
  have hbdd : BddAbove ((fun p : (U : Set H.Carrier) => dist (a p) (f p)) ''
      (Subtype.val ⁻¹' Metric.closedBall o η⁻¹)) := by
    refine (hK.bddAbove_image hcont).mono ?_
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p, hclosed ▸ hp, rfl⟩
  refine ⟨e.toEquiv, e.contMDiff, e.symm.contMDiff, hinner, ?_⟩
  intro p hp
  have hle : dist (a p) (f p) ≤ sSup ((fun p : (U : Set H.Carrier) => dist (a p) (f p)) ''
      (Subtype.val ⁻¹' Metric.closedBall o η⁻¹)) :=
    le_csSup hbdd ⟨⟨p, hUη hp⟩, hclosed ▸ hp, rfl⟩
  have hep : e p = a p := hea p
  have hlt : dist (a p) (f p) < η := hle.trans_lt ha
  change riemannianEDistOf H'.metric (e p) (f p) < ENNReal.ofReal η
  rw [hep]
  change edist (a p) (f p) < ENNReal.ofReal η
  rw [edist_dist]
  exact (ENNReal.ofReal_lt_ofReal_iff hη).2 hlt

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **ch12 `hHG06`（sheet S0）的 `endCount` 形式。** donor 的单对 `∃ ξ n`，`ξ/3` 吸收加权和的换算
常数，cusp 数假设 `endCount H.Carrier ≤ endCount H'.Carrier`（不用 HG03 截断）。 -/
theorem hg06_S0_endCount_HGA :
    ∀ (H : FiniteVolumeHyperbolicModel.{u}) (o : H.Carrier) (η : ℝ), 0 < η →
      ∃ ξ : ℝ, 0 < ξ ∧ ∃ n : ℕ, ξ = 1 / ((n : ℝ) + 1) ∧ η⁻¹ < ξ⁻¹ ∧
        ∀ (H' : FiniteVolumeHyperbolicModel.{v}),
          Geometry.Topology.endCount H.Carrier ≤ Geometry.Topology.endCount H'.Carrier →
          ∀ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
            riemannianClosedBallOf H.metric o ξ⁻¹ ⊆ U →
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
            _root_.Manifold.IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
            (∀ k : ℕ, k ≤ n + 1 → ∀ p ∈ riemannianClosedBallOf H.metric o ξ⁻¹,
              ckErr_HGA H H'.metric 1 f k p < ξ / 3) →
            ∃ e : H.Carrier ≃ H'.Carrier, ContMDiff (𝓡 3) (𝓡 3) ∞ e ∧
              ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm ∧
              (∀ p, localPullInner H'.metric e p = H.metric.inner p) ∧
              ∀ p ∈ riemannianClosedBallOf H.metric o η⁻¹,
                riemannianEDistOf H'.metric (e p) (f p) < ENNReal.ofReal η := by
  intro H o η hη
  let _ : TopologicalSpace.MetrizableSpace H.Carrier := Manifold.metrizableSpace (𝓡 3) H.Carrier
  let _ : PseudoMetricSpace H.Carrier := H.metric.toPseudoMetricSpace
  let _ : MetricSpace H.Carrier := MetricSpace.ofT0PseudoMetricSpace H.Carrier
  obtain ⟨ξ, hξ, n, hn, hr, hclose⟩ :=
    hyperbolic_stability_of_cusp_count_le.{u, v} H.metric H.complete H.finite_volume
      (curvature_identity_HGA H) o hη
  refine ⟨ξ, hξ, n, hn, hr, ?_⟩
  intro H' hends U f hball hcm hemb herr
  let _ : TopologicalSpace.MetrizableSpace H'.Carrier := Manifold.metrizableSpace (𝓡 3) H'.Carrier
  let _ : PseudoMetricSpace H'.Carrier := H'.metric.toPseudoMetricSpace
  let _ : MetricSpace H'.Carrier := MetricSpace.ofT0PseudoMetricSpace H'.Carrier
  have hc : (∑ a ∈ Finset.range (n + 1 + 1), ((a.factorial : ℝ))⁻¹) * (ξ / 3) < ξ := by
    have h3 := sum_inv_factorial_lt_three_HGA (n + 1)
    calc (∑ a ∈ Finset.range (n + 1 + 1), ((a.factorial : ℝ))⁻¹) * (ξ / 3)
        < 3 * (ξ / 3) := mul_lt_mul_of_pos_right h3 (by positivity)
      _ = ξ := by ring
  have hf := isMetricApproximationOnBall_of_ckErr_HGA H H' o hξ (by positivity) (n + 1) hc U f
    hball hcm hemb (fun a ha p hp => (herr a ha p hp).le)
  obtain ⟨a, ha⟩ := hclose H'.Carrier H'.metric H'.complete H'.finite_volume
    (curvature_identity_HGA H') hends (U : Set H.Carrier) (fun x : U => f x) hf
  have hηξ : riemannianClosedBallOf H.metric o η⁻¹ ⊆ riemannianClosedBallOf H.metric o ξ⁻¹ :=
    riemannianClosedBallOf_mono H.metric o hr.le
  exact hg06_pointwise_of_sSup_HGA H H' o hη U f (hηξ.trans hball) hcm ⟨a, ha⟩

/-- **ch12 `hHG06`（sheet S0）逐字形状**（Tr / Tr′ 形式）：cusp 数假设 `Tr.count ≤ Tr'.count`
经 `Tr.count = endCount`（G1）化为 `endCount` 形式。 -/
theorem hg06_S0_HGA :
    ∀ (H : FiniteVolumeHyperbolicModel.{u}) (o : H.Carrier) (η : ℝ), 0 < η →
      ∃ ξ : ℝ, 0 < ξ ∧ ∃ n : ℕ, ξ = 1 / ((n : ℝ) + 1) ∧ η⁻¹ < ξ⁻¹ ∧
        ∀ (H' : FiniteVolumeHyperbolicModel.{v}) (Tr : HyperbolicTruncation H)
          (Tr' : HyperbolicTruncation H'), Tr.count ≤ Tr'.count →
          ∀ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
            riemannianClosedBallOf H.metric o ξ⁻¹ ⊆ U →
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
            _root_.Manifold.IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
            (∀ k : ℕ, k ≤ n + 1 → ∀ p ∈ riemannianClosedBallOf H.metric o ξ⁻¹,
              ckErr_HGA H H'.metric 1 f k p < ξ / 3) →
            ∃ e : H.Carrier ≃ H'.Carrier, ContMDiff (𝓡 3) (𝓡 3) ∞ e ∧
              ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm ∧
              (∀ p, localPullInner H'.metric e p = H.metric.inner p) ∧
              ∀ p ∈ riemannianClosedBallOf H.metric o η⁻¹,
                riemannianEDistOf H'.metric (e p) (f p) < ENNReal.ofReal η := by
  intro H o η hη
  obtain ⟨ξ, hξ, n, hn, hr, h⟩ := hg06_S0_endCount_HGA.{u, v} H o η hη
  exact ⟨ξ, hξ, n, hn, hr, fun H' Tr Tr' hcount =>
    h H' ((truncation_count_le_iff_endCount_le_HGA Tr Tr').1 hcount)⟩

/-- `S_N = Σ_{a ≤ N} 1/a! ≥ 2`（`N = n+1 ≥ 1`）：D-R3-19 公式第三项 `≤ ξ/4`。 -/
theorem two_le_sum_inv_factorial_HGA (n : ℕ) :
    2 ≤ ∑ a ∈ Finset.range (n + 1 + 1), ((a.factorial : ℝ))⁻¹ := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have h0 : 0 ≤ ∑ i ∈ Finset.range n, ((Nat.factorial (i + 1 + 1) : ℝ))⁻¹ :=
    Finset.sum_nonneg (fun i _ => by positivity)
  have e0 : ((Nat.factorial 0 : ℕ) : ℝ)⁻¹ = 1 := by norm_num [Nat.factorial]
  have e1 : ((Nat.factorial (0 + 1) : ℕ) : ℝ)⁻¹ = 1 := by norm_num [Nat.factorial]
  linarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **D-R3-19 all-small-δ adapter（显式阈值，`endCount` 形式）。** `N = n + 1`，
`S_N = Σ_{a ≤ N} 1/a!`，阈值 `δ ≤ min {ξ/2, 1/(2N), ξ/(2 max(1, S_N))}`；`ξ, n` 只依赖
`(H, o, η)`，`k` 自由（`⌈δ⁻¹⌉ ≤ k`）。近似半径 `δ⁻¹`、阶 `k`、误差 `δ`（ch12 `ckErr` 最大型范数）。 -/
theorem hg06_allSmallDelta_endCount_HGA :
    ∀ (H : FiniteVolumeHyperbolicModel.{u}) (o : H.Carrier) (η : ℝ), 0 < η →
      ∃ ξ : ℝ, 0 < ξ ∧ ∃ n : ℕ, ξ = 1 / ((n : ℝ) + 1) ∧ η⁻¹ < ξ⁻¹ ∧
        ∀ (H' : FiniteVolumeHyperbolicModel.{v}),
          Geometry.Topology.endCount H.Carrier ≤ Geometry.Topology.endCount H'.Carrier →
          ∀ (δ : ℝ) (k : ℕ), 0 < δ →
            δ ≤ min (ξ / 2) (min (1 / (2 * ((n : ℝ) + 1)))
              (ξ / (2 * max 1 (∑ a ∈ Finset.range (n + 1 + 1), ((a.factorial : ℝ))⁻¹)))) →
            ⌈δ⁻¹⌉₊ ≤ k →
            ∀ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
              riemannianClosedBallOf H.metric o δ⁻¹ ⊆ U →
              ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
              _root_.Manifold.IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
              (∀ j : ℕ, j ≤ k → ∀ p ∈ riemannianClosedBallOf H.metric o δ⁻¹,
                ckErr_HGA H H'.metric 1 f j p < δ) →
              ∃ e : H.Carrier ≃ H'.Carrier, ContMDiff (𝓡 3) (𝓡 3) ∞ e ∧
                ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm ∧
                (∀ p, localPullInner H'.metric e p = H.metric.inner p) ∧
                ∀ p ∈ riemannianClosedBallOf H.metric o η⁻¹,
                  riemannianEDistOf H'.metric (e p) (f p) < ENNReal.ofReal η := by
  intro H o η hη
  obtain ⟨ξ, hξ, n, hn, hr, h⟩ := hg06_S0_endCount_HGA.{u, v} H o η hη
  refine ⟨ξ, hξ, n, hn, hr, ?_⟩
  intro H' hends δ k hδ hδ₀ hk U f hball hcm hemb herr
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hS2 := two_le_sum_inv_factorial_HGA n
  have hm : 2 ≤ max 1 (∑ a ∈ Finset.range (n + 1 + 1), ((a.factorial : ℝ))⁻¹) :=
    hS2.trans (le_max_right _ _)
  have hδ1 : δ ≤ ξ / 2 := hδ₀.trans (min_le_left _ _)
  have hδ2 : δ ≤ 1 / (2 * ((n : ℝ) + 1)) := hδ₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ3 : δ ≤ ξ / (2 * max 1 (∑ a ∈ Finset.range (n + 1 + 1), ((a.factorial : ℝ))⁻¹)) :=
    hδ₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδξ3 : δ < ξ / 3 := by
    refine lt_of_le_of_lt hδ3 ?_
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- 阶：`n + 1 ≤ 2 (n+1) ≤ δ⁻¹ ≤ ⌈δ⁻¹⌉ ≤ k`
  have hnk : n + 1 ≤ k := by
    have h1 : 2 * ((n : ℝ) + 1) ≤ δ⁻¹ := by
      rw [le_inv_comm₀ (by positivity) hδ]
      simpa [one_div] using hδ2
    have h2 : (n : ℝ) + 1 ≤ (k : ℝ) :=
      (by linarith : (n : ℝ) + 1 ≤ 2 * ((n : ℝ) + 1)).trans
        (h1.trans ((Nat.le_ceil _).trans (by exact_mod_cast hk)))
    exact_mod_cast h2
  -- 半径：`ξ⁻¹ ≤ δ⁻¹`
  have hrad : riemannianClosedBallOf H.metric o ξ⁻¹ ⊆ riemannianClosedBallOf H.metric o δ⁻¹ :=
    riemannianClosedBallOf_mono H.metric o (inv_anti₀ hδ (hδ1.trans (by linarith)))
  refine h H' hends U f (hrad.trans hball) hcm hemb ?_
  intro j hj p hp
  exact (herr j (hj.trans hnk) p (hrad hp)).trans hδξ3

/-- **D-R3-19 all-small-δ adapter（`∃ δ₀` 形式，`endCount`）。** 阈值 `δ₀` 只依赖 `(H, o, η)`，
不依赖 `k`（HPS02 固定阶量词 `∀ m η, 0 < η → ∃ threshold`；不是一个 `δ₀` 管所有 `k`）。 -/
theorem hg06_adapter_endCount_HGA :
    ∀ (H : FiniteVolumeHyperbolicModel.{u}) (o : H.Carrier) (η : ℝ), 0 < η →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (H' : FiniteVolumeHyperbolicModel.{v}),
        Geometry.Topology.endCount H.Carrier ≤ Geometry.Topology.endCount H'.Carrier →
        ∀ (δ : ℝ) (k : ℕ), 0 < δ → δ ≤ δ₀ → ⌈δ⁻¹⌉₊ ≤ k →
        ∀ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
          riemannianClosedBallOf H.metric o δ⁻¹ ⊆ U →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
          _root_.Manifold.IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
          (∀ j : ℕ, j ≤ k → ∀ p ∈ riemannianClosedBallOf H.metric o δ⁻¹,
            ckErr_HGA H H'.metric 1 f j p < δ) →
          ∃ e : H.Carrier ≃ H'.Carrier, ContMDiff (𝓡 3) (𝓡 3) ∞ e ∧
            ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm ∧
            (∀ p, localPullInner H'.metric e p = H.metric.inner p) ∧
            ∀ p ∈ riemannianClosedBallOf H.metric o η⁻¹,
              riemannianEDistOf H'.metric (e p) (f p) < ENNReal.ofReal η := by
  intro H o η hη
  obtain ⟨ξ, hξ, n, hn, hr, h⟩ := hg06_allSmallDelta_endCount_HGA.{u, v} H o η hη
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hm : 0 < max 1 (∑ a ∈ Finset.range (n + 1 + 1), ((a.factorial : ℝ))⁻¹) :=
    lt_max_of_lt_left one_pos
  refine ⟨min (ξ / 2) (min (1 / (2 * ((n : ℝ) + 1)))
    (ξ / (2 * max 1 (∑ a ∈ Finset.range (n + 1 + 1), ((a.factorial : ℝ))⁻¹)))),
    lt_min (by positivity) (lt_min (by positivity) (by positivity)), ?_⟩
  intro H' hends δ k hδ hδδ₀ hk
  exact h H' hends δ k hδ hδδ₀ hk

/-- **D-R3-19 all-small-δ adapter（`∃ δ₀` 形式，`HyperbolicTruncation` 形式）。**
cusp 数假设 `Tr.count ≤ Tr'.count`（ch12 `hHG06` 的 `Tr Tr'` 约定）。 -/
theorem hg06_adapter_HGA :
    ∀ (H : FiniteVolumeHyperbolicModel.{u}) (o : H.Carrier) (η : ℝ), 0 < η →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (H' : FiniteVolumeHyperbolicModel.{v}) (Tr : HyperbolicTruncation H)
        (Tr' : HyperbolicTruncation H'), Tr.count ≤ Tr'.count →
        ∀ (δ : ℝ) (k : ℕ), 0 < δ → δ ≤ δ₀ → ⌈δ⁻¹⌉₊ ≤ k →
        ∀ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
          riemannianClosedBallOf H.metric o δ⁻¹ ⊆ U →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
          _root_.Manifold.IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
          (∀ j : ℕ, j ≤ k → ∀ p ∈ riemannianClosedBallOf H.metric o δ⁻¹,
            ckErr_HGA H H'.metric 1 f j p < δ) →
          ∃ e : H.Carrier ≃ H'.Carrier, ContMDiff (𝓡 3) (𝓡 3) ∞ e ∧
            ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm ∧
            (∀ p, localPullInner H'.metric e p = H.metric.inner p) ∧
            ∀ p ∈ riemannianClosedBallOf H.metric o η⁻¹,
              riemannianEDistOf H'.metric (e p) (f p) < ENNReal.ofReal η := by
  intro H o η hη
  obtain ⟨δ₀, hδ₀, h⟩ := hg06_adapter_endCount_HGA.{u, v} H o η hη
  exact ⟨δ₀, hδ₀, fun H' Tr Tr' hcount =>
    h H' ((truncation_count_le_iff_endCount_le_HGA Tr Tr').1 hcount)⟩

end DifferentialGeometry.Geometry.Hyperbolic
