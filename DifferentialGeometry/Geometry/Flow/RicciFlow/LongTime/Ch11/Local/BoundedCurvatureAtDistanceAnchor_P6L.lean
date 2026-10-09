import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceAnchor

/-!
# `BCAD-Anchor:375` 的 trace-local 局部化（`_P6L`，O-CH11-P6ANCH G2）：P6 的 `hbcad`

原 `ST/BoundedCurvatureAtDistanceAnchor.lean:375`
`eventually_scalar_le_at_normalized_distance_of_anchor` 的论证 = 在更早时刻 `v = t + σ'/R` 的切片上做
**rebase / cap-window 二分**（private `:26` `scalar_le_of_rebase_capWindow_dichotomy`：从 `z` 出发的
极小化线段走到水平集 `{R = max(Rn, R z)}` 的点 `w`，`w` 是 cap-window 点则用标准解比较
（`CapWindowSliceComparison` 的嵌入 + `StandardCloseComparison`），否则用 SLT:249 在 `(v, w)` 的
有界曲率），
其输入（SLT 与 cap-window 嵌入）由**全局** canonical neighborhood / noncollapsing 给出。本文件：
* `scalar_le_of_rebase_capWindow_dichotomy_P6L`：`:26` 的**局部化**副本——`hB3e` / `hP1` 只对
  `w ∈ B_g(z, D/√Rn)` 要求（证明里的 `w` 满足 `d(z, w) ≤ d(z, x) < D/√Rn`）；其余逐字。
* **`ObservedHistory.hbcad_of_slice_dichotomy_P6L`**：P6ClosureP6D2 / 本车道 G5c 的 `hbcad`（K 层双 trace
  形）⇐ **切片前提 `hslice`**：每个更早切片 `v = σ n + σ'/R n`、每个 base-ball 点 `x₁` 的 trace 点
  `z = tr₁(v)`（`R(z) ≤ A·R n`），存在 cap-window 谓词 `CWP`，使 `B_v(z, Dd/√R n)` 内 (i) 非 CWP 高曲率点 `w`
  有半径 `(2Dd√A + 1)/√R(w)` 的有界曲率（= SLT:249_P6L / 窗口版在 `(v, w)` 的结论），(ii) CWP 点有标准帽
  嵌入（= `exists_capWindow_embedding_standard_close` 的结论）。标准解比较常数 `η₃ Cup Lc` 在序列前取
  （`exists_scalar_metric_comparison_of_standard_close (1/2)`），`C = max A 1 · (QB + 2Cup + 1)`。
`hslice` 的两条都是**切片局部**（无 trace）陈述；其生产 = 在 `K.eventPrefix j' v` 上跑 SLT（窗口版）
+ cap-window 嵌入（records / slab 导数数据前提），需 Good 区覆盖 `B_v(z, ·)`（相对 `hdist` 带余量）。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness

universe u

/-- **`_P6L`（`:26` 局部化）**：rebase / cap-window 二分，`hB3e` / `hP1` 只要求在 `B_g(z, D/√Rn)` 内。 -/
theorem scalar_le_of_rebase_capWindow_dichotomy_P6L {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric ThreeModel M) (CWP : M → Prop) (z : M)
    {Rn A D QB AB D₁ D₂ r η₃ Cup Lc : ℝ} (hRn : 0 < Rn) (hA : 1 ≤ A) (hD : 0 < D)
    (hQB : 0 ≤ QB) (hCup : 0 < Cup) (hLc : 0 < Lc) (hAB : 2 * D * Real.sqrt A ≤ AB)
    (hr : 2 * D * Lc * Real.sqrt (2 * A) < r) (hD₂ : D₁ + 1 + r ≤ D₂)
    (hB3e : ∀ w, riemannianEDistOf g z w < ENNReal.ofReal (D / Real.sqrt Rn) → ¬ CWP w →
      Rn ≤ metricScalarAt g w → ∀ x,
      riemannianEDistOf g w x < ENNReal.ofReal (AB / Real.sqrt (metricScalarAt g w)) →
        metricScalarAt g x ≤ QB * metricScalarAt g w)
    (hP1 : ∀ w, riemannianEDistOf g z w < ENNReal.ofReal (D / Real.sqrt Rn) → CWP w →
      ∃ (Ξ : standardCapWindow D₂ → M) (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
        (z₀ : standardCapWindow D₂), Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < D₁ + 1 ∧
        ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
          τw ∈ Icc (0 : ℝ) (1 / 2) ∧
          ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
            metricDerivNorm m (localPullMetric (scaleMetric lam hlam g) Ξ hΞ)
              ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
              (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃)
    (hP3 : ∀ (Q : StandardSolution) (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 3)))
        (g : SmoothRiemannianMetric (𝓡 3) U), ∀ τ ∈ Icc (0 : ℝ) (1 / 2), ∀ x : U,
        (∀ j : ℕ, j ≤ 2 → metricDerivNorm j g ((Q.val.metric τ).restrictOpen U)
          (StandardCap.metric.restrictOpen U) x ≤ η₃) →
        1 / 2 ≤ metricScalarAt g x ∧ metricScalarAt g x ≤ Cup ∧
        ∀ v : TangentSpace (𝓡 3) x,
          (StandardCap.metric.restrictOpen U).inner x v v ≤ Lc ^ 2 * g.inner x v v)
    (x : M) (hz : metricScalarAt g z ≤ A * Rn)
    (hzx : riemannianEDistOf g z x < ENNReal.ofReal (D / Real.sqrt Rn)) :
    metricScalarAt g x ≤ A * (QB + 2 * Cup + 1) * Rn := by
  set R := metricScalarAt g with hRdef
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hbound : A * Rn ≤ A * (QB + 2 * Cup + 1) * Rn := by
    have : A * 1 * Rn ≤ A * (QB + 2 * Cup + 1) * Rn :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hA0.le) hRn.le
    simpa using this
  by_cases hx : R x ≤ A * Rn
  · exact hx.trans hbound
  push Not at hx
  have hsRn : 0 < Real.sqrt Rn := Real.sqrt_pos.mpr hRn
  obtain ⟨w, hRw, hzw⟩ : ∃ w, R w = max Rn (R z) ∧
      riemannianEDistOf g z w ≤ riemannianEDistOf g z x := by
    by_cases hzR : Rn ≤ R z
    · refine ⟨z, by rw [max_eq_right hzR], ?_⟩
      rw [riemannianEDistOf_self]
      exact bot_le
    · push Not at hzR
      have hcont : Continuous R := (metricScalar_smooth g).continuous
      have hK : IsCompact {w | R w ≤ Rn} := (isClosed_le hcont continuous_const).isCompact
      have hRxn : Rn ≤ R x := by nlinarith
      obtain ⟨w, -, hw, -, hwz, -⟩ :=
        Geometry.exists_minimizing_segment_to_level_of_isCompact_sublevel g R hcont hK z x hzR
          hRxn (ne_top_of_lt hzx)
      exact ⟨w, by rw [hw, max_eq_left hzR.le], hwz⟩
  have hzwD : riemannianEDistOf g z w < ENNReal.ofReal (D / Real.sqrt Rn) := hzw.trans_lt hzx
  set L := R w with hLdef
  have hLn : Rn ≤ L := by rw [hRw]; exact le_max_left _ _
  have hLA : L ≤ A * Rn := by
    rw [hRw]
    exact max_le (by nlinarith) hz
  have hL : 0 < L := hRn.trans_le hLn
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hwx : riemannianEDistOf g w x < ENNReal.ofReal (2 * D / Real.sqrt Rn) := by
    have h1 := riemannianEDistOf_triangle g w z x
    rw [riemannianEDistOf_comm g w z] at h1
    have h2 : riemannianEDistOf g z w + riemannianEDistOf g z x <
        ENNReal.ofReal (D / Real.sqrt Rn) + ENNReal.ofReal (D / Real.sqrt Rn) :=
      ENNReal.add_lt_add (hzw.trans_lt hzx) hzx
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at h2
    refine h1.trans_lt (h2.trans_le (le_of_eq ?_))
    congr 1
    ring
  have hsqL : Real.sqrt L ≤ Real.sqrt A * Real.sqrt Rn := by
    rw [← Real.sqrt_mul hA0.le]
    exact Real.sqrt_le_sqrt hLA
  by_cases hcw : CWP w
  · obtain ⟨Ξ, hΞ, z₀, hinj, hz₀, hnorm, lam, hlam, Q, τw, hτw, hclose⟩ := hP1 w hzwD hcw
    set gt := localPullMetric (scaleMetric lam hlam g) Ξ hΞ with hgt
    have hP3u := fun u : standardCapWindow D₂ =>
      hP3 Q (standardCapWindow D₂) gt τw hτw u fun m hm => (hclose u m hm).le
    have hRz₀ : metricScalarAt gt z₀ = lam⁻¹ * L := by
      rw [hgt, metricScalarAt_localPullMetric_scaleMetric, hz₀]
    have hlamL : lam ≤ 2 * L := by
      have h := (hP3u z₀).1
      rw [hRz₀] at h
      have h' : lam * (1 / 2) ≤ lam * (lam⁻¹ * L) := mul_le_mul_of_nonneg_left h hlam.le
      rw [← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul] at h'
      linarith
    have hroom : ‖z₀.val‖ + r < D₂ + 1 := by linarith
    have hr0 : 0 < r := lt_of_le_of_lt (by positivity) hr
    have hcap := ball_subset_image_capWindow_of_scaled_lower g Ξ hΞ hinj z₀ hr0 hlam hLc hroom
      fun u v => (hP3u u).2.2 v
    have hslam : Real.sqrt lam ≤ Real.sqrt (2 * A) * Real.sqrt Rn := by
      rw [← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hsl : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
    have hxball : x ∈ riemannianBallOf g (Ξ z₀) (r / (Lc * Real.sqrt lam)) := by
      change riemannianEDistOf g (Ξ z₀) x < ENNReal.ofReal (r / (Lc * Real.sqrt lam))
      rw [hz₀]
      refine hwx.trans_le (ENNReal.ofReal_le_ofReal ?_)
      rw [div_le_div_iff₀ hsRn (mul_pos hLc hsl)]
      have h1 : 2 * D * (Lc * Real.sqrt lam) ≤ 2 * D * Lc * Real.sqrt (2 * A) * Real.sqrt Rn := by
        have := mul_le_mul_of_nonneg_left hslam (by positivity : (0 : ℝ) ≤ 2 * D * Lc)
        linarith
      have h2 := mul_le_mul_of_nonneg_right hr.le hsRn.le
      linarith
    obtain ⟨u, -, rfl⟩ := hcap hxball
    have hRu : metricScalarAt gt u = lam⁻¹ * R (Ξ u) := by
      rw [hgt, metricScalarAt_localPullMetric_scaleMetric]
    have hup := (hP3u u).2.1
    rw [hRu] at hup
    have hRx : R (Ξ u) ≤ lam * Cup := by
      have h' := mul_le_mul_of_nonneg_left hup hlam.le
      rwa [← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul] at h'
    have : lam * Cup ≤ 2 * A * Cup * Rn := by nlinarith
    nlinarith
  · have hxw : riemannianEDistOf g w x < ENNReal.ofReal (AB / Real.sqrt L) := by
      refine hwx.trans_le (ENNReal.ofReal_le_ofReal ?_)
      rw [div_le_div_iff₀ hsRn hsL]
      have h1 := mul_le_mul_of_nonneg_left hsqL (by positivity : (0 : ℝ) ≤ 2 * D)
      have h2 := mul_le_mul_of_nonneg_right hAB hsRn.le
      nlinarith
    have h := hB3e w hzwD hcw hLn x hxw
    have : QB * L ≤ QB * (A * Rn) := mul_le_mul_of_nonneg_left hLA hQB
    nlinarith

/-- **`_P6L`（P6 `hbcad` ⇐ 切片二分前提）**：标准解比较常数在前；`hslice`（每个更早切片、每个 trace 点
`z` 附近的 SLT 型有界曲率 + cap-window 标准帽嵌入）⇒ K 层双 trace BCAD（P6ClosureP6D2 / G5c 的 `hbcad`
逐字形）。 -/
theorem ObservedHistory.hbcad_of_slice_dichotomy_P6L :
    ∃ η₃ Cup Lc : ℝ, 0 < η₃ ∧ 0 < Cup ∧ 0 < Lc ∧
    ∀ (Kh : ℕ → ObservedHistory.{u}) (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
      (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R : ℕ → ℝ), (∀ n, 0 < R n) →
    (∀ A Dd : ℝ, 1 ≤ A → 0 < Dd → ∃ QB Dcap D₂ : ℝ, 0 ≤ QB ∧
      Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) ≤ D₂ ∧
      ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ᶠ n in atTop,
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
      ∀ tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x₁,
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
        ∃ CWP : ((Kh n).stage ((Kh n).activeStage v)).Carrier → Prop,
          (∀ w, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) w <
              ENNReal.ofReal (Dd / Real.sqrt (R n)) → ¬ CWP w →
            R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w → ∀ x,
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v) w x <
              ENNReal.ofReal ((2 * Dd * Real.sqrt A + 1) /
                Real.sqrt (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w)) →
            metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) x ≤
              QB * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w) ∧
          (∀ w, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) w <
              ENNReal.ofReal (Dd / Real.sqrt (R n)) → CWP w →
            ∃ (Ξ : standardCapWindow D₂ → ((Kh n).stage ((Kh n).activeStage v)).Carrier)
              (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
              Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dcap + 1 ∧
              ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
                τw ∈ Icc (0 : ℝ) (1 / 2) ∧
                ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
                  metricDerivNorm m (localPullMetric (scaleMetric lam hlam
                      ((Kh n).stageMetric ((Kh n).activeStage v) v)) Ξ hΞ)
                    ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
                    (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃)) →
    ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw →
      ∀ᶠ n in atTop,
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
      ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x₁)
        (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x₂),
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
            (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
          ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤
          C * R n := by
  obtain ⟨η₃, Cup, Lc, hη₃, hCup, hLc, hP3⟩ :=
    exists_scalar_metric_comparison_of_standard_close (1 / 2) (by norm_num) (by norm_num)
  refine ⟨η₃, Cup, Lc, hη₃, hCup, hLc, ?_⟩
  intro Kh σ y R hR hslice A Dd hA hDd
  have hA' : (1 : ℝ) ≤ max A 1 := le_max_right _ _
  obtain ⟨QB, Dcap, D₂, hQB, hD₂, hsl⟩ := hslice (max A 1) Dd hA' hDd
  refine ⟨max A 1 * (QB + 2 * Cup + 1), fun σ' hσ' Dw hDw => ?_⟩
  filter_upwards [hsl σ' hσ' Dw hDw] with n hn
  intro x₁ hx₁ x₂ _ v hvt hv tr₁ tr₂ hA1 hD
  have hA1' : metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
      (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ max A 1 * R n :=
    hA1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hR n).le)
  have hcwp := hn x₁ hx₁ v hvt hv tr₁ hA1'
  obtain ⟨CWP, hB3e, hP1⟩ := hcwp
  have hsA : 0 ≤ 2 * Dd * Real.sqrt (max A 1) := by positivity
  have hsL : 0 ≤ 2 * Dd * Lc * Real.sqrt (2 * max A 1) := by positivity
  exact scalar_le_of_rebase_capWindow_dichotomy_P6L _ CWP _ (hR n) hA' hDd hQB hCup hLc
    (by linarith) (by linarith) hD₂ hB3e hP1 hP3 _ hA1' hD

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
