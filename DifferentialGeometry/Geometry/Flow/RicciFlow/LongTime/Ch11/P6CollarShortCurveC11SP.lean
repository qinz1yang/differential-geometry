import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventCapNoShortcut

/-!
# O-CH11-NATIVE-SHORT G1：(D4′) 的 `hshort′`（collar 内短曲线，`_C11SP`）

**A2 G5/G6 的 `hshort` 原形为假**：`w` 可取 core 边界球点 `boundaryOldPoint hOld y`
（`CapBoundaryChord.lean:46`，`RetainedBoundary` ⇒ 属于 `E.old`）；`oldOutput_boundaryOldPoint` +
`standardCapL = transitionEnd` + 静态 witness `window_deep` ⇒ 它在 b₀ window 半径恰 = `transitionEnd`，
是 cap 的边界点，`∉ interior (range oldOutput)`；取 buffer 点 `x = (TE + h)·y`，`d_out < c/√scale`，
但 `hshort` 要 `γ 1 = oldOutput w` 且 `MapsTo γ [0,1] interior`，不可满足。

本文件证 **`hshort′` = `hshort` + `hw`**（`w` 受保护或在某 cap 的 buffer；G5 两处调用点 `hw`/`hu`
都在作用域）+ `hdisj`，PROVED，常数显式（`TE = transitionEnd`，`K = TE + 11`）：
`c = min (1/(2K)) ((D − TE − 10)/K²)`，`Cs = 4·K·(TE + 13)`。
路线：(i) Hopf–Rinow 常速最短线（本文件 `exists_minimizing_curve_speed_C11SP`，EventCapNoShortcut 私有
引理的带 speed 版本）+ `exists_window_exit` + `window_radial_change_le_length` ⇒ 最短线留在 b₀ window
半径 `≤ TE + 10 + 2c` 内；(ii) lift 到模型，`radialBilinearField_lower_bound` + warping ≥ r/K 给
Euclid 位移 `‖z − x‖ ≤ 2K·√scale·d_out`；(iii) 多项式曲线 `(1 + h²τ(1−τ))·(x + τ(z − x))`
（`τ = (1 − cos πt)/2`）留在 `TE < ‖·‖ < D`，长度用 `metric_inner_le`（g ≤ Euclid）+ quad 3/2。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Manifold TopologicalSpace Bundle MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private exceptional_mem_inner_window actual_window_quad_bounds exists_window_exit
  exists_window_smooth_lift edist_le_elength window_radial_change_le_length from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventCapNoShortcut

universe u

/-- `π/4 ≤ transitionStart/√2`。 -/
theorem pi_div_four_le_transitionStart_div_C11SP :
    Real.pi / 4 ≤ StandardCap.transitionStart / Real.sqrt 2 := by
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs1 : 1 ≤ Real.sqrt 2 := by nlinarith
  have hpi := Real.pi_gt_three
  have hpis : Real.pi * 1 ≤ Real.pi * Real.sqrt 2 := mul_le_mul_of_nonneg_left hs1 Real.pi_pos.le
  have hdiv : Real.pi / Real.sqrt 2 = Real.pi * Real.sqrt 2 / 2 := by
    rw [div_eq_div_iff hs0.ne' (by norm_num)]
    linear_combination (-Real.pi) * hsq
  rw [le_div_iff₀ hs0, StandardCap.transitionStart, hdiv]
  nlinarith

/-- `transitionStart/√2 ≤ π/2`。 -/
theorem transitionStart_div_le_pi_div_two_C11SP :
    StandardCap.transitionStart / Real.sqrt 2 ≤ Real.pi / 2 := by
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hdiv : Real.pi / Real.sqrt 2 = Real.pi * Real.sqrt 2 / 2 := by
    rw [div_eq_div_iff hs0.ne' (by norm_num)]
    linear_combination (-Real.pi) * hsq
  rw [div_le_iff₀ hs0, StandardCap.transitionStart, hdiv]
  nlinarith

/-- warping 下界：`0 < r ≤ K`、`π/2 ≤ K` ⇒ `r / K ≤ warpingFunction r`。 -/
theorem warpingFunction_ge_div_C11SP {r K : ℝ} (hr : 0 < r) (hrK : r ≤ K)
    (hK : Real.pi / 2 ≤ K) : r / K ≤ StandardCap.warpingFunction r := by
  have hpi := Real.pi_pos
  have hKpos : 0 < K := lt_of_lt_of_le (by positivity) hK
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rcases le_total r StandardCap.transitionStart with hrs | hrs
  · rw [StandardCap.warpingFunction_eq_sqrt_two_mul_sin hrs]
    have hy0 : 0 ≤ r / Real.sqrt 2 := div_nonneg hr.le hs0.le
    have hy1 : r / Real.sqrt 2 ≤ Real.pi / 2 :=
      (div_le_div_of_nonneg_right hrs hs0.le).trans transitionStart_div_le_pi_div_two_C11SP
    have hj := Real.mul_le_sin hy0 hy1
    have h3 : Real.sqrt 2 * (2 / Real.pi * (r / Real.sqrt 2)) = 2 * r / Real.pi := by
      field_simp
    have h4 : r / K ≤ 2 * r / Real.pi := by
      rw [div_le_div_iff₀ hKpos hpi]
      nlinarith
    calc r / K ≤ 2 * r / Real.pi := h4
      _ = Real.sqrt 2 * (2 / Real.pi * (r / Real.sqrt 2)) := h3.symm
      _ ≤ Real.sqrt 2 * Real.sin (r / Real.sqrt 2) := mul_le_mul_of_nonneg_left hj hs0.le
  · have hang : Real.pi / 4 ≤ StandardCap.angle r :=
      pi_div_four_le_transitionStart_div_C11SP.trans
        ((StandardCap.angle_eq_div_sqrt_two le_rfl).symm.le.trans (StandardCap.monotone_angle hrs))
    have hsin : Real.sin (Real.pi / 4) ≤ Real.sin (StandardCap.angle r) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (StandardCap.angle_le_pi_div_two r) hang
    rw [Real.sin_pi_div_four] at hsin
    have hmul := mul_le_mul_of_nonneg_left hsin hs0.le
    have hw1 : 1 ≤ StandardCap.warpingFunction r := by
      change 1 ≤ Real.sqrt 2 * Real.sin (StandardCap.angle r)
      nlinarith
    calc r / K ≤ 1 := (div_le_one hKpos).mpr hrK
      _ ≤ _ := hw1

/-- 标准 cap 度量的 Euclid 下界：`‖y‖ ≤ K`、`π/2 ≤ K` ⇒ `‖v‖² ≤ K²·g_cap(y)(v,v)`。 -/
theorem norm_sq_le_metric_C11SP {y v : ThreeSpace} {K : ℝ} (hyK : ‖y‖ ≤ K)
    (hK : Real.pi / 2 ≤ K) :
    ‖v‖ ^ 2 ≤ K ^ 2 * StandardCap.metric.inner y v v := by
  have hpi := Real.pi_pos
  have hKpos : 0 < K := lt_of_lt_of_le (by positivity) hK
  have hK1 : 1 ≤ K := le_trans (by linarith [Real.pi_gt_three]) hK
  by_cases hy : y = 0
  · subst hy
    rw [StandardCap.metric_inner_zero, real_inner_self_eq_norm_sq]
    have : 1 ≤ K ^ 2 := by nlinarith
    nlinarith [sq_nonneg ‖v‖]
  · have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hlow := DifferentialGeometry.Geometry.Riemannian.radialBilinearField_lower_bound
      StandardCap.warpingFunction hy v
    rw [← StandardCap.metric_inner_of_ne_zero hy] at hlow
    have hw := warpingFunction_ge_div_C11SP hr hyK hK
    have hq0 : 1 / K ≤ StandardCap.warpingFunction ‖y‖ / ‖y‖ := by
      rw [le_div_iff₀ hr, one_div_mul_eq_div]
      exact hw
    have hq : (1 / K) ^ 2 ≤ (StandardCap.warpingFunction ‖y‖ / ‖y‖) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hq0 2
    have hK1' : (1 / K) ^ 2 ≤ 1 := by
      rw [div_pow, one_pow]
      exact div_le_one_of_le₀ (by nlinarith) (by positivity)
    have hmin : (1 / K) ^ 2 ≤ min ((StandardCap.warpingFunction ‖y‖ / ‖y‖) ^ 2) 1 :=
      le_min hq hK1'
    have h1 : (1 / K) ^ 2 * ‖v‖ ^ 2 ≤ StandardCap.metric.inner y v v :=
      (mul_le_mul_of_nonneg_right hmin (sq_nonneg _)).trans hlow
    calc ‖v‖ ^ 2 = K ^ 2 * ((1 / K) ^ 2 * ‖v‖ ^ 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (sq_nonneg K)

/-- 线段范数平方恒等式。 -/
theorem norm_add_smul_sub_sq_C11SP (x z : ThreeSpace) (τ : ℝ) :
    ‖x + τ • (z - x)‖ ^ 2 =
      (1 - τ) * ‖x‖ ^ 2 + τ * ‖z‖ ^ 2 - τ * (1 - τ) * ‖z - x‖ ^ 2 := by
  have h1 : ‖x + τ • (z - x)‖ ^ 2 =
      ‖x‖ ^ 2 + 2 * τ * ⟪x, z - x⟫_ℝ + τ ^ 2 * ‖z - x‖ ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have h2 : ‖z‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, z - x⟫_ℝ + ‖z - x‖ ^ 2 := by
    calc ‖z‖ ^ 2 = ‖x + (z - x)‖ ^ 2 := by simp
      _ = _ := norm_add_sq_real _ _
  rw [h1, h2]
  ring

/-- collar 连接曲线 `F τ = (1 + h²τ(1−τ))·(x + τ(z − x))` 的三个界（`h = ‖z − x‖ ≤ 1`）。 -/
theorem collarPath_bounds_C11SP {x z : ThreeSpace} {R m τ : ℝ}
    (hxR : ‖x‖ ≤ R) (hzR : ‖z‖ ≤ R) (hm1 : 1 ≤ m) (hmx : m ≤ ‖x‖) (hmz : m ≤ ‖z‖)
    (hh : ‖z - x‖ ≤ 1) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    m ≤ ‖(1 + ‖z - x‖ ^ 2 * (τ * (1 - τ))) • (x + τ • (z - x))‖ ∧
    ‖(1 + ‖z - x‖ ^ 2 * (τ * (1 - τ))) • (x + τ • (z - x))‖ ≤ (1 + ‖z - x‖ ^ 2 / 4) * R ∧
    ‖(‖z - x‖ ^ 2 * (1 - 2 * τ)) • (x + τ • (z - x)) +
        (1 + ‖z - x‖ ^ 2 * (τ * (1 - τ))) • (z - x)‖ ≤ ‖z - x‖ * (R + 2) := by
  have hs0 : 0 ≤ τ * (1 - τ) := mul_nonneg hτ0 (by linarith)
  have hs1 : τ * (1 - τ) ≤ 1 / 4 := by nlinarith [sq_nonneg (τ - 1 / 2)]
  have hh0 : 0 ≤ ‖z - x‖ := norm_nonneg _
  have hh2 : ‖z - x‖ ^ 2 ≤ 1 := by nlinarith
  have hhh : ‖z - x‖ ^ 2 ≤ ‖z - x‖ := by nlinarith
  have hR0 : 0 ≤ R := (norm_nonneg x).trans hxR
  have ha0 : 0 ≤ ‖z - x‖ ^ 2 * (τ * (1 - τ)) := mul_nonneg (sq_nonneg _) hs0
  have ha1 : ‖z - x‖ ^ 2 * (τ * (1 - τ)) ≤ 1 / 4 := by nlinarith
  have hA' : 1 + ‖z - x‖ ^ 2 * (τ * (1 - τ)) ≤ 1 + ‖z - x‖ ^ 2 / 4 := by nlinarith
  have hqR : ‖x + τ • (z - x)‖ ≤ R := by
    have hq : x + τ • (z - x) = (1 - τ) • x + τ • z := by
      rw [smul_sub, sub_smul, one_smul]
      abel
    rw [hq]
    calc ‖(1 - τ) • x + τ • z‖ ≤ ‖(1 - τ) • x‖ + ‖τ • z‖ := norm_add_le _ _
      _ = (1 - τ) * ‖x‖ + τ * ‖z‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hτ0]
      _ ≤ (1 - τ) * R + τ * R := by
          have h1 := mul_le_mul_of_nonneg_left hxR (by linarith : (0 : ℝ) ≤ 1 - τ)
          have h2 := mul_le_mul_of_nonneg_left hzR hτ0
          linarith
      _ = R := by ring
  have hq2 := norm_add_smul_sub_sq_C11SP x z τ
  have hFn : ‖(1 + ‖z - x‖ ^ 2 * (τ * (1 - τ))) • (x + τ • (z - x))‖ =
      (1 + ‖z - x‖ ^ 2 * (τ * (1 - τ))) * ‖x + τ • (z - x)‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hFn]
    have hx2 : m ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (by linarith) hmx 2
    have hz2 : m ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (by linarith) hmz 2
    have hqsq : m ^ 2 - ‖z - x‖ ^ 2 * (τ * (1 - τ)) ≤ ‖x + τ • (z - x)‖ ^ 2 := by
      rw [hq2]
      nlinarith
    have hm2 : 1 ≤ m ^ 2 := by nlinarith
    have key : 0 ≤ ‖z - x‖ ^ 2 * (τ * (1 - τ)) *
        ((2 + ‖z - x‖ ^ 2 * (τ * (1 - τ))) * m ^ 2 - (1 + ‖z - x‖ ^ 2 * (τ * (1 - τ))) ^ 2) :=
      mul_nonneg ha0 (by nlinarith)
    have hmul := mul_le_mul_of_nonneg_left hqsq (sq_nonneg (1 + ‖z - x‖ ^ 2 * (τ * (1 - τ))))
    have hsq : m ^ 2 ≤ ((1 + ‖z - x‖ ^ 2 * (τ * (1 - τ))) * ‖x + τ • (z - x)‖) ^ 2 := by
      rw [mul_pow]
      nlinarith
    have hB : 0 ≤ (1 + ‖z - x‖ ^ 2 * (τ * (1 - τ))) * ‖x + τ • (z - x)‖ :=
      mul_nonneg (by linarith) (norm_nonneg _)
    nlinarith
  · rw [hFn]
    exact mul_le_mul hA' hqR (norm_nonneg _) (by positivity)
  · have habs : |1 - 2 * τ| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    calc ‖(‖z - x‖ ^ 2 * (1 - 2 * τ)) • (x + τ • (z - x)) +
          (1 + ‖z - x‖ ^ 2 * (τ * (1 - τ))) • (z - x)‖
        ≤ ‖(‖z - x‖ ^ 2 * (1 - 2 * τ)) • (x + τ • (z - x))‖ +
            ‖(1 + ‖z - x‖ ^ 2 * (τ * (1 - τ))) • (z - x)‖ := norm_add_le _ _
      _ = ‖z - x‖ ^ 2 * |1 - 2 * τ| * ‖x + τ • (z - x)‖ +
            (1 + ‖z - x‖ ^ 2 * (τ * (1 - τ))) * ‖z - x‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (sq_nonneg _),
            abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + ‖z - x‖ ^ 2 * (τ * (1 - τ)))]
      _ ≤ ‖z - x‖ * (R + 2) := by
          have h1 : ‖z - x‖ ^ 2 * |1 - 2 * τ| ≤ ‖z - x‖ ^ 2 :=
            mul_le_of_le_one_right (sq_nonneg _) habs
          have h2 : ‖z - x‖ ^ 2 * |1 - 2 * τ| * ‖x + τ • (z - x)‖ ≤ ‖z - x‖ * R :=
            mul_le_mul (h1.trans hhh) hqR (norm_nonneg _) hh0
          have h3 : (1 + ‖z - x‖ ^ 2 * (τ * (1 - τ))) * ‖z - x‖ ≤ 2 * ‖z - x‖ := by
            nlinarith
          linarith

/-- 余弦参数 `θ t = (1 − cos πt)/2` 的导数。 -/
theorem hasDerivAt_cosParam_C11SP (t : ℝ) :
    HasDerivAt (fun t : ℝ => (1 - Real.cos (Real.pi * t)) / 2)
      (Real.pi * Real.sin (Real.pi * t) / 2) t := by
  have h1 : HasDerivAt (fun t : ℝ => Real.cos (Real.pi * t))
      (-Real.sin (Real.pi * t) * (Real.pi * 1)) t :=
    (Real.hasDerivAt_cos (Real.pi * t)).comp t ((hasDerivAt_id t).const_mul Real.pi)
  convert (h1.const_sub 1).div_const 2 using 1
  ring

/-- collar 连接曲线的导数。 -/
theorem hasDerivAt_collarPath_C11SP (x z : ThreeSpace) (h τ : ℝ) :
    HasDerivAt (fun τ : ℝ => (1 + h ^ 2 * (τ * (1 - τ))) • (x + τ • (z - x)))
      ((h ^ 2 * (1 - 2 * τ)) • (x + τ • (z - x)) + (1 + h ^ 2 * (τ * (1 - τ))) • (z - x)) τ := by
  have h1 : HasDerivAt (fun τ : ℝ => τ * (1 - τ)) (1 * (1 - τ) + τ * (0 - 1)) τ :=
    (hasDerivAt_id' τ).mul ((hasDerivAt_const τ (1 : ℝ)).sub (hasDerivAt_id' τ))
  have hA : HasDerivAt (fun τ : ℝ => 1 + h ^ 2 * (τ * (1 - τ))) (h ^ 2 * (1 - 2 * τ)) τ := by
    convert (h1.const_mul (h ^ 2)).const_add 1 using 1
    ring
  have hq : HasDerivAt (fun τ : ℝ => x + τ • (z - x)) (z - x) τ := by
    simpa using ((hasDerivAt_id' τ).smul_const (z - x)).const_add x
  convert hA.smul hq using 1
  exact add_comm _ _


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- `EventCapNoShortcut` 私有 `exists_post_minimizing_curve` 的带 pointwise speed 版本
（证明逐行同源，只多导出 `hspeed`）：Hopf–Rinow 常速最短线。 -/
theorem exists_minimizing_curve_speed_C11SP
    (Q : OrientedThreeStage.{u}) (g : SmoothRiemannianMetric ThreeModel Q.Carrier)
    (p q : Q.Carrier) (hfin : riemannianEDistOf g p q ≠ ⊤) :
    ∃ (γ : ℝ → Q.Carrier) (c : ℝ), 0 ≤ c ∧
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ ∧ γ 0 = p ∧ γ 1 = q ∧
      (∀ t : ℝ, riemannianCurveSpeed g γ t = c) ∧
      (∀ l r : ℝ, l ≤ r → riemannianCurveELength g γ l r = ENNReal.ofReal (c * (r - l))) ∧
      (∀ l r : ℝ, 0 ≤ l → l ≤ r → r ≤ 1 →
        riemannianEDistOf g (γ l) (γ r) = ENNReal.ofReal (c * (r - l))) := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let : IsManifold ThreeModel 1 Q.Carrier :=
    IsManifold.of_le (I := ThreeModel) (M := Q.Carrier) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : MetrizableSpace Q.Carrier := Manifold.metrizableSpace ThreeModel Q.Carrier
  let : T3Space Q.Carrier := inferInstance
  let : RiemannianBundle (fun x : Q.Carrier => TangentSpace ThreeModel x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle ThreeSpace (fun x : Q.Carrier => TangentSpace ThreeModel x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace Q.Carrier := EMetricSpace.ofRiemannianMetric ThreeModel Q.Carrier
  let : PseudoEMetricSpace Q.Carrier :=
    (EMetricSpace.ofRiemannianMetric ThreeModel Q.Carrier).toPseudoEMetricSpace
  let : CompleteSpace Q.Carrier := (RiemannianMetricComplete.of_compact g).complete
  have hEnorm : Riemannian.IsMetricNorm (I := ThreeModel) (M := Q.Carrier) g := by
    intro x v
    exact Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := ThreeModel) g x v
  obtain ⟨v, hv, hnorm⟩ :=
    Riemannian.Exponential.hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top
      g hEnorm p q hfin
  let γ : ℝ → Q.Carrier := Riemannian.Exponential.intrinsicGeodesic g hEnorm p v
  let c : ℝ := Real.sqrt (g.inner p v v)
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ :=
    Riemannian.Exponential.intrinsicGeodesic_contMDiff g hEnorm p v
  have hγ0 : γ 0 = p := Riemannian.Exponential.intrinsicGeodesic_zero g hEnorm p v
  have hγ1 : γ 1 = q := hv
  have hspeed (t : ℝ) : riemannianCurveSpeed g γ t = c := by
    exact congrArg Real.sqrt
      (Riemannian.Exponential.intrinsicGeodesic_speedSq_eq g hEnorm p v t)
  have hlen (l r : ℝ) (_hlr : l ≤ r) :
      riemannianCurveELength g γ l r = ENNReal.ofReal (c * (r - l)) := by
    unfold riemannianCurveELength
    simp_rw [hspeed]
    rw [setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul hc]
  have hupper (l r : ℝ) (hlr : l ≤ r) :
      riemannianEDistOf g (γ l) (γ r) ≤ ENNReal.ofReal (c * (r - l)) := by
    exact (edist_le_elength g hlr (hγ.of_le (by simp)).contMDiffOn).trans_eq (hlen l r hlr)
  have hfinite (l r : ℝ) (hlr : l ≤ r) : riemannianEDistOf g (γ l) (γ r) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hupper l r hlr)
  have hupperReal (l r : ℝ) (hlr : l ≤ r) :
      (riemannianEDistOf g (γ l) (γ r)).toReal ≤ c * (r - l) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hupper l r hlr)
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hc (sub_nonneg.mpr hlr))] using h
  have h01 : (riemannianEDistOf g (γ 0) (γ 1)).toReal = c := by
    rw [hγ0, hγ1]
    exact hnorm.symm
  refine ⟨γ, c, hc, hγ, hγ0, hγ1, hspeed, hlen, ?_⟩
  intro l r hl hlr hr
  apply (ENNReal.toReal_eq_toReal_iff' (hfinite l r hlr) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (mul_nonneg hc (sub_nonneg.mpr hlr))]
  refine le_antisymm (hupperReal l r hlr) ?_
  have htri1 := riemannianEDistOf_toReal_triangle g (γ 0) (γ r) (γ 1)
    (hfinite 0 r (hl.trans hlr)) (hfinite r 1 hr)
  have htri2 := riemannianEDistOf_toReal_triangle g (γ 0) (γ l) (γ r)
    (hfinite 0 l hl) (hfinite l r hlr)
  rw [h01] at htri1
  have ha := hupperReal 0 l hl
  have hb := hupperReal r 1 hr
  nlinarith

local notation "𝒯" => StandardCap.transitionEnd

/-- collar 连接曲线（模型层）：`p = F ∘ θ`，`θ t = (1 − cos πt)/2`，`F` 见 `collarPath_bounds_C11SP`。 -/
theorem exists_collarPath_C11SP {x z : ThreeSpace} {R m : ℝ}
    (hxR : ‖x‖ ≤ R) (hzR : ‖z‖ ≤ R) (hm1 : 1 ≤ m) (hmx : m ≤ ‖x‖) (hmz : m ≤ ‖z‖)
    (hh : ‖z - x‖ ≤ 1) :
    ∃ p : ℝ → ThreeSpace, ContDiff ℝ ∞ p ∧ p 0 = x ∧ p 1 = z ∧
      ∀ t, m ≤ ‖p t‖ ∧ ‖p t‖ ≤ (1 + ‖z - x‖ ^ 2 / 4) * R ∧
        ∃ V : ThreeSpace, HasDerivAt p V t ∧ ‖V‖ ≤ Real.pi / 2 * (‖z - x‖ * (R + 2)) := by
  let θ : ℝ → ℝ := fun t => (1 - Real.cos (Real.pi * t)) / 2
  have hθ0 (t : ℝ) : 0 ≤ θ t := by
    have := Real.cos_le_one (Real.pi * t)
    change 0 ≤ (1 - Real.cos (Real.pi * t)) / 2
    linarith
  have hθ1 (t : ℝ) : θ t ≤ 1 := by
    have := Real.neg_one_le_cos (Real.pi * t)
    change (1 - Real.cos (Real.pi * t)) / 2 ≤ 1
    linarith
  let F : ℝ → ThreeSpace := fun τ => (1 + ‖z - x‖ ^ 2 * (τ * (1 - τ))) • (x + τ • (z - x))
  have hθs : ContDiff ℝ ∞ θ :=
    (contDiff_const.sub (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))).div_const 2
  have hFs : ContDiff ℝ ∞ F :=
    (contDiff_const.add (contDiff_const.mul
      (contDiff_id.mul (contDiff_const.sub contDiff_id)))).smul
        (contDiff_const.add (contDiff_id.smul contDiff_const))
  refine ⟨F ∘ θ, hFs.comp hθs, ?_, ?_, fun t => ?_⟩
  · have h0 : θ 0 = 0 := by
      change (1 - Real.cos (Real.pi * 0)) / 2 = 0
      simp
    change F (θ 0) = x
    rw [h0]
    change (1 + ‖z - x‖ ^ 2 * (0 * (1 - 0))) • (x + (0 : ℝ) • (z - x)) = x
    simp
  · have h1 : θ 1 = 1 := by
      change (1 - Real.cos (Real.pi * 1)) / 2 = 1
      rw [mul_one, Real.cos_pi]
      norm_num
    change F (θ 1) = z
    rw [h1]
    change (1 + ‖z - x‖ ^ 2 * (1 * (1 - 1))) • (x + (1 : ℝ) • (z - x)) = z
    simp
  · obtain ⟨hlo, hhi, hder⟩ :=
      collarPath_bounds_C11SP hxR hzR hm1 hmx hmz hh (hθ0 t) (hθ1 t)
    refine ⟨hlo, hhi, (Real.pi * Real.sin (Real.pi * t) / 2) •
      ((‖z - x‖ ^ 2 * (1 - 2 * θ t)) • (x + θ t • (z - x)) +
        (1 + ‖z - x‖ ^ 2 * (θ t * (1 - θ t))) • (z - x)), ?_, ?_⟩
    · exact (hasDerivAt_collarPath_C11SP x z ‖z - x‖ (θ t)).scomp t
        (hasDerivAt_cosParam_C11SP t)
    · have hth : |Real.pi * Real.sin (Real.pi * t) / 2| ≤ Real.pi / 2 := by
        rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have h := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (Real.pi * t)) Real.pi_pos.le
        linarith
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul hth hder (norm_nonneg _) (by positivity)

/-- 速度算术：`scale·S² ≤ (3/2)(π/2·h·T)²`、`h² ≤ 4K²·scale·c₀²` ⇒ `S ≤ 4K·T·c₀`。 -/
theorem speed_arith_C11SP {sc S h K T c₀ : ℝ} (hsc : 0 < sc) (hc₀ : 0 ≤ c₀) (hK : 0 ≤ K)
    (hT : 0 ≤ T) (hS0 : 0 ≤ S) (hh2 : h ^ 2 ≤ 4 * (K ^ 2 * (sc * c₀ ^ 2)))
    (hS : sc * S ^ 2 ≤ 3 / 2 * (Real.pi / 2 * (h * T)) ^ 2) :
    S ≤ 4 * K * T * c₀ := by
  have hpi2' : (Real.pi / 2) ^ 2 ≤ 5 / 2 := by
    have h := Real.pi_lt_d2
    have h0 := Real.pi_pos
    nlinarith
  have e1 : sc * S ^ 2 ≤ 3 / 2 * ((Real.pi / 2) ^ 2 * (h ^ 2 * T ^ 2)) := by
    rw [mul_pow, mul_pow] at hS
    exact hS
  have e2 : (Real.pi / 2) ^ 2 * (h ^ 2 * T ^ 2) ≤ 5 / 2 * (4 * (K ^ 2 * (sc * c₀ ^ 2)) * T ^ 2) :=
    mul_le_mul hpi2' (mul_le_mul_of_nonneg_right hh2 (sq_nonneg _)) (by positivity)
      (by norm_num)
  have e3 : sc * S ^ 2 ≤ sc * (4 * K * T * c₀) ^ 2 := by
    have h : sc * (4 * K * T * c₀) ^ 2 = 16 * (K ^ 2 * (sc * c₀ ^ 2) * T ^ 2) := by ring
    rw [h]
    have hP : 0 ≤ K ^ 2 * (sc * c₀ ^ 2) * T ^ 2 := by positivity
    linarith
  exact (pow_le_pow_iff_left₀ hS0 (by positivity) two_ne_zero).mp (le_of_mul_le_mul_left e3 hsc)

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

/-- lift 的 Euclid 速度：常速 `c₀` 的输出曲线 `γ = window ∘ η`（`t` 附近），`‖η t‖ ≤ K`、`< D` ⇒
`‖(val ∘ η)'(t)‖ ≤ 2K·√scale·c₀`。 -/
theorem lift_deriv_norm_le_C11SP {E : MetricCutCapEvent P Q a s}
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b₀ : E.RetainedBoundaryIndex}
    (S : E.PresentedStaticCap fixed D m ε b₀) (hcanonical : S.hasCanonicalWindow)
    (hε : ε ≤ 1 / 2) {γ : ℝ → Q.Carrier} {η : ℝ → standardCapWindow D} {t c₀ K : ℝ}
    (hspeed : riemannianCurveSpeed E.outputMetric γ t = c₀)
    (hηC : ContMDiffAt 𝓘(ℝ, ℝ) ThreeModel ∞ η t)
    (hnear : S.window ∘ η =ᶠ[𝓝 t] γ) (hpoint : S.window (η t) = γ t)
    (hK : ‖(η t).val‖ ≤ K) (hKpi : Real.pi / 2 ≤ K) (hD : ‖(η t).val‖ < D) :
    HasDerivAt (fun r => (η r).val) (mfderiv 𝓘(ℝ, ℝ) ThreeModel η t 1 : ThreeSpace) t ∧
      ‖(mfderiv 𝓘(ℝ, ℝ) ThreeModel η t 1 : ThreeSpace)‖ ≤
        2 * K * (Real.sqrt S.neck.scale * c₀) := by
  have hsc : 0 < S.neck.scale := S.neck.scale_pos
  have hσsq : Real.sqrt S.neck.scale ^ 2 = S.neck.scale := Real.sq_sqrt hsc.le
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hK
  have hδC : ContMDiffAt 𝓘(ℝ, ℝ) ThreeModel ∞ (Subtype.val ∘ η) t :=
    (contMDiff_subtype_val (U := standardCapWindow D)).contMDiffAt.comp t hηC
  have hvalD := mfderiv_comp t
    ((contMDiff_subtype_val (U := standardCapWindow D) (n := ∞)).mdifferentiableAt (by simp))
    (hηC.mdifferentiableAt (by simp))
  rw [DifferentialGeometry.mfderiv_subtype_val] at hvalD
  let v : ThreeSpace := mfderiv 𝓘(ℝ, ℝ) ThreeModel η t 1
  have hδD : (mfderiv 𝓘(ℝ, ℝ) ThreeModel (Subtype.val ∘ η) t 1 : ThreeSpace) = v :=
    congrArg (fun A : ℝ →L[ℝ] ThreeSpace => A 1) hvalD
  have hdiff : DifferentiableAt ℝ (Subtype.val ∘ η) t :=
    mdifferentiableAt_iff_differentiableAt.mp (hδC.mdifferentiableAt (by simp))
  have hderiv : deriv (Subtype.val ∘ η) t = v := by
    rw [← hδD, mfderiv_eq_fderiv]
    exact (fderiv_apply_one_eq_deriv).symm
  refine ⟨?_, ?_⟩
  · have h := hdiff.hasDerivAt
    rw [hderiv] at h
    exact h
  · have hD' := (hnear.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel)).symm
    rw [mfderiv_comp t (S.window_smooth.contMDiff.mdifferentiableAt (by simp))
      (hηC.mdifferentiableAt (by simp))] at hD'
    have hγD : (mfderiv 𝓘(ℝ, ℝ) ThreeModel γ t 1 : ThreeSpace) =
        mfderiv ThreeModel ThreeModel S.window (η t) v :=
      congrArg (fun A : ℝ →L[ℝ] ThreeSpace => A 1) hD'
    have hγspeed : riemannianCurveSpeed E.outputMetric γ t =
        Real.sqrt (E.outputMetric.inner (S.window (η t))
          (mfderiv ThreeModel ThreeModel S.window (η t) v)
          (mfderiv ThreeModel ThreeModel S.window (η t) v)) :=
      congrArg Real.sqrt (congrArg₂
        (fun (p : Q.Carrier) (v : ThreeSpace) => E.outputMetric.inner p v v)
        hpoint.symm hγD)
    have hquad := (actual_window_quad_bounds S hcanonical hε (η t) hD v).1
    have hlow := norm_sq_le_metric_C11SP (v := v) hK hKpi
    have hY0 := metric_inner_self_nonneg E.outputMetric (S.window (η t))
      (mfderiv ThreeModel ThreeModel S.window (η t) v)
    rw [hspeed] at hγspeed
    generalize E.outputMetric.inner (S.window (η t))
      (mfderiv ThreeModel ThreeModel S.window (η t) v)
      (mfderiv ThreeModel ThreeModel S.window (η t) v) = Y at hquad hγspeed hY0
    have hYc : c₀ ^ 2 = Y := by
      have h := Real.sq_sqrt hY0
      rw [← hγspeed] at h
      exact h
    have hsq : ‖v‖ ^ 2 ≤ (2 * K * (Real.sqrt S.neck.scale * c₀)) ^ 2 := by
      have hA : 0 ≤ K ^ 2 * (S.neck.scale * c₀ ^ 2) := by positivity
      have h1 : K ^ 2 * StandardCap.metric.inner (η t).val v v ≤
          K ^ 2 * (2 * (S.neck.scale * c₀ ^ 2)) :=
        mul_le_mul_of_nonneg_left (by rw [hYc]; linarith) (sq_nonneg _)
      have h2 : (2 * K * (Real.sqrt S.neck.scale * c₀)) ^ 2 =
          4 * K ^ 2 * (Real.sqrt S.neck.scale ^ 2 * c₀ ^ 2) := by ring
      rw [h2, hσsq]
      linarith
    have h := Real.sqrt_le_sqrt hsq
    have hc0 : 0 ≤ c₀ := by rw [hγspeed]; exact Real.sqrt_nonneg _
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h

/-- (i)+(ii)：最短线留在 b₀ window 半径 `≤ TE + 10 + 2c` 内，另一端 `= window z`，且
Euclid 位移 `‖z − x‖ ≤ 2(TE + 11)·√scale·c₀`，`d_out = c₀`、`√scale·c₀ < c`。 -/
theorem short_lift_C11SP (E : MetricCutCapEvent P Q a s)
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b₀ : E.RetainedBoundaryIndex}
    (S : E.PresentedStaticCap fixed D m ε b₀) (hcanonical : S.hasCanonicalWindow)
    (hε : ε ≤ 1 / 2) {x : standardCapWindow D} {q : Q.Carrier} {c : ℝ}
    (hc0 : 0 < c) (hx2 : ‖x.val‖ ≤ 𝒯 + 10) (hRD : 𝒯 + 10 + 2 * c < D) (h4c : 4 * c ≤ 1)
    (hlt : riemannianEDistOf E.outputMetric (S.window x) q <
      ENNReal.ofReal (c / Real.sqrt S.neck.scale)) :
    ∃ (c₀ : ℝ) (z : standardCapWindow D), 0 ≤ c₀ ∧
      riemannianEDistOf E.outputMetric (S.window x) q = ENNReal.ofReal c₀ ∧
      Real.sqrt S.neck.scale * c₀ < c ∧ S.window z = q ∧ ‖z.val‖ ≤ 𝒯 + 10 + 2 * c ∧
      ‖z.val - x.val‖ ≤ 2 * (𝒯 + 11) * (Real.sqrt S.neck.scale * c₀) := by
  have hTE0 := StandardCap.transitionEnd_pos
  have hpi2 : Real.pi / 2 ≤ 𝒯 + 11 := by linarith [Real.pi_lt_d2]
  have hsc : 0 < S.neck.scale := S.neck.scale_pos
  have hσ : 0 < Real.sqrt S.neck.scale := Real.sqrt_pos.mpr hsc
  have hfin : riemannianEDistOf E.outputMetric (S.window x) q ≠ ⊤ := ne_top_of_lt hlt
  obtain ⟨γ, c₀, hc₀, hγ, hγ0, hγ1, hspeed, hlen, hseg⟩ :=
    exists_minimizing_curve_speed_C11SP Q E.outputMetric (S.window x) q hfin
  have hd : riemannianEDistOf E.outputMetric (S.window x) q = ENNReal.ofReal c₀ := by
    have h := hseg 0 1 le_rfl zero_le_one le_rfl
    rw [hγ0, hγ1, sub_zero, mul_one] at h
    exact h
  have hσc : Real.sqrt S.neck.scale * c₀ < c := by
    rw [hd] at hlt
    have h := (ENNReal.ofReal_lt_ofReal_iff (div_pos hc0 hσ)).mp hlt
    rw [lt_div_iff₀ hσ] at h
    linarith
  have hxR : ‖x.val‖ < 𝒯 + 10 + 2 * c := by linarith
  have hstay : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ S.window ''
      {y : standardCapWindow D | ‖y.val‖ ≤ 𝒯 + 10 + 2 * c} := by
    intro t ht
    by_contra hout
    have ht0 : 0 < t := by
      rcases ht.1.lt_or_eq with h | h
      · exact h
      · exfalso
        apply hout
        rw [← h, hγ0]
        exact ⟨x, hxR.le, rfl⟩
    obtain ⟨τ, hτ, hτstay, y, hyR, hyτ⟩ := exists_window_exit S
      (by linarith : 𝒯 + 10 + 2 * c < D + 1) ht0 γ hγ.continuous.continuousOn x hxR hγ0 hout
    have hmap : MapsTo γ (Icc 0 τ) (S.window '' {y : standardCapWindow D | ‖y.val‖ < D}) := by
      intro t' ht'
      obtain ⟨y', hy', hy'e⟩ := hτstay t' ht'
      exact ⟨y', lt_of_le_of_lt hy' hRD, hy'e⟩
    have hrad := window_radial_change_le_length S hcanonical hε γ hγ hτ.1.le hmap
      x y hγ0.symm hyτ
    have hτ1 : τ ≤ 1 := hτ.2.trans ht.2
    rw [hlen 0 τ hτ.1.le, ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity)
        (mul_nonneg hc₀ (by linarith [hτ.1])))] at hrad
    have hab := le_abs_self (‖y.val‖ - ‖x.val‖)
    have hτm : Real.sqrt S.neck.scale * c₀ * τ ≤ Real.sqrt S.neck.scale * c₀ :=
      mul_le_of_le_one_right (mul_nonneg hσ.le hc₀) hτ1
    linarith
  obtain ⟨η, hη⟩ := exists_window_smooth_lift S γ hγ x
  have hinj := S.window_smooth.isEmbedding.injective
  have hrange : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ range S.window := by
    intro t ht
    obtain ⟨y, _, hy⟩ := hstay t ht
    exact ⟨y, hy⟩
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1, S.window (η t) = γ t :=
    fun t ht => (hη t (hrange t ht)).2
  have hηR : ∀ t ∈ Icc (0 : ℝ) 1, ‖(η t).val‖ ≤ 𝒯 + 10 + 2 * c := by
    intro t ht
    obtain ⟨y, hy, hyt⟩ := hstay t ht
    have h : η t = y := hinj ((hpoint t ht).trans hyt.symm)
    rw [h]
    exact hy
  have hη0 : η 0 = x := hinj ((hpoint 0 ⟨le_rfl, zero_le_one⟩).trans hγ0)
  have hJ := DifferentialGeometry.Topology.Manifold.isOpenEmbedding_of_injective_immersion
    S.window S.window_smooth.contMDiff S.window_smooth.isEmbedding.injective
    (fun y => (S.window_smooth.isImmersion.isImmersionAt y).mfderiv_injective (by simp)) rfl
  have hU : IsOpen (γ ⁻¹' range S.window) := hJ.isOpen_range.preimage hγ.continuous
  have hδ : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun r => (η r).val) (mfderiv 𝓘(ℝ, ℝ) ThreeModel η t 1 : ThreeSpace) t ∧
      ‖(mfderiv 𝓘(ℝ, ℝ) ThreeModel η t 1 : ThreeSpace)‖ ≤
        2 * (𝒯 + 11) * (Real.sqrt S.neck.scale * c₀) := by
    intro t ht
    have hnear : S.window ∘ η =ᶠ[𝓝 t] γ := by
      filter_upwards [hU.mem_nhds (hrange t ht)] with r hr
      exact (hη r hr).2
    exact lift_deriv_norm_le_C11SP S hcanonical hε (hspeed t) (hη t (hrange t ht)).1 hnear
      (hpoint t ht) ((hηR t ht).trans (by linarith)) hpi2 (lt_of_le_of_lt (hηR t ht) hRD)
  have hdisp : ‖(η 1).val - x.val‖ ≤ 2 * (𝒯 + 11) * (Real.sqrt S.neck.scale * c₀) := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (a := (0 : ℝ)) (b := 1)
      (f := fun r => (η r).val)
      (f' := fun r => (mfderiv 𝓘(ℝ, ℝ) ThreeModel η r 1 : ThreeSpace))
      (fun r hr => (hδ r hr).1.hasDerivWithinAt)
      (fun r hr => (hδ r (Ico_subset_Icc_self hr)).2) 1 ⟨zero_le_one, le_rfl⟩
    simpa only [hη0, sub_zero, mul_one] using h
  exact ⟨c₀, η 1, hc₀, hd, hσc, (hpoint 1 ⟨zero_le_one, le_rfl⟩).trans hγ1,
    hηR 1 ⟨zero_le_one, le_rfl⟩, hdisp⟩

/-- (iii) 事件层：模型曲线 `p`（`TE < ‖p‖ < D`，导数 `≤ L`）经 b₀ window 推到输出侧：光滑、
落在 `interior (range oldOutput)`（`exceptional_mem_inner_window` + 单射 + `hdisj`）、
`scale·speed² ≤ (3/2)·L²`。 -/
theorem window_curve_of_path_C11SP (E : MetricCutCapEvent P Q a s)
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    (S : ∀ b : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D m ε b)
    (hOld : E.old = E.transition.trace.retainedCore)
    (hcanonical : ∀ b, (S b).hasCanonicalWindow) (hε : ε ≤ 1 / 2)
    (hdisj : ∀ b b' : E.RetainedBoundaryIndex, b ≠ b' → ∀ y z : standardCapWindow D,
      ‖z.val‖ ≤ StandardCap.transitionEnd + 10 → (S b).window y ≠ (S b').window z)
    (b₀ : E.RetainedBoundaryIndex) {p : ℝ → ThreeSpace} {L : ℝ} (hp : ContDiff ℝ ∞ p)
    (hlo : ∀ t, 𝒯 < ‖p t‖) (hhi : ∀ t, ‖p t‖ < D)
    (hder : ∀ t, ∃ V : ThreeSpace, HasDerivAt p V t ∧ ‖V‖ ≤ L)
    (y₀ y₁ : standardCapWindow D) (h0 : p 0 = y₀.val) (h1 : p 1 = y₁.val) :
    ∃ γ : ℝ → Q.Carrier, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ ∧
      γ 0 = (S b₀).window y₀ ∧ γ 1 = (S b₀).window y₁ ∧
      MapsTo γ (Icc (0 : ℝ) 1) (interior (range E.oldOutput)) ∧
      ∀ t, (S b₀).neck.scale * riemannianCurveSpeed E.outputMetric γ t ^ 2 ≤ 3 / 2 * L ^ 2 := by
  have hmem (t : ℝ) : p t ∈ standardCapWindow D := by
    change ‖p t‖ < D + 1
    linarith [hhi t]
  let η : ℝ → standardCapWindow D := fun t => ⟨p t, hmem t⟩
  have hη : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ η :=
    (ContMDiff.subtypeVal_comp_iff (standardCapWindow D) η).mp hp.contMDiff
  have hinj := (S b₀).window_smooth.isEmbedding.injective
  refine ⟨(S b₀).window ∘ η, (S b₀).window_smooth.contMDiff.comp hη, ?_, ?_, ?_, ?_⟩
  · change (S b₀).window (η 0) = _
    congr 1
    exact Subtype.ext h0
  · change (S b₀).window (η 1) = _
    congr 1
    exact Subtype.ext h1
  · intro t _
    by_contra hnot
    obtain ⟨b, z', hz', hzt⟩ := exceptional_mem_inner_window E S hOld hcanonical hnot
    by_cases hb : b = b₀
    · subst hb
      have hzη : z' = η t := hinj hzt
      have h1' : ‖z'.val‖ = ‖p t‖ := by rw [hzη]
      linarith [hlo t]
    · exact hdisj b₀ b (Ne.symm hb) (η t) z' (by linarith) hzt.symm
  · intro t
    obtain ⟨V, hV, hVn⟩ := hder t
    have hD' := mfderiv_comp t ((S b₀).window_smooth.contMDiff.mdifferentiableAt (by simp))
      (hη.mdifferentiableAt (by simp) (x := t))
    have hvalD := mfderiv_comp t
      ((contMDiff_subtype_val (U := standardCapWindow D) (n := ∞)).mdifferentiableAt
        (by simp)) (hη.mdifferentiableAt (by simp) (x := t))
    rw [DifferentialGeometry.mfderiv_subtype_val] at hvalD
    let v : ThreeSpace := mfderiv 𝓘(ℝ, ℝ) ThreeModel η t 1
    have hpD : mfderiv 𝓘(ℝ, ℝ) ThreeModel (Subtype.val ∘ η) t 1 = V := by
      change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ThreeSpace) p t 1 = V
      rw [mfderiv_eq_fderiv]
      exact hV.deriv
    have hv : v = V := by
      have := congrArg (fun L : ℝ →L[ℝ] ThreeSpace => L 1) hvalD
      exact this.symm.trans hpD
    have hγD : (mfderiv 𝓘(ℝ, ℝ) ThreeModel ((S b₀).window ∘ η) t 1 : ThreeSpace) =
        mfderiv ThreeModel ThreeModel (S b₀).window (η t) v :=
      congrArg (fun L : ℝ →L[ℝ] ThreeSpace => L 1) hD'
    have hX : StandardCap.metric.inner (η t).val v v ≤ L ^ 2 := by
      rw [hv]
      exact (StandardCap.metric_inner_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) hVn 2)
    have hquad := (actual_window_quad_bounds (S b₀) (hcanonical b₀) hε (η t) (hhi t) v).2
    have hY0 := metric_inner_self_nonneg E.outputMetric ((S b₀).window (η t))
      (mfderiv ThreeModel ThreeModel (S b₀).window (η t) v)
    have hsp : riemannianCurveSpeed E.outputMetric ((S b₀).window ∘ η) t =
        Real.sqrt (E.outputMetric.inner ((S b₀).window (η t))
          (mfderiv ThreeModel ThreeModel (S b₀).window (η t) v)
          (mfderiv ThreeModel ThreeModel (S b₀).window (η t) v)) :=
      congrArg Real.sqrt (congrArg (fun w : ThreeSpace =>
        E.outputMetric.inner ((S b₀).window (η t)) w w) hγD)
    rw [hsp, Real.sq_sqrt hY0]
    linarith

/-- **G1（PROVED）`hshort′`**：buffer 端点 `oldOutput u = window_{b₀} x`、另一端 `w` 受保护或在
某 cap 的 buffer、`d_out < c/√scale_{b₀}` ⇒ retained 区（`interior (range oldOutput)`）内有长
`≤ Cs·d_out` 的光滑曲线；`c = min (1/(2K)) ((D − TE − 10)/K²)`，`Cs = 4K(TE + 13)`，`K = TE + 11`。
（A2 G5 的 `hshort` 原形无 `hw`，为假：见文件头。） -/
theorem hshort_of_collar_C11SP (E : MetricCutCapEvent P Q a s)
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    (S : ∀ b : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D m ε b)
    (hOld : E.old = E.transition.trace.retainedCore)
    (hcanonical : ∀ b, (S b).hasCanonicalWindow) (hε : ε ≤ 1 / 2)
    (hD : StandardCap.transitionEnd + 10 < D)
    (hdisj : ∀ b b' : E.RetainedBoundaryIndex, b ≠ b' → ∀ y z : standardCapWindow D,
      ‖z.val‖ ≤ StandardCap.transitionEnd + 10 → (S b).window y ≠ (S b').window z) :
    ∀ (u w : E.old) (b₀ : E.RetainedBoundaryIndex) (x : standardCapWindow D),
      StandardCap.transitionEnd < ‖x.val‖ → ‖x.val‖ ≤ StandardCap.transitionEnd + 10 →
      (S b₀).window x = E.oldOutput u →
      ((∀ b, E.oldOutput w ∉ (S b).window ''
          {y : standardCapWindow D | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
        ∃ (b₁ : E.RetainedBoundaryIndex) (x' : standardCapWindow D),
          StandardCap.transitionEnd < ‖x'.val‖ ∧ ‖x'.val‖ ≤ StandardCap.transitionEnd + 10 ∧
          (S b₁).window x' = E.oldOutput w) →
      riemannianEDistOf E.outputMetric (E.oldOutput u) (E.oldOutput w) <
        ENNReal.ofReal (min (1 / (2 * (StandardCap.transitionEnd + 11)))
          ((D - (StandardCap.transitionEnd + 10)) / (StandardCap.transitionEnd + 11) ^ 2) /
            Real.sqrt (S b₀).neck.scale) →
      ∃ γ : ℝ → Q.Carrier, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ ∧
        γ 0 = E.oldOutput u ∧ γ 1 = E.oldOutput w ∧
        MapsTo γ (Icc (0 : ℝ) 1) (interior (range E.oldOutput)) ∧
        riemannianCurveELength E.outputMetric γ 0 1 ≤
          ENNReal.ofReal (4 * (StandardCap.transitionEnd + 11) *
            (StandardCap.transitionEnd + 13)) *
            riemannianEDistOf E.outputMetric (E.oldOutput u) (E.oldOutput w) := by
  intro u w b₀ x hx1 hx2 hxu hw hlt
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = min (1 / (2 * (𝒯 + 11))) ((D - (𝒯 + 10)) / (𝒯 + 11) ^ 2) :=
    ⟨_, rfl⟩
  rw [← hcdef] at hlt
  have hTE0 := StandardCap.transitionEnd_pos
  have hTE1 : 1 < 𝒯 := by
    have h := StandardCap.transitionStart_pos
    have h' : 𝒯 = StandardCap.transitionStart + 1 := rfl
    linarith
  have hKpos : 0 < 𝒯 + 11 := by linarith
  have hD0 : 0 < D - (𝒯 + 10) := by linarith
  have hc0 : 0 < c := by
    rw [hcdef]
    exact lt_min (by positivity) (by positivity)
  have hcle1 : c ≤ 1 / (2 * (𝒯 + 11)) := by
    rw [hcdef]
    exact min_le_left _ _
  have hcle2 : c ≤ (D - (𝒯 + 10)) / (𝒯 + 11) ^ 2 := by
    rw [hcdef]
    exact min_le_right _ _
  have hc1 : 2 * (𝒯 + 11) * c ≤ 1 := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (𝒯 + 11))).mp hcle1
    linarith
  have hc2 : (𝒯 + 11) ^ 2 * c ≤ D - (𝒯 + 10) := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < (𝒯 + 11) ^ 2)).mp hcle2
    linarith
  have h4c1 : 4 * c ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ 𝒯 + 11) hc0.le
    linarith
  have h4c2 : 4 * c ≤ D - (𝒯 + 10) := by
    have h4 : (4 : ℝ) ≤ (𝒯 + 11) ^ 2 := by nlinarith
    have h := mul_le_mul_of_nonneg_right h4 hc0.le
    linarith
  have hRD : 𝒯 + 10 + 2 * c < D := by linarith
  have hsc : 0 < (S b₀).neck.scale := (S b₀).neck.scale_pos
  have hσ : 0 < Real.sqrt (S b₀).neck.scale := Real.sqrt_pos.mpr hsc
  have hσsq : Real.sqrt (S b₀).neck.scale ^ 2 = (S b₀).neck.scale := Real.sq_sqrt hsc.le
  rw [← hxu] at hlt ⊢
  obtain ⟨c₀, z, hc₀, hd, hσc, hη1, hzR, hdisp⟩ :=
    short_lift_C11SP E (S b₀) (hcanonical b₀) hε hc0 hx2 hRD h4c1 hlt
  have hinj := (S b₀).window_smooth.isEmbedding.injective
  have hzTE : 𝒯 < ‖z.val‖ := by
    rcases hw with hprot | ⟨b₁, x', hx'1, _, hx'w⟩
    · by_contra hle
      exact hprot b₀ ⟨z, (by change ‖z.val‖ ≤ 𝒯 + 10; linarith [not_lt.mp hle]), hη1⟩
    · by_cases hb : b₁ = b₀
      · subst hb
        have h : x' = z := hinj (hx'w.trans hη1.symm)
        rw [← h]
        exact hx'1
      · by_contra hle
        exact hdisj b₁ b₀ hb x' z (by linarith [not_lt.mp hle]) (hx'w.trans hη1.symm)
  have hKσ : 2 * (𝒯 + 11) * (Real.sqrt (S b₀).neck.scale * c₀) < 2 * (𝒯 + 11) * c :=
    mul_lt_mul_of_pos_left hσc (by positivity)
  have hhK : ‖z.val - x.val‖ < 2 * (𝒯 + 11) * c := lt_of_le_of_lt hdisp hKσ
  have hh1 : ‖z.val - x.val‖ ≤ 1 := by linarith
  have hm1 : 1 ≤ min ‖x.val‖ ‖z.val‖ := le_min (by linarith) (by linarith)
  obtain ⟨p, hp, hp0, hp1, hpb⟩ := exists_collarPath_C11SP (R := 𝒯 + 10 + 2 * c)
    (by linarith) hzR hm1 (min_le_left _ _) (min_le_right _ _) hh1
  have hRK : 𝒯 + 10 + 2 * c ≤ 𝒯 + 11 := by linarith
  have hphi (t : ℝ) : ‖p t‖ < D := by
    have h1 := (hpb t).2.1
    have hhh : ‖z.val - x.val‖ ^ 2 ≤ ‖z.val - x.val‖ := by
      nlinarith [norm_nonneg (z.val - x.val)]
    have h2 : ‖z.val - x.val‖ ^ 2 * (𝒯 + 10 + 2 * c) ≤ ‖z.val - x.val‖ * (𝒯 + 11) :=
      mul_le_mul hhh hRK (by linarith) (norm_nonneg _)
    have h3 : ‖z.val - x.val‖ * (𝒯 + 11) < 2 * (𝒯 + 11) * c * (𝒯 + 11) :=
      mul_lt_mul_of_pos_right hhK hKpos
    have h4 : 2 * (𝒯 + 11) * c * (𝒯 + 11) ≤ 2 * (D - (𝒯 + 10)) := by linarith
    linarith
  have hder (t : ℝ) : ∃ V : ThreeSpace, HasDerivAt p V t ∧
      ‖V‖ ≤ Real.pi / 2 * (‖z.val - x.val‖ * (𝒯 + 13)) := by
    obtain ⟨V, hV, hVn⟩ := (hpb t).2.2
    refine ⟨V, hV, hVn.trans ?_⟩
    have h2 : ‖z.val - x.val‖ * (𝒯 + 10 + 2 * c + 2) ≤ ‖z.val - x.val‖ * (𝒯 + 13) :=
      mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  obtain ⟨γ, hγ, hγ0, hγ1, hmap, hspeed⟩ := window_curve_of_path_C11SP E S hOld hcanonical hε
    hdisj b₀ hp (fun t => lt_of_lt_of_le (lt_min (by linarith) hzTE) (hpb t).1) hphi hder x z
    hp0 hp1
  refine ⟨γ, hγ, hγ0, hγ1.trans hη1, hmap, ?_⟩
  have hspeed' (t : ℝ) : riemannianCurveSpeed E.outputMetric γ t ≤
      4 * (𝒯 + 11) * (𝒯 + 13) * c₀ := by
    have hh2 : ‖z.val - x.val‖ ^ 2 ≤ 4 * ((𝒯 + 11) ^ 2 * ((S b₀).neck.scale * c₀ ^ 2)) := by
      have h := pow_le_pow_left₀ (norm_nonneg _) hdisp 2
      have h2 : (2 * (𝒯 + 11) * (Real.sqrt (S b₀).neck.scale * c₀)) ^ 2 =
          4 * (𝒯 + 11) ^ 2 * (Real.sqrt (S b₀).neck.scale ^ 2 * c₀ ^ 2) := by ring
      rw [h2, hσsq] at h
      linarith
    exact speed_arith_C11SP hsc hc₀ hKpos.le (by linarith) (riemannianCurveSpeed_nonneg _ _ _)
      hh2 (hspeed t)
  have hle : riemannianCurveELength E.outputMetric γ 0 1 ≤
      ∫⁻ _ in Icc (0 : ℝ) 1, ENNReal.ofReal (4 * (𝒯 + 11) * (𝒯 + 13) * c₀) := by
    unfold riemannianCurveELength
    exact lintegral_mono fun t => ENNReal.ofReal_le_ofReal (hspeed' t)
  rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one] at hle
  rw [hd, ← ENNReal.ofReal_mul (by positivity)]
  exact hle

end MetricCutCapEvent

namespace ObservedHistory

/-- **G1 history 层（PROVED）**：`hshort′` 的 history 形（= G2 twin
`surgery_no_shortcut_buffer_short_C11SP` 的 `hshort′` binder，`c`、`Cs` 取显式值）。 -/
theorem hshort_of_collar_history_C11SP (H : ObservedHistory.{u}) (e : Fin H.eventCount)
    {fixed : StaticCapScaffold} {Dc εc : ℝ} {mc : ℕ}
    (S : ∀ b : (H.event e).RetainedBoundaryIndex,
      (H.event e).PresentedStaticCap fixed Dc mc εc b)
    (hOld : (H.event e).old = (H.event e).transition.trace.retainedCore)
    (hcanonical : ∀ b, (S b).hasCanonicalWindow) (hε : εc ≤ 1 / 2)
    (hD : StandardCap.transitionEnd + 10 < Dc)
    (hdisj : ∀ b b' : (H.event e).RetainedBoundaryIndex, b ≠ b' →
      ∀ y z : standardCapWindow Dc, ‖z.val‖ ≤ StandardCap.transitionEnd + 10 →
        (S b).window y ≠ (S b').window z) :
    ∀ (u w : (H.event e).old) (b₀ : (H.event e).RetainedBoundaryIndex)
      (x : standardCapWindow Dc),
      StandardCap.transitionEnd < ‖x.val‖ → ‖x.val‖ ≤ StandardCap.transitionEnd + 10 →
      (S b₀).window x = (H.event e).oldOutput u →
      ((∀ b, (H.event e).oldOutput w ∉ (S b).window ''
          {y : standardCapWindow Dc | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
        ∃ (b₁ : (H.event e).RetainedBoundaryIndex) (x' : standardCapWindow Dc),
          StandardCap.transitionEnd < ‖x'.val‖ ∧ ‖x'.val‖ ≤ StandardCap.transitionEnd + 10 ∧
          (S b₁).window x' = (H.event e).oldOutput w) →
      riemannianEDistOf (H.event e).outputMetric ((H.event e).oldOutput u)
          ((H.event e).oldOutput w) <
        ENNReal.ofReal (min (1 / (2 * (StandardCap.transitionEnd + 11)))
          ((Dc - (StandardCap.transitionEnd + 10)) / (StandardCap.transitionEnd + 11) ^ 2) /
            Real.sqrt (S b₀).neck.scale) →
      ∃ γ : ℝ → (H.stage e.succ).Carrier, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ ∧
        γ 0 = (H.event e).oldOutput u ∧ γ 1 = (H.event e).oldOutput w ∧
        MapsTo γ (Icc (0 : ℝ) 1) (interior (range (H.event e).oldOutput)) ∧
        riemannianCurveELength (H.event e).outputMetric γ 0 1 ≤
          ENNReal.ofReal (4 * (StandardCap.transitionEnd + 11) *
            (StandardCap.transitionEnd + 13)) * riemannianEDistOf (H.event e).outputMetric
            ((H.event e).oldOutput u) ((H.event e).oldOutput w) :=
  (H.event e).hshort_of_collar_C11SP S hOld hcanonical hε hD hdisj

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
