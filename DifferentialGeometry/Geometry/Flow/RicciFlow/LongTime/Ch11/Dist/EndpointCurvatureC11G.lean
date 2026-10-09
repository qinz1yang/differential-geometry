import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.SurgeryNoShortcutC11D
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaSeedPatchC11Q
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PinchingTimeScale

/-!
# P6 几何输入 G2：端点 `|Rm|` 界（O-CH11-P6GEO，后缀 `_C11G`）

DIST 的 (D3) 端点曲率前提（R-C11-2 D-7）：`hsmooth_of_rmNorm_le_C11D` 的 `hRm`（末 stage 窗口内，种子点与
`x` 的 `ℓ`-球上 `|Rm| ≤ K`）与 `hevent_of_records_C11D` 的 `hRic`（event stage 上两 trace 点的 `ℓ`-球
`Ric ≤ (3/ℓ²) g`）；序列层 = DIST `hrate_of_endpoint_bounds_C11D` 的 `hgeom` 的 (i) 与 (iii)。

* **种子端（K0）** `seed_rmNorm_le_of_smallParabolic_C11G`：`hasSmallParabolicCurvature H T p r`、
  `aSeed = T − r²` ⇒ 对 `[aSeed, T]` 内每个时刻 `τ`，`B_τ(O_τ, r/50)` 上 `|Rm| ≤ r⁻²`。证明 = K0 的
  `exists_terminal_preimage_of_past_seed_ball_C11Q`（深度 `v² = T − τ ≤ r²`，`L = e³`，`R = r/2`，
  core `r/50 < (r/2)/e³`）：球内每点是某个 `r`-受控 trace 在 `τ` 的点。
* **另一端（BCAD + pinching）**：标量上界 `R ≤ C Q`（BCAD 形，显式前提——窗口一致版要等
  P6ANCH G2 / 窗口 BCAD）+ Pre841 native 的 Hamilton–Ivey pinching
  （`InFixedHamiltonIveyRegion … (a₀ + t)`）
  ⇒ `|Rm| ≤ 2√3 (C/2 + max C (2e⁴)) Q`（`sqrt_rmNormSq_le_of_HI_scalar_C11G`，树内
  `FILL910.A04b_rm_le_of_pinching_at_time_scale` 取 `s = Q^{-1/2}`、`b = 1`，要 `Q t ≥ 1`）。
* 单 history 生产：`hRm_of_seed_pinching_C11G`（DIST `hRm` 逐字形）、`hRic_of_seed_pinching_C11G`
  （DIST `hRic` 逐字形）。
* **序列层** `hgeom_smooth_ric_of_K0_pinching_C11G`：`R_n r_n² → ∞`、`(D2)` 窗口、晚期
  `R_n (s_n − T/R_n) ≥ 1`、pinching、BCAD 形标量界（半径 `R_n^{-1/2}`、常数 `C_{D,T}`）⇒ DIST `hgeom`
  的 (i) ∧ (iii)（`ℓ = K^{-1/2}`，`K = max 1 (2√3(C/2 + max C (2e⁴)))`，`K ℓ² = 1`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

/-! ## 换算 -/

/-- `r⁴ X ≤ 1`（`X ≥ 0`）⇒ `√X ≤ r⁻²`。 -/
theorem sqrt_le_one_div_sq_of_pow_four_mul_le_one_C11G {r X : ℝ} (hr : 0 < r) (hX : 0 ≤ X)
    (h : r ^ 4 * X ≤ 1) : Real.sqrt X ≤ 1 / r ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  have hs := Real.sqrt_nonneg X
  have heq : (Real.sqrt X * r ^ 2) ^ 2 = r ^ 4 * X := by
    rw [mul_pow, Real.sq_sqrt hX]
    ring
  have h1 : (Real.sqrt X * r ^ 2) ^ 2 ≤ 1 := heq ▸ h
  nlinarith [mul_nonneg hs (sq_nonneg r)]

/-- stage 内部时刻的 `activeStage`：`time (activeStage s) ≤ τ ≤ s` ⇒ `activeStage τ = activeStage s`。 -/
theorem activeStage_eq_of_time_le_C11G (H : ObservedHistory.{u}) (τ s : Icc (0 : ℝ) H.horizon)
    (h1 : H.time (H.activeStage s) ≤ τ) (h2 : (τ : ℝ) ≤ s) :
    H.activeStage τ = H.activeStage s :=
  H.activeStage_eq_of_maximal τ _ h1 fun k hk => H.le_activeStage s k (hk.trans h2)

/-- event slab 内部时刻：`time e⁻ ≤ τ < time e⁺` ⇒ `activeStage τ = e⁻`。 -/
theorem activeStage_eq_castSucc_C11G (H : ObservedHistory.{u}) (e : Fin H.eventCount)
    (τ : Icc (0 : ℝ) H.horizon) (h1 : H.time e.castSucc ≤ τ) (h2 : (τ : ℝ) < H.time e.succ) :
    H.activeStage τ = e.castSucc := by
  refine H.activeStage_eq_of_maximal τ e.castSucc h1 fun k hk => ?_
  by_contra hlt
  have hs : e.succ ≤ k := Fin.castSucc_lt_iff_succ_le.mp (not_le.mp hlt)
  have := H.time_strictMono.monotone hs
  linarith

/-- pinching 的 stage 形：`hpin`（Pre841 native 形，`activeStage` 包装）⇒ 在 `k = activeStage τ` 上。 -/
theorem inFixedHI_stage_C11G (H : ObservedHistory.{u}) {a₀ : ℝ}
    (hpin : ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a₀ + t) x)
    (τ : Icc (0 : ℝ) H.horizon) (k : Fin (H.eventCount + 1)) (hk : H.activeStage τ = k)
    (x : (H.stage k).Carrier) :
    InFixedHamiltonIveyRegion (H.stageMetric k τ) (a₀ + τ) x := by
  subst hk
  exact hpin τ x

/-- **pinching ⇒ `|Rm|`（`_C11G`）**：Hamilton–Ivey 区域（年龄 `a₀ + τ`）、`R ≤ C Q`、`Q τ ≥ 1`
⇒ `|Rm| ≤ 2√3 (C/2 + max C (2e⁴)) Q`。 -/
theorem sqrt_rmNormSq_le_of_HI_scalar_C11G {X : Type*} [TopologicalSpace X]
    [ChartedSpace ThreeSpace X] [IsManifold ThreeModel ∞ X] [T2Space X]
    (g : SmoothRiemannianMetric ThreeModel X) (x : X) {a₀ τ Q C : ℝ} (ha₀ : 0 ≤ a₀)
    (hτ : 0 < τ) (hQ : 0 < Q) (hQτ : 1 ≤ Q * τ) (hC : 0 ≤ C)
    (hfixed : InFixedHamiltonIveyRegion g (a₀ + τ) x) (hscalar : metricScalarAt g x ≤ C * Q) :
    Real.sqrt (normSq0S g x 4 (metricRm04At g x)) ≤
      2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)) * Q := by
  have hsq : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ
  have hs : 0 < (Real.sqrt Q)⁻¹ := inv_pos.2 hsq
  have hs2 : (Real.sqrt Q)⁻¹ ^ 2 = Q⁻¹ := by rw [inv_pow, Real.sq_sqrt hQ.le]
  have hQinv : Q⁻¹ ≤ τ := by
    rw [inv_eq_one_div, div_le_iff₀ hQ]
    linarith
  have hsb : (Real.sqrt Q)⁻¹ ≤ 1 * Real.sqrt τ := by
    rw [one_mul, ← Real.sqrt_inv]
    exact Real.sqrt_le_sqrt hQinv
  have hscal' : metricScalarAt g x ≤ C / (Real.sqrt Q)⁻¹ ^ 2 := by
    rw [hs2, div_inv_eq_mul]
    exact hscalar
  have h := FILL910.A04b_rm_le_of_pinching_at_time_scale g x ha₀ hτ (by linarith : τ / 2 ≤ τ)
    hs one_pos hsb hC hfixed hscal'
  rw [hs2, one_pow, mul_one, div_inv_eq_mul] at h
  exact h

/-! ## 种子端（K0） -/

/-- **种子端 `|Rm|`（K0，`_C11G`）**：`hasSmallParabolicCurvature H T p r`、`aSeed = T − r²`；
`aSeed ≤ τ ≤ T`（stage `k = activeStage τ`）⇒ `B_τ(O_τ, r/50)` 上 `|Rm| ≤ r⁻²`。 -/
theorem seed_rmNorm_le_of_smallParabolic_C11G (H : ObservedHistory.{u})
    {T aSeed : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ T) {p : (H.stageAt T).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature H T p r)
    (hclock : (aSeed : ℝ) = (T : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (τ : Icc (0 : ℝ) H.horizon) (h1 : aSeed ≤ τ) (h2 : τ ≤ T) (k : Fin (H.eventCount + 1))
    (hk : H.activeStage τ = k) (hk1 : H.activeStage aSeed ≤ k) (hk2 : k ≤ H.activeStage T)
    (z : (H.stage k).Carrier)
    (hz : riemannianEDistOf (H.stageMetric k τ) (seedTrace.point k hk1 hk2) z <
      ENNReal.ofReal (r / 50)) :
    Real.sqrt (normSq0S (H.stageMetric k τ) z 4 (metricRm04At (H.stageMetric k τ) z)) ≤
      1 / r ^ 2 := by
  have hr : 0 < r := hsmall.1
  subst hk
  have hball := GC.LongTime.Ch11.isParabolicallyRmControlledBall_of_seed_C11Q hsmall
  have hτT : (τ : ℝ) ≤ T := h2
  have haτ : (aSeed : ℝ) ≤ τ := h1
  have hTτ : (T : ℝ) - τ ≤ r ^ 2 := by linarith
  have hv0 : 0 ≤ Real.sqrt ((T : ℝ) - τ) := Real.sqrt_nonneg _
  have hv2 : Real.sqrt ((T : ℝ) - τ) ^ 2 = (T : ℝ) - τ := Real.sq_sqrt (sub_nonneg.2 hτT)
  have hvr : Real.sqrt ((T : ℝ) - τ) ≤ r :=
    (Real.sqrt_le_sqrt hTτ).trans_eq (Real.sqrt_sq hr.le)
  have hclockτ : (τ : ℝ) = (T : ℝ) - Real.sqrt ((T : ℝ) - τ) ^ 2 := by
    rw [hv2]
    ring
  have hdist : Real.exp (2 * (3 / r ^ 2) * Real.sqrt ((T : ℝ) - τ) ^ 2) ≤ Real.exp 3 ^ 2 := by
    have hr2 : 0 < r ^ 2 := by positivity
    have hle : 2 * (3 / r ^ 2) * Real.sqrt ((T : ℝ) - τ) ^ 2 ≤ 3 + 3 := by
      rw [hv2]
      have hq : ((T : ℝ) - τ) / r ^ 2 ≤ 1 := (div_le_one hr2).2 hTτ
      calc 2 * (3 / r ^ 2) * ((T : ℝ) - τ) = 6 * (((T : ℝ) - τ) / r ^ 2) := by ring
        _ ≤ 6 * 1 := by gcongr
        _ = 3 + 3 := by norm_num
    calc Real.exp (2 * (3 / r ^ 2) * Real.sqrt ((T : ℝ) - τ) ^ 2) ≤ Real.exp (3 + 3) :=
          Real.exp_le_exp.2 hle
      _ = Real.exp 3 ^ 2 := by rw [Real.exp_add, sq]
  have he3 : Real.exp 3 < 25 := by
    have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [h3]
    calc Real.exp 1 ^ 3 < 2.7182818286 ^ 3 := by
          gcongr
          exact Real.exp_one_lt_d9
      _ < 25 := by norm_num
  have hmargin : r / 50 < (r / 2) / Real.exp 3 := by
    rw [lt_div_iff₀ (Real.exp_pos 3)]
    nlinarith
  have hcov := H.exists_terminal_preimage_of_past_seed_ball_C11Q T τ h2 p r
    (Real.sqrt ((T : ℝ) - τ)) hball hv0 hvr hclockτ
    (seedTrace.restrictFirst (H.activeStage_mono h1) (H.activeStage_mono h2)) (r / 50)
    (r / 2) (Real.exp 3) (by positivity) (by linarith) (Real.exp_pos 3) hdist hmargin
  obtain ⟨b', hb'τ, -, hcov⟩ := hcov
  have hz' : riemannianEDistOf
      (H.stageMetric (H.activeStage τ) ((T : ℝ) - Real.sqrt ((T : ℝ) - τ) ^ 2))
      ((seedTrace.restrictFirst (H.activeStage_mono h1) (H.activeStage_mono h2)).point
        (H.activeStage τ) le_rfl (H.activeStage_mono h2)) z < ENNReal.ofReal (r / 50) := by
    rw [← hclockτ]
    exact hz
  obtain ⟨x', -, A, hA, hApt⟩ := hcov z hz'
  have hb := hA.1 τ hb'τ h2
  rw [hApt] at hb
  exact sqrt_le_one_div_sq_of_pow_four_mul_le_one_C11G hr (normSq0S_nonneg _ _ _ _) hb

/-! ## 单 history 生产：DIST `hRm` / `hRic` -/

/-- **DIST `hRm` 的生产（`_C11G`）**：末 stage 窗口 `(s − θ/Q, s)`；种子端 K0（`ℓ ≤ r/50`、
`r⁻² ≤ K`）；`x` 端 `ℓ`-球标量 `≤ C Q`（BCAD 形）+ pinching（`Q (s − θ/Q) ≥ 1`、
`2√3(C/2 + max C (2e⁴)) Q ≤ K`）⇒ `hsmooth_of_rmNorm_le_C11D` 的 `hRm`。 -/
theorem hRm_of_seed_pinching_C11G (H : ObservedHistory.{u})
    {T aSeed s : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ T) (hsT : s ≤ T) (has : aSeed ≤ s)
    {p : (H.stageAt T).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature H T p r)
    (hclock : (aSeed : ℝ) = (T : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (y : (H.stageAt s).Carrier) {Q θ Rad ℓ K C a₀ : ℝ}
    (hwin : (aSeed : ℝ) ≤ (s : ℝ) - θ / Q) (hℓr : ℓ ≤ r / 50) (hKr : 1 / r ^ 2 ≤ K)
    (hQ : 0 < Q) (hlate : 1 ≤ Q * ((s : ℝ) - θ / Q)) (ha₀ : 0 ≤ a₀) (hC : 0 ≤ C)
    (hKC : 2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)) * Q ≤ K)
    (hpin : ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a₀ + t) x)
    (hscal : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ t : ℝ, (s : ℝ) - θ / Q < t → H.time (H.activeStage s) < t → t < s →
      ∀ z : (H.stageAt s).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage s) t) x z < ENNReal.ofReal ℓ →
        metricScalarAt (H.stageMetric (H.activeStage s) t) z ≤ C * Q) :
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ t : ℝ, (s : ℝ) - θ / Q < t → H.time (H.activeStage s) < t → t < s →
      ∀ z : (H.stageAt s).Carrier,
        (riemannianEDistOf (H.stageMetric (H.activeStage s) t)
            (seedTrace.point (H.activeStage s) (H.activeStage_mono has)
              (H.activeStage_mono hsT)) z < ENNReal.ofReal ℓ ∨
          riemannianEDistOf (H.stageMetric (H.activeStage s) t) x z < ENNReal.ofReal ℓ) →
        Real.sqrt (normSq0S (H.stageMetric (H.activeStage s) t) z 4
          (metricRm04At (H.stageMetric (H.activeStage s) t) z)) ≤ K := by
  intro x hx t h1 h2 h3 z hz
  have hsT' : (s : ℝ) ≤ T := hsT
  have ht0 : 0 ≤ t := (H.time_nonneg _).trans h2.le
  have hsw : 0 < (s : ℝ) - θ / Q := by
    by_contra hneg
    have hle := not_lt.mp hneg
    nlinarith
  let τ : Icc (0 : ℝ) H.horizon := ⟨t, ht0, h3.le.trans s.2.2⟩
  have hk : H.activeStage τ = H.activeStage s := H.activeStage_eq_of_time_le_C11G τ s h2.le h3.le
  rcases hz with hz | hz
  · have hzr : riemannianEDistOf (H.stageMetric (H.activeStage s) τ)
        (seedTrace.point (H.activeStage s) (H.activeStage_mono has) (H.activeStage_mono hsT)) z <
          ENNReal.ofReal (r / 50) :=
      hz.trans_le (ENNReal.ofReal_le_ofReal hℓr)
    have h : Real.sqrt (normSq0S (H.stageMetric (H.activeStage s) t) z 4
        (metricRm04At (H.stageMetric (H.activeStage s) t) z)) ≤ 1 / r ^ 2 :=
      H.seed_rmNorm_le_of_smallParabolic_C11G haT hsmall hclock seedTrace τ
        (by change (aSeed : ℝ) ≤ t; linarith) (by change t ≤ (T : ℝ); linarith)
        (H.activeStage s) hk _ _ z hzr
    exact h.trans hKr
  · have hfix : InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage s) t) (a₀ + t) z :=
      H.inFixedHI_stage_C11G hpin τ (H.activeStage s) hk z
    have hQt : 1 ≤ Q * t := by nlinarith
    exact (sqrt_rmNormSq_le_of_HI_scalar_C11G _ z ha₀ (by linarith) hQ hQt hC hfix
      (hscal x hx t h1 h2 h3 z hz)).trans hKC

/-- **DIST `hRic` 的生产（`_C11G`）**：event stage `e⁻` 上 `(max(v, time e⁻), time e⁺)` 内：种子 trace 点
的 `ℓ`-球由 K0（`ℓ ≤ r/50`、`r⁻² ≤ K`）、`x` 的 trace 点的 `ℓ`-球由标量 `≤ C Q` + pinching 给 `|Rm| ≤ K`；
`K ℓ² ≤ 1` ⇒ `Ric ≤ 3K g ≤ (3/ℓ²) g`（`hevent_of_records_C11D` 的 `hRic`）。 -/
theorem hRic_of_seed_pinching_C11G (H : ObservedHistory.{u})
    {T aSeed s : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ T)
    {p : (H.stageAt T).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature H T p r)
    (hclock : (aSeed : ℝ) = (T : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (y : (H.stageAt s).Carrier) {Q θ Rad ℓ K C a₀ : ℝ}
    (hℓ : 0 < ℓ) (hKℓ : K * ℓ ^ 2 ≤ 1) (hℓr : ℓ ≤ r / 50) (hKr : 1 / r ^ 2 ≤ K)
    (hQ : 0 < Q) (hlate : 1 ≤ Q * ((s : ℝ) - θ / Q)) (ha₀ : 0 ≤ a₀) (hC : 0 ≤ C)
    (hKC : 2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)) * Q ≤ K)
    (hpin : ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a₀ + t) x)
    (hscal : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : aSeed ≤ v) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
      ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s) (H.activeStage_mono hvs) x,
      ∀ (e : Fin H.eventCount) (h3 : H.activeStage v ≤ e.castSucc)
        (h4 : e.succ ≤ H.activeStage s) (t' : ℝ),
        (v : ℝ) < t' → H.time e.castSucc < t' → t' < H.time e.succ →
      ∀ z : (H.stage e.castSucc).Carrier,
        riemannianEDistOf (H.stageMetric e.castSucc t')
            (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) z < ENNReal.ofReal ℓ →
        metricScalarAt (H.stageMetric e.castSucc t') z ≤ C * Q) :
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : aSeed ≤ v) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
      ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s) (H.activeStage_mono hvs) x,
      ∀ (e : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ e.castSucc)
        (h2 : e.succ ≤ H.activeStage T) (h3 : H.activeStage v ≤ e.castSucc)
        (h4 : e.succ ≤ H.activeStage s) (t' : ℝ),
        (v : ℝ) < t' → H.time e.castSucc < t' → t' < H.time e.succ →
      ∀ z : (H.stage e.castSucc).Carrier, ∀ ξ : TangentSpace ThreeModel z,
        (riemannianEDistOf (H.stageMetric e.castSucc t')
            (seedTrace.point e.castSucc h1 (e.castSucc_lt_succ.le.trans h2)) z <
            ENNReal.ofReal ℓ ∨
          riemannianEDistOf (H.stageMetric e.castSucc t')
            (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) z < ENNReal.ofReal ℓ) →
        ricciTensor (H.stageMetric e.castSucc t') z ξ ξ ≤
          (3 / ℓ ^ 2) * (H.stageMetric e.castSucc t').inner z ξ ξ := by
  intro x hx v hav hvs hθv tr e h1 h2 h3 h4 t' ht1 ht2 ht3 z ξ hz
  have hav' : (aSeed : ℝ) ≤ v := hav
  have hsw : 0 < (s : ℝ) - θ / Q := by
    by_contra hneg
    have hle := not_lt.mp hneg
    nlinarith
  have ht0 : 0 ≤ t' := (H.time_nonneg _).trans ht2.le
  have hτT : t' ≤ (T : ℝ) :=
    ht3.le.trans ((H.time_strictMono.monotone h2).trans (H.activeStage_time_le T))
  let τ : Icc (0 : ℝ) H.horizon := ⟨t', ht0, hτT.trans T.2.2⟩
  have hk : H.activeStage τ = e.castSucc := H.activeStage_eq_castSucc_C11G e τ ht2.le ht3
  have hK : Real.sqrt (normSq0S (H.stageMetric e.castSucc t') z 4
      (metricRm04At (H.stageMetric e.castSucc t') z)) ≤ K := by
    rcases hz with hz | hz
    · have hzr : riemannianEDistOf (H.stageMetric e.castSucc τ)
          (seedTrace.point e.castSucc h1 (e.castSucc_lt_succ.le.trans h2)) z <
            ENNReal.ofReal (r / 50) :=
        hz.trans_le (ENNReal.ofReal_le_ofReal hℓr)
      have h : Real.sqrt (normSq0S (H.stageMetric e.castSucc t') z 4
          (metricRm04At (H.stageMetric e.castSucc t') z)) ≤ 1 / r ^ 2 :=
        H.seed_rmNorm_le_of_smallParabolic_C11G haT hsmall hclock seedTrace τ
          (by change (aSeed : ℝ) ≤ t'; linarith) (by change t' ≤ (T : ℝ); exact hτT)
          e.castSucc hk _ _ z hzr
      exact h.trans hKr
    · have hfix : InFixedHamiltonIveyRegion (H.stageMetric e.castSucc t') (a₀ + t') z :=
        H.inFixedHI_stage_C11G hpin τ e.castSucc hk z
      have hvt : (s : ℝ) - θ / Q < t' := lt_of_le_of_lt hθv ht1
      have hQt : 1 ≤ Q * t' := by nlinarith
      exact (sqrt_rmNormSq_le_of_HI_scalar_C11G _ z ha₀ (by linarith) hQ hQt hC hfix
        (hscal x hx v hav hvs hθv tr e h3 h4 t' ht1 ht2 ht3 z hz)).trans hKC
  have hg : 0 ≤ (H.stageMetric e.castSucc t').inner z ξ ξ := metric_inner_self_nonneg _ z ξ
  have hK' : K ≤ 1 / ℓ ^ 2 := by
    rw [le_div_iff₀ (pow_pos hℓ 2)]
    exact hKℓ
  calc ricciTensor (H.stageMetric e.castSucc t') z ξ ξ ≤
        3 * K * (H.stageMetric e.castSucc t').inner z ξ ξ :=
        ricciTensor_le_of_sqrt_rmNormSq_le_C11D _ z hK ξ
    _ ≤ (3 / ℓ ^ 2) * (H.stageMetric e.castSucc t').inner z ξ ξ := by
      apply mul_le_mul_of_nonneg_right _ hg
      calc 3 * K ≤ 3 * (1 / ℓ ^ 2) := by linarith
        _ = 3 / ℓ ^ 2 := by ring

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

/-! ## 序列层：DIST `hgeom` 的 (i) ∧ (iii) -/

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- 序列层数值：`R r² ≥ 2500 K`、`K ≥ 1` ⇒ `K^{-1/2}/√R ≤ r/50`、`r⁻² ≤ K R`、`K R (K^{-1/2}/√R)² = 1`。 -/
theorem seq_scale_bounds_C11G {K R r : ℝ} (hK1 : 1 ≤ K) (hR : 0 < R) (hr : 0 < r)
    (hX : 2500 * K ≤ R * r ^ 2) :
    1 / Real.sqrt K / Real.sqrt R ≤ r / 50 ∧ 1 / r ^ 2 ≤ K * R ∧
      K * R * (1 / Real.sqrt K / Real.sqrt R) ^ 2 ≤ 1 ∧ 1 / Real.sqrt K / Real.sqrt R ≤
        1 / Real.sqrt R := by
  have hKpos : 0 < K := by linarith
  have hsK : 1 ≤ Real.sqrt K := Real.one_le_sqrt.mpr hK1
  have hsq : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hℓ1 : 1 / Real.sqrt K ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact hsK
  have hX1 : 2500 ≤ R * r ^ 2 := by nlinarith
  have h4 : 1 / Real.sqrt K / Real.sqrt R ≤ 1 / Real.sqrt R :=
    div_le_div_of_nonneg_right hℓ1 hsq.le
  refine ⟨?_, ?_, ?_, h4⟩
  · have hy2 : (r * Real.sqrt R) ^ 2 = R * r ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hR.le]
      ring
    have hy0 : 0 ≤ r * Real.sqrt R := mul_nonneg hr.le hsq.le
    have h50 : 50 ≤ r * Real.sqrt R := by nlinarith
    refine h4.trans ?_
    rw [div_le_div_iff₀ hsq (by norm_num)]
    linarith
  · rw [div_le_iff₀ (by positivity)]
    have h1 : R * r ^ 2 ≤ K * (R * r ^ 2) := le_mul_of_one_le_left (by positivity) hK1
    nlinarith
  · have heq : K * R * (1 / Real.sqrt K / Real.sqrt R) ^ 2 = 1 := by
      rw [div_pow, div_pow, one_pow, Real.sq_sqrt hKpos.le, Real.sq_sqrt hR.le]
      field_simp
    exact heq.le

/-- **DIST `hgeom` 的 (i) ∧ (iii)（序列层，`_C11G`）**：K0 种子（`hasSmallParabolicCurvature`、
`aSeed = t − r²`、`R_n r_n² → ∞`）、(D2) 窗口 `hwin`、晚期 `hlate`、Pre841 形 pinching `hpin`、BCAD 形标量界
`hscal`（半径 `R_n^{-1/2}`、常数 `C_{D,T}`）⇒ 对每个 `D, T` 有 `ℓ, K`（`K ℓ² ≤ 1`）使 eventually
DIST `hrate_of_endpoint_bounds_C11D` 的 `hgeom` (i)（末 stage `|Rm| ≤ K R_n`）与 (iii)（event 段
`Ric ≤ 3R_n/ℓ² g`）成立。 -/
theorem hgeom_smooth_ric_of_K0_pinching_C11G (Hs : ℕ → ObservedHistory.{u})
    (t : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (p : ∀ n, ((Hs n).stageAt (t n)).Carrier)
    (aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (haT : ∀ n, aSeed n ≤ t n)
    (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
      ((Hs n).activeStage (t n)) ((Hs n).activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (hst : ∀ n, s n ≤ t n) (has : ∀ n, aSeed n ≤ s n)
    (y : ∀ n, ((Hs n).stageAt (s n)).Carrier) (R r : ℕ → ℝ) (hR : ∀ᶠ n in atTop, 0 < R n)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Hs n) (t n) (p n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2)
    (hX : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ (s n : ℝ) - T / R n)
    (hlate : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, 1 ≤ R n * ((s n : ℝ) - T / R n))
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ : Icc (0 : ℝ) (Hs n).horizon) (x : ((Hs n).stageAt τ).Carrier),
      InFixedHamiltonIveyRegion ((Hs n).stageMetric ((Hs n).activeStage τ) τ) (a₀ + τ) x)
    (hscal : ∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ τ : ℝ, (s n : ℝ) - T / R n < τ → (Hs n).time ((Hs n).activeStage (s n)) < τ →
          τ < s n →
        ∀ z : ((Hs n).stageAt (s n)).Carrier,
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) x z <
            ENNReal.ofReal (1 / Real.sqrt (R n)) →
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) z ≤ C * R n) ∧
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)) (t' : ℝ),
          (v : ℝ) < t' → (Hs n).time e.castSucc < t' → t' < (Hs n).time e.succ →
        ∀ z : ((Hs n).stage e.castSucc).Carrier,
          riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
              (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) z <
            ENNReal.ofReal (1 / Real.sqrt (R n)) →
          metricScalarAt ((Hs n).stageMetric e.castSucc t') z ≤ C * R n)) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∃ ℓ K : ℝ, 0 < ℓ ∧ K * ℓ ^ 2 ≤ 1 ∧ ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ τ : ℝ, (s n : ℝ) - T / R n < τ → (Hs n).time ((Hs n).activeStage (s n)) < τ →
          τ < s n →
        ∀ z : ((Hs n).stageAt (s n)).Carrier,
          (riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ)
              ((seedTrace n).point ((Hs n).activeStage (s n))
                ((Hs n).activeStage_mono (has n)) ((Hs n).activeStage_mono (hst n))) z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n)) ∨
            riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) x z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n))) →
          Real.sqrt (normSq0S ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) z 4
            (metricRm04At ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) z)) ≤ K * R n) ∧
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h1 : (Hs n).activeStage (aSeed n) ≤ e.castSucc)
          (h2 : e.succ ≤ (Hs n).activeStage (t n)) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)) (t' : ℝ),
          (v : ℝ) < t' → (Hs n).time e.castSucc < t' → t' < (Hs n).time e.succ →
        ∀ z : ((Hs n).stage e.castSucc).Carrier, ∀ ξ : TangentSpace ThreeModel z,
          (riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
              ((seedTrace n).point e.castSucc h1 (e.castSucc_lt_succ.le.trans h2)) z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n)) ∨
            riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
              (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n))) →
          ricciTensor ((Hs n).stageMetric e.castSucc t') z ξ ξ ≤
            (3 / (ℓ / Real.sqrt (R n)) ^ 2) *
              ((Hs n).stageMetric e.castSucc t').inner z ξ ξ) := by
  intro D T hD hT
  obtain ⟨C, hC, hev⟩ := hscal D T hD hT
  obtain ⟨K, hK1, hKp⟩ : ∃ K : ℝ, 1 ≤ K ∧
      2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)) ≤ K :=
    ⟨max 1 _, le_max_left _ _, le_max_right _ _⟩
  have hKpos : 0 < K := by linarith
  refine ⟨1 / Real.sqrt K, K, by positivity, ?_, ?_⟩
  · rw [div_pow, one_pow, Real.sq_sqrt hKpos.le]
    rw [mul_one_div_cancel hKpos.ne']
  filter_upwards [hev, hR, hwin T hT, hlate T hT, hX.eventually_ge_atTop (2500 * K)] with n hn
    hRn hwn hln hXn
  obtain ⟨hsc1, hsc2⟩ := hn
  obtain ⟨hℓr, hKr, hKℓ, hℓ1⟩ := seq_scale_bounds_C11G hK1 hRn (hsmall n).1 hXn
  have hKC : 2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)) * R n ≤ K * R n :=
    mul_le_mul_of_nonneg_right hKp hRn.le
  have hball : ENNReal.ofReal (1 / Real.sqrt K / Real.sqrt (R n)) ≤
      ENNReal.ofReal (1 / Real.sqrt (R n)) := ENNReal.ofReal_le_ofReal hℓ1
  refine ⟨?_, ?_⟩
  · exact (Hs n).hRm_of_seed_pinching_C11G (haT n) (hst n) (has n) (hsmall n) (hclock n)
      (seedTrace n) (y n) hwn hℓr hKr hRn hln ha₀ hC hKC (hpin n)
      (fun x hx τ h1 h2 h3 z hz => hsc1 x hx τ h1 h2 h3 z (hz.trans_le hball))
  · have hℓn : 0 < 1 / Real.sqrt K / Real.sqrt (R n) := by
      have := Real.sqrt_pos.2 hRn
      positivity
    exact (Hs n).hRic_of_seed_pinching_C11G (haT n) (hsmall n) (hclock n) (seedTrace n) (y n)
      hℓn hKℓ hℓr hKr hRn hln ha₀ hC hKC (hpin n)
      (fun x hx v hav hvs hθv tr e h3 h4 t' ht1 ht2 ht3 z hz =>
        hsc2 x hx v hav hvs hθv tr e h3 h4 t' ht1 ht2 ht3 z (hz.trans_le hball))

/-- **consumer（G2）**：单 history 的 `hRm` 生产喂 DIST `hsmooth_of_rmNorm_le_C11D`（速率 `8/ℓ`）。 -/
example (H : ObservedHistory.{u})
    {T aSeed s : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ T) (hsT : s ≤ T) (has : aSeed ≤ s)
    {p : (H.stageAt T).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature H T p r)
    (hclock : (aSeed : ℝ) = (T : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (y : (H.stageAt s).Carrier) {Q θ Rad ℓ K C a₀ : ℝ} (hℓ : 0 < ℓ) (hKℓ : K * ℓ ^ 2 ≤ 1)
    (hwin : (aSeed : ℝ) ≤ (s : ℝ) - θ / Q) (hℓr : ℓ ≤ r / 50) (hKr : 1 / r ^ 2 ≤ K)
    (hQ : 0 < Q) (hlate : 1 ≤ Q * ((s : ℝ) - θ / Q)) (ha₀ : 0 ≤ a₀) (hC : 0 ≤ C)
    (hKC : 2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)) * Q ≤ K)
    (hpin : ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a₀ + t) x)
    (hscal : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ t : ℝ, (s : ℝ) - θ / Q < t → H.time (H.activeStage s) < t → t < s →
      ∀ z : (H.stageAt s).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage s) t) x z < ENNReal.ofReal ℓ →
        metricScalarAt (H.stageMetric (H.activeStage s) t) z ≤ C * Q) :
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ t : ℝ, (s : ℝ) - θ / Q ≤ t → H.time (H.activeStage s) ≤ t → t ≤ s →
      riemannianEDistOf (H.stageMetric (H.activeStage s) t)
          (seedTrace.point (H.activeStage s) (H.activeStage_mono has) (H.activeStage_mono hsT))
          x ≤
        riemannianEDistOf (H.stageMetric (H.activeStage s) s)
            (seedTrace.point (H.activeStage s) (H.activeStage_mono has) (H.activeStage_mono hsT))
            x +
          ENNReal.ofReal ((8 / ℓ) * ((s : ℝ) - t)) :=
  H.hsmooth_of_rmNorm_le_C11D haT hsT has seedTrace y hℓ hKℓ
    (H.hRm_of_seed_pinching_C11G haT hsT has hsmall hclock seedTrace y hwin hℓr hKr hQ hlate ha₀
      hC hKC hpin hscal)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
