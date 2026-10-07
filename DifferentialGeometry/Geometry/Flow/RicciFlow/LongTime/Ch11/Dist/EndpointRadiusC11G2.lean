import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.EndpointAssemblyC11G

/-!
# P6 几何输入 G4：半径参数化的 `hgeom`（S-CH11-P6PFX G4，后缀 `_C11G2`）

P6GEO `exists_hgeom_of_K0_pinching_C11G` 的 BCAD 形标量界 `hscal` 的球半径写死为 `1/√R_n`；
P6 的局部传播（`scalar_le_on_ball_of_gradient_bound_P6L`）只给 `ℓ₀/√R_n`（`ℓ₀ ≤ 1` 小常数）。
本文件出**半径参数化变体**：

* `hgeom_smooth_ric_of_K0_pinching_radius_C11G2 ℓ₀`（序列层 (i) ∧ (iii)）：`hscal` 两分量的球半径
  `1/√R_n` 改为 `ℓ₀/√R_n`，其余前提 / 结论逐字不变。
* **`exists_hgeom_of_K0_pinching_radius_C11G2 ℓ₀ hℓ₀`**：同上 + 窗口 hprot，结论 = DIST
  `hrate_of_endpoint_bounds_C11D` 的整个 `hgeom`（形状与 `exists_hgeom_of_K0_pinching_C11G` 逐字相同）。

**换算（`ℓ₀` 只在两处出现）**：单 history 引理 `hRm_/hRic_of_seed_pinching_C11G` 本来就对任意球半径
`ℓ`（`ℓ ≤ r/50`）陈述，序列层只是选 `ℓ_out = 1/√K`、用 `hscal`（半径 `1/√R`）覆盖 `ℓ_out/√R` 球。
变体取 `ℓ_out = ℓ₀/√K`：`ℓ_out/√R ≤ ℓ₀/√R`（`√K ≥ 1`）⇒ 同一个 `hscal` 覆盖；
`K ℓ_out² = ℓ₀² ≤ 1`（**需要 `ℓ₀ ≤ 1`**）、`K R (ℓ_out/√R)² = ℓ₀² ≤ 1`；
`ℓ_out/√R ≤ 1/√K/√R ≤ r/50`（`R r² ≥ 2500 K`，同原）。**常数 `C_{D,T}`、`K` 的选取不依赖 `ℓ₀`**
（`K = max 1 (2√3 (C/2 + max C (2e⁴)))`）；`ℓ₀` 只进输出半径 `ℓ_out = ℓ₀/√K`。
窗口 hprot 的 `hslab` 取 `hscal` 第二分量在 trace 点自身（`z = x`，`riemannianEDistOf_self = 0 < ℓ₀/√R`）。
`ℓ₀ = 1` 恢复原定理（`exists_hgeom_of_K0_pinching_C11G`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **序列层 (i) ∧ (iii)（半径 `ℓ₀`，`_C11G2`）**：`hgeom_smooth_ric_of_K0_pinching_C11G` 的 `hscal`
球半径 `1/√R_n` 换成 `ℓ₀/√R_n`（`0 < ℓ₀ ≤ 1`）；结论 `ℓ = ℓ₀/√K`。 -/
theorem hgeom_smooth_ric_of_K0_pinching_radius_C11G2 (ℓ₀ : ℝ) (hℓ₀ : 0 < ℓ₀ ∧ ℓ₀ ≤ 1)
    (Hs : ℕ → ObservedHistory.{u})
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
            ENNReal.ofReal (ℓ₀ / Real.sqrt (R n)) →
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
            ENNReal.ofReal (ℓ₀ / Real.sqrt (R n)) →
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
  obtain ⟨hℓ₀pos, hℓ₀1⟩ := hℓ₀
  have hKpos : 0 < K := by linarith
  have hsK : 1 ≤ Real.sqrt K := Real.one_le_sqrt.mpr hK1
  have hsKpos : 0 < Real.sqrt K := by linarith
  have hℓK : ℓ₀ / Real.sqrt K ≤ ℓ₀ := div_le_self hℓ₀pos.le hsK
  refine ⟨ℓ₀ / Real.sqrt K, K, by positivity, ?_, ?_⟩
  · have heq : K * (ℓ₀ / Real.sqrt K) ^ 2 = ℓ₀ ^ 2 := by
      rw [div_pow, Real.sq_sqrt hKpos.le]
      field_simp
    rw [heq]
    exact pow_le_one₀ hℓ₀pos.le hℓ₀1
  filter_upwards [hev, hR, hwin T hT, hlate T hT, hX.eventually_ge_atTop (2500 * K)] with n hn
    hRn hwn hln hXn
  obtain ⟨hsc1, hsc2⟩ := hn
  obtain ⟨hℓr1, hKr, -, -⟩ := seq_scale_bounds_C11G hK1 hRn (hsmall n).1 hXn
  have hsq : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 hRn
  have hℓr : ℓ₀ / Real.sqrt K / Real.sqrt (R n) ≤ r n / 50 :=
    le_trans (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hℓ₀1 hsKpos.le) hsq.le) hℓr1
  have hKℓ : K * R n * (ℓ₀ / Real.sqrt K / Real.sqrt (R n)) ^ 2 ≤ 1 := by
    have heq : K * R n * (ℓ₀ / Real.sqrt K / Real.sqrt (R n)) ^ 2 = ℓ₀ ^ 2 := by
      rw [div_pow, div_pow, Real.sq_sqrt hKpos.le, Real.sq_sqrt hRn.le]
      field_simp
    rw [heq]
    exact pow_le_one₀ hℓ₀pos.le hℓ₀1
  have hKC : 2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)) * R n ≤ K * R n :=
    mul_le_mul_of_nonneg_right hKp hRn.le
  have hball : ENNReal.ofReal (ℓ₀ / Real.sqrt K / Real.sqrt (R n)) ≤
      ENNReal.ofReal (ℓ₀ / Real.sqrt (R n)) :=
    ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hℓK hsq.le)
  refine ⟨?_, ?_⟩
  · exact (Hs n).hRm_of_seed_pinching_C11G (haT n) (hst n) (has n) (hsmall n) (hclock n)
      (seedTrace n) (y n) hwn hℓr hKr hRn hln ha₀ hC hKC (hpin n)
      (fun x hx τ h1 h2 h3 z hz => hsc1 x hx τ h1 h2 h3 z (hz.trans_le hball))
  · have hℓn : 0 < ℓ₀ / Real.sqrt K / Real.sqrt (R n) := by positivity
    exact (Hs n).hRic_of_seed_pinching_C11G (haT n) (hsmall n) (hclock n) (seedTrace n) (y n)
      hℓn hKℓ hℓr hKr hRn hln ha₀ hC hKC (hpin n)
      (fun x hx v hav hvs hθv tr e h3 h4 t' ht1 ht2 ht3 z hz =>
        hsc2 x hx v hav hvs hθv tr e h3 h4 t' ht1 ht2 ht3 z (hz.trans_le hball))


/-- **DIST `hgeom` 的生产（半径 `ℓ₀`，`_C11G2`）**：`exists_hgeom_of_K0_pinching_C11G` 的 `hscal`
球半径 `1/√R_n` 换成 `ℓ₀/√R_n`（`0 < ℓ₀ ≤ 1`），其余逐字；结论逐字（`∃ ε₀`，`∃ ℓ K`）。 -/
theorem exists_hgeom_of_K0_pinching_radius_C11G2 (ℓ₀ : ℝ) (hℓ₀ : 0 < ℓ₀ ∧ ℓ₀ ≤ 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (Hs : ℕ → ObservedHistory.{u})
      (t : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (p : ∀ n, ((Hs n).stageAt (t n)).Carrier)
      (aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (haT : ∀ n, aSeed n ≤ t n)
      (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
        ((Hs n).activeStage (t n)) ((Hs n).activeStage_mono (haT n)) (p n))
      (s : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (hst : ∀ n, s n ≤ t n) (has : ∀ n, aSeed n ≤ s n)
      (y : ∀ n, ((Hs n).stageAt (s n)).Carrier) (R r : ℕ → ℝ), (∀ᶠ n in atTop, 0 < R n) →
      (∀ n, GC.LongTime.hasSmallParabolicCurvature (Hs n) (t n) (p n) (r n)) →
      (∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ (s n : ℝ) - T / R n) →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, 1 ≤ R n * ((s n : ℝ) - T / R n)) →
      ∀ {a₀ : ℝ}, 0 ≤ a₀ →
      (∀ n (τ : Icc (0 : ℝ) (Hs n).horizon) (x : ((Hs n).stageAt τ).Carrier),
        InFixedHamiltonIveyRegion ((Hs n).stageMetric ((Hs n).activeStage τ) τ) (a₀ + τ) x) →
      (∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
        (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
            (D / Real.sqrt (R n)),
          ∀ τ : ℝ, (s n : ℝ) - T / R n < τ → (Hs n).time ((Hs n).activeStage (s n)) < τ →
            τ < s n →
          ∀ z : ((Hs n).stageAt (s n)).Carrier,
            riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) x z <
              ENNReal.ofReal (ℓ₀ / Real.sqrt (R n)) →
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
              ENNReal.ofReal (ℓ₀ / Real.sqrt (R n)) →
            metricScalarAt ((Hs n).stageMetric e.castSucc t') z ≤ C * R n)) →
    ∀ (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
      (records : ∀ n (e : Fin (Hs n).eventCount), T₀ n ≤ (Hs n).time e.succ →
        GeometricCutoffRecord (Hs n) e (q n)),
      (∀ n (e : Fin (Hs n).eventCount) (he : T₀ n ≤ (Hs n).time e.succ) b,
        ((records n e he).static b).hasCanonicalWindow) →
      (∀ n, (q n).modelAccuracy ≤ ε₀) → (∀ n, 2 ≤ (q n).modelOrder) →
      (∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius) →
      (∀ C : ℝ, 0 ≤ C → ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
        ∀ (e : Fin (Hs n).eventCount) (he : T₀ n ≤ (Hs n).time e.succ) b,
          (s n : ℝ) - T / R n < (Hs n).time e.succ →
          2 * max (3 / r n ^ 2) (C * R n) < ((records n e he).static b).neck.scale) →
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
          (h4 : e.succ ≤ (Hs n).activeStage (s n)), (v : ℝ) < (Hs n).time e.succ →
        ∀ (he : T₀ n ≤ (Hs n).time e.succ) b,
          (seedTrace n).point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
              ((records n e he).static b).window ''
                {z : standardCapWindow (q n).modelRadius |
                  ‖z.val‖ ≤ StandardCap.transitionEnd + 10} ∧
            tr.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
              ((records n e he).static b).window ''
                {z : standardCapWindow (q n).modelRadius |
                  ‖z.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
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
  obtain ⟨ε₀, hε₀, hP⟩ := ObservedHistory.exists_hprot_window_C11G.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro Hs t p aSeed haT seedTrace s hst has y R r hR hsmall hclock hX hwin hlate a₀ ha₀ hpin
    hscal q T₀ records hcan hacc0 hm hDm hsepW D T hD hT
  obtain ⟨ℓ, K, hℓ, hKℓ, hev⟩ := hgeom_smooth_ric_of_K0_pinching_radius_C11G2 ℓ₀ hℓ₀ Hs t p
    aSeed haT seedTrace s hst has y R r hR hsmall hclock hX hwin hlate ha₀ hpin hscal D T hD hT
  obtain ⟨C, hC, hevC⟩ := hscal D T hD hT
  refine ⟨ℓ, K, hℓ, hKℓ, ?_⟩
  filter_upwards [hev, hevC, hsepW C hC T hT, hR] with n hn hnC hsep hRn
  obtain ⟨hi, hiii⟩ := hn
  have hslab : ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n))
      (y n) (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
        (s n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
        ((Hs n).activeStage_mono hvs) x,
      ∀ (e : Fin (Hs n).eventCount) (h3 : (Hs n).activeStage v ≤ e.castSucc)
        (h4 : e.succ ≤ (Hs n).activeStage (s n)) (t' : ℝ),
        (v : ℝ) < t' → (Hs n).time e.castSucc < t' → t' < (Hs n).time e.succ →
        metricScalarAt ((Hs n).stageMetric e.castSucc t')
          (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) ≤ C * R n := by
    intro x hx v hav hvs hθv tr e h3 h4 t' ht1 ht2 ht3
    refine hnC.2 x hx v hav hvs hθv tr e h3 h4 t' ht1 ht2 ht3 _ ?_
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (div_pos hℓ₀.1 (Real.sqrt_pos.2 hRn))
  exact ⟨hi, hP (Hs n) (haT n) (hsmall n) (hclock n) (seedTrace n) (y n) (records n) (hcan n)
    (hacc0 n) (hm n) (hDm n) hsep hslab, hiii⟩

/-- **consumer（G4）**：`ℓ₀ = 1` 恢复 P6GEO 原定理 `exists_hgeom_of_K0_pinching_C11G`（陈述逐字相同，
`type_of%` 对齐）——变体是严格推广。 -/
example : type_of% exists_hgeom_of_K0_pinching_C11G.{u} :=
  exists_hgeom_of_K0_pinching_radius_C11G2 1 ⟨one_pos, le_rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
