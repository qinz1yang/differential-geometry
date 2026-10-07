import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.EndpointRadiusC11G2

/-!
# P6 几何输入：`(D,T)` 逐点形（S-CH11-P6PFX，后缀 `_C11G2`；P6ANCH2 G2 的 Dist 侧接口）

P6ANCH2 的条件形 driver 只在"已控 `(D,T)`"处给 `hscal`，所以 Dist 侧需要逐点形：

* `hgeom_smooth_ric_pointwise_radius_C11G2`：序列层 (i) ∧ (iii)，`hwin` / `hlate` / `hscal`（常数 `C`）
  只在给定 `(D,T)`。
* **`exists_hgeom_pointwise_radius_C11G2 ℓ₀`**：`∀ D T, 0<D → 0<T → hwin(T) → hlate(T) →
  (∃ C, hscal(D,T,C)) → hsepW(T) → ∃ ℓ K, 0<ℓ ∧ Kℓ²≤1 ∧ ∀ᶠ n, hgeom(D,T)`
  （`exists_hgeom_of_K0_pinching_radius_C11G2` 的逐点版；`ε₀` 绝对常数，数据前提（K0 / pinching /
  records）在 `D T` 之前）。
* `hrate_pointwise_C11G2`：`hrate_of_endpoint_bounds_C11D` 的逐点版（`hgeom(D,T)` ⇒ `∃ c, hrate(D,T)`）。
* **`hdist_rel_pointwise_radius_C11G2 ℓ₀`**（端到端）：上面两步 + `hdist_rel_of_stage_bounds_C11D` ⇒
  相对 `hdist(D,T)`（`L_n → ∞` eventually；结论 = P6M `false_of_selection_eventSlab_Kdata_P6M` 的
  `hdist` 在 `Hs` 层的逐字内层，`σ ↦ s`、`Tn ↦ t`）。`ε₀` 取 `min ε₀' (1/2)`，同时给
  `hacc : modelAccuracy ≤ 1/2`。
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

/-- **序列层 (i) ∧ (iii)，逐点 `(D,T)` 形（半径 `ℓ₀`，`_C11G2`）**：`hscal` / `hwin` / `hlate` 只在给定
`(D,T)`（常数 `C` 给定）处。 -/
theorem hgeom_smooth_ric_pointwise_radius_C11G2 (ℓ₀ : ℝ) (hℓ₀ : 0 < ℓ₀ ∧ ℓ₀ ≤ 1)
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
    {D T C : ℝ} (hC : 0 ≤ C)
    (hwin : ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ (s n : ℝ) - T / R n)
    (hlate : ∀ᶠ n in atTop, 1 ≤ R n * ((s n : ℝ) - T / R n))
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ : Icc (0 : ℝ) (Hs n).horizon) (x : ((Hs n).stageAt τ).Carrier),
      InFixedHamiltonIveyRegion ((Hs n).stageMetric ((Hs n).activeStage τ) τ) (a₀ + τ) x)
    (hscal : ∀ᶠ n in atTop,
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
    ∃ ℓ K : ℝ, 0 < ℓ ∧ K * ℓ ^ 2 ≤ 1 ∧ ∀ᶠ n in atTop,
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
  filter_upwards [hscal, hR, hwin, hlate, hX.eventually_ge_atTop (2500 * K)] with n hn
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


/-- **DIST `hgeom` 的生产，逐点 `(D,T)` 形（半径 `ℓ₀`，`_C11G2`）**：`exists_hgeom_of_K0_pinching_radius_C11G2`
的逐点版——`D T` 之后才出现 `hwin` / `hlate` / `hscal`（`∃ C`）/ `hsepW`（∀ C，只在该 `T`），结论是该 `(D,T)` 的
`∃ ℓ K, 0<ℓ ∧ Kℓ²≤1 ∧ ∀ᶠ n, (i) ∧ (ii) ∧ (iii)`。 -/
theorem exists_hgeom_pointwise_radius_C11G2 (ℓ₀ : ℝ) (hℓ₀ : 0 < ℓ₀ ∧ ℓ₀ ≤ 1) :
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
      ∀ {a₀ : ℝ}, 0 ≤ a₀ →
      (∀ n (τ : Icc (0 : ℝ) (Hs n).horizon) (x : ((Hs n).stageAt τ).Carrier),
        InFixedHamiltonIveyRegion ((Hs n).stageMetric ((Hs n).activeStage τ) τ) (a₀ + τ) x) →
    ∀ (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
      (records : ∀ n (e : Fin (Hs n).eventCount), T₀ n ≤ (Hs n).time e.succ →
        GeometricCutoffRecord (Hs n) e (q n)),
      (∀ n (e : Fin (Hs n).eventCount) (he : T₀ n ≤ (Hs n).time e.succ) b,
        ((records n e he).static b).hasCanonicalWindow) →
      (∀ n, (q n).modelAccuracy ≤ ε₀) → (∀ n, 2 ≤ (q n).modelOrder) →
      (∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius) →
    ∀ D T : ℝ, 0 < D → 0 < T →
      (∀ᶠ n in atTop, (aSeed n : ℝ) ≤ (s n : ℝ) - T / R n) →
      (∀ᶠ n in atTop, 1 ≤ R n * ((s n : ℝ) - T / R n)) →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
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
      (∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
        ∀ (e : Fin (Hs n).eventCount) (he : T₀ n ≤ (Hs n).time e.succ) b,
          (s n : ℝ) - T / R n < (Hs n).time e.succ →
          2 * max (3 / r n ^ 2) (C * R n) < ((records n e he).static b).neck.scale) →
    ∃ ℓ K : ℝ, 0 < ℓ ∧ K * ℓ ^ 2 ≤ 1 ∧ ∀ᶠ n in atTop,
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
  intro Hs t p aSeed haT seedTrace s hst has y R r hR hsmall hclock hX a₀ ha₀ hpin q T₀ records
    hcan hacc0 hm hDm D T _hD _hT hwin hlate hscal hsepW
  obtain ⟨C, hC, hevC⟩ := hscal
  obtain ⟨ℓ, K, hℓ, hKℓ, hev⟩ := hgeom_smooth_ric_pointwise_radius_C11G2 ℓ₀ hℓ₀ Hs t p aSeed
    haT seedTrace s hst has y R r hR hsmall hclock hX hC hwin hlate ha₀ hpin hevC
  refine ⟨ℓ, K, hℓ, hKℓ, ?_⟩
  filter_upwards [hev, hevC, hsepW C hC, hR] with n hn hnC hsep hRn
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

/-- **`hrate` 的生产，逐点 `(D,T)` 形（`_C11G2`）**：`hrate_of_endpoint_bounds_C11D` 的逐点版（`hgeom(D,T)` 与
`hT₀(T)` 给定 ⇒ `∃ c ≥ 0, hrate(D,T)`）。证明同原。 -/
theorem hrate_pointwise_C11G2 (Hs : ℕ → ObservedHistory.{u})
    (t : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (p : ∀ n, ((Hs n).stageAt (t n)).Carrier)
    (aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (haT : ∀ n, aSeed n ≤ t n)
    (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
      ((Hs n).activeStage (t n)) ((Hs n).activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (hst : ∀ n, s n ≤ t n) (has : ∀ n, aSeed n ≤ s n)
    (y : ∀ n, ((Hs n).stageAt (s n)).Carrier) (R : ℕ → ℝ) (hR : ∀ᶠ n in atTop, 0 < R n)
    (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
    (records : ∀ n (e : Fin (Hs n).eventCount), T₀ n ≤ (Hs n).time e.succ →
      GeometricCutoffRecord (Hs n) e (q n))
    (hOld : ∀ n (e : Fin (Hs n).eventCount), T₀ n ≤ (Hs n).time e.succ →
      ((Hs n).event e).old = ((Hs n).event e).transition.trace.retainedCore)
    (hcan : ∀ n (e : Fin (Hs n).eventCount) (he : T₀ n ≤ (Hs n).time e.succ) b,
      ((records n e he).static b).hasCanonicalWindow)
    (hacc : ∀ n, (q n).modelAccuracy ≤ 1 / 2)
    (hDm : ∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius)
    {D T : ℝ} (hT₀ : ∀ᶠ n in atTop, T₀ n ≤ (s n : ℝ) - T / R n)
    (hgeom : ∃ ℓ K : ℝ, 0 < ℓ ∧ K * ℓ ^ 2 ≤ 1 ∧ ∀ᶠ n in atTop,
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
              ((Hs n).stageMetric e.castSucc t').inner z ξ ξ)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ τ : ℝ, (s n : ℝ) - T / R n ≤ τ → (Hs n).time ((Hs n).activeStage (s n)) ≤ τ →
          τ ≤ s n →
        riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ)
            ((seedTrace n).point ((Hs n).activeStage (s n)) ((Hs n).activeStage_mono (has n))
              ((Hs n).activeStage_mono (hst n))) x ≤
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n))
              ((seedTrace n).point ((Hs n).activeStage (s n))
                ((Hs n).activeStage_mono (has n)) ((Hs n).activeStage_mono (hst n))) x +
            ENNReal.ofReal (c * Real.sqrt (R n) * ((s n : ℝ) - τ))) ∧
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h1 : (Hs n).activeStage (aSeed n) ≤ e.castSucc)
          (h2 : e.succ ≤ (Hs n).activeStage (t n)) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)) (τ : ℝ),
          (v : ℝ) ≤ τ → (Hs n).time e.castSucc ≤ τ → τ < (Hs n).time e.succ →
        riemannianEDistOf ((Hs n).stageMetric e.castSucc τ)
            ((seedTrace n).point e.castSucc h1 (e.castSucc_lt_succ.le.trans h2))
            (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) ≤
          riemannianEDistOf ((Hs n).stageMetric e.succ ((Hs n).time e.succ))
              ((seedTrace n).point e.succ (h1.trans e.castSucc_lt_succ.le) h2)
              (tr.point e.succ (h3.trans e.castSucc_lt_succ.le) h4) +
            ENNReal.ofReal (c * Real.sqrt (R n) * ((Hs n).time e.succ - τ))) := by
  obtain ⟨ℓ, K, hℓ, hKℓ, hev⟩ := hgeom
  refine ⟨8 / ℓ, div_nonneg (by norm_num) hℓ.le, ?_⟩
  filter_upwards [hev, hR, hT₀] with n hn hRn hT₀n
  obtain ⟨hRm, hprot, hRic⟩ := hn
  have hsq : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 hRn
  have hℓn : 0 < ℓ / Real.sqrt (R n) := div_pos hℓ hsq
  have hKn : K * R n * (ℓ / Real.sqrt (R n)) ^ 2 ≤ 1 := by
    have h : K * R n * (ℓ / Real.sqrt (R n)) ^ 2 = K * ℓ ^ 2 := by
      rw [div_pow, Real.sq_sqrt hRn.le]
      field_simp
    rw [h]
    exact hKℓ
  refine ⟨fun x hx τ h1 h2 h3 => ?_, fun x hx v hav hvs hθv tr e h1 h2 h3 h4 τ hτ1 hτ2 hτ3 => ?_⟩
  · have h := (Hs n).hsmooth_of_rmNorm_le_C11D (haT n) (hst n) (has n) (seedTrace n) (y n) hℓn
      hKn hRm x hx τ h1 h2 h3
    rwa [rate_scaled_eq_C11D] at h
  · have h := (Hs n).hevent_of_records_C11D (haT n) (seedTrace n) (y n) hℓn hT₀n (records n)
      (hOld n) (hcan n) (hacc n) (hDm n) hprot hRic x hx v hav hvs hθv tr e h1 h2 h3 h4 τ hτ1
      hτ2 hτ3
    rwa [rate_scaled_eq_C11D] at h

/-- **端到端相对 `hdist`，逐点 `(D,T)` 形（半径 `ℓ₀`，`_C11G2`）**：`exists_hgeom_pointwise_radius_C11G2` →
`hrate_pointwise_C11G2` → DIST `hdist_rel_of_stage_bounds_C11D`（`L_n → ∞`，数值条件 `D + cT ≤ L_n`
eventually）。结论是 P6M `false_of_selection_eventSlab_Kdata_P6M` 的 `hdist` 在 `Hs` 层的内层（`(D,T)` 给定，
`σ ↦ s`、`Tn ↦ t`、`Kh ↦ Hs`）。`ε₀` 取 `min ε₀' (1/2)`（`hacc : ≤ 1/2` 同时给）。 -/
theorem hdist_rel_pointwise_radius_C11G2 (ℓ₀ : ℝ) (hℓ₀ : 0 < ℓ₀ ∧ ℓ₀ ≤ 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (Hs : ℕ → ObservedHistory.{u})
      (t : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (p : ∀ n, ((Hs n).stageAt (t n)).Carrier)
      (aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (haT : ∀ n, aSeed n ≤ t n)
      (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
        ((Hs n).activeStage (t n)) ((Hs n).activeStage_mono (haT n)) (p n))
      (s : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (hst : ∀ n, s n ≤ t n) (has : ∀ n, aSeed n ≤ s n)
      (y : ∀ n, ((Hs n).stageAt (s n)).Carrier) (R r L : ℕ → ℝ), (∀ᶠ n in atTop, 0 < R n) →
      Tendsto L atTop atTop →
      (∀ n, GC.LongTime.hasSmallParabolicCurvature (Hs n) (t n) (p n) (r n)) →
      (∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      ∀ {a₀ : ℝ}, 0 ≤ a₀ →
      (∀ n (τ : Icc (0 : ℝ) (Hs n).horizon) (x : ((Hs n).stageAt τ).Carrier),
        InFixedHamiltonIveyRegion ((Hs n).stageMetric ((Hs n).activeStage τ) τ) (a₀ + τ) x) →
    ∀ (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
      (records : ∀ n (e : Fin (Hs n).eventCount), T₀ n ≤ (Hs n).time e.succ →
        GeometricCutoffRecord (Hs n) e (q n)),
      (∀ n (e : Fin (Hs n).eventCount) (he : T₀ n ≤ (Hs n).time e.succ) b,
        ((records n e he).static b).hasCanonicalWindow) →
      (∀ n, (q n).modelAccuracy ≤ ε₀) → (∀ n, 2 ≤ (q n).modelOrder) →
      (∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius) →
    ∀ D T : ℝ, 0 < D → 0 < T →
      (∀ᶠ n in atTop, (aSeed n : ℝ) ≤ (s n : ℝ) - T / R n) →
      (∀ᶠ n in atTop, 1 ≤ R n * ((s n : ℝ) - T / R n)) →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
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
      (∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
        ∀ (e : Fin (Hs n).eventCount) (he : T₀ n ≤ (Hs n).time e.succ) b,
          (s n : ℝ) - T / R n < (Hs n).time e.succ →
          2 * max (3 / r n ^ 2) (C * R n) < ((records n e he).static b).neck.scale) →
      (∀ᶠ n in atTop, T₀ n ≤ (s n : ℝ) - T / R n) →
    ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ s n),
        (s n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
            ((seedTrace n).point ((Hs n).activeStage v) ((Hs n).activeStage_mono hav)
              ((Hs n).activeStage_mono (hvs.trans (hst n))))
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n))
              ((seedTrace n).point ((Hs n).activeStage (s n)) ((Hs n).activeStage_mono (has n))
                ((Hs n).activeStage_mono (hst n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  obtain ⟨ε₀, hε₀, hA⟩ := exists_hgeom_pointwise_radius_C11G2.{u} ℓ₀ hℓ₀
  refine ⟨min ε₀ (1 / 2), lt_min hε₀ (by norm_num), ?_⟩
  intro Hs t p aSeed haT seedTrace s hst has y R r L hR hL hsmall hclock hX a₀ ha₀ hpin q T₀ records
    hcan hacc0 hm hDm D T hD hT hwin hlate hscal hsepW hT₀
  have hgeom := hA Hs t p aSeed haT seedTrace s hst has y R r hR hsmall hclock hX ha₀ hpin q T₀
    records hcan (fun n => (hacc0 n).trans (min_le_left _ _)) hm hDm D T hD hT hwin hlate hscal
    hsepW
  obtain ⟨c, hc, hev⟩ := hrate_pointwise_C11G2 Hs t p aSeed haT seedTrace s hst has y R hR q T₀
    records (fun n e he => (records n e he).old_eq_retained) hcan
    (fun n => (hacc0 n).trans (min_le_right _ _)) hDm hT₀ hgeom
  filter_upwards [hev, hR, hL.eventually_ge_atTop (D + c * T)] with n hn hRn hLn
  obtain ⟨hsm, hevt⟩ := hn
  have hsq : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 hRn
  have hΛ : 0 ≤ c * Real.sqrt (R n) := mul_nonneg hc hsq.le
  have hnum : D / Real.sqrt (R n) + c * Real.sqrt (R n) * (T / R n) ≤
      L n / Real.sqrt (R n) := by
    have h2 : c * Real.sqrt (R n) * (T / R n) = c * T / Real.sqrt (R n) := by
      have h := Real.sqrt_div_self' (x := R n)
      calc c * Real.sqrt (R n) * (T / R n) = c * T * (Real.sqrt (R n) / R n) := by ring
        _ = c * T * (1 / Real.sqrt (R n)) := by rw [h]
        _ = c * T / Real.sqrt (R n) := by ring
    rw [h2, ← add_div]
    exact div_le_div_of_nonneg_right hLn hsq.le
  exact (Hs n).hdist_rel_of_stage_bounds_C11D (haT n) (hst n) (has n) (seedTrace n) (y n) hΛ hnum
    hsm hevt

/-- **consumer**：逐点版 ⇒ 全 `(D,T)` 版（`exists_hgeom_of_K0_pinching_radius_C11G2`，类型 `type_of%`
对齐）：对每个 `(D,T)` 用逐点定理，`hwin T hT` / `hlate T hT` / `hscal D T hD hT` / `hsepW · · T hT`。 -/
example (ℓ₀ : ℝ) (hℓ₀ : 0 < ℓ₀ ∧ ℓ₀ ≤ 1) :
    type_of% (exists_hgeom_of_K0_pinching_radius_C11G2.{u} ℓ₀ hℓ₀) := by
  obtain ⟨ε₀, hε₀, hA⟩ := exists_hgeom_pointwise_radius_C11G2.{u} ℓ₀ hℓ₀
  refine ⟨ε₀, hε₀, ?_⟩
  intro Hs t p aSeed haT seedTrace s hst has y R r hR hsmall hclock hX hwin hlate a₀ ha₀ hpin hscal
    q T₀ records hcan hacc0 hm hDm hsepW D T hD hT
  exact hA Hs t p aSeed haT seedTrace s hst has y R r hR hsmall hclock hX ha₀ hpin q T₀ records
    hcan hacc0 hm hDm D T hD hT (hwin T hT) (hlate T hT) (hscal D T hD hT)
    (fun C hC => hsepW C hC T hT)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
