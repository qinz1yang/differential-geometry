import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.EndpointPointwiseC11G2

/-!
# uniform `ε₀`：半径参数化 `hgeom` / 逐点 `hgeom` / 逐点相对 `hdist`（S-CH11-P6PFX G5，`_C11G2`）

`ε₀`（`exists_hprot_window_C11G` 给的端点保护精度）**与半径参数 `ℓ₀` 无关**：`ℓ₀` 只进 `hscal` 的球半径与
输出半径 `ℓ = ℓ₀/√K`（`K` 只依赖 `hscal` 的常数 `C_{D,T}`），不进任何阈值。所以 `∃ ε₀, ∀ ℓ₀ ∈ (0,1]` 的
重排成立：本文件把 `…_radius_C11G2` / `…_pointwise_…` / eventPrefix 层定理的量词序改成
`∃ ε₀ > 0, ∀ ℓ₀, 0 < ℓ₀ → ℓ₀ ≤ 1 → …`（证明同原，只是 `ℓ₀` 移到 `ε₀` 之后；消费端 (α) 路线里 `ℓ₀` 随
`(D, T, K)` 变，要的正是这个形）。（`hdist` / `hrate` 型定理的 `ε₀ := min ε₀' (1/2)` 同样与 `ℓ₀` 无关。）
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

/-- **uniform `ε₀`（G4 全 `(D,T)` 版）**：`∃ ε₀, ∀ ℓ₀ ∈ (0,1], …`；`ε₀` 与 `ℓ₀` 无关。 -/
theorem exists_hgeom_of_K0_pinching_radius_uniform_C11G2 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (ℓ₀ : ℝ), 0 < ℓ₀ → ℓ₀ ≤ 1 →
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
  intro ℓ₀ hℓ₀1 hℓ₀2 Hs t p aSeed haT seedTrace s hst has y R r hR hsmall hclock hX hwin hlate a₀
    ha₀ hpin
    hscal q T₀ records hcan hacc0 hm hDm hsepW D T hD hT
  obtain ⟨ℓ, K, hℓ, hKℓ, hev⟩ := hgeom_smooth_ric_of_K0_pinching_radius_C11G2 ℓ₀ ⟨hℓ₀1, hℓ₀2⟩ Hs t p
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
    exact ENNReal.ofReal_pos.mpr (div_pos hℓ₀1 (Real.sqrt_pos.2 hRn))
  exact ⟨hi, hP (Hs n) (haT n) (hsmall n) (hclock n) (seedTrace n) (y n) (records n) (hcan n)
    (hacc0 n) (hm n) (hDm n) hsep hslab, hiii⟩

/-- **uniform `ε₀`（逐点 `hgeom`）**：`∃ ε₀, ∀ ℓ₀ ∈ (0,1], ∀ D T, …`。 -/
theorem exists_hgeom_pointwise_radius_uniform_C11G2 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (ℓ₀ : ℝ), 0 < ℓ₀ → ℓ₀ ≤ 1 →
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
  intro ℓ₀ hℓ₀1 hℓ₀2 Hs t p aSeed haT seedTrace s hst has y R r hR hsmall hclock hX a₀ ha₀ hpin q
    T₀ records
    hcan hacc0 hm hDm D T _hD _hT hwin hlate hscal hsepW
  obtain ⟨C, hC, hevC⟩ := hscal
  obtain ⟨ℓ, K, hℓ, hKℓ, hev⟩ := hgeom_smooth_ric_pointwise_radius_C11G2 ℓ₀ ⟨hℓ₀1, hℓ₀2⟩ Hs t p
    aSeed
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
    exact ENNReal.ofReal_pos.mpr (div_pos hℓ₀1 (Real.sqrt_pos.2 hRn))
  exact ⟨hi, hP (Hs n) (haT n) (hsmall n) (hclock n) (seedTrace n) (y n) (records n) (hcan n)
    (hacc0 n) (hm n) (hDm n) hsep hslab, hiii⟩

/-- **uniform `ε₀`（端到端逐点相对 `hdist`）**：`∃ ε₀, ∀ ℓ₀ ∈ (0,1], ∀ D T, …`。 -/
theorem hdist_rel_pointwise_radius_uniform_C11G2 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (ℓ₀ : ℝ), 0 < ℓ₀ → ℓ₀ ≤ 1 →
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
  obtain ⟨ε₀, hε₀, hA⟩ := exists_hgeom_pointwise_radius_uniform_C11G2.{u}
  refine ⟨min ε₀ (1 / 2), lt_min hε₀ (by norm_num), ?_⟩
  intro ℓ₀ hℓ₀1 hℓ₀2 Hs t p aSeed haT seedTrace s hst has y R r L hR hL hsmall hclock hX a₀ ha₀
    hpin q T₀ records
    hcan hacc0 hm hDm D T hD hT hwin hlate hscal hsepW hT₀
  have hgeom := hA ℓ₀ hℓ₀1 hℓ₀2 Hs t p aSeed haT seedTrace s hst has y R r hR hsmall hclock hX ha₀
    hpin q T₀
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

/-- **consumer**：uniform ⇒ 原（`ℓ₀` 在 `∃ ε₀` 之前）形，`type_of%` 对齐。 -/
example (ℓ₀ : ℝ) (hℓ₀ : 0 < ℓ₀ ∧ ℓ₀ ≤ 1) :
    type_of% (exists_hgeom_of_K0_pinching_radius_C11G2.{u} ℓ₀ hℓ₀) := by
  obtain ⟨ε₀, hε₀, h⟩ := exists_hgeom_of_K0_pinching_radius_uniform_C11G2.{u}
  exact ⟨ε₀, hε₀, h ℓ₀ hℓ₀.1 hℓ₀.2⟩

/-- **consumer**：uniform ⇒ 原（`ℓ₀` 在 `∃ ε₀` 之前）形，`type_of%` 对齐。 -/
example (ℓ₀ : ℝ) (hℓ₀ : 0 < ℓ₀ ∧ ℓ₀ ≤ 1) :
    type_of% (exists_hgeom_pointwise_radius_C11G2.{u} ℓ₀ hℓ₀) := by
  obtain ⟨ε₀, hε₀, h⟩ := exists_hgeom_pointwise_radius_uniform_C11G2.{u}
  exact ⟨ε₀, hε₀, h ℓ₀ hℓ₀.1 hℓ₀.2⟩

/-- **consumer**：uniform ⇒ 原（`ℓ₀` 在 `∃ ε₀` 之前）形，`type_of%` 对齐。 -/
example (ℓ₀ : ℝ) (hℓ₀ : 0 < ℓ₀ ∧ ℓ₀ ≤ 1) :
    type_of% (hdist_rel_pointwise_radius_C11G2.{u} ℓ₀ hℓ₀) := by
  obtain ⟨ε₀, hε₀, h⟩ := hdist_rel_pointwise_radius_uniform_C11G2.{u}
  exact ⟨ε₀, hε₀, h ℓ₀ hℓ₀.1 hℓ₀.2⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
