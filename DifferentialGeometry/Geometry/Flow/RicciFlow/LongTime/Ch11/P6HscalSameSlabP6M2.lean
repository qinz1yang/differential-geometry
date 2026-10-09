import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BallContainmentSameSlab_P6L2

/-!
# hscal 第一分量（同 slab）⇐ traced region：序列层（O-CH11-P6ANCH2 G2b，后缀 `_P6M2`）

(α) 球包含路线的同 slab 部分（设计段见 state-O-CH11-P6ANCH2）。单 history 引理
`scalar_le_on_ball_of_isTracedRegion_sameSlab_P6L2`（first-exit 球包含 + 度量比较）在序列层取
`ρ = 2D/√R`、`θ = T/R`、`K ↦ K·R`、`r = D/√R`、`ℓ = ℓ₀/√R`；条件 `r + e^{9(KR)(T/R)} ℓ ≤ ρ`
⇔ `ℓ₀ · e^{9KT} ≤ D`。输出 = P6PFX G4b `exists_hgeom_pointwise_radius_C11G2` 的 `hscal` 第一分量
（`C = 9K`）逐字；filter 任取（条件形 driver 用 `map φ atTop`）。
consumer `exists_hscal_of_isTracedRegion_of_crossEvent_P6M2`：第一分量（本文件）+ 第二分量（跨 event，
G2c / O-CH11-P6CE 交付前显式 `hcross`）⇒ P6PFX `hscal` 前提整块逐字（`C = max (9K) C₂`）。
**`ℓ₀` 依赖 `(D, T, K)`**（`ℓ₀ ≤ D e^{−9KT}`）⇒ 接 P6PFX 逐点形时要求其 `ε₀` 不依赖 `ℓ₀`
（`∃ ε₀, ∀ ℓ₀` 重排；P6PFX 的证明里 `ε₀` 取自 `exists_hprot_window_C11G`，与 `ℓ₀` 无关）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- **hscal 第一分量 ⇐ traced region `(2D, T, K)`**（序列层，任意 filter `l`；`ℓ₀ e^{9KT} ≤ D`）。 -/
theorem hscal_sameSlab_of_isTracedRegion_P6M2 {Hs : ℕ → ObservedHistory.{u}}
    {s : ∀ n, Icc (0 : ℝ) (Hs n).horizon} {y : ∀ n, ((Hs n).stageAt (s n)).Carrier} {R : ℕ → ℝ}
    {l : Filter ℕ} (hR : ∀ᶠ n in l, 0 < R n) {D T K ℓ₀ : ℝ} (hK : 0 ≤ K) (hℓ₀ : 0 < ℓ₀)
    (hℓD : ℓ₀ * Real.exp (9 * K * T) ≤ D)
    (htr : ∀ᶠ n in l, (Hs n).isTracedRegion (s n) (y n) (2 * D / Real.sqrt (R n)) (T / R n)
      (K * R n)) :
    ∀ᶠ n in l,
    ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
        (D / Real.sqrt (R n)),
      ∀ τ : ℝ, (s n : ℝ) - T / R n < τ → (Hs n).time ((Hs n).activeStage (s n)) < τ →
        τ < s n →
      ∀ z : ((Hs n).stageAt (s n)).Carrier,
        riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) x z <
          ENNReal.ofReal (ℓ₀ / Real.sqrt (R n)) →
        metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) z ≤ 9 * K * R n := by
  filter_upwards [hR, htr] with n hRn hn
  intro x hx τ h1 h2 h3 z hz
  have hsq : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 hRn
  have hexp : Real.exp (9 * (K * R n) * (T / R n)) = Real.exp (9 * K * T) := by
    congr 1
    field_simp
  have hrad : D / Real.sqrt (R n) + Real.exp (9 * (K * R n) * (T / R n)) *
      (ℓ₀ / Real.sqrt (R n)) ≤ 2 * D / Real.sqrt (R n) := by
    rw [hexp, show Real.exp (9 * K * T) * (ℓ₀ / Real.sqrt (R n)) =
      ℓ₀ * Real.exp (9 * K * T) / Real.sqrt (R n) by ring, ← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hsq.le
  have h := scalar_le_on_ball_of_isTracedRegion_sameSlab_P6L2 (Hs n) (s n) (y n) hn
    (mul_nonneg hK hRn.le) (div_pos hℓ₀ hsq) hrad x hx τ h1 h2 h3 z hz
  linarith

/-- **consumer**：同 slab 分量（本文件）+ 跨 event 分量 `hcross`（G2c 交付前显式）⇒ P6PFX G4b
`exists_hgeom_pointwise_radius_C11G2` 的 `hscal` 前提整块（逐字，`C = max (9K) C₂`）。 -/
theorem exists_hscal_of_isTracedRegion_of_crossEvent_P6M2 {Hs : ℕ → ObservedHistory.{u}}
    {s : ∀ n, Icc (0 : ℝ) (Hs n).horizon} {y : ∀ n, ((Hs n).stageAt (s n)).Carrier}
    {aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon} {R : ℕ → ℝ} (hR : ∀ᶠ n in atTop, 0 < R n)
    {D T K ℓ₀ C₂ : ℝ} (hK : 0 ≤ K) (hℓ₀ : 0 < ℓ₀) (hℓD : ℓ₀ * Real.exp (9 * K * T) ≤ D)
    (htr : ∀ᶠ n in atTop, (Hs n).isTracedRegion (s n) (y n) (2 * D / Real.sqrt (R n)) (T / R n)
      (K * R n))
    (hcross : ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
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
          metricScalarAt ((Hs n).stageMetric e.castSucc t') z ≤ C₂ * R n) :
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
          metricScalarAt ((Hs n).stageMetric e.castSucc t') z ≤ C * R n)) := by
  refine ⟨max (9 * K) C₂, (by positivity : (0 : ℝ) ≤ 9 * K).trans (le_max_left _ _), ?_⟩
  filter_upwards [hscal_sameSlab_of_isTracedRegion_P6M2 hR hK hℓ₀ hℓD htr, hcross, hR]
    with n h1 h2 hRn
  refine ⟨fun x hx τ a1 a2 a3 z hz => (h1 x hx τ a1 a2 a3 z hz).trans ?_,
    fun x hx v hav hvs hvT tr e h3 h4 t' b1 b2 b3 z hz =>
      (h2 x hx v hav hvs hvT tr e h3 h4 t' b1 b2 b3 z hz).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) hRn.le
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) hRn.le

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
