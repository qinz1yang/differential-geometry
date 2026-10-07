import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TracedBallSurvivalP6E
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HscalSameSlabP6M2
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm

/-!
# hscal 第二分量（跨 event）⇐ traced region（O-CH11-P6CE G2，后缀 `_P6E`）

(α) 球包含路线的跨 event 部分（G0 设计段见 `build-logs/resume/state-O-CH11-P6CE.md`）。
* `scalar_le_crossEvent_of_isTracedRegion_P6E`（单 history）：traced region `(ρ, θ, K)` 于 `(s, y)`、
  `x ∈ B_s(y, r)`、`r + e^{9Kθ} ℓ ≤ ρ`；`tr` = `x` 在 `[activeStage v, activeStage s]` 的 trace
  （`s − θ ≤ v`），event `e`（`activeStage v ≤ e⁻`、`e⁺ ≤ activeStage s`），
  `t' ∈ (max(v, time e⁻), time e⁺)`：
  `g_{e⁻}(t')`-球 `B(tr.point e⁻, ℓ)` 上 `R ≤ 9K`。= G1 `survives_of_traced_ball_P6E`（`j = e⁻`，
  `tr.restrictFirst`）+ `scalar_abs_le_rm`。
* **`hscal_crossEvent_of_traced_P6E`**（序列层，任意 filter `l`）：`ρ = 2D/√R`、`θ = T/R`、`K ↦ K R`、
  `r = D/√R`、`ℓ = ℓ₀/√R`，条件 `ℓ₀ e^{9KT} ≤ D`（与 P6ANCH2 G2b 同一个）⇒ P6PFX
  `EndpointPointwiseC11G2` / `EndpointRadiusC11G2` 的 `hscal` 第二分量逐字（`C = 9K`）。
* consumer **`exists_hscal_of_isTracedRegion_P6E`**：P6ANCH2 G2b 的
  `exists_hscal_of_isTracedRegion_of_crossEvent_P6M2`（第一分量 + 显式 `hcross`）的 `hcross` 由本文件给出
  ⇒ 完整 `hscal(D, T, ℓ₀)`（`C = max (9K) (9K)`），只剩 traced region `(2D, T, K)` 一个前提。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- `|Rm|² ≤ C²` ⇒ `R ≤ 9|C|`（三维，`scalar_abs_le_rm`；`_P6E`）。 -/
theorem scalar_le_of_normSq_le_P6E {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M) (x : M) {C : ℝ}
    (h : normSq0S g x 4 (metricRm04At g x) ≤ C ^ 2) : metricScalarAt g x ≤ 9 * |C| := by
  have hfin : Module.finrank ℝ (TangentSpace ThreeModel x) = 3 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    simp
  have h1 := scalar_abs_le_rm g x
  rw [hfin] at h1
  have h2 : Real.sqrt (normSq0S g x 4 (metricRm04At g x)) ≤ |C| := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h
  have h3 := le_abs_self (metricScalarAt g x)
  push_cast at h1
  nlinarith

/-- **hscal 第二分量，单 history（`_P6E`）**：traced region `(ρ, θ, K)` 于 `(s, y)`、`x ∈ B_s(y, r)`、
`r + e^{9Kθ} ℓ ≤ ρ`、`s − θ ≤ v`、`tr` = `x` 在 `[activeStage v, activeStage s]` 的 trace、event `e`
夹在其间、`t' ∈ (max(v, time e⁻), time e⁺)` ⇒ `B_{g_{e⁻}(t')}(tr.point e⁻, ℓ)` 上 `R ≤ 9K`。 -/
theorem scalar_le_crossEvent_of_isTracedRegion_P6E (H : ObservedHistory.{u})
    (s : Icc (0 : ℝ) H.horizon) (y : (H.stageAt s).Carrier) {ρ θ K r ℓ : ℝ}
    (htr : H.isTracedRegion s y ρ θ K) (hK : 0 ≤ K) (hℓ : 0 < ℓ)
    (hrad : r + Real.exp (9 * K * θ) * ℓ ≤ ρ)
    (x : (H.stageAt s).Carrier)
    (hx : x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y r)
    (v : Icc (0 : ℝ) H.horizon) (hvs : v ≤ s) (hvθ : (s : ℝ) - θ ≤ v)
    (tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s) (H.activeStage_mono hvs) x)
    (e : Fin H.eventCount) (h3 : H.activeStage v ≤ e.castSucc)
    (h4 : e.succ ≤ H.activeStage s) (t' : ℝ)
    (hvt : (v : ℝ) < t') (hlo : H.time e.castSucc < t') (hhi : t' < H.time e.succ)
    (z : (H.stage e.castSucc).Carrier)
    (hz : riemannianEDistOf (H.stageMetric e.castSucc t')
        (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) z < ENNReal.ofReal ℓ) :
    metricScalarAt (H.stageMetric e.castSucc t') z ≤ 9 * K := by
  have hjs : e.castSucc ≤ H.activeStage s := e.castSucc_lt_succ.le.trans h4
  have ht's : t' ≤ s := by
    have h1 := H.time_strictMono.monotone h4
    have h2 := H.activeStage_time_le s
    linarith
  have hdom : t' ∈ H.stageDomain e.castSucc := by
    simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, Set.mem_Ico]
    exact ⟨hlo.le, hhi⟩
  obtain ⟨-, -, -, -, -, hRm⟩ := H.survives_of_traced_ball_P6E s y htr hK hℓ hrad x hx
    e.castSucc hjs (tr.restrictFirst h3 hjs) t' (by linarith) ht's hdom z hz
  have h := scalar_le_of_normSq_le_P6E (H.stageMetric e.castSucc t') z hRm
  rwa [abs_of_nonneg hK] at h

/-- **hscal 第二分量 ⇐ traced region `(2D, T, K)`**（序列层，任意 filter `l`；`ℓ₀ e^{9KT} ≤ D`；
`C = 9K`）：P6PFX `EndpointPointwiseC11G2` / `EndpointRadiusC11G2` 的 `hscal` 第二分量逐字。 -/
theorem hscal_crossEvent_of_traced_P6E {Hs : ℕ → ObservedHistory.{u}}
    {s : ∀ n, Icc (0 : ℝ) (Hs n).horizon} {y : ∀ n, ((Hs n).stageAt (s n)).Carrier}
    {aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon} {R : ℕ → ℝ}
    {l : Filter ℕ} (hR : ∀ᶠ n in l, 0 < R n) {D T K ℓ₀ : ℝ} (hK : 0 ≤ K) (hℓ₀ : 0 < ℓ₀)
    (hℓD : ℓ₀ * Real.exp (9 * K * T) ≤ D)
    (htr : ∀ᶠ n in l, (Hs n).isTracedRegion (s n) (y n) (2 * D / Real.sqrt (R n)) (T / R n)
      (K * R n)) :
    ∀ᶠ n in l,
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
          metricScalarAt ((Hs n).stageMetric e.castSucc t') z ≤ 9 * K * R n := by
  filter_upwards [hR, htr] with n hRn hn
  intro x hx v _ hvs hvT tr e h3 h4 t' b1 b2 b3 z hz
  have hsq : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 hRn
  have hexp : Real.exp (9 * (K * R n) * (T / R n)) = Real.exp (9 * K * T) := by
    congr 1
    field_simp
  have hrad : D / Real.sqrt (R n) + Real.exp (9 * (K * R n) * (T / R n)) *
      (ℓ₀ / Real.sqrt (R n)) ≤ 2 * D / Real.sqrt (R n) := by
    rw [hexp, show Real.exp (9 * K * T) * (ℓ₀ / Real.sqrt (R n)) =
      ℓ₀ * Real.exp (9 * K * T) / Real.sqrt (R n) by ring, ← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hsq.le
  have h := scalar_le_crossEvent_of_isTracedRegion_P6E (Hs n) (s n) (y n) hn
    (mul_nonneg hK hRn.le) (div_pos hℓ₀ hsq) hrad x hx v hvs hvT tr e h3 h4 t' b1 b2 b3 z hz
  linarith

/-- **consumer：完整 `hscal(D, T, ℓ₀)` ⇐ traced region `(2D, T, K)`**：P6ANCH2 G2b
`exists_hscal_of_isTracedRegion_of_crossEvent_P6M2` 的 `hcross` 由 `hscal_crossEvent_of_traced_P6E`
给出；结论 = P6PFX G4b `exists_hgeom_pointwise_radius_C11G2` 的 `hscal` 前提整块（逐字）。 -/
theorem exists_hscal_of_isTracedRegion_P6E {Hs : ℕ → ObservedHistory.{u}}
    {s : ∀ n, Icc (0 : ℝ) (Hs n).horizon} {y : ∀ n, ((Hs n).stageAt (s n)).Carrier}
    {aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon} {R : ℕ → ℝ} (hR : ∀ᶠ n in atTop, 0 < R n)
    {D T K ℓ₀ : ℝ} (hK : 0 ≤ K) (hℓ₀ : 0 < ℓ₀) (hℓD : ℓ₀ * Real.exp (9 * K * T) ≤ D)
    (htr : ∀ᶠ n in atTop, (Hs n).isTracedRegion (s n) (y n) (2 * D / Real.sqrt (R n)) (T / R n)
      (K * R n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
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
          metricScalarAt ((Hs n).stageMetric e.castSucc t') z ≤ C * R n) :=
  exists_hscal_of_isTracedRegion_of_crossEvent_P6M2 (aSeed := aSeed) (C₂ := 9 * K) hR hK hℓ₀ hℓD
    htr (hscal_crossEvent_of_traced_P6E (aSeed := aSeed) hR hK hℓ₀ hℓD htr)

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
