import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HscalSameSlabP6M2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AnchorP6AN
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionMaximalDepth

/-!
# hgap4 OPEN 合取 J14（slab BCBD）⇐ hPN 中心的 driver 输出（J8KAPPA G4，`_P6HA`）

hPN 中心 `(σ, y)` 在 slab 内部，maximal-depth driver 直接在 `(Kh, σ, y, R)` 上跑（不需要 R4 的 crossing 平移）。
driver 输出形 `hDext : ∀ φ StrictMono, ∃ ψ StrictMono, ∀ T > 0, DepthExtendable Kh σ y R (φ ∘ ψ) T`
（树内 producer：DEPTH4C2 `exists_subseq_forall_depthExtendable_of_hPN_anyPos_local_P6DP4C2`，对 hPN 数据的
任意子列重索引适用）⇒ J14（KT2c `hOpenJ` / `hOpen8J` 的 J14 合取逐字，生成器从
`P6GapProducersLocP6KT2c.lean` l.343–357 抽取并 assert）：
* 深度 `T`、半径 `A := 2D` 的 traced region（`K·R`）⇒ 同 slab 窗 `(σ − T/R, σ)` 内 `B_s(x, ℓ₀/√R)` 上
  `R ≤ 9K·R`（`hscal_sameSlab_of_isTracedRegion_P6M2`，`ℓ₀ := D e^{−9KT}`）；
* `C := max (max (9K) ℓ₀⁻²) 1` ⇒ `1/√(C R) ≤ ℓ₀/√R`；
* 子列 → `∀ᶠ n`：`exists_const_eventually_of_subseq_P6AN`。
J14 的 footprint 前提（`d_s(seed, x) ≤ …`）不用。**`j14_of_depthExt_P6HA`**（PROVED ⇐ `hDext`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- **J14 ⇐ hPN 中心 driver 输出（`_P6HA`，PROVED ⇐ `hDext`）**：结论 = KT2c J14 合取逐字。 -/
theorem j14_of_depthExt_P6HA {Kh : ℕ → ObservedHistory.{u}}
    {Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon} {haT : ∀ n, aSeed n ≤ Tn n}
    {pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier}
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
    (R : ℕ → ℝ) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n) (L : ℕ → ℝ)
    (hRpos : ∀ n, 0 < R n)
    (hDext : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ T : ℝ, 0 < T → DepthExtendable Kh σ y R (φ ∘ ψ) T) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - T / R n < s → s < σ n → (Kh n).time ((Kh n).activeStage (σ n)) < s →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) →
          ∀ z : ((Kh n).stageAt (σ n)).Carrier,
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x z <
                ENNReal.ofReal (1 / Real.sqrt (C * R n)) →
              metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) z ≤ C * R n := by
  intro D T hD hT
  refine exists_const_eventually_of_subseq_P6AN (P := fun n C =>
            ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
              (D / Real.sqrt (R n)),
          ∀ s : ℝ, (σ n : ℝ) - T / R n < s → s < σ n → (Kh n).time ((Kh n).activeStage (σ n)) < s →
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) x ≤
              riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                  ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                    ((Kh n).activeStage_mono (hsT n))) (y n) +
                ENNReal.ofReal (L n / Real.sqrt (R n)) →
            ∀ z : ((Kh n).stageAt (σ n)).Carrier,
              riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x z <
                  ENNReal.ofReal (1 / Real.sqrt (C * R n)) →
                metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) z ≤ C * R n) ?_
  intro φ hφ
  obtain ⟨ψ, hψ, hdx⟩ := hDext φ hφ
  obtain ⟨K, hK0, htr⟩ := hdx T hT (2 * D) (by positivity)
  set ℓ₀ : ℝ := D * Real.exp (-(9 * K * T)) with hℓ₀def
  have hℓ₀ : 0 < ℓ₀ := by positivity
  have hℓD : ℓ₀ * Real.exp (9 * K * T) ≤ D := by
    rw [hℓ₀def, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have H := hscal_sameSlab_of_isTracedRegion_P6M2 (Hs := fun i => Kh (φ (ψ i)))
    (s := fun i => σ (φ (ψ i))) (y := fun i => y (φ (ψ i))) (R := fun i => R (φ (ψ i)))
    (l := atTop) (Eventually.of_forall fun i => hRpos _) hK0 hℓ₀ hℓD htr
  refine ⟨ψ, hψ, max (max (9 * K) (1 / ℓ₀ ^ 2)) 1, ?_⟩
  filter_upwards [H] with i hi
  intro C hC x hx s h1 h2 h3 _ z hz
  have hR := hRpos (φ (ψ i))
  have hC1 : 1 ≤ C := (le_max_right _ _).trans hC
  have hC9 : 9 * K ≤ C := ((le_max_left _ _).trans (le_max_left _ _)).trans hC
  have hCℓ : 1 / ℓ₀ ^ 2 ≤ C := ((le_max_right _ _).trans (le_max_left _ _)).trans hC
  have hball : 1 / Real.sqrt (C * R (φ (ψ i))) ≤ ℓ₀ / Real.sqrt (R (φ (ψ i))) := by
    have hsR : 0 < Real.sqrt (R (φ (ψ i))) := Real.sqrt_pos.2 hR
    have hsC : 0 < Real.sqrt C := Real.sqrt_pos.2 (by linarith)
    rw [Real.sqrt_mul (by linarith), div_le_div_iff₀ (by positivity) hsR, one_mul]
    have hlow : 1 / ℓ₀ ≤ Real.sqrt C := by
      apply Real.le_sqrt_of_sq_le
      rw [div_pow, one_pow]
      exact hCℓ
    have : 1 ≤ ℓ₀ * Real.sqrt C := by
      rw [div_le_iff₀ hℓ₀] at hlow
      linarith
    nlinarith
  have hsc := hi x hx s h1 h3 h2 z (lt_of_lt_of_le hz (ENNReal.ofReal_le_ofReal hball))
  have : 9 * K * R (φ (ψ i)) ≤ C * R (φ (ψ i)) := mul_le_mul_of_nonneg_right hC9 hR.le
  exact hsc.trans this

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
