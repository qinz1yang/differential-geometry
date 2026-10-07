import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.HdistCondC11G3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.EarlierSeedC11G3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6WitnessConditionalP6M2

/-!
# 条件形 `hdistC`，K0 种子时刻 `Tn ≥ σ` 任意（S-CH11-HDISTC G2，后缀 `_C11G3`）

G0 `hdistC_of_traced_C11G3` 要 `Tn ≤ t`（E 的 horizon = `t`，K-route 里即 `Tn = σ = t`）。本文件用 G1
`earlier_seed_small_on_half_depth_C11G3` 把 K0 种子从 `Tn` 回推到 `σ`（半深度，半径 `r/100`，新时钟
`a' = σ − (r/100)²`，新 trace 逐点等于原 trace），再套 G0：

* 前提变成 `σ ≤ t`（`σ ≤ Tn` 不再要 `Tn ≤ t`）、半深度 `Tn − r²/2 ≤ σ`、`2r² < Tn`；
* `hwin` / `hlate` **不再是前提**（`R (r/100)² → ∞` ⇒ `a' ≤ σ − T/R` 与 `R (σ − T/R) ≥ 1` eventually）；
* `hsepWK` 的 scale 阈值用新半径 `r/100`：`2 max (3/(r/100)², C R) < neck.scale`；
* 结论仍是 P6ANCH2 `hdistC` binder 逐字（原 `aSeed`、原 `seedTrace`；新 trace 逐点相等，窗口
  `σ − T/R ≤ v` 落在 `a' ≤ v` 内 eventually）。
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

/-- **条件形 `hdistC` ⇐ traced region，任意 `Tn ≥ σ` 种子（`_C11G3`）**：G0 去掉 `Tn ≤ t`
（代之以 `σ ≤ t` + 半深度 `Tn − r²/2 ≤ σ` + `2r² < Tn`），`hwin / hlate` 由 `R r² → ∞` 推出。 -/
theorem hdistC_of_traced_anySeed_C11G3 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (K : ℕ → RetainedCoreHistory.{u}) (j : ∀ n, Fin (K n).eventCount) (t : ℕ → ℝ)
      (_hjt : ∀ n, (K n).time (j n).castSucc < t n) (_htj : ∀ n, t n < (K n).time (j n).succ),
    let Kh : ℕ → ObservedHistory.{u} := fun n => (K n).toHistory
    ∀ (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
      (R r L : ℕ → ℝ) (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
      (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
      (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
      (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
        ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)),
      (∀ n, (σ n : ℝ) ≤ t n) →
      (∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ)) → (∀ n, 2 * r n ^ 2 < (Tn n : ℝ)) →
      (∀ᶠ n in atTop, 0 < R n) → Tendsto L atTop atTop →
      (∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n)) →
      (∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      ∀ {a₀ : ℝ}, 0 ≤ a₀ →
      (∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
        InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₀ + τ') x) →
    ∀ (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
      (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (q n)),
      (∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
        ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n, (q n).modelAccuracy ≤ ε₀) → (∀ n, 2 ≤ (q n).modelOrder) →
      (∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius) →
      (∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
        ∀ (i : Fin (K n).eventCount) (_hij : i.val < (j n).val) (hi : T₀ n ≤ (K n).time i.succ) b,
          (σ n : ℝ) - T / R n < (K n).time i.succ →
          2 * max (3 / (r n / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale) →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - T / R n) →
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  obtain ⟨ε₀, hε₀, hC⟩ := hdistC_of_traced_C11G3.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro K j t hjt htj Kh σ y R r L Tn aSeed haT hsT has pT seedTrace hσt hhalf htime hR hL
    hsmallK hclockK hRr a₀ ha₀ hpinK q T₀ recordsK hcanK hacc0 hm hDm hsepWK hT₀ φ hφ D T Kc hD hT
    hKc htr
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hshift := fun n => GC.LongTime.Ch11.earlier_seed_small_on_half_depth_C11G3 (haT n) (pT n)
    (r n) (htime n) (hclockK n) (hsmallK n) (seedTrace n) (σ n) (has n) (hsT n) (hhalf n)
  choose a' haa' hav' tr' hclk' hsm' hR2' hpt' using hshift
  have hRr' : Tendsto (fun n => R n * (r n / 100) ^ 2) atTop atTop := by
    refine ((hRr.atTop_div_const (by norm_num : (0 : ℝ) < 10000)).congr fun n => ?_)
    ring
  have hwin' : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (a' n : ℝ) ≤ (σ n : ℝ) - T / R n := by
    intro T hT
    filter_upwards [hR, hRr'.eventually_ge_atTop T] with n hRn hn
    rw [hclk' n]
    have : T / R n ≤ (r n / 100) ^ 2 := by
      rw [div_le_iff₀ hRn]
      linarith
    linarith
  have hlate' : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, 1 ≤ R n * ((σ n : ℝ) - T / R n) := by
    intro T hT
    filter_upwards [hR, hRr'.eventually_ge_atTop (T + 1)] with n hRn hn
    have h1 : R n * (2 * (r n / 100) ^ 2) < R n * (σ n : ℝ) :=
      mul_lt_mul_of_pos_left (hR2' n) hRn
    have h2 : R n * ((σ n : ℝ) - T / R n) = R n * (σ n : ℝ) - T := by
      field_simp
    rw [h2]
    linarith
  have hmain := hC K j t hjt htj σ y R (fun n => r n / 100) L σ a' hav' (fun n => le_rfl) hav'
    (fun n => (seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
      ((Kh n).activeStage_mono (hsT n))) tr' hσt hR hL hsm' hclk' hRr' ha₀ hpinK q T₀ recordsK
    hcanK hacc0 hm hDm hwin' hlate' hsepWK hT₀ φ hφ D T Kc hD hT hKc htr
  filter_upwards [hmain, Filter.Eventually.filter_mono hφt (hwin' T hT)] with n hn hw
  intro x hx v hav hvs hvT tr
  have hav'' : a' n ≤ v := by
    have h1 : (a' n : ℝ) ≤ v := hw.trans hvT
    exact h1
  have h := hn x hx v hav'' hvs hvT tr
  rw [hpt' n v hav'' hvs, hpt' n (σ n) (hav' n) le_rfl] at h
  exact h

/-- **consumer（P6ANCH2 的条件形接口，任意 `Tn ≥ σ`）**：`hdistC_of_traced_anySeed_C11G3` 的结论
（`Kh := fun n => (K n).toHistory`，原 `aSeed` / 原 `seedTrace`）逐字就是
`hwitC_hderivC_of_hdistC_P6M2` 的 `hdistC` binder；`hwin`（P6M2 自带）同时喂给 P6M2。 -/
example {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    (K : ℕ → RetainedCoreHistory.{u}) (j : ∀ n, Fin (K n).eventCount) (t : ℕ → ℝ)
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (p : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (p n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R r L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((Kh n).stageAt v).Carrier,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        4 * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hσt : ∀ n, ((σ n : Icc (0 : ℝ) (Kh n).horizon) : ℝ) ≤ t n)
    (hhalf : ∀ n, ((Tn n : Icc (0 : ℝ) (Kh n).horizon) : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ))
    (htime : ∀ n, 2 * r n ^ 2 < ((Tn n : Icc (0 : ℝ) (Kh n).horizon) : ℝ))
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (p n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop) {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₀ + τ') x)
    (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (q n)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ((∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
        ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n, (q n).modelAccuracy ≤ ε₀) → (∀ n, 2 ≤ (q n).modelOrder) →
      (∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius) →
      (∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
        ∀ (i : Fin (K n).eventCount) (_hij : i.val < (j n).val) (hi : T₀ n ≤ (K n).time i.succ) b,
          (σ n : ℝ) - T / R n < (K n).time i.succ →
          2 * max (3 / (r n / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale) →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - T / R n) → True) := by
  subst hKh
  obtain ⟨ε₀, hε₀, hC⟩ := hdistC_of_traced_anySeed_C11G3.{u}
  refine ⟨ε₀, hε₀, fun hcan hacc hord hrad hsep hT₀ => ?_⟩
  have _hwit := ObservedHistory.hwitC_hderivC_of_hdistC_P6M2 (eps := eps) (C1' := C1')
    (C2' := C2') (Ctime' := Ctime') (fun n => (K n).toHistory) Tn aSeed σ haT hsT has p seedTrace y
    R L hR hL hgood hwin
    (hC K j t hjt htj σ y R r L Tn aSeed haT hsT has p seedTrace hσt hhalf htime
      (Filter.Eventually.of_forall hR) hL hsmall hclock hRr ha₀ hpin q T₀ recordsK hcan hacc hord
      hrad hsep hT₀)
  trivial

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
