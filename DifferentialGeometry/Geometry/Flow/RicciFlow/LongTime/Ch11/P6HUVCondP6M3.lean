import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HUVKappaClosure_P6L3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6BcadCondP6M3

/-!
# 条件形 `hUVC` ⇐ selection + seed closure + 区域 κ（O-CH11-P6ANCH3 G2，后缀 `_P6M3`）

G1 `hsliceRC_of_slice_data_P6M3` 的 U 侧 binder `hUVC`（near-trace、条件形）的生产：
* **witness 项**：全生产——slice 时刻 `v` 上 `d_v(O, x) ≤ d(O, w) + d(w, x) ≤ d_σ + L/(2√R) + Rad/√R`
  （`seed_triangle_P6L3`）⇒ selection `hgood`（阈值 `4R`、`L/√R`）⇒ witness（`witness_of_hgood_slab_P6L3`）；
* **梯度项**：`hgood` 于 `(v', x)`（`v' ∈ [v − B/R(w), v)` 同 slab）⇐ **seed closure** `hclosC`；
* **区域 κ 项**（D-8）：KAPPA3 `regionalKappa_of_window_center_C11Q4` 的逐 history 结论形 `hκR`（中心取
  `c := O_j`，`ρU := d_σ + (L+1)/√R`，`regionalKappa_of_closure_P6L3`）⇐ 同一 `hclosC` + `hdistσ`
  （`d_σ(O_σ, y) + (L+1)/√R ≤ Aκ r`，selection 侧）+ `hroom`（`Tn − r²/2 ≤ σ − L²/R`，D-10 window room）。
**剩余显式 binder = `hclosC`（parabolic seed-distance closure）**：near-trace 点 `x ∈ B_v(w, Rad/√R(w))` 在
`τ ∈ [v − B/R(w), v]` 上仍在 seed Good 区（`d_τ(O_j, x) ≤ d_σ + L/√R`）。它**不能**只由 `hUVC` 的条件
（traced `(2Dw, T, Kc)`、`−σ₁ < T`）生产（设计发现 DF-1：深度溢出 `B` + near-trace 覆盖 `K(ρ)`）；数学上是
Perelman I.8.3(b)（树内 `smooth_distance_distortion_C11D`）+ canonical neighborhood 的时间连续性论证
（B2 同源）。consumer：`hUVC` 逐字喂 G1 `hbcadC_of_slice_data_P6M3`。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

/-- **条件形 `hUVC` ⇐ selection `hgood` + seed closure `hclosC` + 区域 κ `hκR`**（`_P6M3`）：结论逐字 =
`hsliceRC_of_slice_data_P6M3` 的 `hUVC` binder（`ε C1 C2 := eps C1' C2'`、`Cgrad := C2'.toNNReal`）。 -/
theorem ObservedHistory.hUVC_of_selection_P6M3 {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} (hC2 : 0 ≤ C2')
    {κ Aκ : ℝ} (Kh : ℕ → ObservedHistory.{u}) (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L r ρV : ℕ → ℝ) (hR : ∀ n, 0 < R n)
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
    (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (hdistσ : ∀ᶠ n in atTop,
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n))
    (hκR : ∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
      (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
      (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
            ENNReal.ofReal (Aκ * r n)) →
      ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
              ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b))
    (hclosC : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
        v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
        ∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
            (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
        ∀ τ : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ τ → τ ≤ v →
          (Kh n).time j'.castSucc < τ →
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric τ)
              ((seedTrace n).point j'.castSucc h1 h2) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))) :
    ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
        v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
          (∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            4 * R n < ((Kh n).event j').incoming.flow.scalar v x →
            ∃ W : SpatialCanonicalWitness (((Kh n).event j').incoming.flow.base.metric v)
              eps C1' C2' x, W.capTubeHasNeckChart eps) ∧
          (∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            ∀ v' ∈ Ioo ((Kh n).time j'.castSucc) v,
            v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ v' →
            4 * R n < ((Kh n).event j').incoming.flow.scalar v' x →
            ∀ ξ : TangentSpace ThreeModel x,
              |scalarDifferential ((Kh n).event j').incoming.flow v' x ξ| ≤
                (C2'.toNNReal : ℝ) * ((Kh n).event j').incoming.flow.scalar v' x *
                  Real.sqrt (((Kh n).event j').incoming.flow.scalar v' x) *
                  Real.sqrt ((((Kh n).event j').incoming.flow.base.metric v').inner x ξ ξ)) ∧
          (∀ (τ : Icc (0 : ℝ) (Kh n).horizon),
            v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
            (Kh n).time j'.castSucc < τ → (τ : ℝ) < (Kh n).time j'.succ →
            ∀ z ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                  (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
            ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                  ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                  (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)) := by
  intro Rad B σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hX1 : (1 : ℝ) ≤ max B 0 - σ₁ + 1 := by
    have := le_max_right B 0
    linarith
  filter_upwards [hclosC Rad B σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr,
    Filter.Eventually.filter_mono hφt
      (hL.eventually_ge_atTop (max (2 * max Rad 0) (max B 0 - σ₁ + 1))),
    Filter.Eventually.filter_mono hφt (hwin (max B 0 - σ₁ + 1) (by linarith)),
    Filter.Eventually.filter_mono hφt hκR, Filter.Eventually.filter_mono hφt hdistσ]
    with n hcl hLn hwn hκn hdσ
  intro j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hwseed hwnear hRw
  have hcl' := hcl j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hwseed hwnear hRw
  have hRn := hR n
  have hLX : max B 0 - σ₁ + 1 ≤ L n := (le_max_right _ _).trans hLn
  have hL0 : 0 ≤ L n := by linarith
  have hRad : 2 * max Rad 0 ≤ L n := (le_max_left _ _).trans hLn
  have hvσ : v ≤ (σ n : ℝ) := by
    have : σ₂ / R n < 0 := div_neg_of_neg_of_pos hσ₂ hRn
    linarith
  have hwinB : ∀ τ : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ τ →
      (aSeed n : ℝ) ≤ τ ∧ (σ n : ℝ) - L n ^ 2 / R n ≤ τ := fun τ hτ => by
    obtain ⟨e1, e2⟩ := window_P6L3 hRn hRw hvσ1 hτ le_rfl hX1 hLX
    exact ⟨hwn.trans e1, e2⟩
  have hwin0 : (aSeed n : ℝ) ≤ v ∧ (σ n : ℝ) - L n ^ 2 / R n ≤ v := by
    have hX0 : max 0 0 - σ₁ + 1 ≤ max B 0 - σ₁ + 1 := by
      rw [max_self]
      linarith [le_max_right B 0]
    obtain ⟨e1, e2⟩ := window_P6L3 (B := 0) (τ := v) hRn hRw hvσ1 (by simp) hX0 hX1 hLX
    exact ⟨hwn.trans e1, e2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x hx hRx
    exact (Kh n).witness_of_hgood_slab_P6L3 (haT n) (hsT n) (has n) (seedTrace n) (y n) (R n)
      (L n) (hgood n) j' v hv1 hv2 hwin0.1 hvσ hwin0.2 h1 h2 x
      (seed_triangle_P6L3 (Kh n) j' v _ w x _ hRn hRw hL0 hRad hwseed hx) hRx.le
  · intro x hx v' hv' hBv' hRx ξ
    obtain ⟨ha, hLτ⟩ := hwinB v' hBv'
    exact (Kh n).gradient_of_hgood_slab_P6L3 hC2 (haT n) (hsT n) (has n) (seedTrace n) (y n)
      (R n) (L n) (hgood n) j' v' hv'.1 (hv'.2.trans hv2) ha (hv'.2.le.trans hvσ) hLτ h1 h2 x
      (hcl' x hx v' hBv' hv'.2.le hv'.1) hRx.le ξ
  · have ha : (Tn n : ℝ) - r n ^ 2 / 2 ≤ v - B / ((Kh n).event j').incoming.flow.scalar v w :=
      (hroom n).trans (hwinB _ le_rfl).2
    exact regionalKappa_of_closure_P6L3 (Kh n) (haT n) (hsT n) (has n) (seedTrace n) (y n) hRn hL0
      hκn hdσ j' _ _ v ha (hvσ.trans (hsT n)) h1 h2
      (fun τ haτ hτv hτ1 _ x hx => hcl' x hx τ haτ hτv hτ1)

/-- **consumer（G2 → G1）**：`hUVC_of_selection_P6M3` 的结论逐字填进 G1 `hbcadC_of_slice_data_P6M3` 的 `hUVC`
（`eps C1' C2' := ε C1 C2`、`Cgrad := C2.toNNReal`）⇒ driver 第二版的 `hbcadC`；剩余显式 = `hclosC`。 -/
example
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (htj : ∀ n, t n < (K n).time (j n).succ)
    {D qcan : ℕ → ℝ} {p₀ p : ℕ → CutoffParameters} {δb ρb : ℕ → ℝ}
    {recordsK : ∀ n i, GeometricCutoffRecord (K n).toHistory i (p n)}
    (hrecK : ∀ n, (K n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (recordsK n))
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscaleK : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * qcan n ≤ ((recordsK n i).static b).neck.scale)
    (hpinchK0 : ∀ n, (K n).EventSlabsPinched phi)
    (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (qcan n) (Fin.last (K n).eventCount))
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hHI0 : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) a₀ x)
    (hlow0 : ∀ n x, -3 / a₀ ≤ metricScalarAt ((K n).initialMetric 0) x)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hRpos : ∀ n, 0 < R n) (hqR : ∀ n, qcan n ≤ R n)
    (hRt : Tendsto (fun n => R n * σ n) atTop atTop)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hdistQC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
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
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (ρV : ℕ → ℝ) (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
    (hC2 : 0 ≤ C2) {Aκ : ℝ} {Ctime' : ℝ≥0} (r : ℕ → ℝ)
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
        (Kh n).HasSpatialCanonicalTimeControl ε C1 C2 Ctime' v z)
    (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (hdistσ : ∀ᶠ n in atTop,
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n))
    (hκR : ∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
      (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
      (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
            ENNReal.ofReal (Aκ * r n)) →
      ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
              ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b))
    (hclosC : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
        v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
        ∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
            (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
        ∀ τ : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ τ → τ ≤ v →
          (Kh n).time j'.castSucc < τ →
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric τ)
              ((seedTrace n).point j'.castSucc h1 h2) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)))
    :
    ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T K : ℝ, -σ' < T → 0 ≤ K →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (K * R n)) →
      ∀ᶠ n in map φ atTop,
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
          C * R n :=
  ObservedHistory.hbcadC_of_slice_data_P6M3 hεle hκ hphi htj hrecK hqcan hpar hscaleK hpinchK0
    hslabK ha₀ hHI0 hlow0 Kh hKh σ y R hσ hRpos hqR hRt Tn aSeed haT hsT has pT seedTrace L hL hwin
    hdistQC ρV hρV
    (ObservedHistory.hUVC_of_selection_P6M3 (Ctime' := Ctime') hC2 Kh Tn aSeed σ haT hsT has pT
      seedTrace y R L r ρV hRpos hL hgood hwin hroom hdistσ hκR hclosC)

/-- **consumer（KAPPA3 → `hκR`）**：KAPPA3 `regionalKappa_of_window_center_half_C11Q4`（window κ `hW`，
`ρ_nc = r/200`）在 tower 子列 `Kh n := (F.tower.history (m n)).toHistory`、种子 `(Tn n, pT n, r n)`、
`Tn → ∞` 上逐字给出 `hUVC_of_selection_P6M3` 的 `hκR`（`ρV n := r n / 200`；`RegionalKappa_C11Q3` 展开）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {Aκ κ : ℝ}
    (hκ : 0 ≤ κ) (hW : GC.LongTime.Ch11.LocalKappaWindowAt_P6B F (fun _ => 0) Aκ κ) (m : ℕ → ℕ)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (m n)).toHistory.horizon)
    (haT : ∀ n, aSeed n ≤ Tn n)
    (pT : ∀ n, ((F.tower.history (m n)).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (m n)).toHistory
      ((F.tower.history (m n)).toHistory.activeStage (aSeed n))
      ((F.tower.history (m n)).toHistory.activeStage (Tn n))
      ((F.tower.history (m n)).toHistory.activeStage_mono (haT n)) (pT n))
    (r : ℕ → ℝ) (hTn : Tendsto (fun n => (Tn n : ℝ)) atTop atTop)
    (hr : ∀ n, 2 * r n ^ 2 < (Tn n : ℝ))
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (F.tower.history (m n)).toHistory (Tn n)
      (pT n) (r n))
    (hvol : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r n ^ 3) ≤
      Geometry.Collapse.ballVolume ((F.tower.history (m n)).toHistory.stageMetric
        ((F.tower.history (m n)).toHistory.activeStage (Tn n)) (Tn n)) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2) :
    let Kh : ℕ → ObservedHistory.{u} := fun n => (F.tower.history (m n)).toHistory
    let ρV : ℕ → ℝ := fun n => r n / 200
    ∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
      (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
      (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
            ENNReal.ofReal (Aκ * r n)) →
      ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
              ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)
  := by
  intro Kh ρV
  obtain ⟨T, -, hK⟩ := GC.LongTime.Ch11.regionalKappa_of_window_center_half_C11Q4 hκ hW
  filter_upwards [hTn.eventually_ge_atTop T] with n hn
  intro j c U a t ρU ha ht hUc hdistV
  exact hK (m n) (Tn n) (pT n) (r n) hn (hr n) (hsmall n) (hvol n) (aSeed n) (haT n) (hclock n)
    (seedTrace n) j c U a t ρU ha ht hUc hdistV

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
