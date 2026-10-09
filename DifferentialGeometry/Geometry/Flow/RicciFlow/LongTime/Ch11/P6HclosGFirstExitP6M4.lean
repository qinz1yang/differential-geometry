import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HclosFirstExit_P6L4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HUVGlobalP6M3

/-!
# DF-1 `hclosG` ⇐ 首出时刻 + K0 种子 + pinching + U 端条件标量界（O-CH11-P6ANCH4 G2，后缀 `_P6M4`）

* **`hclosG_of_firstExit_P6M4`**：结论逐字 = `hUVG_of_selection_P6M3` 的 `hclosG` binder（= P6CG
  `hUVG_of_selection_Cg_P6S3` / `false_of_selection_eventSlab_late(HI)_closed_Cg_P6S3`
  的 `hclosG`，逐字同形）。
  前提：selection 自带 `hwin`、`hL`；Dist / HDISTC 同款数据 `hsmall`（K0，`(Tn, pT, r)`）、`hclock`
  （`aSeed = Tn − r²`）、`R r² → ∞`、`hlate`、Hamilton–Ivey `hpin`；**唯一残余 `hscalU`**：U 端
  `B_s(x, 1/√(CQ))` 上 `R ≤ C Q`（`Q = R(v, w)`，`1 ≤ C`），只在窗 `[v − B/Q, v]` 内 **x 已 seed-Good**
  （`d_s(O_j, x) ≤ d_σ + L/√R`）的时刻要求，常数 `C` 依赖 `(Rad, B, σ₁, σ₂, Dw, Dd)`。
  证明 = `seed_closure_firstExit_P6L4`（`firstExit_distance_P6M4` 的实例）逐 history；窗在 hclosG 自带的
  `time j'⁻ < τ` guard 内 ⇒ 单 slab，无 event 跨越。DF-1 的覆盖问题（`K(ρ)` 随半径变）消失；
  `hcover`（`hclosC_of_cover_P6M3`）路线被绕过。
* `hclosC_of_hclosG_P6M4`：全局 ⇒ 条件形（`map φ atTop ≤ atTop`），结论逐字 = `hUVC_of_selection_P6M3`
  的 `hclosC` binder。
* 深度溢出的精确去向 = `hscalU`（G3：逐点 `HasSpatialCanonicalTimeControl` 只控深度 `≲ 1/(Ctime C₂ Q)`，
  SLT `Bw` 无界）。
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

/-- **DF-1 `hclosG` ⇐ 首出时刻（`_P6M4`）**：结论逐字 = `hUVG_of_selection_P6M3` 的 `hclosG` binder；
唯一残余 = U 端条件标量界 `hscalU`（深度 `B/Q`、条件于 seed-Good）。 -/
theorem ObservedHistory.hclosG_of_firstExit_P6M4 (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (r : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hlate : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, 1 ≤ R n * ((σ n : ℝ) - T / R n))
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₀ + τ') x)
    (hscalU : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
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
        ∀ s : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ s → s ≤ v →
          (Kh n).time j'.castSucc < s →
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s)
              ((seedTrace n).point j'.castSucc h1 h2) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) →
          ∀ z : ((Kh n).stage j'.castSucc).Carrier,
            riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s) x z <
                ENNReal.ofReal
                  (1 / Real.sqrt (C * ((Kh n).event j').incoming.flow.scalar v w)) →
              ((Kh n).event j').incoming.flow.scalar s z ≤
                C * ((Kh n).event j').incoming.flow.scalar v w) :
    ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
      ∀ᶠ n in atTop,
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
              ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  intro Rad B σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd
  obtain ⟨C, hC, hev⟩ := hscalU Rad B σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd
  have hθ : 0 < max B 0 - σ₁ + 1 := by
    have := le_max_right B 0
    linarith
  filter_upwards [hev, hwin _ hθ, hlate _ hθ,
    hL.eventually_ge_atTop (2 * max Rad 0 +
      16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * max B 0),
    hRr.eventually_ge_atTop
      (2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))))]
    with n hn hwn hln hLn hrn
  intro j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hwseed hwnear hRw x hx τ hτ hτv hτ1
  have hRn := hR n
  have hQ : 0 < ((Kh n).event j').incoming.flow.scalar v w := hRn.trans_le hRw
  have hB : B / ((Kh n).event j').incoming.flow.scalar v w ≤ max B 0 / R n :=
    (div_le_div_of_nonneg_right (le_max_left _ _) hQ.le).trans
      (div_le_div_of_nonneg_left (le_max_right _ _) hRn hRw)
  have e1 : (max B 0 - σ₁ + 1) / R n = max B 0 / R n - σ₁ / R n + 1 / R n := by ring
  have hR1 : 0 < 1 / R n := by positivity
  have hθR : (σ n : ℝ) - (max B 0 - σ₁ + 1) / R n ≤ τ := by linarith
  have hpos : 0 < (σ n : ℝ) - (max B 0 - σ₁ + 1) / R n := by
    by_contra hneg
    have hle := not_lt.mp hneg
    nlinarith
  have hτ0 : 0 ≤ τ := by linarith
  have hQτ : 1 ≤ ((Kh n).event j').incoming.flow.scalar v w * τ :=
    calc (1 : ℝ) ≤ R n * ((σ n : ℝ) - (max B 0 - σ₁ + 1) / R n) := hln
      _ ≤ R n * τ := mul_le_mul_of_nonneg_left hθR hRn.le
      _ ≤ ((Kh n).event j').incoming.flow.scalar v w * τ := mul_le_mul_of_nonneg_right hRw hτ0
  have haτ : (aSeed n : ℝ) ≤ τ := hwn.trans hθR
  have hσT : (σ n : ℝ) ≤ Tn n := hsT n
  have hvT : v ≤ (Tn n : ℝ) := by
    have : σ₂ / R n < 0 := div_neg_of_neg_of_pos hσ₂ hRn
    linarith
  by_cases htop : riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
      ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
        ((Kh n).activeStage_mono (hsT n))) (y n) = ⊤
  · rw [htop, top_add]
    exact le_top
  exact (Kh n).seed_closure_firstExit_P6L4 (haT n) (hsmall n) (hclock n) (seedTrace n) ha₀
    (hpin n) j' h1 h2 w x (ENNReal.ofReal_toReal htop).symm ENNReal.toReal_nonneg hRn hRw hC
    hrn hLn hwseed hx hτ hτv hτ1 hv2 haτ hvT hQτ
    (hn j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hwseed hwnear hRw x hx)

/-- **全局 ⇒ 条件形（`_P6M4`）**：`hclosG` ⇒ `hUVC_of_selection_P6M3` 的 `hclosC` binder 逐字。 -/
theorem ObservedHistory.hclosC_of_hclosG_P6M4 (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ)
    (hclosG : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
      ∀ᶠ n in atTop,
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
        ∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
            (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
        ∀ τ : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ τ → τ ≤ v →
          (Kh n).time j'.castSucc < τ →
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric τ)
              ((seedTrace n).point j'.castSucc h1 h2) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  intro Rad B σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd _hT _hKc _htr
  exact Filter.Eventually.filter_mono hφ.tendsto_atTop (hclosG Rad B σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
