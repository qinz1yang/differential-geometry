import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GuardWireT1P6GW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PickedCenterSelP6PS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6WindowSeedBaseC11WB

/-!
# GUARDWIRE G3c：PICKSEL 中心邻域 producer 的 guarded 版（O-CH11-GUARDWIRE，后缀 `_P6GW`）

`pickedCenterNeighborhoodGuarded_of_hgood_fresh_P6GW`：PICKSEL
`pickedCenterNeighborhood_of_hgood_fresh_P6PS` 的孪生，
产出 G3b 的 `PickedCenterNeighborhoodGuarded_P6GW`；**`hWS` → WSBASE
`pickedCenterWindowSeed_guardKX_C11WB`**（PROVED）。
κ 字段仍走原 `hRic` 路线（OPEN owner DIST）；改走 `pickedCenterFootprint_twoScale_C11WB` 去 `hRic` =
DESIGN（state）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

section GuardedPickSel

variable {K : ℕ → RetainedCoreHistory.{u}}
  {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
  {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
  {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
  {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
    ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
  {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ}
  {Ctime : ℝ≥0} {Cg : ℝ}

/-- **guard 点 κ footprint（`_P6GW`，PROVED，无 `hRic`）**：中心区域点 `x` 在 guard 点 `τ`
（`GuardKX_C11KX (R(v, ·)) qthr Ct v τ x`）处 `d_τ(O, x) < A·r`。`τ = v`：slice 时刻 seed 距离
（`seedDist_slice_P6PS`）+ top gate `hdσ`；`τ < v`：guard ⇒ WSBASE 双尺度窗 `v − θw / max(R_n, R(v, x)/Λ)
≤ τ`
（`Λ·R_n ≤ qthr`、`1 ≤ 2·Ctime·Λ·θw`、`Ctime ≤ Ct`）⇒ `pickedCenterFootprint_twoScale_C11WB`。 -/
theorem pickedCenterFootprintGuarded_P6GW
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctime)
    (n : ℕ) {Dw Dc Tc θw Λ Cw Lc A r qthr : ℝ} {Ct : ℝ≥0} (hRn : 0 < R n) (hDc : 0 ≤ Dc)
    (hC20 : 0 ≤ C2) {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (τ' : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ') τ')
        (a₀ + τ') x)
    (hsmall : GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) r)
    (hclock : (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (hθw : 0 ≤ θw) (hDcL : L n / 4 + Dc ≤ Lc / 2) (hTLw : Tc + θw ≤ L n ^ 2)
    (haSw : (aSeed n : ℝ) ≤ (σ n : ℝ) - (Tc + θw) / R n)
    (hlatew : 1 ≤ R n * ((σ n : ℝ) - (Tc + θw) / R n))
    (hΛ : 0 < Λ) (hCgΛ : Cg ≤ Λ) (hΛq : Λ * R n ≤ qthr)
    (hbud : (Ctime : ℝ) * Λ * θw ≤ 1 / 2) (hθ2 : 1 ≤ 2 * (Ctime : ℝ) * Λ * θw)
    (hC1 : 1 ≤ Cw) (hΛC : 6 * Λ ≤ Cw) (hρC : 2 * Λ ≤ localPropagationRadius C2 ^ 2 * Cw)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (Cw / 2 + max Cw (2 * Real.exp 4))) ≤ R n * r ^ 2)
    (hLw : 2 + 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (Cw / 2 + max Cw (2 * Real.exp 4)))) * θw ≤
      Lc)
    (hρL : Lc + 2 * (localPropagationRadius C2 / Real.sqrt (2 * Λ)) ≤ L n)
    (hCt : (Ctime : ℝ) ≤ Ct)
    (hdl : ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
          (σ n : ℝ) - Tc / R n ≤ v →
        ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
            ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvs) x,
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              ((seedTrace n).point ((K n).toHistory.activeStage v)
                  ((K n).toHistory.activeStage_mono hav)
                ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
              (tr.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvs)) ≤
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
                (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (haS : (aSeed n : ℝ) ≤ (σ n : ℝ) - Tc / R n)
    (O : ∀ j' : Fin (K n).eventCount, ((K n).stage j'.castSucc).Carrier)
    (hO : ∀ (j' : Fin (K n).eventCount)
      (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
      (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)),
      O j' = (seedTrace n).point j'.castSucc h1 h2)
    (hdσ : riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
      ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (A * r))
    (j' : Fin (K n).eventCount) (v : ℝ) (hv1 : (K n).time j'.castSucc < v)
    (hv2 : v < (K n).time j'.succ) (hvT : (σ n : ℝ) - Tc / R n ≤ v) (hvσ : v ≤ σ n)
    (x₁ : ((K n).toHistory.stage ((K n).toHistory.activeStage (σ n))).Carrier)
    (hx₁ : x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
      (σ n)) (y n) (Dw / Real.sqrt (R n)))
    (hjσ : j'.castSucc ≤ (K n).toHistory.activeStage (σ n))
    (tr : BackwardPointTrace (K n).toHistory j'.castSucc ((K n).toHistory.activeStage (σ n)) hjσ
      x₁)
    (x : ((K n).stage j'.castSucc).Carrier)
    (hx : x ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v)
      (tr.point j'.castSucc le_rfl hjσ) (Dc / Real.sqrt (R n)))
    (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
    (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n))
    (τ : ℝ) (hτ1 : (K n).time j'.castSucc < τ) (hτ2 : τ ≤ v)
    (hg : GuardKX_C11KX (((K n).toHistory.event j').incoming.flow.scalar v) qthr Ct v τ x) :
    riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric τ)
        ((seedTrace n).point j'.castSucc h1 h2) x < ENNReal.ofReal (A * r) := by
  have hs : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 hRn
  have hlp : 0 ≤ 2 * (localPropagationRadius C2 / Real.sqrt (2 * Λ)) := by
    have := localPropagationRadius_pos hC20
    positivity
  have hL0 : 0 ≤ L n := by linarith
  have hfin : riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) ≠ ⊤ := by
    intro hT
    rw [hT, top_add] at hdσ
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hdσ)
  rcases eq_or_lt_of_le hτ2 with hτv | hτv
  · rw [hτv]
    have hsl := seedDist_slice_P6PS (haT := haT) (hsT := hsT) (has := has) n hRn hL0 hDc hdl haS
      j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx h1 h2
    refine lt_of_le_of_lt hsl (lt_of_lt_of_le ?_ hdσ)
    refine ENNReal.add_lt_add_left hfin ((ENNReal.ofReal_lt_ofReal_iff (div_pos ?_ hs)).2 ?_)
    · linarith
    · exact div_lt_div_of_pos_right (by linarith) hs
  · have hq0 : 0 < qthr := lt_of_lt_of_le (mul_pos hΛ hRn) hΛq
    have hM' : 0 < max (R n) (((K n).toHistory.event j').incoming.flow.scalar v x / Λ) :=
      lt_of_lt_of_le hRn (le_max_left _ _)
    have hΛΛ : Λ * (((K n).toHistory.event j').incoming.flow.scalar v x / Λ) =
        ((K n).toHistory.event j').incoming.flow.scalar v x := by
      field_simp
    have hΛM : Λ * max (R n) (((K n).toHistory.event j').incoming.flow.scalar v x / Λ) ≤
        max (((K n).toHistory.event j').incoming.flow.scalar v x) qthr := by
      rw [mul_max_of_nonneg _ _ hΛ.le, hΛΛ]
      exact max_le (hΛq.trans (le_max_right _ _)) (le_max_left _ _)
    have hCt0 : 0 < (Ctime : ℝ) := by
      rcases (Ctime.coe_nonneg).lt_or_eq with h | h
      · exact h
      · rw [← h] at hθ2
        norm_num at hθ2
    have hCt1 : 0 < (Ct : ℝ) := lt_of_lt_of_le hCt0 hCt
    have hd0 : 0 ≤ v - τ := by linarith
    unfold GuardKX_C11KX at hg
    have hkey : max (R n) (((K n).toHistory.event j').incoming.flow.scalar v x / Λ) * (v - τ) ≤
        θw := by
      have a1 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hΛM (by positivity : (0 : ℝ) ≤ 2 * (Ct : ℝ))) hd0
      have a2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hCt (by norm_num : (0 : ℝ) ≤ 2)) hΛ.le) hθw
      have e1 : 2 * (Ct : ℝ) * Λ *
          (max (R n) (((K n).toHistory.event j').incoming.flow.scalar v x / Λ) * (v - τ)) ≤
          2 * (Ct : ℝ) * Λ * θw := by
        linarith
      exact le_of_mul_le_mul_left e1 (mul_pos (mul_pos two_pos hCt1) hΛ)
    have hwin : v - θw / max (R n) (((K n).toHistory.event j').incoming.flow.scalar v x / Λ) ≤
        τ := by
      have : v - τ ≤ θw / max (R n) (((K n).toHistory.event j').incoming.flow.scalar v x / Λ) := by
        rw [le_div_iff₀ hM']
        linarith
      linarith
    have hf := pickedCenterFootprint_twoScale_C11WB hC20 (K n) (haT n) (hsT n) (has n) hsmall
      hclock (seedTrace n) ha₀ hpin (y n) hRn (hgood n) hDc hθw hDcL hTLw haSw hlatew hΛ hCgΛ
      hbud hC1 hΛC hρC hRr hLw hρL hdl O hO hdσ j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx τ
      ⟨hτ1, hτv⟩ hwin
    rw [hO j' h1 h2] at hf
    exact hf

/-- **中心 κ 字段 guarded（`_P6GW`，PROVED ⇐ FRESH supply + WSBASE 双尺度 footprint，无 `hRic`）**：PICKSEL
`pickedCenterKappa_of_fresh_P6PS` 的孪生，测试点 `(τ, x)` 加 guard；footprint 由
`pickedCenterFootprintGuarded_P6GW`（不经 I.8.3(b) / 端点 Ricci）给。其余证明体逐字。 -/
theorem pickedCenterKappaGuarded_of_fresh_P6GW (n : ℕ) {Dw Dc Tc θ ρ κ A r Tκ qthr : ℝ}
    {Ct : ℝ≥0}
    {nr : ℝ → ℝ} (hRn : 0 < R n) (hDc : 0 ≤ Dc)
    (hdσ : riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
      ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (A * r))
    (hdl : ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
          (σ n : ℝ) - Tc / R n ≤ v →
        ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
            ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvs) x,
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              ((seedTrace n).point ((K n).toHistory.activeStage v)
                  ((K n).toHistory.activeStage_mono hav)
                ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
              (tr.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvs)) ≤
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
                (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (haS : (aSeed n : ℝ) ≤ (σ n : ℝ) - Tc / R n)
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctime)
    (hC20 : 0 ≤ C2) {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (τ' : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ') τ')
        (a₀ + τ') x)
    {Lc θw Λ Cw : ℝ} (hθw : 0 ≤ θw) (hDcL : L n / 4 + Dc ≤ Lc / 2) (hTLw : Tc + θw ≤ L n ^ 2)
    (haSw : (aSeed n : ℝ) ≤ (σ n : ℝ) - (Tc + θw) / R n)
    (hlatew : 1 ≤ R n * ((σ n : ℝ) - (Tc + θw) / R n))
    (hΛ : 0 < Λ) (hCgΛ : Cg ≤ Λ) (hΛq : Λ * R n ≤ qthr)
    (hbud : (Ctime : ℝ) * Λ * θw ≤ 1 / 2) (hθ2 : 1 ≤ 2 * (Ctime : ℝ) * Λ * θw)
    (hC1 : 1 ≤ Cw) (hΛC : 6 * Λ ≤ Cw) (hρC : 2 * Λ ≤ localPropagationRadius C2 ^ 2 * Cw)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (Cw / 2 + max Cw (2 * Real.exp 4))) ≤ R n * r ^ 2)
    (hLw : 2 + 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (Cw / 2 + max Cw (2 * Real.exp 4)))) * θw ≤
      Lc)
    (hρL : Lc + 2 * (localPropagationRadius C2 / Real.sqrt (2 * Λ)) ≤ L n)
    (hCt : (Ctime : ℝ) ≤ Ct)
    (O : ∀ j' : Fin (K n).eventCount, ((K n).stage j'.castSucc).Carrier)
    (hO : ∀ (j' : Fin (K n).eventCount)
      (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
      (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)),
      O j' = (seedTrace n).point j'.castSucc h1 h2)
    (hW : KappaSeedWindowFwd_C11PK nr A κ Tκ (K n).toHistory) (hTκ : Tκ ≤ (Tn n : ℝ))
    (htime : 2 * r ^ 2 < (Tn n : ℝ))
    (hsmall : GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) r)
    (hvol : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (Tn n)) (Tn n)) (pT n) r)
    (hnr : ∀ w : ℝ, (Tn n : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr w ≤ r)
    (hclock : (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (hwinF : (Tn n : ℝ) - r ^ 2 / 2 ≤ (σ n : ℝ) - (Tc + θ) / R n)
    (hρ : ρ < r / 100) (hκ : 0 ≤ κ)
    (j' : Fin (K n).eventCount) (v : ℝ) (hv1 : (K n).time j'.castSucc < v)
    (hv2 : v < (K n).time j'.succ) (hvT : (σ n : ℝ) - Tc / R n ≤ v) (hvσ : v ≤ σ n)
    (x₁ : ((K n).toHistory.stage ((K n).toHistory.activeStage (σ n))).Carrier)
    (hx₁ : x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
      (σ n)) (y n) (Dw / Real.sqrt (R n)))
    (hjσ : j'.castSucc ≤ (K n).toHistory.activeStage (σ n))
    (tr : BackwardPointTrace (K n).toHistory j'.castSucc ((K n).toHistory.activeStage (σ n)) hjσ
      x₁)
    (x : ((K n).stage j'.castSucc).Carrier)
    (hx : x ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v)
      (tr.point j'.castSucc le_rfl hjσ) (Dc / Real.sqrt (R n)))
    (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
    (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)) :
    ∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon),
      v - θ / R n ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
      (K n).time j'.castSucc < τ → (τ : ℝ) < (K n).time j'.succ →
      GuardKX_C11KX (((K n).toHistory.event j').incoming.flow.scalar v) qthr Ct v τ x →
      ∀ zz : ((K n).toHistory.stageAt τ).Carrier, HEq zz x →
      ∀ b : ℝ, 0 < b → b ≤ ρ → (K n).toHistory.isParabolicallyRmControlledBall τ zz b →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel ((K n).toHistory.stageAt τ).Carrier
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
            (riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
              zz b) := by
  intro τ hτ1 hτ2 hτ3 hτ4 hg zz hzz b hb hbρ hball
  have hr2 := sq_nonneg r
  have hθR : (Tc + θ) / R n = Tc / R n + θ / R n := add_div _ _ _
  have hσT : (σ n : ℝ) ≤ (Tn n : ℝ) := hsT n
  have hav : aSeed n ≤ τ := by
    change (aSeed n : ℝ) ≤ (τ : ℝ)
    linarith
  have hvt : τ ≤ Tn n := by
    change (τ : ℝ) ≤ (Tn n : ℝ)
    linarith
  have hact := (K n).activeStage_eq_castSucc_C11PB j' τ hτ3 hτ4
  have key : ∀ (k : Fin ((K n).toHistory.eventCount + 1))
      (_hk : (K n).toHistory.activeStage τ = k)
      (h1' : (K n).toHistory.activeStage (aSeed n) ≤ k)
      (h2' : k ≤ (K n).toHistory.activeStage (Tn n))
      (z' : ((K n).toHistory.stage k).Carrier), HEq zz z' →
      riemannianEDistOf ((K n).toHistory.stageMetric k τ) ((seedTrace n).point k h1' h2') z' <
        ENNReal.ofReal (A * r) →
      zz ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
        ((seedTrace n).point ((K n).toHistory.activeStage τ)
          ((K n).toHistory.activeStage_mono hav) ((K n).toHistory.activeStage_mono hvt))
        (A * r) := by
    intro k hk
    subst hk
    intro h1' h2' z' hzz' hd'
    rw [eq_of_heq hzz']
    exact hd'
  have hd' : riemannianEDistOf ((K n).toHistory.stageMetric j'.castSucc τ)
      ((seedTrace n).point j'.castSucc h1 h2) x < ENNReal.ofReal (A * r) := by
    rw [ObservedHistory.stageMetric_castSucc_apply]
    exact pickedCenterFootprintGuarded_P6GW hgood n hRn hDc hC20 ha₀ hpin hsmall hclock hθw hDcL
      hTLw haSw hlatew hΛ hCgΛ hΛq hbud hθ2 hC1 hΛC hρC hRr hLw hρL hCt hdl haS O hO hdσ j' v
      hv1 hv2
      hvT hvσ x₁ hx₁ hjσ tr x hx h1 h2 τ hτ3 hτ2 hg
  have hx' := key j'.castSucc hact h1 h2 x hzz hd'
  have h := hW (Tn n) (pT n) r hTκ htime hsmall hvol hnr (aSeed n) (haT n) hclock (seedTrace n)
    τ hav hvt (by linarith) zz hx' b hb.le (by linarith) hball
  rw [ENNReal.ofReal_mul hκ, ENNReal.ofReal_pow hb.le] at h
  exact h

/-- **G3c `pickedCenterNeighborhoodGuarded_of_hgood_fresh_P6GW`（`_P6GW`，PROVISIONAL[WSBASE
point-anchor 数值前提 +
PICKSEL 原输入（hgood、`hdl`、FRESH `hW` / `hsmall` / `hvol` / `hnr` / `hclock` / `hwinF`、`hdσ`）]；**无
`hWS`、无
`hRic`**）**：PICKSEL `pickedCenterNeighborhood_of_hgood_fresh_P6PS` 的 guarded 孪生，结论 =
`PickedCenterNeighborhoodGuarded_P6GW`。(1) witness 逐字；(2)
梯度：`hWS`（`PickedCenterWindowSeed_C11PT`）换成 WSBASE
`pickedCenterWindowSeed_guardKX_C11WB`（guard 点 seed localization）——合同 guard 常数 `Ct ≥ Ctime`；(3)
κ：footprint 由
`pickedCenterFootprintGuarded_P6GW`（WSBASE `pickedCenterFootprint_twoScale_C11WB`）给，端点 Ricci
`hRic`（OPEN owner DIST）
在 guard 集上退役。 -/
theorem pickedCenterNeighborhoodGuarded_of_hgood_fresh_P6GW
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctime)
    (n : ℕ) {Dw Dc Tc θ qthr ρ κ ℓ A r Tκ : ℝ} {nr : ℝ → ℝ} {Ct Cgrad : ℝ≥0}
    (hRn : 0 < R n) (hDc : 0 ≤ Dc) (hθ : 0 ≤ θ) (hℓ : 0 < ℓ)
    (hLR : 4 * (Dc + 8 * θ / (ℓ * Real.sqrt (R n))) ≤ 3 * L n)
    (hTL : Tc + θ ≤ L n ^ 2) (haS : (aSeed n : ℝ) ≤ (σ n : ℝ) - (Tc + θ) / R n)
    (hq : Cg * R n ≤ qthr) (hC2 : C2 ≤ (Cgrad : ℝ))
    (hdl : ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
          (σ n : ℝ) - Tc / R n ≤ v →
        ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
            ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvs) x,
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              ((seedTrace n).point ((K n).toHistory.activeStage v)
                  ((K n).toHistory.activeStage_mono hav)
                ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
              (tr.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvs)) ≤
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
                (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (O : ∀ j' : Fin (K n).eventCount, ((K n).stage j'.castSucc).Carrier)
    (hO : ∀ (j' : Fin (K n).eventCount)
      (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
      (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)),
      O j' = (seedTrace n).point j'.castSucc h1 h2)
    (hC20 : 0 ≤ C2) {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (τ' : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ') τ')
        (a₀ + τ') x)
    {Lc θw Λ Cw : ℝ} (hθw : 0 ≤ θw) (hDcL : L n / 4 + Dc ≤ Lc / 2) (hTLw : Tc + θw ≤ L n ^ 2)
    (haSw : (aSeed n : ℝ) ≤ (σ n : ℝ) - (Tc + θw) / R n)
    (hlatew : 1 ≤ R n * ((σ n : ℝ) - (Tc + θw) / R n))
    (hΛ : 0 < Λ) (hCgΛ : Cg ≤ Λ) (hΛq : Λ * R n ≤ qthr)
    (hbud : (Ctime : ℝ) * Λ * θw ≤ 1 / 2) (hθ2 : 1 ≤ 2 * (Ctime : ℝ) * Λ * θw)
    (hC1 : 1 ≤ Cw) (hΛC : 6 * Λ ≤ Cw) (hρC : 2 * Λ ≤ localPropagationRadius C2 ^ 2 * Cw)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (Cw / 2 + max Cw (2 * Real.exp 4))) ≤ R n * r ^ 2)
    (hLw : 2 + 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (Cw / 2 + max Cw (2 * Real.exp 4)))) * θw ≤
      Lc)
    (hρL : Lc + 2 * (localPropagationRadius C2 / Real.sqrt (2 * Λ)) ≤ L n)
    (hCt : (Ctime : ℝ) ≤ Ct)
    (hW : KappaSeedWindowFwd_C11PK nr A κ Tκ (K n).toHistory) (hTκ : Tκ ≤ (Tn n : ℝ))
    (htime : 2 * r ^ 2 < (Tn n : ℝ))
    (hsmall : GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) r)
    (hvol : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (Tn n)) (Tn n)) (pT n) r)
    (hnr : ∀ w : ℝ, (Tn n : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr w ≤ r)
    (hclock : (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (hwinF : (Tn n : ℝ) - r ^ 2 / 2 ≤ (σ n : ℝ) - (Tc + θ) / R n)
    (hρ : ρ < r / 100) (hκ : 0 ≤ κ)
    (hdσ : riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
      ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (A * r)) :
    PickedCenterNeighborhoodGuarded_P6GW Dw Dc Tc θ (R n) qthr ρ κ eps C1 C2 Ct Cgrad (K n) (σ n)
      (y n) := by
  intro j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx
  have hs : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 hRn
  have hX0 : 0 ≤ 8 * θ / (ℓ * Real.sqrt (R n)) :=
    div_nonneg (by linarith) (mul_pos hℓ hs).le
  have hL0 : 0 ≤ L n := by linarith
  have hTR : Tc / R n ≤ (Tc + θ) / R n := div_le_div_of_nonneg_right (by linarith) hRn.le
  have hθR : (Tc + θ) / R n = Tc / R n + θ / R n := add_div _ _ _
  have hLR' : (Tc + θ) / R n ≤ L n ^ 2 / R n := div_le_div_of_nonneg_right hTL hRn.le
  have hvh : v ≤ (K n).toHistory.horizon := hvσ.trans (σ n).2.2
  let vI : Icc (0 : ℝ) (K n).toHistory.horizon :=
    ⟨v, ((K n).toHistory.time_nonneg _).trans hv1.le, hvh⟩
  have hact : (K n).toHistory.activeStage vI = j'.castSucc :=
    (K n).activeStage_eq_castSucc_C11PB j' vI hv1 hv2
  have hav : aSeed n ≤ vI := by
    change (aSeed n : ℝ) ≤ v
    linarith
  have hvs : vI ≤ σ n := by
    change v ≤ (σ n : ℝ)
    exact hvσ
  have h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc := by
    rw [← hact]
    exact (K n).toHistory.activeStage_mono hav
  have h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n) := by
    rw [← hact]
    exact (K n).toHistory.activeStage_mono (hvs.trans (hsT n))
  have hslice := seedDist_slice_P6PS (haT := haT) (hsT := hsT) (has := has) n hRn hL0 hDc hdl
    (by linarith) j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx h1 h2
  refine ⟨fun hqx => ?_, fun v' hv' hv'θ hqx hg ξ => ?_, ?_⟩
  · have hvL : (σ n : ℝ) - L n ^ 2 / R n ≤ (vI : ℝ) := by
      change (σ n : ℝ) - L n ^ 2 / R n ≤ v
      linarith
    exact witness_of_seedDist_P6PS hgood n j' vI hv1 hv2 hav hvs hvL h1 h2 x
      (hslice.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (by linarith) hs.le)))) (hq.trans hqx.le)
  · have hv'2 : v' < (K n).time j'.succ := hv'.2.trans hv2
    let τ : Icc (0 : ℝ) (K n).toHistory.horizon :=
      ⟨v', ((K n).toHistory.time_nonneg _).trans hv'.1.le,
        hv'2.le.trans ((K n).toHistory.time_le_horizon_at _)⟩
    have hav' : aSeed n ≤ τ := by
      change (aSeed n : ℝ) ≤ v'
      linarith
    have hvs' : τ ≤ σ n := by
      change v' ≤ (σ n : ℝ)
      linarith [hv'.2]
    have hvL' : (σ n : ℝ) - L n ^ 2 / R n ≤ (τ : ℝ) := by
      change (σ n : ℝ) - L n ^ 2 / R n ≤ v'
      linarith
    have hq0 : 0 < qthr := lt_of_lt_of_le (mul_pos hΛ hRn) hΛq
    have hMq : 0 ≤ max (((K n).toHistory.event j').incoming.flow.scalar v x) qthr :=
      hq0.le.trans (le_max_right _ _)
    have hvv : 0 ≤ v - v' := by linarith [hv'.2]
    have hg' : 2 * (Ctime : ℝ) * max (((K n).toHistory.event j').incoming.flow.scalar v x) qthr *
        (v - v') ≤ 1 := by
      unfold GuardKX_C11KX at hg
      have h2' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hCt (by norm_num : (0 : ℝ) ≤ 2)) hMq) hvv
      linarith
    have hd := pickedCenterWindowSeed_guardKX_C11WB hC20 (K n) (haT n) (hsT n) (has n) hsmall
      hclock (seedTrace n) ha₀ hpin (y n) hRn (hgood n) hDc hθw hDcL hTLw haSw hlatew hΛ hCgΛ hbud
      hθ2 hC1 hΛC hρC hRr hLw hρL hdl O hO j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx qthr hΛq v' hv'
      hg'
    rw [hO j' h1 h2] at hd
    obtain ⟨W, -⟩ := witness_of_seedDist_P6PS hgood n j' τ hv'.1 hv'2 hav' hvs' hvL' h1 h2 x hd
      (hq.trans hqx.le)
    have hR0 : 0 ≤ ((K n).toHistory.event j').incoming.flow.scalar v' x := W.Q_pos.le
    exact (W.gradient ξ).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC2 hR0) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  · exact pickedCenterKappaGuarded_of_fresh_P6GW (haT := haT) (hsT := hsT) (has := has) n hRn hDc
      hdσ hdl (by linarith) hgood hC20 ha₀ hpin hθw hDcL hTLw haSw hlatew hΛ hCgΛ hΛq hbud hθ2 hC1
      hΛC hρC hRr hLw hρL hCt O hO hW hTκ htime hsmall hvol hnr hclock hwinF hρ hκ j' v hv1 hv2 hvT
      hvσ x₁ hx₁ hjσ tr x hx h1 h2

end GuardedPickSel

/-- consumer（G3c，`_P6GW`）：guarded producer 的输出即 G3b guarded T1 核心形的合同族形。 -/
example := @pickedCenterNeighborhoodGuarded_of_hgood_fresh_P6GW.{u}

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
