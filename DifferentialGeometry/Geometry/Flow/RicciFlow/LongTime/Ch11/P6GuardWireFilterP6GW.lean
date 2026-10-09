import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GuardWirePickSelP6GW

/-!
# GUARDWIRE G4：T1 filter 级 consumer（O-CH11-GUARDWIRE，后缀 `_P6GW`）

* `hPCGuarded_filter_of_hgood_fresh_P6GW`：G3c 逐 `n` producer ⇒ G3 guarded T1 核心形的 `hPC` 槽
  （`∀ᶠ n in l, PickedCenterNeighborhoodGuarded_P6GW Dw Dc (−σ₁) θ₀ (R n) (Cq·R n) (ρV n) κ ε C1 C2
Ct Cgrad …`）。
* `ObservedHistory.hsliceR_lateHI_core_pickedCenter_hgood_guarded_P6GW`：G3 核心形结论逐字，`hPC` 槽内部付清 ⇒
T1 路线的
  U 侧不再有 `hPC` / `hWS` / `hRic`；`hK` 无 binder（KSWEXIT）。
常数对齐见 `hPCGuarded_filter_of_hgood_fresh_P6GW` docstring。
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

section FilterPC

variable {K : ℕ → RetainedCoreHistory.{u}}
  {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
  {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
  {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
  {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
    ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
  {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ}
  {Ctime : ℝ≥0} {Cg : ℝ}

/-- **G4 filter 级 consumer（`_P6GW`，PROVED ⇐ 显式 family 输入）**：G3c 的逐 `n` producer
`pickedCenterNeighborhoodGuarded_of_hgood_fresh_P6GW` 在 filter `l ≤ atTop` 上 eventually 成立，结论 = G3
guarded T1 核心形
`hsliceR_lateHI_core_pickedCenter_guarded_P6GW` 的 `hPC` 槽逐字（`Tc := −σ₁`、`θ := θ₀`、`qthr :=
Cq·R_n`、`ρ := ρV n`）。
常数对齐（state 方案）：hgood 阈值 `Cg ≤ Cq`（壳的 `Cg`）、hgood 时间常数 `Ctime ≤ Ct`（壳的 KSW `Ctime`）；WSBASE `Λ := Cg`、
`θw := 1/(2·Ctime·Cg)`、`Cw := max (max 1 (6Cg)) (2Cg/ρ_lp(C2)²)`、`Lc := L_n/2 + 2·Dc`；`ℓ :=
1`（guarded producer 里 `ℓ` 只供
witness 余量）；`O j′` = seed trace 在 `j′⁻` 的点（`h1 h2` 不成立时取 `source_nonempty` 的任意点，合同只在成立处用）；
`hdl` 由核心形的 `σ + σ₁/R_n ≤ v` 形换成 `σ − (−σ₁)/R_n ≤ v`。eventually 条件 ⇐ `hwin`、`L → ∞`、`R → ∞`、`R·σ →
∞`、
`R·r² → ∞`、`hwinF`、`hdσ`。 -/
theorem hPCGuarded_filter_of_hgood_fresh_P6GW
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctime)
    (hCg : 0 < Cg) (hCt0 : 0 < (Ctime : ℝ)) {Cq : ℝ} (hCq : Cg ≤ Cq) {Ct Cgrad : ℝ≥0}
    (hCt : (Ctime : ℝ) ≤ Ct) (hC2 : C2 ≤ (Cgrad : ℝ)) (hC20 : 0 ≤ C2)
    (hRpos : ∀ n, 0 < R n) (hRlim : Tendsto R atTop atTop)
    (hRσ : Tendsto (fun n => R n * (σ n : ℝ)) atTop atTop) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    {a₁ : ℝ} (ha₁ : 0 ≤ a₁)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ') τ')
        (a₁ + τ') x)
    {r : ℕ → ℝ}
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    {nr : ℕ → ℝ → ℝ} {Aκ κ : ℝ} {Tκ ρV : ℕ → ℝ}
    (hW : ∀ n, KappaSeedWindowFwd_C11PK (nr n) Aκ κ (Tκ n) (K n).toHistory)
    (hTκ : ∀ n, Tκ n ≤ (Tn n : ℝ)) (htime : ∀ n, 2 * r n ^ 2 < (Tn n : ℝ))
    (hvol : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r n ^ 3) ≤ ballVolume ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (Tn n)) (Tn n)) (pT n) (r n))
    (hnr : ∀ n (w : ℝ), (Tn n : ℝ) - r n ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr n w ≤ r n)
    (hwinF : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ) - T / R n)
    (hρ : ∀ n, ρV n < r n / 100) (hκ : 0 ≤ κ)
    (hdσ : ∀ᶠ n in atTop,
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n))
    {l : Filter ℕ} (hl : l ≤ atTop) {σ₁ θ₀ Dw Dc : ℝ} (hσ₁ : σ₁ < 0) (hθ₀ : 0 < θ₀)
    (hDc : 0 ≤ Dc)
    (hdl : ∀ᶠ n in l,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) + σ₁ / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
                ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n))) :
    ∀ᶠ n in l, PickedCenterNeighborhoodGuarded_P6GW Dw Dc (-σ₁) θ₀ (R n) (Cq * R n) (ρV n) κ eps
      C1 C2 Ct Cgrad (K n) (σ n) (y n) := by
  have hlpr := localPropagationRadius_pos hC20
  set θw : ℝ := 1 / (2 * (Ctime : ℝ) * Cg) with hθwdef
  have hθw0 : 0 < θw := by positivity
  have hθ1 : 2 * (Ctime : ℝ) * Cg * θw = 1 := mul_one_div_cancel (by positivity)
  have hbud : (Ctime : ℝ) * Cg * θw ≤ 1 / 2 := by linarith
  set Cw : ℝ := max (max 1 (6 * Cg)) (2 * Cg / localPropagationRadius C2 ^ 2) with hCwdef
  have hC1 : 1 ≤ Cw := (le_max_left _ _).trans (le_max_left _ _)
  have hΛC : 6 * Cg ≤ Cw := (le_max_right _ _).trans (le_max_left _ _)
  have hρC : 2 * Cg ≤ localPropagationRadius C2 ^ 2 * Cw := by
    have hl2 : 0 < localPropagationRadius C2 ^ 2 := by positivity
    have h := (le_max_right (max 1 (6 * Cg)) (2 * Cg / localPropagationRadius C2 ^ 2))
    rw [← hCwdef, div_le_iff₀ hl2] at h
    linarith
  have hlp : 0 ≤ 2 * (localPropagationRadius C2 / Real.sqrt (2 * Cg)) := by positivity
  have hT1 : 0 < -σ₁ + θ₀ := by linarith
  have hT2 : 0 < -σ₁ + θw := by linarith
  filter_upwards [hl (hwin (-σ₁ + θ₀) hT1), hl (hwin (-σ₁ + θw) hT2),
    hl (hL.eventually_ge_atTop (max 1 (-σ₁ + θ₀))), hl (hL.eventually_ge_atTop (max 1 (-σ₁ + θw))),
    hl (hL.eventually_ge_atTop (4 * Dc + 32 * θ₀)), hl (hL.eventually_ge_atTop (4 * Dc + 2 *
      (localPropagationRadius C2 / Real.sqrt (2 * Cg)) * 2)),
    hl (hL.eventually_ge_atTop
      (2 * (2 + 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (Cw / 2 + max Cw (2 * Real.exp 4)))) *
        θw))),
    hl (hRr.eventually_ge_atTop (2500 * max 1 (2 * Real.sqrt 3 * (Cw / 2 + max Cw
      (2 * Real.exp 4))))),
    hl (hRσ.eventually_ge_atTop (1 + (-σ₁ + θw))), hl (hRlim.eventually_ge_atTop 1),
    hl (hwinF (-σ₁ + θ₀) hT1), hl hdσ, hdl] with n ha1 ha2 hL1 hL2 hL3 hL4 hL5 hRrn hRσn hR1 hwF
    hdσn hdln
  have hRn := hRpos n
  have hTL : -σ₁ + θ₀ ≤ L n ^ 2 := by
    have e1 := le_max_left 1 (-σ₁ + θ₀)
    have e2 := le_max_right 1 (-σ₁ + θ₀)
    nlinarith
  have hTLw : -σ₁ + θw ≤ L n ^ 2 := by
    have e1 := le_max_left 1 (-σ₁ + θw)
    have e2 := le_max_right 1 (-σ₁ + θw)
    nlinarith
  have hs1 : 1 ≤ Real.sqrt (R n) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hR1
  have hX : 8 * θ₀ / (1 * Real.sqrt (R n)) ≤ 8 * θ₀ := by
    rw [one_mul]
    exact div_le_self (by positivity) hs1
  have hLR : 4 * (Dc + 8 * θ₀ / (1 * Real.sqrt (R n))) ≤ 3 * L n := by linarith
  have hRθ : R n * ((-σ₁ + θw) / R n) = -σ₁ + θw := by field_simp [hRn.ne']
  have hlatew : 1 ≤ R n * ((σ n : ℝ) - (-σ₁ + θw) / R n) := by
    rw [mul_sub, hRθ]
    linarith
  have hq : Cg * R n ≤ Cq * R n := mul_le_mul_of_nonneg_right hCq hRn.le
  let O : ∀ j' : Fin (K n).eventCount, ((K n).stage j'.castSucc).Carrier := fun j' =>
    if h : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc ∧
        j'.castSucc ≤ (K n).toHistory.activeStage (Tn n) then
      (seedTrace n).point j'.castSucc h.1 h.2
    else Classical.choice ((K n).toHistory.event j').transition.source_nonempty
  have hO : ∀ (j' : Fin (K n).eventCount)
      (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
      (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)),
      O j' = (seedTrace n).point j'.castSucc h1 h2 := fun j' h1 h2 => dite_eq_left ⟨h1, h2⟩
  exact pickedCenterNeighborhoodGuarded_of_hgood_fresh_P6GW hgood n (ℓ := 1) (Ct := Ct) hRn hDc
    hθ₀.le one_pos hLR hTL ha1 hq hC2
    (fun x hx v hav hvs hvT tr => hdln x hx v hav hvs
      (by rw [neg_div, sub_neg_eq_add] at hvT; exact hvT) tr)
    O hO hC20 ha₁ (hpin n) (Lc := L n / 2 + 2 * Dc) (θw := θw) (Λ := Cg) (Cw := Cw) hθw0.le
    (by linarith) hTLw ha2 hlatew hCg le_rfl hq hbud (le_of_eq hθ1.symm) hC1 hΛC hρC hRrn
    (by linarith) (by linarith) hCt (hW n) (hTκ n) (htime n) (hsmall n) (hvol n) (hnr n)
    (hclock n) hwF (hρ n) hκ hdσn

end FilterPC

section Composite

/-- **G4 组合：T1 核心形 ⇐ hgood + FRESH family（`_P6GW`，PROVISIONAL：binder = G3 核心形原有前提（KSW 侧无 binder、
late K 层 / selection / `hqR` inherited）+ hgood（阈值 `Cgg ≤ Cg`、时间常数 `Ctg ≤ Ctime`）+ FRESH family（`hW
/ hTκ / htime /
hvol / hnr / hwinF / hρ`）+ top gate `hdσ` + K0 `hsmall / hclock / hRr` + `hpin` + `R → ∞`、`R·σ →
∞` + `0 ≤ C2 ≤ Cgrad`；**无
`hPC` 合同族、无 `hWS`、无 `hRic`**）**：G3 `hsliceR_lateHI_core_pickedCenter_guarded_P6GW` 的结论逐字，`hPC` 槽由
`hPCGuarded_filter_of_hgood_fresh_P6GW` 付（`Dd + Rad ≥ 0`），`Dd + Rad < 0` 走 PICKSEL
`pickedCenterNeighborhood_of_nonpos_P6PS`
的弱化（区域球空）。 -/
theorem ObservedHistory.hsliceR_lateHI_core_pickedCenter_hgood_guarded_P6GW
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hθ₀2 : θ₀ ≤ 1 / 2)
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {Cg : ℝ} (hCg : 1 ≤ Cg) {η₃ Lc : ℝ}
    (hη₃ : 0 < η₃) (hLc : 0 < Lc)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (htj : ∀ n, t n < (K n).time (j n).succ)
    {Q T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n))
    {a₀ : ℕ → ℝ}
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x)
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1))
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount))
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (y : ∀ n, ((K n).toHistory.stageAt
        (σ n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hRpos : ∀ n, 0 < R n)
    (hqR : ∀ n : ℕ, max ((n : ℝ) + 1) (Q n) ≤ R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (ρV : ℕ → ℝ) (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
    {Cgg : ℝ} {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cgg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L ε C1 C2 Ctg)
    (hCgg : 0 < Cgg) (hCgq : Cgg ≤ Cg) (hCtg0 : 0 < (Ctg : ℝ)) (hCtg : (Ctg : ℝ) ≤ Ctime)
    (hC2 : C2 ≤ (Cgrad : ℝ)) (hC20 : 0 ≤ C2) (hRlim : Tendsto R atTop atTop)
    (hRσ : Tendsto (fun n => R n * (σ n : ℝ)) atTop atTop)
    {a₁ : ℝ} (ha₁ : 0 ≤ a₁)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ') τ')
        (a₁ + τ') x)
    {r : ℕ → ℝ}
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    {nr : ℕ → ℝ → ℝ} {Aκ : ℝ} {Tκ : ℕ → ℝ}
    (hW : ∀ n, KappaSeedWindowFwd_C11PK (nr n) Aκ κ (Tκ n) (K n).toHistory)
    (hTκ : ∀ n, Tκ n ≤ (Tn n : ℝ)) (htime : ∀ n, 2 * r n ^ 2 < (Tn n : ℝ))
    (hvol : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r n ^ 3) ≤ ballVolume ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (Tn n)) (Tn n)) (pT n) (r n))
    (hnr : ∀ n (w : ℝ), (Tn n : ℝ) - r n ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr n w ≤ r n)
    (hwinF : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ) - T / R n)
    (hρ : ∀ n, ρV n < r n / 100)
    (hdσ : ∀ᶠ n in atTop,
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n))
 :
    ∀ A Dd : ℝ, 1 ≤ A → 0 < Dd → ∃ QB Dcap D₂ : ℝ, 0 ≤ QB ∧
      Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) ≤ D₂ ∧
      ∀ l : Filter ℕ, l ≤ atTop → ∀ σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw : ℝ, 0 < Dw →
      (∀ᶠ n in l,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) + σ₁ / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
                ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n))) →
      ∀ᶠ n in l,
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) + σ₁ / R n ≤ v →
        (v : ℝ) ≤ σ n + σ₂ / R n → (K n).toHistory.time ((K n).toHistory.activeStage v) < v →
      ∀ tr₁ : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvt) x₁,
        metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
          (tr₁.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono hvt))
              ≤ A * R n →
        ∃ CWP : ((K n).toHistory.stage ((K n).toHistory.activeStage v)).Carrier → Prop,
          (∀ w, riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              (tr₁.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvt)) w <
              ENNReal.ofReal (Dd / Real.sqrt (R n)) → ¬ CWP w →
            R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
                w → ∀ x,
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) w x <
              ENNReal.ofReal ((2 * Dd * Real.sqrt A + 1) /
                Real.sqrt (metricScalarAt ((K n).toHistory.stageMetric
                    ((K n).toHistory.activeStage v) v) w)) →
            metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) x ≤
              QB * metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
                  w) ∧
          (∀ w, riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              (tr₁.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvt)) w <
              ENNReal.ofReal (Dd / Real.sqrt (R n)) → CWP w →
            ∃ (Ξ : standardCapWindow D₂ → ((K n).toHistory.stage
                ((K n).toHistory.activeStage v)).Carrier)
              (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
              Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dcap + 1 ∧
              ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
                τw ∈ Icc (0 : ℝ) (1 / 2) ∧
                ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
                  metricDerivNorm m (localPullMetric (scaleMetric lam hlam
                      ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)) Ξ hΞ)
                    ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
                    (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃) := by
  intro A Dd hA hDd
  obtain ⟨QB, Dcap, D₂, Rad, hQB, hD₂, hcore⟩ :=
    ObservedHistory.hsliceR_lateHI_core_pickedCenter_guarded_P6GW (C1 := C1) (C2 := C2)
      (Cgrad := Cgrad) (Ctime := Ctime) hθ₀ hθ₀2 hεle hκ hphi hCg hη₃ hLc htj recordsF hHI hcanK
      hδF hacc hrad hord hscaleK hbirthA hpinchK0 hslabK σ y R hσ hRpos hqR hT₀ Tn aSeed haT hsT
      has pT seedTrace L hL hwin ρV hρV A Dd hA hDd
  refine ⟨QB, Dcap, D₂, hQB, hD₂, fun l hl σ₁ σ₂ h12 hσ₂ Dw hDw hdl =>
    hcore l hl σ₁ σ₂ h12 hσ₂ Dw hDw hdl ?_⟩
  rcases le_or_gt 0 (Dd + Rad) with hDc | hDc
  · exact hPCGuarded_filter_of_hgood_fresh_P6GW (Cg := Cgg) (Ctime := Ctg) hgood hCgg hCtg0 hCgq
      hCtg hC2 hC20 hRpos hRlim hRσ hL hwin ha₁ hpin hsmall hclock hRr hW hTκ htime hvol hnr hwinF
      hρ hκ.le hdσ hl (by linarith) hθ₀ hDc hdl
  · exact Eventually.of_forall fun n =>
      (pickedCenterNeighborhood_of_nonpos_P6PS (K n) (σ n) (y n) hDc.le).guarded_P6GW Ctime

end Composite

/-- consumer（G4，`_P6GW`）：T1 核心形（guarded，`hPC` 内部付清）。 -/
example := @ObservedHistory.hsliceR_lateHI_core_pickedCenter_hgood_guarded_P6GW.{u}

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
