import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HUVGlobalCgP6S3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6BcadLateCgP6S3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ClosureLateHIP6LT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SelectionCoeffP6M3

/-!
# P6 收口 late 主形（逐 n HI + 窗口 pinching），`hgood` 阈值 `Cg·R`，`hbcad` / `hdist` 消去
（S-CH11-P6CG G3，后缀 `_P6S3`）

`false_of_selection_eventSlab_lateHI_closed_Cg_P6S3`：P6LATE
`false_of_selection_eventSlab_lateHI_P6LT`（P6SEL rescale transport adapter 用的逐 n HI + 窗口
pinching 主形）去 `hdist` / `hbcad` 两个 binder，换 `hdistQ` + U 侧数据 + 全局 seed closure
`hclosG`（同 `false_of_selection_eventSlab_late_closed_Cg_P6S3`），并按 G5 同法 Cg 化：新 binder
`(Cg : ℝ) (hCg : 2 ≤ Cg)` 紧接 `hgood`，`hgood` 阈值 `Cg * R n`，SLT anchor `(Cq, q) := (Cg, Cg·R)`、
K-route 收口 `Cs = Cq := Cg`、`qs = qd := Cg·R`、selection 三引理换 `_Cg_P6M3` 版。
其余 binder（含逐 n `a₀`、`hbirthA`、窗口形 `hpinchK0`）与 lateHI 主形逐字。`hbcad` ⇐ G2
`hbcad_lateHI_of_slice_data_P6S3`（binder 与 lateHI 主形一一对齐，直接取 `hbirthA` / `hpinchK0`）+ G1
`hUVG_of_selection_Cg_P6S3`。剩余几何缺口 = `hclosG`（DF-1，O-CH11-P6ANCH4）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

/-- **P6 收口 late 主形（逐 n HI + 窗口 pinching，`hgood` 阈值 `Cg·R`，`hbcad` / `hdist` 消去）**：
见文件头。 -/
theorem false_of_selection_eventSlab_lateHI_closed_Cg_P6S3 :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, C ≤ C1' → C ≤ C2' → C.toNNReal ≤ Ctime' →
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ}, (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {j : ∀ n, Fin (K n).eventCount} → {t : ℕ → ℝ} →
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {Q T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} →
      {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} →
      {a₀ : ℕ → ℝ} →
      (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
        -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) →
      (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
      (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) →
      (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder) →
      (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
        ((recordsK n i hi).static b).neck.scale) →
      (hbirthA : ∀ᶠ n in atTop, ∀ i hi b, 1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale) →
      (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
        ((K n).toHistory.event i).incoming.flow
        (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi) →
      (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount)) →
      (hqR : ∀ n : ℕ, max ((n : ℝ) + 1) (Q n) <
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hnotK : ∀ n, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ (j n).castSucc)
        (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          t n - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hRpos : ∀ n, 0 < R n) →
      (d : GC.LongTime.Ch11.Pre841Data_C11K Kh σ y R hRpos) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n) →
      (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (haT : ∀ n, aSeed n ≤ Tn n) →
      (hsT : ∀ n, σ n ≤ Tn n) → (has : ∀ n, aSeed n ≤ σ n) →
      (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier) →
      (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
        ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)) →
      (L : ℕ → ℝ) → (hL : Tendsto L atTop atTop) →
      (Cg : ℝ) → (hCg : 2 ≤ Cg) →
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
          Cg * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
          (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z) →
      (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      (hdistQ : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
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
              ENNReal.ofReal (L n / 4 / Real.sqrt (R n))) →
      {κ Aκ : ℝ} → (hκ : 0 < κ) → (r ρV : ℕ → ℝ) →
      (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) →
      (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n) →
      (hdistσ : ∀ᶠ n in atTop,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n)) →
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
                (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)) →
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
                ENNReal.ofReal (L n / Real.sqrt (R n))) →
      (hsel : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' (σ n) (y n)) →
      False := by
  obtain ⟨epsW, hepsW, hB⟩ := false_of_selection_eventSlab_lateHI_prefix_P6LT.{u}
  refine ⟨epsW, hepsW, fun ε hε hsmall hεW hεX hεN hεcone => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall hεW hεX hεN
  refine ⟨C, hC, fun {C1' C2' Ctime'} hC1 hC2 hCt => ?_⟩
  intro Ctime phi hphi K j t hjt htj Q T₀ p pF recordsK recordsF yG a₀ hHI hcanK hδF hacc hrad
    hord hscaleK hbirthA hpinchK0 hslabK hqR hnotK Kh hKh σ y R hσ hyG hRn hRpos d hT₀ Tn aSeed haT
    hsT has
    pT seedTrace L hL Cg hCg hgood hwin hdistQ κ Aκ hκ r ρV hρV hroom hdistσ hκR hclosG hsel
  have hC2' : 0 ≤ C2' := by linarith
  have hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
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
    intro D T hD hT
    filter_upwards [hdistQ D T hD hT, hL.eventually_ge_atTop 0] with n hn hL0
    intro x hx v hav hvs hvT tr
    refine (hn x hx v hav hvs hvT tr).trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
    exact div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  have hqRR : ∀ n : ℕ, max ((n : ℝ) + 1) (Q n) ≤ R n :=
    fun n => (hqR n).le.trans_eq (hRn n).symm
  have hUVG := ObservedHistory.hUVG_of_selection_Cg_P6S3 (Ctime' := Ctime') (Cg := Cg) hC2' Kh Tn
    aSeed σ haT hsT has pT seedTrace y R L r ρV hRpos hL hgood hwin hroom hdistσ hκR hclosG
  have hbcad := ObservedHistory.hbcad_lateHI_of_slice_data_P6S3 hεcone hκ hphi (by linarith) htj
    recordsF hHI hcanK hδF hacc hrad hord hscaleK hbirthA hpinchK0 hslabK Kh hKh σ y R hσ hRpos
    hqRR hT₀ Tn aSeed haT hsT has pT seedTrace L hL hwin ρV hρV hdistQ hUVG
  have hRt := tendsto_scalar_mul_time_of_window_P6LS hσ hRn hRpos hwin
  obtain ⟨qcan, θcap, D, hqc, hθ, hD, hqcan, hQq, hθcap, hDn⟩ := exists_params_P6D Q
  -- K 层 → prefix 形
  have hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧
      (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
    fun n => ⟨hacc n, hDn n, by rw [hD n]; exact hrad n, hord n, le_rfl⟩
  have hscale : ∀ (n : ℕ) (i : Fin ((K n).prefixAt (j n).castSucc).eventCount) hi b,
      ((n : ℝ) + 1) * qcan n ≤
        (((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i hi).static b).neck.scale :=
    fun n i hi b => by
      rw [hqc n]
      exact hscaleK n (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) i) hi b
  have hslab' : ∀ n, (K n).EventSlabsDerivative Ctime (qcan n) (Fin.last (K n).eventCount) :=
    fun n => RetainedCoreHistory.eventSlabsDerivative_mono_P6D (hslabK n) (hQq n)
  have hq0 (n : ℕ) : 0 < qcan n := by
    have := hqcan n
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have hctime : ((2 * Ctime : ℝ≥0) : ℝ) = 2 * (Ctime : ℝ) := by push_cast; ring
  have hderG : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore (2 * Ctime)
      (2 * qcan n) (t n) := fun n x v hv hR => by
    have hlt : qcan n < ((K n).toHistory.event (j n)).incoming.flow.scalar v x := by
      have := hq0 n
      linarith
    have h := hslab' n (j n) (Fin.castSucc_lt_last _) x v ⟨hv.1, hv.2.trans (htj n)⟩ hlt
    rw [hctime]
    have h0 : 0 ≤ (Ctime : ℝ) * ((K n).toHistory.event (j n)).incoming.flow.scalar v x ^ 2 :=
      mul_nonneg Ctime.coe_nonneg (sq_nonneg _)
    linarith
  have hqR' : ∀ n, qcan n <
      ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) := fun n => by
    rw [hqc n]
    exact hqR n
  have hnot := fun n => (K n).not_capWindowPoint_prefix_of_late_P6N (j n).castSucc (recordsK n)
    (yG n) (hnotK n)
  have hnot' : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
      (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
      (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl =
          (((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i hi).static b).window x ∧
        ‖x.val‖ < D n + 1 ∧
        t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤ θcap n *
          ((((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i hi).static b).neck.scale
            )⁻¹ :=
    fun n => by
      rw [hD n, hθ n]
      exact hnot n
  have hT₀' : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) :=
    fun B => (hT₀ B).mono fun n hn => by
      rw [← hRn n, ← hσ n]
      exact hn
  have hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
        Perelman.PhiAlmostNonnegative
          (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow
          (Ico (((K n).prefixAt (j n).castSucc).time i.castSucc)
            (((K n).prefixAt (j n).castSucc).time i.succ) ∩ Ici (T₀ n)) phi) ∧
      Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
        (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ) ∩ Ici (T₀ n)) phi :=
    fun n => ⟨fun i => hpinchK0 n (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) i),
      hpinchK0 n (j n)⟩
  have hbirthA' : ∀ᶠ n in atTop, ∀ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount) hi b,
      1 ≤ a₀ n *
        (((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i hi).static b).neck.scale :=
    hbirthA.mono fun n hn i hi b => hn (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) i) hi b
  have hslab : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (qcan n)
      (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) :=
    fun n => (K n).eventSlabsDerivative_prefixAt _
      (fun i _ => hslab' n i (Fin.castSucc_lt_last i))
  have hHI' := fun n => (K n).hHI_prefixAt_P6LT (j n).castSucc (hHI n)
  have hcan := fun n => (K n).prefixLateRecords_hcan_P6N (j n).castSucc (recordsK n) (hcanK n)
  have hδF' : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
      T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
      (pF n).delta (((K n).prefixAt (j n).castSucc).time i.succ) ≤ 1 / ((n : ℝ) + 1) :=
    fun n i hi => hδF n (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) i) hi
  -- selection / `Pre841` 侧（同 G1y / G4b / G5c）
  have hk := exists_tracedKappa_of_kseq_P6D2 d.volume_ge
  obtain ⟨ρnc, hradii, hkappa⟩ := hk
  obtain ⟨Phi, hPhi, hpinchK⟩ := exists_tracedPinching_of_pre841_P6M d
  subst hKh
  have hC20 : 0 ≤ C2' := (zero_le_one.trans hC).trans hC2
  have hnc := hnc_window_of_tracedKappa_P6M hjt htj σ hσ y yG hyG R hRpos hRn d.kappa_pos ρnc
    hkappa
  have hρ : Tendsto (fun n => ρnc n *
      Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))) atTop atTop :=
    hradii.congr fun n => by rw [hRn n]
  have hW := hW_of_selection_Cg_P6M3 hjt htj σ hσ y yG hyG R hRpos hRn Tn aSeed haT hsT has pT
    seedTrace L hL hgood
  have hgrad := hgrad_of_selection_Cg_P6M3 hC20 hjt htj σ hσ y yG hyG R hRpos hRn Tn aSeed haT hsT
    has pT seedTrace L hL hgood hwin hdist
  have hq2 : ∀ n, 2 * qcan n ≤ Cg * R n := fun n => by
    have h1 := hqR' n
    have h2 := hqcan n
    have h3 : (0 : ℝ) ≤ n := n.cast_nonneg
    have h4 : 2 * R n ≤ Cg * R n := mul_le_mul_of_nonneg_right hCg (hRpos n).le
    rw [hRn n] at h4 ⊢
    linarith
  have hqC : ∀ n, Cg * R n ≤
      Cg * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) := fun n => by
    rw [hRn n]
  have hanchor0 := RetainedCoreHistory.hanchor0_lateW_P6LT
    (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming)
    (s := fun n => (K n).time (j n).succ) (y := yG) (ρ := ρnc) hεcone d.kappa_pos hphi
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) hcan hqcan hpar
    hθcap hpinch hslab hjt htj hderG hqR' hnot' hT₀' hRt (Cq := Cg) (fun n => Cg * R n) hq2 hqC hW
    hgrad hnc hρ
  obtain ⟨r₀, hr₀, hctrl⟩ := exists_hctrl_lateHI_P6LT
    (records := fun n => (K n).prefixLateRecords_P6N (j n).castSucc (recordsK n)) hphi hjt htj
    (fun n => (K n).prefixRecords (j n).castSucc (recordsF n)) hHI' hcan hδF' hqcan hpar
    hscale hbirthA' hθcap hpinch hslab hderG hqR' hnot' hT₀' hRt hanchor0 (fun n => (K
    n).toHistory) rfl σ
    y R hσ hyG hRn
  have hctrl' := hctrl r₀ hr₀ le_rfl
  obtain ⟨hwit, hderivK⟩ := hwit_hderiv_of_selection_Cg_P6M3 (fun n => (K n).toHistory) Tn aSeed σ
    haT
    hsT has pT seedTrace y R L hRpos hL hgood hwin hdist
  exact hB' hC1 hC2 hCt hphi hjt htj
    (records := fun n => (K n).prefixLateRecords_P6N (j n).castSucc (recordsK n))
    (fun n => (K n).prefixRecords (j n).castSucc (recordsF n)) hHI' hcan hδF' hqcan hpar
    hscale hbirthA' hθcap hpinch hslab hderG hqR' hnot' hT₀' hRt hanchor0 (fun n => (K n).toHistory)
    rfl σ y R hσ hyG hRn hr₀ d.kappa_pos (hseed_of_pre841_P6M d hr₀ hctrl') d.kappa_pos ρnc hradii
    hkappa hPhi hpinchK (Cs := Cg) (Cq := Cg) (qs := fun n => Cg * R n)
    (qd := fun n => Cg * R n)
    (fun _ => le_rfl) (fun _ => le_rfl) hwit hderivK hbcad hsel

/-- consumer（常数层）。 -/
example : ∃ epsW : ℝ, 0 < epsW :=
  false_of_selection_eventSlab_lateHI_closed_Cg_P6S3.{0}.imp fun _ h => h.1

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
