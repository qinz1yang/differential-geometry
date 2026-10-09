import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SepTailP6SN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CwsUniformP6SN

/-!
# SEPTN G3 的 (CWS) diagonal 包接进 `P6SepTailP6SN` 的 ev / native 定理（S-CH11-KDIAG G2，后缀 `_P6KD2`）

`false_of_selection_eventSlab_late_closed_residual_cond_ev_P6SN` 的 binder `{η} (hcws : ∀ᶠ n …)`
（(CWS)：late cap-window 点的标量下界）由 SEPTN G3 `cws_uniform_of_diagonal_P6SN` 供给，**η := c 统一**，
诊断序列 `Cb Rn ζ δ₀ m₀` 只依赖 `(Ctime, n)`，故在 `∃ …` 里放在 `Ctime phi hphi` 之后、`K` 之前。
**INTEGRATION-ONLY**（无新数学）：
* **`…_cond_ev_diag_P6KD2`**：statement = ev 形，K 层 binder `hδF hacc hrad hord hscaleK` 换成
  diagonal 档 `δ₀ ζ Rn m₀` + `hbirth`（`max (Q n) 1 ≤ Cb n·scale`）+ `hbirthA`（`1 ≤ a₀·scale`，**∀ n**）；
  `{η} hcws` 删去，`hsepK` 的 `η` 取 `c`（`∃ c > 0` 在最前）。证明：ev 形 + G3 `hdiag` 给 `hcws`
  （∀ n ⇒ eventually），主形 `hδF hacc hrad hord hscaleK` 由 diagonal 蕴含
  （`min`/`max` 取过的界 + `hscaleK_of_diag_P6SN`）。
* **`…_cond_native_diag_P6KD2`**：native 形（`hsepWK hsepK` 换 native 输入 `hlate hsel4 hδK hnomId`；`η`
  固定为 `c`，内部 `hη := hc`），K 层同 ev_diag；证明经 ev_diag。
K 层 diagonal 档的 producer = S-CH11-KDIAG G1 `diagonalPack_of_lateKdata_P6KD2`（conjunct 顺序
`hcanK hδF hacc hrad hord hbirth hbirthA` 逐字）。
由 build-logs/scratch/S-CH11-KDIAG/mk_g2.py 生成。
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

/-- **closed 主形残余形，条件化，(CWS) 取 SEPTN G3 diagonal 包（`_P6KD2`）**：见文件头。 -/
theorem false_of_selection_eventSlab_late_closed_residual_cond_ev_diag_P6KD2 :
    ∃ c : ℝ, 0 < c ∧ ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, C ≤ C1' → C ≤ C2' → C.toNNReal ≤ Ctime' →
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ}, (hphi : Perelman.AdmissiblePinchingFunction phi) →
      ∃ (Cb Rn ζ δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ),
      (∀ n, 0 < Cb n ∧ Cb n ≤ 1 / ((n : ℝ) + 1) ^ 2) ∧
      (∀ n, 0 < ζ n ∧ ζ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n, 0 < δ₀ n ∧ δ₀ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, (n : ℝ) + 1 ≤ Rn n) ∧ (∀ n : ℕ, n + 2 ≤ m₀ n) ∧
      ({K : ℕ → RetainedCoreHistory.{u}} → {j : ∀ n, Fin (K n).eventCount} → {t : ℕ → ℝ} →
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {Q T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} →
      {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} →
      {a₀ : ℝ} → (ha₀ : 0 < a₀) →
      (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        (pF n).delta ((K n).time i.succ) ≤ δ₀ n) →
      (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ ζ n) →
      (hrad : ∀ n : ℕ, Rn n ≤ (p n).modelRadius) →
      (hord : ∀ n : ℕ, m₀ n ≤ (p n).modelOrder) →
      (hbirth : ∀ n i hi b, max (Q n) 1 ≤ Cb n * ((recordsK n i hi).static b).neck.scale) →
      (hbirthA : ∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
      (hpinchK0 : ∀ n, (K n).EventSlabsPinched phi) →
      (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount)) →
      (hqR : ∀ n : ℕ, max ((n : ℝ) + 1) (Q n) <
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
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
      {κ Aκ : ℝ} → (hκ : 0 < κ) → (r ρV : ℕ → ℝ) →
      (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) →
      (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n) →
      (htime : ∀ n, 2 * r n ^ 2 < (Tn n : ℝ)) →
      (hsmallS : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n)) →
      (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2) →
      (hsepWK : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
        ∀ (i : Fin (K n).eventCount) (_hij : i.val < (j n).val) (hi : T₀ n ≤ (K n).time i.succ) b,
          (σ n : ℝ) - T / R n < (K n).time i.succ →
          2 * max (3 / (r n / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale) →
      (hdistW : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
          (σ n : ℝ) - T / R n ≤ v →
          (Kh n).activeStage v = (Kh n).activeStage (σ n) →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvs) x,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono (hvs.trans (hsT n))))
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))) →
      (hsepK : ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
        i.succ ≤ (j n).castSucc →
        t n - (K n).time i.succ ≤ (((recordsK n i hi).static b).neck.scale)⁻¹ →
        R n < c * ((recordsK n i hi).static b).neck.scale) →
      (hr : ∀ n, 0 < r n) → (A : ℝ) → (hA : 0 < A) → (hAκ : A + 3 ≤ Aκ) → (R0 : ℕ → ℝ) →
      (hR0 : ∀ n, 0 < R0 n) → (hR0R : ∀ n, R0 n ≤ R n) →
      (hLdef : ∀ n, L n = Real.sqrt (R0 n * r n ^ 2) / 4) →
      (hdiv : Tendsto (fun n => R0 n * r n ^ 2) atTop atTop) →
      (hball : ∀ n, y n ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono (hsT n))) ((A + 1) * r n)) →
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
      False) := by
  obtain ⟨c, hc, hall⟩ := cws_uniform_of_diagonal_P6SN.{u}
  obtain ⟨epsW, hepsW, hB⟩ := false_of_selection_eventSlab_late_closed_residual_cond_ev_P6SN.{u}
  refine ⟨c, hc, epsW, hepsW, fun ε hε hsmall hεW hεX hεN hεcone => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall hεW hεX hεN hεcone
  refine ⟨C, hC, fun {C1' C2' Ctime'} hC1 hC2 hCt => ?_⟩
  intro Ctime phi hphi
  obtain ⟨Cb, Rn, ζ, δ₀, m₀, hCb, hζ, hδ, hRb, hm₀, hdiag⟩ := hall Ctime
  refine ⟨Cb, Rn, ζ, δ₀, m₀, hCb, hζ, hδ, hRb, hm₀, ?_⟩
  intro K j t hjt htj Q T₀ p pF recordsK recordsF yG a₀ ha₀ hHI hcanK hδF hacc hrad hord hbirth
    hbirthA hpinchK0 hslabK hqR Kh hKh σ y R hσ hyG hRn hRpos d hT₀ Tn aSeed haT hsT has pT
    seedTrace L hL Cg hCg hgood hwin κ Aκ hκ r ρV hρV hroom htime hsmallS hclock hsepWK hdistW
    hsepK hr A hA hAκ R0 hR0 hR0R hLdef hdiv hball hκR hclosG hsel
  exact hB' hC1 hC2 hCt hphi hjt htj recordsF ha₀ hHI hcanK
    (fun n i hi => (hδF n i hi).trans (hδ n).2) (fun n => (hacc n).trans (hζ n).2)
    (fun n => (hRb n).trans (hrad n)) (fun n => (hm₀ n).trans (hord n))
    (fun n i hi b => hscaleK_of_diag_P6SN (hCb n).2 ((recordsK n i hi).static b).neck.scale_pos
      (hbirth n i hi b)) hpinchK0 hslabK hqR
    (Filter.Eventually.of_forall fun n =>
      hdiag hjt htj recordsF hHI hcanK hδF hacc hrad hord hslabK hbirth hbirthA n)
    Kh hKh σ y R hσ hyG hRn hRpos d hT₀ Tn aSeed haT hsT has pT seedTrace L hL Cg hCg hgood hwin
    hκ r ρV hρV hroom htime hsmallS hclock hsepWK hdistW hsepK hr A hA hAκ R0 hR0 hR0R hLdef hdiv
    hball hκR hclosG hsel


/-- **closed 主形残余形，(SEP) / (SEP′) 取 native 输入、(CWS) 取 diagonal 包（`_P6KD2`）**：
`…_native_P6SN` 的 `{η} hcws hη` 删去（`η := c` 由 G3 给），K 层 `hδF hacc hrad hord hscaleK` 换 diagonal
档 + `hbirth hbirthA`；证明经 `…_ev_diag_P6KD2`。 -/
theorem false_of_selection_eventSlab_late_closed_residual_cond_native_diag_P6KD2 :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, C ≤ C1' → C ≤ C2' → C.toNNReal ≤ Ctime' →
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ}, (hphi : Perelman.AdmissiblePinchingFunction phi) →
      ∃ (Cb Rn ζ δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ),
      (∀ n, 0 < Cb n ∧ Cb n ≤ 1 / ((n : ℝ) + 1) ^ 2) ∧
      (∀ n, 0 < ζ n ∧ ζ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n, 0 < δ₀ n ∧ δ₀ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, (n : ℝ) + 1 ≤ Rn n) ∧ (∀ n : ℕ, n + 2 ≤ m₀ n) ∧
      ({K : ℕ → RetainedCoreHistory.{u}} → {j : ∀ n, Fin (K n).eventCount} → {t : ℕ → ℝ} →
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {Q T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} →
      {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} →
      {a₀ : ℝ} → (ha₀ : 0 < a₀) →
      (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        (pF n).delta ((K n).time i.succ) ≤ δ₀ n) →
      (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ ζ n) →
      (hrad : ∀ n : ℕ, Rn n ≤ (p n).modelRadius) →
      (hord : ∀ n : ℕ, m₀ n ≤ (p n).modelOrder) →
      (hbirth : ∀ n i hi b, max (Q n) 1 ≤ Cb n * ((recordsK n i hi).static b).neck.scale) →
      (hbirthA : ∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
      (hpinchK0 : ∀ n, (K n).EventSlabsPinched phi) →
      (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount)) →
      (hqR : ∀ n : ℕ, max ((n : ℝ) + 1) (Q n) <
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) → (y : ∀ n, ((K n).toHistory.stageAt (σ
          n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hRpos : ∀ n, 0 < R n) →
      (d : GC.LongTime.Ch11.Pre841Data_C11K (fun n => (K n).toHistory) σ y R hRpos) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n) →
      (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) → (haT : ∀ n, aSeed n ≤ Tn n) →
      (hsT : ∀ n, σ n ≤ Tn n) → (has : ∀ n, aSeed n ≤ σ n) →
      (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier) →
      (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
        ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)) →
      (L : ℕ → ℝ) → (hL : Tendsto L atTop atTop) →
      (Cg : ℝ) → (hCg : 2 ≤ Cg) →
      (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
        ∀ z : ((K n).toHistory.stageAt v).Carrier,
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              ((seedTrace n).point ((K n).toHistory.activeStage v) ((K
                  n).toHistory.activeStage_mono hav)
                ((K n).toHistory.activeStage_mono (hvs.trans (hsT n)))) z ≤
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
                n))
                ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                    n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) →
          Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v)
              v) z →
          (K n).toHistory.HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z) →
      (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      {κ Aκ : ℝ} → (hκ : 0 < κ) → (r ρV : ℕ → ℝ) →
      (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) →
      (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n) →
      (htime : ∀ n, 2 * r n ^ 2 < (Tn n : ℝ)) →
      (hsmallS : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) (r n)) →
      (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2) →
      (hlate : ∀ n : ℕ, (n : ℝ) + 1 ≤ (Tn n : ℝ)) →
      (hsel4 : ∀ n, R n ≤ (d.native.params.neckRadius (Tn n) ^ 2)⁻¹) →
      (hδK : ∃ Tδ : ℝ, ∀ (n : ℕ) (τ : ℝ), Tδ ≤ τ →
        (p n).recenterConstant * (p n).delta τ ≤ 1 / 2) →
      (hnomId : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) h,
        (recordsK n i hi).nominalRadius h = (d.native.records n i).nominalRadius h) →
      (hdistW : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
            n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
          (σ n : ℝ) - T / R n ≤ v →
          (K n).toHistory.activeStage v = (K n).toHistory.activeStage (σ n) →
        ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v) ((K
            n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono hvs) x,
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              ((seedTrace n).point ((K n).toHistory.activeStage v) ((K
                  n).toHistory.activeStage_mono hav)
                ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
              (tr.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono
                  hvs)) ≤
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
                n))
                ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                    n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))) →
      (hr : ∀ n, 0 < r n) → (A : ℝ) → (hA : 0 < A) → (hAκ : A + 3 ≤ Aκ) → (R0 : ℕ → ℝ) →
      (hR0 : ∀ n, 0 < R0 n) → (hR0R : ∀ n, R0 n ≤ R n) →
      (hLdef : ∀ n, L n = Real.sqrt (R0 n * r n ^ 2) / 4) →
      (hdiv : Tendsto (fun n => R0 n * r n ^ 2) atTop atTop) →
      (hball : ∀ n, y n ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K
          n).toHistory.activeStage (σ n)) (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono
            (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) ((A + 1) * r n)) →
      (hκR : ∀ᶠ n in atTop, ∀ (j : Fin (K n).toHistory.eventCount) (c : ((K n).toHistory.stage
          j.castSucc).Carrier)
        (U : Set ((K n).toHistory.stage j.castSucc).Carrier) (a t ρU : ℝ),
        (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
        (∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (K n).toHistory.time j.castSucc < τ → (τ : ℝ) < (K n).toHistory.time j.succ →
          ∀ z ∈ U, ∀ zz cc : ((K n).toHistory.stageAt τ).Carrier, HEq zz z → HEq cc c →
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ) cc
                zz <
              ENNReal.ofReal ρU) →
        (∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (K n).toHistory.time j.castSucc < τ → (τ : ℝ) < (K n).toHistory.time j.succ →
          ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((K n).toHistory.stageAt τ).Carrier, HEq
              cc c →
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                ((seedTrace n).point ((K n).toHistory.activeStage τ) ((K
                    n).toHistory.activeStage_mono hav)
                  ((K n).toHistory.activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
              ENNReal.ofReal (Aκ * r n)) →
        ∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (K n).toHistory.time j.castSucc < τ → (τ : ℝ) < (K n).toHistory.time j.succ →
          ∀ z ∈ U, ∀ zz : ((K n).toHistory.stageAt τ).Carrier, HEq zz z →
          ∀ b : ℝ, 0 < b → b ≤ ρV n → (K n).toHistory.isParabolicallyRmControlledBall τ zz b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel ((K n).toHistory.stageAt τ).Carrier
                ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                (riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                    zz b)) →
      (hclosG : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
        ∀ᶠ n in atTop,
        ∀ (j' : Fin (K n).toHistory.eventCount) (v : ℝ), (K n).toHistory.time j'.castSucc < v →
          v < (K n).toHistory.time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
        ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
            (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (hjσ : j'.castSucc ≤ (K n).toHistory.activeStage (σ n))
          (tr : BackwardPointTrace (K n).toHistory j'.castSucc ((K n).toHistory.activeStage (σ n))
              hjσ x₁),
        ∀ (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
          (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)) (w : ((K n).toHistory.stage
              j'.castSucc).Carrier),
          riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v)
              ((seedTrace n).point j'.castSucc h1 h2) w ≤
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
                n))
                ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                    n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
          riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v)
              (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          R n ≤ ((K n).toHistory.event j').incoming.flow.scalar v w →
          ∀ x ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v) w
              (Rad / Real.sqrt (((K n).toHistory.event j').incoming.flow.scalar v w)),
          ∀ τ : ℝ, v - B / ((K n).toHistory.event j').incoming.flow.scalar v w ≤ τ → τ ≤ v →
            (K n).toHistory.time j'.castSucc < τ →
            riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric τ)
                ((seedTrace n).point j'.castSucc h1 h2) x ≤
              riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
                  (σ n))
                  ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                      n).toHistory.activeStage_mono (has n))
                    ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
                ENNReal.ofReal (L n / Real.sqrt (R n))) →
      (hsel : ∀ n, ¬ (K n).toHistory.HasSpatialCanonicalTimeControl ε C1' C2' Ctime' (σ n) (y n)) →
      False) := by
  obtain ⟨c, hc, epsW, hepsW, hB⟩ :=
    false_of_selection_eventSlab_late_closed_residual_cond_ev_diag_P6KD2.{u}
  refine ⟨epsW, hepsW, fun ε hε hsmall hεW hεX hεN hεcone => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall hεW hεX hεN hεcone
  refine ⟨C, hC, fun {C1' C2' Ctime'} hC1 hC2 hCt => ?_⟩
  intro Ctime phi hphi
  obtain ⟨Cb, Rn, ζ, δ₀, m₀, hCb, hζ, hδ, hRb, hm₀, hrest⟩ :=
    @hB' C1' C2' Ctime' hC1 hC2 hCt Ctime phi hphi
  refine ⟨Cb, Rn, ζ, δ₀, m₀, hCb, hζ, hδ, hRb, hm₀, ?_⟩
  intro K j t hjt htj Q T₀ p pF recordsK recordsF yG a₀ ha₀ hHI hcanK hδF hacc hrad hord hbirth
    hbirthA hpinchK0 hslabK hqR σ y R hσ hyG hRn hRpos d hT₀ Tn aSeed haT hsT has pT seedTrace L
    hL Cg hCg hgood hwin κ Aκ hκ r ρV hρV hroom htime hsmallS hclock hlate hsel4 hδK hnomId hdistW
    hr A hA hAκ R0 hR0 hR0R hLdef hdiv hball hκR hclosG hsel
  have hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale := fun n i hi b =>
    hscaleK_of_diag_P6SN (hCb n).2 ((recordsK n i hi).static b).neck.scale_pos (hbirth n i hi b)
  have hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop :=
    tendsto_atTop_mono (fun n => mul_le_mul_of_nonneg_right (hR0R n) (sq_nonneg _)) hdiv
  have hhalf : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ) := fun n => by
    have : 0 ≤ L n ^ 2 / R n := div_nonneg (sq_nonneg _) (hRpos n).le
    linarith [hroom n]
  have htT : ∀ n, t n ≤ (Tn n : ℝ) := fun n => by
    rw [← hσ n]
    exact hsT n
  have hhalf' : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ t n := fun n => by
    rw [← hσ n]
    exact hhalf n
  have hTn := tendsto_Tn_atTop_P6SN Tn hlate
  have hsmallK := recordsK_smallness_of_native_P6CD recordsK d.native hnomId
  have hsepWK := sepWK_of_smallness_P6CD recordsK (s := fun n => (σ n : ℝ)) hjt htT hhalf htime
    hRpos hRr hTn hsel4 hδK hsmallK
  have hsepK := sepK_eventually_of_smallness_P6CD hjt htT hhalf' htime hRpos hTn hsel4 hscaleK hδK
    hsmallK hc
  exact hrest hjt htj recordsF ha₀ hHI hcanK hδF hacc hrad hord hbirth hbirthA hpinchK0 hslabK
    hqR (fun n => (K n).toHistory) rfl σ y R hσ hyG hRn hRpos d hT₀ Tn aSeed haT hsT has pT
    seedTrace L hL Cg hCg hgood hwin hκ r ρV hρV hroom htime hsmallS hclock hsepWK hdistW hsepK hr
    A hA hAκ R0 hR0 hR0R hLdef hdiv hball hκR hclosG hsel

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
