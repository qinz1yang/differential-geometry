import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GapWireKP6WR
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ClosedResidualP6R2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KDataSupplyP6D

/-!
# P6REST2 closed residual 形的 K 层接线（S-CH11-P6WIRE G3，后缀 `_P6WR`）

closed 主形（原尺度，数据在前）`false_of_selection_eventSlab_late_closed_residual_P6R2` 的 K 层 binder
（`Ctime phi hphi pF recordsF a₀ ha₀ hHI hpinchK0 hslabK`）由已有 producer 供给，`K n := F.tower.history
(ind n)`；`Q n := qcanSup S horizon_n`（ch12 F2 band 阈值）、`T₀ := lateThrFree_P6WR Sg …`
（`Sg n := (n+1)·max (n+1) (Q n)`，与 `ind`、selection 无关）都是**显式**项，因此 selection 侧的 `hqR` /
`hT₀` 读得出。**INTEGRATION-ONLY / PROVISIONAL**。

**`false_of_selection_eventSlab_late_closed_residual_wired_P6WR`**：残余 binder = `p recordsK` 及其 6 条
producer 事实（`hcanK hδF hacc hrad hord hscaleK`；由 `exists_lateThr_free_P6WR` 供给，见文件末 example）
+ selection 侧 OPEN 项（逐字同 `…_closed_residual_P6R2`）：`hqR`（`Q < R`，S2：band 阈值 vs
`R ≤ ρ⁻²`）、`hcws` / `hsepK` / `hsepWK` / `htr`（(CWS)(SEP′)(SEP)(TR)）、`d`（原尺度；FINEPACK / CXSK /
SEEDWIN-P producer 需要 `hvol` + 块数据，未接）、κ 组（`hκ hρV hκR`，CXSK 区域结论）、`hclosG`、
`hroom`（`hP6R` 给）等。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

/-- `Sg n := (n+1)·max (n+1) Q ≥ 1`（`lateThrFree_P6WR` 的目标下界）。 -/
theorem one_le_scaleTarget_P6WR (n : ℕ) (Q : ℝ) :
    1 ≤ ((n : ℝ) + 1) * max ((n : ℝ) + 1) Q := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h : (n : ℝ) + 1 ≤ max ((n : ℝ) + 1) Q := le_max_left _ _
  nlinarith

/-- **closed residual 形的 K 层接线（`_P6WR`）**：见文件头。 -/
theorem false_of_selection_eventSlab_late_closed_residual_wired_P6WR :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, C ≤ C1' → C ≤ C2' → C.toNNReal ≤ Ctime' →
      ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
        {q : CutoffParameters},
      (hanti : AntitoneOn q.neckRadius (Ici 0)) →
      (hP5L : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q) →
      (hδq : Tendsto q.delta atTop (𝓝 0)) →
      GC.LongTime.Ch11.CutoffRecords_C11S F q →
      ∀ {pBase : CutoffParameters} {Cb : GC.GeneralFlow.ClosedBirthConstants}
        (S : GC.GeneralFlow.PreparedSpatialChain pBase Cb P g) (εcut Dcut : ℕ → ℝ)
        (mcut : ℕ → ℕ),
      (∀ m, GC.GeneralFlow.PreparedSpatialStepRetention (S.state m) (S.state (m + 1))
        (S.accuracy m) (1 / ((m : ℝ) + 2)) (εcut m) (Dcut m) (mcut m)) →
      (∀ m, (S.state (m + 1)).shift =
        (S.state m).history.time (Fin.last (S.state m).history.eventCount)) →
      (∀ m, (S.state (m + 1)).offset = (S.state m).history.eventCount) →
      F.tower = S.tower →
      ∀ (ind : ℕ → ℕ),
      let K : ℕ → RetainedCoreHistory.{u} := fun n => F.tower.history (ind n)
      let Q : ℕ → ℝ := fun n => GC.LongTime.Ch11.qcanSup_P6WR S (K n).horizon
      let T₀ : ℕ → ℝ := lateThrFree_P6WR (fun n => ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n))
        (fun n => one_le_scaleTarget_P6WR n (Q n)) hP5L hδq hanti
      {p : ℕ → CutoffParameters} →
      {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (p n)} →
      (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        q.delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) →
      (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
      (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) →
      (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder) →
      (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
        ((recordsK n i hi).static b).neck.scale) →
      {j : ∀ n, Fin (K n).eventCount} → {t : ℕ → ℝ} →
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} →
      (hqR : ∀ n : ℕ, max ((n : ℝ) + 1) (Q n) <
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      {η : ℝ} →
      (hcws : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ (j n).castSucc) (z : ((K n).stage (j n).castSucc).Carrier)
        (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl z)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x →
        ‖x.val‖ < ((n : ℝ) + 1) + 1 →
        t n - (K n).time i.succ ≤
          (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹ →
        η * ((recordsK n i hi).static b).neck.scale ≤
          ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z) →
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
      (htr : ∀ D T : ℝ, 0 < D → 0 < T → ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ᶠ n in atTop,
        (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n)) (T / R n) (Kc * R n)) →
      (hsepK : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
        i.succ ≤ (j n).castSucc →
        t n - (K n).time i.succ ≤ (((recordsK n i hi).static b).neck.scale)⁻¹ →
        R n < η * ((recordsK n i hi).static b).neck.scale) →
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
      False := by
  obtain ⟨epsW, hepsW, h⟩ := false_of_selection_eventSlab_late_closed_residual_P6R2.{u}
  refine ⟨epsW, hepsW, fun ε hε hs hW hX hN hc => ?_⟩
  obtain ⟨C, hC, h'⟩ := h ε hε hs hW hX hN hc
  refine ⟨C, hC, ?_⟩
  intro C1' C2' Ctime' hC1 hC2 hCt P g F q hanti hP5L hδq records pBase Cb S εcut Dcut mcut W
    hshift hoffset hTower ind K Q T₀ p recordsK hcanK hδF hacc hrad hord hscaleK j t hjt htj yG hqR
    η hcws Kh hKh σ y R hσ hyG hRn hRpos d hT₀ Tn aSeed haT hsT has pT seedTrace L hL Cg hCg hgood
    hwin κ Aκ hκ r ρV hρV hroom htime hsmallS hclock hsepWK htr hsepK hr A hA hAκ R0 hR0 hR0R hLdef
    hdiv hball hκR hclosG hsel
  obtain ⟨a₀, ha₀, hHI⟩ := exists_initialHI_P6WR F
  obtain ⟨phi, hphi, hP⟩ := exists_phi_eventSlabsPinched_P6D P g
  exact h' hC1 hC2 hCt hphi hjt htj (fun n i => records (ind n) i) ha₀ (fun n x => hHI (ind n) x)
    hcanK hδF hacc hrad hord hscaleK
    (fun n => hP (K n) ⟨F.tower.initial (ind n)⟩ q (records (ind n)))
    (fun n => GC.LongTime.Ch11.eventSlabsDerivative_qcanSup_P6WR S εcut Dcut mcut W hshift
      hoffset F hTower (ind n))
    hqR hcws Kh hKh σ y R hσ hyG hRn hRpos d hT₀ Tn aSeed haT hsT has pT seedTrace L hL Cg hCg
    hgood hwin hκ r ρV hρV hroom htime hsmallS hclock hsepWK htr hsepK hr A hA hAκ R0 hR0 hR0R
    hLdef hdiv hball hκR hclosG hsel

/-- **consumer**：producer 事实（`exists_lateThr_free_P6WR`，`T₀ := lateThrFree_P6WR Sg …`）恰好是
`false_of_selection_eventSlab_late_closed_residual_wired_P6WR` 的 `p recordsK hcanK … hscaleK` 位：
对任一 `ind`，`T₀ ≥ Tmin` 时 `p recordsK` 与六条事实存在（`le_rfl`）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hP5L : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q)
    (hδq : Tendsto q.delta atTop (𝓝 0)) (Q : ℕ → ℝ) (ind : ℕ → ℕ) :
    ∃ (p : ℕ → CutoffParameters)
      (recordsK : ∀ n (i : Fin (F.tower.history (ind n)).eventCount),
        lateThrFree_P6WR (fun n => ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n))
          (fun n => one_le_scaleTarget_P6WR n (Q n)) hP5L hδq hanti n ≤
          (F.tower.history (ind n)).time i.succ →
        GeometricCutoffRecord (F.tower.history (ind n)).toHistory i (p n)),
      (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
      (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) ∧
      (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) ∧
      (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
        ((recordsK n i hi).static b).neck.scale) ∧
      (∀ n (i : Fin (F.tower.history (ind n)).eventCount),
        lateThrFree_P6WR (fun n => ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n))
          (fun n => one_le_scaleTarget_P6WR n (Q n)) hP5L hδq hanti n ≤
          (F.tower.history (ind n)).time i.succ →
        q.delta ((F.tower.history (ind n)).time i.succ) ≤ 1 / ((n : ℝ) + 1)) :=
  Classical.choose_spec (exists_lateThr_free_P6WR (fun n => ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n))
    (fun n => one_le_scaleTarget_P6WR n (Q n)) hP5L hδq hanti) _ (fun _ => le_rfl) ind

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
