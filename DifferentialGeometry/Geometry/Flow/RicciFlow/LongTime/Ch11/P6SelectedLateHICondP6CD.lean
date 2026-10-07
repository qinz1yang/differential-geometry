import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ClosedHICondP6CD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SelectedLateHIP6X2

/-!
# P6SEL3 hclos 链入口换接：event 内部类的条件化（O-CH11-P6COND G2b，后缀 `_P6CD`）

`false_of_selected_eventInterior_lateHI_cond_P6CD`：P6SEL3 hclos 链（`eventBranch_lateHI_P6X2` →
`hPN_of_pureClass_lateHI_P6X2` → `canonicalLateCore_of_lateHI_P6X2` →
`canonicalLateCore_of_normalized_full_P6X3` → `canonicalLateCore_of_normalized_hclos_P6X3` /
`s15_of_normalized_hclos_P6X3`）唯一直接消费 closed 主形的入口（`P6SelectedLateHIP6X2`）的条件化版。
文件末 `example`：新形推出旧入口（方向核）。上层四层的 gap 元组
`hdistQ` 分量逐字换成 `hdistC ∧ hdistW` 即可沿用本定理（剩余接线见 DELIVERIES G2 块）。
由 build-logs/scratch/O-CH11-P6COND/mk_g2b3.py 从 tracked 文本生成。
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

/-- **event 内部类，条件化（`_P6CD`）**：P6SEL2 G1a `false_of_selected_eventInterior_lateHI_P6X2` 的 binder
逐字，`hdistQ` → `hdistC`（HDISTC 形）+ `hdistW`（(TR₀)）；证明改调条件化 lateHI closed 主形。 -/
theorem false_of_selected_eventInterior_lateHI_cond_P6CD :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, C ≤ C1' → C ≤ C2' → C.toNNReal ≤ Ctime' →
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ}, (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} →
      {Q T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} →
      {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) →
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
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (hpos : ∀ n, ∃ j : Fin (Kh n).eventCount, (Kh n).time j.castSucc < (σ n : ℝ) ∧
        (σ n : ℝ) < (Kh n).time j.succ) →
      (R : ℕ → ℝ) →
      (hRdef : ∀ n, R n =
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)) →
      (hRpos : ∀ n, 0 < R n) →
      (hRlt : ∀ n : ℕ, (n : ℝ) + 1 < R n) → (hQR : ∀ n, Q n < R n) →
      (hcwpL : ∀ (n : ℕ) (j' : Fin (K n).eventCount) (yG' : ((K n).stage j'.castSucc).Carrier),
        HEq (y n) yG' →
        (∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ j'.castSucc)
        (A : BackwardPointTrace (K n).toHistory i.succ j'.castSucc hl yG')
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          (σ n : ℝ) - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹) →
        (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' (σ n) (y n)) →
      (d : GC.LongTime.Ch11.Pre841Data_C11K Kh σ y R hRpos) →
      (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (haT : ∀ n, aSeed n ≤ Tn n) →
      (hsT : ∀ n, σ n ≤ Tn n) → (has : ∀ n, aSeed n ≤ σ n) →
      (hT₀a : ∀ n, T₀ n ≤ (aSeed n : ℝ)) →
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
      (hdistC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
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
              ENNReal.ofReal (L n / 4 / Real.sqrt (R n))) →
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
  obtain ⟨epsW, hepsW, hB⟩ := false_of_selection_eventSlab_lateHI_closed_cond_P6CD.{u}
  refine ⟨epsW, hepsW, fun ε hε hsmall hεW hεX hεN hεcone => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall hεW hεX hεN hεcone
  refine ⟨C, hC, fun {C1' C2' Ctime'} hC1 hC2 hCt => ?_⟩
  intro Ctime phi hphi K Q T₀ p pF recordsK recordsF a₀ hHI hcanK hδF hacc hrad hord hscaleK
    hbirthA hpinchK0 hslabK Kh hKh σ y hpos R hRdef hRpos hRlt hQR hcwpL d Tn aSeed haT hsT has
    hT₀a pT seedTrace L hL Cg hCg hgood hwin hdistC hdistW κ Aκ hκ r ρV hρV hroom hdistσ hκR
    hclosG hsel
  subst hKh
  have hev := RetainedCoreHistory.eventInterior_data_P6X σ y hpos
  obtain ⟨j, yG, hjt, htj, hyG, hsc⟩ := hev
  have hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n) (yG n) :=
    fun n => (hRdef n).trans (hsc n)
  have hqR : ∀ n : ℕ, max ((n : ℝ) + 1) (Q n) <
      ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n) (yG n) := fun n => by
    rw [← hRn n]
    exact max_lt (hRlt n) (hQR n)
  have hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n := by
    intro B
    rcases le_or_gt B 0 with hB0 | hB0
    · refine Eventually.of_forall fun n => ?_
      have h1 : (aSeed n : ℝ) ≤ σ n := has n
      have h2 : B / R n ≤ 0 := div_nonpos_of_nonpos_of_nonneg hB0 (hRpos n).le
      linarith [hT₀a n]
    · filter_upwards [hwin B hB0] with n hn
      linarith [hT₀a n]
  exact hB' hC1 hC2 hCt hphi (K := K) (t := fun n => (σ n : ℝ)) hjt htj (recordsK := recordsK)
    recordsF hHI hcanK hδF hacc hrad hord hscaleK hbirthA hpinchK0 hslabK hqR
    (fun n hC => hsel n (hcwpL n (j n) (yG n) (hyG n) hC)) _ rfl σ y R (fun _ => rfl) hyG hRn
    hRpos d hT₀ Tn aSeed haT hsT has pT seedTrace L hL Cg hCg hgood hwin hdistC hdistW hκ r ρV hρV
    hroom hdistσ hκR hclosG hsel

/-- consumer（方向核）：旧入口 `false_of_selected_eventInterior_lateHI_P6X2` ⇐ 新入口（`hdistQ` ⇒
`hdistC`、`hdistW`）。 -/
example : type_of% @false_of_selected_eventInterior_lateHI_P6X2.{u} := by
  obtain ⟨epsW, hepsW, hB⟩ := false_of_selected_eventInterior_lateHI_cond_P6CD.{u}
  refine ⟨epsW, hepsW, fun ε hε hsmall hεW hεX hεN hεcone => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall hεW hεX hεN hεcone
  refine ⟨C, hC, fun {C1' C2' Ctime'} hC1 hC2 hCt => ?_⟩
  intro Ctime phi hphi K Q T₀ p pF recordsK recordsF a₀ hHI hcanK hδF hacc hrad hord hscaleK
    hbirthA hpinchK0 hslabK Kh hKh σ y hpos R hRdef hRpos hRlt hQR hcwpL d Tn aSeed haT hsT has
    hT₀a pT seedTrace L hL Cg hCg hgood hwin hdistQ κ Aκ hκ r ρV hρV hroom hdistσ hκR hclosG hsel
  exact hB' hC1 hC2 hCt hphi recordsF hHI hcanK hδF hacc hrad hord hscaleK hbirthA hpinchK0 hslabK
    Kh hKh σ y hpos R hRdef hRpos hRlt hQR hcwpL d Tn aSeed haT hsT has hT₀a pT seedTrace L hL Cg
    hCg hgood hwin
    (fun φ hφ D T _ hD hT _ _ => (hdistQ D T hD hT).filter_mono hφ.tendsto_atTop)
    (fun D T hD hT => by
      filter_upwards [hdistQ D T hD hT, hL.eventually_ge_atTop 0] with n hn hL0
      intro x hx v hav hvs hvT _ tr
      refine (hn x hx v hav hvs hvT tr).trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
      exact div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))
    hκ r ρV hρV hroom hdistσ hκR hclosG hsel

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
