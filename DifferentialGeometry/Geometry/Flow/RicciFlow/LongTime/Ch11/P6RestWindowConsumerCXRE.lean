import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CloseLateCgP6S3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaRegionalCenterC11Q4

/-!
# P6 closed-Cg 主形的实际 regional-kappa 接线（CX-REST）

保留原主形的常数顺序，在同一 raw tower 子序列上用 window κ 与实际 seed K0 数据
生产原 `hκR`，并在证明体内直接消费；`ρV := r/200` 与原 `hradii` 对齐。
没有导入未提交 P6R WIP，也没有新增 regional-kappa 假设的包装。
`hroom / hdistσ / hdistQ / hclosG / hnotK` 仍明示保留，window κ 也仍须由 κ 线供给。
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

/-- 实际 closed-Cg consumer：原 `hκR` 由 tracked window theorem 与同源 seed 数据支付。 -/
theorem false_of_selection_eventSlab_window_CXRE :
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
      {a₀ : ℝ} → (ha₀ : 0 < a₀) →
      (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) →
      (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
      (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) →
      (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder) →
      (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
        ((recordsK n i hi).static b).neck.scale) →
      (hpinchK0 : ∀ n, (K n).EventSlabsPinched phi) →
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
      {κ Aκ : ℝ} → (hκ : 0 < κ) → (r : ℕ → ℝ) →
      (hradii : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop) →
      (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n) →
      (hdistσ : ∀ᶠ n in atTop,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n)) →
      (P : OrientedThreeStage.{u}) → (g : P.Metric) →
      (F : GC.Interface.RawSurgery P g) → (m : ℕ → ℕ) →
      (hK : K = fun n => F.tower.history (m n)) →
      (hW : GC.LongTime.Ch11.LocalKappaWindowAt_P6B F (fun _ => 0) Aκ κ) →
      (hTn : Tendsto (fun n => (Tn n : ℝ)) atTop atTop) →
      (htime : ∀ n, 2 * r n ^ 2 < (Tn n : ℝ)) →
      (hsmallSeed : ∀ n,
        GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n)) →
      (hvol : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r n ^ 3) ≤
        Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n))
          (pT n) (r n)) →
      (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2) →
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
  obtain ⟨epsW, hepsW, hB⟩ := false_of_selection_eventSlab_late_closed_Cg_P6S3.{u}
  refine ⟨epsW, hepsW, fun ε hε hsmall hεW hεX hεN hεcone => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall hεW hεX hεN hεcone
  refine ⟨C, hC, fun {C1' C2' Ctime'} hC1 hC2 hCt => ?_⟩
  intro Ctime phi hphi K j t hjt htj Q T₀ p pF recordsK recordsF yG a₀ ha₀ hHI hcanK hδF hacc hrad
    hord hscaleK hpinchK0 hslabK hqR hnotK Kh hKh σ y R hσ hyG hRn hRpos d hT₀ Tn aSeed haT hsT has
    pT seedTrace L hL Cg hCg hgood hwin hdistQ κ Aκ hκ r hradii hroom hdistσ P g F m hK hW hTn
    htime hsmallSeed hvol hclock hclosG hsel
  refine hB' hC1 hC2 hCt hphi hjt htj recordsF ha₀ hHI hcanK hδF hacc hrad hord hscaleK
    hpinchK0 hslabK hqR hnotK Kh hKh σ y R hσ hyG hRn hRpos d hT₀ Tn aSeed haT hsT has pT
    seedTrace L hL Cg hCg hgood hwin hdistQ hκ r (fun n => r n / 200) hradii hroom hdistσ ?_
    hclosG hsel
  subst hKh
  subst hK
  obtain ⟨T, -, hregion⟩ :=
    GC.LongTime.Ch11.regionalKappa_of_window_center_half_C11Q4 hκ.le hW
  filter_upwards [hTn.eventually_ge_atTop T] with n hn
  intro j' c U a v ρU ha hv hUc hdistV τ haτ hτv hs1 hs2 z hz zz hzz b hb hbr hball
  exact hregion (m n) (Tn n) (pT n) (r n) hn (htime n) (hsmallSeed n) (hvol n) (aSeed n)
    (haT n) (hclock n) (seedTrace n) j' c U a v ρU ha hv hUc hdistV τ haτ hτv hs1 hs2 z hz
    zz hzz b hb hbr hball

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
