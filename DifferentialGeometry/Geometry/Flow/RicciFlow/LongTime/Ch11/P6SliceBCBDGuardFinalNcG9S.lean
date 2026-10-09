import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDGuardAlignedA2B
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDGuardFinalSupplyG9S
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceHistoryBridgeFinalP6M

/-!
# guarded `hnc` 的 final-slab 孪生（O-CH11-G9SHIFT G6，后缀 `_G9S`）

BCBD-A2 G5 `tested_kappaG_window_sameStage / hnc_window_sameStageG / hnc_window_of_freshG`
的 final 换帧（P6M `tested_kappa_window_final / hnc_window_final` 加 c⋆ guard 与同 stage 条件）：
桥用 `tested_noncollapse_final_P6M`（`a := T`，guard 对 `τ ≥ T` 单调）。
`hkappaSG_of_fresh_A2B` 帧通用，直接复用。生成器 `gen/genF2.py`。无新分析、无新 binder。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **单 history 同 stage tested κ，guarded，final（`_G9S`）**：A2B 同名引理换帧。 -/
theorem RetainedCoreHistory.tested_kappaGF_window_final_G9S (K : RetainedCoreHistory.{u})
    (hfin : K.time (Fin.last K.eventCount) < K.horizon)
    (G : (K.stage (Fin.last K.eventCount)).IncomingSlab (K.time (Fin.last K.eventCount)) K.horizon)
    (hG : G = (K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl)
    {t : ℝ} (htl : K.time (Fin.last K.eventCount) < t)
    (σ : Icc (0 : ℝ) K.toHistory.horizon) (hσ : (σ : ℝ) = t)
    (y : (K.toHistory.stageAt σ).Carrier) (yG : (K.stage (Fin.last K.eventCount)).Carrier) (hyG :
        HEq y yG)
    {κ ρ Rad θ qg cg : ℝ} (hκ : 0 ≤ κ)
    (hK : ∀ x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y Rad,
      ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hvt : v ≤ σ), (σ : ℝ) - θ ≤ v →
      K.toHistory.activeStage v = K.toHistory.activeStage σ →
      ((σ : ℝ) - v) * max qg (metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
        x) ≤ cg →
      ∀ tr : BackwardPointTrace K.toHistory (K.toHistory.activeStage v)
        (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρ →
        K.toHistory.isParabolicallyRmControlledBall v
          (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvt)) r'') :
    ∀ (τ : Icc (0 : ℝ) K.toHistory.horizon), t - θ ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
      K.time (Fin.last K.eventCount) < τ → (τ : ℝ) < K.horizon →
      ∀ z ∈ riemannianBallOf (G.flow.base.metric t) yG Rad,
      (t - τ) * max qg (G.flow.scalar t z) ≤ cg →
      ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
      ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
            (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
            (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b) := by
  intro τ haτ hτt hjτ _ z hz hg zz hzz b hb hbρ hball
  have hσact : K.toHistory.activeStage σ = Fin.last K.eventCount :=
    K.toHistory.activeStage_eq_last_of_time_last_le σ (by rw [hσ]; exact htl.le)
  have hτact : K.toHistory.activeStage τ = Fin.last K.eventCount :=
    K.toHistory.activeStage_eq_last_of_time_last_le τ hjτ.le
  have hvt : τ ≤ σ := show (τ : ℝ) ≤ σ by rw [hσ]; exact hτt
  let x : (K.toHistory.stageAt σ).Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hσact.symm) z
  have hxz : HEq x z := cast_heq _ _
  have hx : x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y Rad :=
    K.mem_ball_final_G9S hfin G hG hσact.symm σ Rad z yG x y hxz hyG (by rw [hσ]; exact hz)
  obtain ⟨tr, htr⟩ := exists_trace_of_stage_eq_P6SB K.toHistory (hτact.trans hσact.symm)
    (K.toHistory.activeStage_mono hvt) x
  have hθ' : (σ : ℝ) - θ ≤ τ := by rw [hσ]; exact haτ
  have hpt : tr.point (K.toHistory.activeStage τ) le_rfl (K.toHistory.activeStage_mono hvt) = zz :=
    eq_of_heq (htr.trans (hxz.trans hzz.symm))
  have hball' : K.toHistory.isParabolicallyRmControlledBall τ
      (tr.point (K.toHistory.activeStage τ) le_rfl (K.toHistory.activeStage_mono hvt)) b := by
    rw [hpt]
    exact hball
  have hg' : ((σ : ℝ) - τ) * max qg (metricScalarAt (K.toHistory.stageMetric
      (K.toHistory.activeStage σ) σ) x) ≤ cg := by
    rw [K.scalar_final_G9S hfin G hG hσact.symm σ z x hxz, hσ]
    exact hg
  have h := hK x hx τ hvt hθ' (hτact.trans hσact.symm) hg' tr b hb hbρ hball'
  rw [hpt, ENNReal.ofReal_mul hκ, ENNReal.ofReal_pow hb.le] at h
  exact h

/-- **guarded kernel `hnc`（同 stage，final，`_G9S`）**：A2B 同名引理换帧，桥 `tested_noncollapse_final_P6M`。 -/
theorem ObservedHistory.hnc_window_sameStageGF_G9S {K : ℕ → RetainedCoreHistory.{u}} {Cg : ℝ}
    {Ctime' : ℝ≥0} (hCg0 : 0 ≤ Cg)
    {t : ℕ → ℝ} (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n)
    (htK : ∀ n, t n < (K n).horizon)
    (G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon)
    (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n))
    {κ : ℝ} (hκ : 0 < κ) (ρnc : ℕ → ℝ)
    (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      (K n).toHistory.activeStage v = (K n).toHistory.activeStage (σ n) →
      ((σ n : ℝ) - v) * max (Cg * R n) (metricScalarAt ((K n).toHistory.stageMetric
        ((K n).toHistory.activeStage (σ n)) (σ n)) x) ≤ 1 / (2 * max (Ctime' : ℝ) 1) →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
        ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
        (K n).toHistory.isParabolicallyRmControlledBall v
          (tr.point ((K n).toHistory.activeStage v) le_rfl
            ((K n).toHistory.activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            (tr.point ((K n).toHistory.activeStage v) le_rfl
              ((K n).toHistory.activeStage_mono hvt)) r'') :
    ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ (T : ℝ)
      (hT : ((K n).prefixAt (Fin.last (K n).eventCount)).time
        (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) < T)
      (hTs : T < (K n).horizon), T ≤ t n →
        t n - B / (G n).flow.scalar (t n) (yG n) ≤ T →
        let Bh := ((K n).prefixAt (Fin.last (K n).eventCount)).extendHorizon T
          ((K n).prefixAt_time_last _ ▸ hT.le)
          ((G n).closedPrefix T hT hTs)
          (by rw [hG n]; exact (K n).final_initial ((htl n).trans (htK n)))
        let tm : Icc (0 : ℝ) Bh.horizon :=
          ⟨T, ((K n).prefixAt (Fin.last (K n).eventCount)).horizon_nonneg.trans
            ((K n).prefixAt_time_last _ ▸ hT.le), le_rfl⟩
        ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (yG n)
            (Rad / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
        (t n - T) * max (Cg * R n) ((G n).flow.scalar (t n) z) ≤
          1 / (2 * max (Ctime' : ℝ) 1) →
        ∀ (yy : (Bh.toHistory.stageAt tm).Carrier), HEq yy z →
        ∀ (b : ℝ), 0 < b → b ≤ ρnc n →
          Bh.toHistory.isParabolicallyRmControlledBall tm yy b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (Bh.toHistory.stageAt tm).Carrier
                (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                (riemannianBallOf (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                  yy b) := by
  intro Rad B
  filter_upwards [hkappa (max Rad 1) (max B 1) (by positivity) (by positivity)] with n hn
  have hfin : (K n).time (Fin.last (K n).eventCount) < (K n).horizon := (htl n).trans (htK n)
  have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr (hR n)
  have hsingle := (K n).tested_kappaGF_window_final_G9S hfin (G n) (hG n) (htl n) (σ n) (hσ n)
    (y n) (yG n) (hyG n) (Rad := max Rad 1 / Real.sqrt (R n)) (θ := max B 1 / R n)
    (qg := Cg * R n) (cg := 1 / (2 * max (Ctime' : ℝ) 1)) hκ.le hn
  have hU : ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (yG n)
      (Rad / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
      z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (yG n)
        (max Rad 1 / Real.sqrt (R n)) := by
    intro z hz
    rw [← hRn n] at hz
    exact riemannianBallOf_mono _ _ (div_le_div_of_nonneg_right (le_max_left _ _) hsR.le) hz
  intro T hT hTs hTt hBT
  have hBT' : t n - max B 1 / R n ≤ T := by
    rw [← hRn n] at hBT
    have : B / R n ≤ max B 1 / R n := div_le_div_of_nonneg_right (le_max_left _ _) (hR n).le
    linarith
  have hbridge := (K n).tested_noncollapse_final_P6M hfin (a := T) (t := t n)
    (ρ := ρnc n)
    {z | z ∈ riemannianBallOf ((G n).flow.base.metric (t n))
        (yG n) (Rad / Real.sqrt ((G n).flow.scalar (t n) (yG n)))
      ∧ (t n - T) * max (Cg * R n) ((G n).flow.scalar (t n) z) ≤
        1 / (2 * max (Ctime' : ℝ) 1)}
    (fun τ haτ hτt hjτ hτj z hz zz hzz b hb hbρ hball => by
      have hM : 0 ≤ max (Cg * R n) ((G n).flow.scalar (t n) z) :=
        (mul_nonneg hCg0 (hR n).le).trans (le_max_left _ _)
      have hgτ : (t n - τ) * max (Cg * R n) ((G n).flow.scalar (t n) z) ≤
          1 / (2 * max (Ctime' : ℝ) 1) :=
        (mul_le_mul_of_nonneg_right (by linarith) hM).trans hz.2
      exact hsingle τ (hBT'.trans haτ) hτt hjτ hτj z (hU z hz.1) hgτ zz hzz b hb hbρ hball)
    ((K n).prefixAt_time_last _)
  obtain rfl : G = fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl := funext hG
  intro Bh tm z hz hg
  exact hbridge T hT hTs hTt le_rfl z ⟨hz, hg⟩

/-- **guarded kernel `hnc` ⇐ FRESH + `hdistWG`，final（`_G9S`）**：A2B 同名引理换帧。 -/
theorem ObservedHistory.hnc_window_of_freshGF_G9S {K : ℕ → RetainedCoreHistory.{u}} {Cg : ℝ}
    {Ctime' : ℝ≥0} (hCg0 : 0 ≤ Cg)
    {t : ℕ → ℝ} (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n)
    (htK : ∀ n, t n < (K n).horizon)
    (G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon)
    (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hRlim : Tendsto R atTop atTop)
    (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n))
    {nr : ℝ → ℝ} {Aκ κ Tκ r : ℝ} (hκ : 0 < κ) (hr : 0 < r)
    (hWK : ∀ n, KappaSeedWindowFwd_C11PK nr Aκ κ Tκ (K n).toHistory)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hTκ : ∀ n, Tκ ≤ (Tn n : ℝ)) (htimeS : ∀ n, 2 * r ^ 2 < (Tn n : ℝ))
    (hsmallS : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) r)
    (hvolS : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r ^ 3) ≤ ballVolume ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (Tn n)) (Tn n)) (pT n) r)
    (hnrS : ∀ n (w : ℝ), (Tn n : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr w ≤ r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (hwinF : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r ^ 2 / 2 ≤ (σ n : ℝ) - T / R n)
    (hgate : ∀ᶠ n in atTop,
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r))
    (hdistWG : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (K n).toHistory.activeStage v = (K n).toHistory.activeStage (σ n) →
        ((σ n : ℝ) - v) * max (Cg * R n) (metricScalarAt ((K n).toHistory.stageMetric
          ((K n).toHistory.activeStage (σ n)) (σ n)) x) ≤ 1 / (2 * max (Ctime' : ℝ) 1) →
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
            ENNReal.ofReal (L n / Real.sqrt (R n))) :
    Tendsto (fun n => r / 200 * Real.sqrt ((G n).flow.scalar (t n) (yG n))) atTop atTop ∧
    ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ (T : ℝ)
      (hT : ((K n).prefixAt (Fin.last (K n).eventCount)).time
        (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) < T)
      (hTs : T < (K n).horizon), T ≤ t n →
        t n - B / (G n).flow.scalar (t n) (yG n) ≤ T →
        let Bh := ((K n).prefixAt (Fin.last (K n).eventCount)).extendHorizon T
          ((K n).prefixAt_time_last _ ▸ hT.le)
          ((G n).closedPrefix T hT hTs)
          (by rw [hG n]; exact (K n).final_initial ((htl n).trans (htK n)))
        let tm : Icc (0 : ℝ) Bh.horizon :=
          ⟨T, ((K n).prefixAt (Fin.last (K n).eventCount)).horizon_nonneg.trans
            ((K n).prefixAt_time_last _ ▸ hT.le), le_rfl⟩
        ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (yG n)
            (Rad / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
        (t n - T) * max (Cg * R n) ((G n).flow.scalar (t n) z) ≤
          1 / (2 * max (Ctime' : ℝ) 1) →
        ∀ (yy : (Bh.toHistory.stageAt tm).Carrier), HEq yy z →
        ∀ (b : ℝ), 0 < b → b ≤ r / 200 →
          Bh.toHistory.isParabolicallyRmControlledBall tm yy b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (Bh.toHistory.stageAt tm).Carrier
                (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                (riemannianBallOf (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                  yy b) := by
  refine ⟨?_, ?_⟩
  · have hs : Tendsto (fun n => Real.sqrt (R n)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp hRlim
    refine (hs.const_mul_atTop (by positivity : (0 : ℝ) < r / 200)).congr fun n => ?_
    rw [hRn n]
  · exact hnc_window_sameStageGF_G9S hCg0 htl htK G hG σ hσ y yG hyG R hRpos hRn hκ
      (fun _ => r / 200)
      (hkappaSG_of_fresh_A2B hWK Tn aSeed σ haT hsT has pT seedTrace y R L hRpos hL hTκ
        htimeS hsmallS hvolS hnrS hclock hwinF hgate hdistWG)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
