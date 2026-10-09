import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J11StayDrvJ11S
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PickedBallKappaC11PK

/-!
# driver `hkappaC`（hPN interior 中心）⇐ driver records 包 + FRESH（无 `hfamT`；O-CH11-J11STAY G7，`_J11S`）

G2 `hkappaC_driver_interior_J11S` 的孪生：`hfamT` 换成 driver 在同一中心的 records 包（G4
`hstayK_of_drv_J11S` 的输入，= DEPTH4C2 anyPos driver `recordsK / hsep / hT₀ / hcanK / hacc / hrad /
hord` 逐字形）+ pinching（任一全 records 族）；端点有限由 top gate `hdσ` 付；FRESH 以 K 帧形
（`fresh_rescale_adapter_P6JA` 的输出）进入。结论 = driver `hkappaC` 槽逐字（`Hs = (KH ·).toHistory`、
`ts = σ`、`ys = y`、`ρnc = 1/200`）。**`hkappaC_driver_of_drv_J11S`**（PROVED）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- **driver `hkappaC` ⇐ driver records 包 + FRESH（`_J11S`，PROVED）**。 -/
theorem hkappaC_driver_of_drv_J11S {ε C1 C2 Cg : ℝ} {Ctime : ℝ≥0} (hC2 : 0 ≤ C2)
    (KH : ℕ → RetainedCoreHistory.{u})
    {Tn aSeed : ∀ k, Icc (0 : ℝ) (KH k).toHistory.horizon} {haT : ∀ k, aSeed k ≤ Tn k}
    {pT : ∀ k, ((KH k).toHistory.stageAt (Tn k)).Carrier}
    (hclock : ∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) (hone : ∀ k, 1 ≤ (aSeed k : ℝ))
    (hsm : ∀ k, GC.LongTime.hasSmallParabolicCurvature (KH k).toHistory (Tn k) (pT k) 1)
    (seedTrace : ∀ k, BackwardPointTrace (KH k).toHistory ((KH k).toHistory.activeStage (aSeed k))
      ((KH k).toHistory.activeStage (Tn k)) ((KH k).toHistory.activeStage_mono (haT k)) (pT k))
    (σ : ∀ k, Icc (0 : ℝ) (KH k).toHistory.horizon)
    (y : ∀ k, ((KH k).toHistory.stageAt (σ k)).Carrier)
    (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ)
    (hRpos : ∀ k, 0 < R k) (hRr : ∀ k : ℕ, (k : ℝ) + 1 ≤ R k) (hL : Tendsto L atTop atTop)
    (hgood : ∀ k, ∀ (v : Icc (0 : ℝ) (KH k).toHistory.horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
      (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
      ∀ z : ((KH k).toHistory.stageAt v).Carrier,
        riemannianEDistOf ((KH k).toHistory.stageMetric ((KH k).toHistory.activeStage v) v)
            ((seedTrace k).point ((KH k).toHistory.activeStage v)
              ((KH k).toHistory.activeStage_mono hav)
              ((KH k).toHistory.activeStage_mono (hvs.trans (hsT k)))) z ≤
          riemannianEDistOf
              ((KH k).toHistory.stageMetric ((KH k).toHistory.activeStage (σ k)) (σ k))
              ((seedTrace k).point ((KH k).toHistory.activeStage (σ k))
                ((KH k).toHistory.activeStage_mono (has k))
                ((KH k).toHistory.activeStage_mono (hsT k))) (y k) +
            ENNReal.ofReal (L k / Real.sqrt (R k)) →
        Cg * R k ≤ metricScalarAt ((KH k).toHistory.stageMetric ((KH k).toHistory.activeStage v) v)
          z →
        (KH k).toHistory.HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z)
    (hσH : ∀ k, (σ k : ℝ) < (KH k).toHistory.horizon)
    (hpin : ∀ k (τ : Icc (0 : ℝ) (KH k).toHistory.horizon)
      (x : ((KH k).toHistory.stageAt τ).Carrier),
      InFixedHamiltonIveyRegion ((KH k).toHistory.stageMetric ((KH k).toHistory.activeStage τ) τ)
        (0 + τ) x)
    (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
    (recordsK : ∀ n (i : Fin (KH n).eventCount), T₀ n ≤ (KH n).time i.succ →
      GeometricCutoffRecord (KH n).toHistory i (q n))
    (hsep : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (KH n).eventCount) (hi : T₀ n ≤ (KH n).time i.succ) b,
        (σ n : ℝ) - T / R n < (KH n).time i.succ →
        2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale)
    (hT₀ : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - T / R n)
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (q n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (q n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (q n).modelOrder)
    {Aseed κ : ℝ} (hAs : 0 < Aseed) (nrK : ℕ → ℝ → ℝ) (TfK : ℕ → ℝ)
    (hsupK : ∀ k, KappaSeedWindowFwd_C11PK (nrK k) (Aseed + 7) κ (TfK k) (KH k).toHistory)
    (hTf : ∀ᶠ k in atTop, TfK k ≤ (Tn k : ℝ)) (hTn2 : ∀ k, 2 < (Tn k : ℝ))
    (hvol : ∀ k, ENNReal.ofReal (Aseed⁻¹ * 1 ^ 3) ≤
      ballVolume ((KH k).toHistory.stageMetric ((KH k).toHistory.activeStage (Tn k)) (Tn k))
        (pT k) 1)
    (hnr : ∀ k (w : ℝ), (Tn k : ℝ) - 1 ^ 2 / 2 ≤ w → w ≤ (Tn k : ℝ) → nrK k w ≤ 1)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k)
    (hwin' : ∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k)
    (hdσ : ∀ᶠ k in atTop,
      riemannianEDistOf ((KH k).toHistory.stageMetric ((KH k).toHistory.activeStage (σ k)) (σ k))
          ((seedTrace k).point ((KH k).toHistory.activeStage (σ k))
            ((KH k).toHistory.activeStage_mono (has k))
            ((KH k).toHistory.activeStage_mono (hsT k))) (y k) +
        ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((Aseed + 3) * 1)) :
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
    (∀ᶠ n in map φ atTop, (KH n).toHistory.isTracedRegion (σ n) (y n)
      (2 * D / Real.sqrt (R n)) (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
    ∀ x ∈ riemannianBallOf ((KH n).toHistory.stageMetric ((KH n).toHistory.activeStage (σ n))
        (σ n)) (y n) (D / Real.sqrt (R n)),
    ∀ (v : Icc (0 : ℝ) (KH n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
    ∀ tr : BackwardPointTrace (KH n).toHistory ((KH n).toHistory.activeStage v)
      ((KH n).toHistory.activeStage (σ n)) ((KH n).toHistory.activeStage_mono hvt) x,
    ∀ r'' : ℝ, 0 < r'' → r'' ≤ (fun _ : ℕ => (1 : ℝ) / 200) n →
      (KH n).toHistory.isParabolicallyRmControlledBall v
        (tr.point ((KH n).toHistory.activeStage v) le_rfl
          ((KH n).toHistory.activeStage_mono hvt)) r'' →
      ENNReal.ofReal (κ * r'' ^ 3) ≤
        Geometry.Collapse.ballVolume ((KH n).toHistory.stageMetric
          ((KH n).toHistory.activeStage v) v)
          (tr.point ((KH n).toHistory.activeStage v) le_rfl
            ((KH n).toHistory.activeStage_mono hvt)) r'' := by
  intro φ hφ D T K hD hT hK hTR
  have hfinE := hdσ.mono fun k hk =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans le_self_add hk)
  have hst := ObservedHistory.hstayK_of_drv_J11S (Cg := Cg) (haT := haT) hC2 KH hclock hone hsm
    seedTrace σ y R hsT has L hRpos hRr hL hgood hσH hfinE hpin q T₀ recordsK hsep hT₀ hcanK
    hacc hrad hord T D hT hD K hK
  have hev : ∀ᶠ k in atTop, _ := hst.and (hdσ.and (hTf.and ((hwin (2 * T) (by positivity)).and
    (hwin' (2 * T) (by positivity)))))
  filter_upwards [hφ.tendsto_atTop hev, hTR] with k hk hTRk
  obtain ⟨hstk, hdσk, hTfk, haSk, hwk⟩ := hk
  intro x hx v hvt hvT tr b hb0 hbρ hctrl
  have hRk := hRpos k
  have hTR0 : 0 < T / R k := div_pos hT hRk
  have e2 : 2 * T / R k = T / R k + T / R k := by ring
  have hvT' : (σ k : ℝ) - T / R k ≤ (v : ℝ) := hvT
  have haS' : aSeed k ≤ v := by
    change (aSeed k : ℝ) ≤ v
    linarith
  have hTR' := hTRk.mono_radius (div_pos hD (Real.sqrt_pos.2 hRk))
    (div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))
  have hd := hstk hTR' x hx v hvt hvT haS' tr
  have hvTn : v ≤ Tn k := hvt.trans (hsT k)
  have hτw : (Tn k : ℝ) - 1 ^ 2 / 2 ≤ v := by linarith
  have hvolA : ENNReal.ofReal ((Aseed + 7)⁻¹ * 1 ^ 3) ≤
      ballVolume ((KH k).toHistory.stageMetric ((KH k).toHistory.activeStage (Tn k)) (Tn k))
        (pT k) 1 := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hvol k)
    have : (Aseed + 7)⁻¹ ≤ Aseed⁻¹ := inv_anti₀ hAs (by linarith)
    simpa using this
  have hL1 : L k / Real.sqrt (R k) ≤ (L k + 1) / Real.sqrt (R k) :=
    div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  have hmem : riemannianEDistOf ((KH k).toHistory.stageMetric ((KH k).toHistory.activeStage v) v)
      ((seedTrace k).point ((KH k).toHistory.activeStage v)
        ((KH k).toHistory.activeStage_mono haS') ((KH k).toHistory.activeStage_mono hvTn))
      (tr.point ((KH k).toHistory.activeStage v) le_rfl
        ((KH k).toHistory.activeStage_mono hvt)) <
      ENNReal.ofReal ((Aseed + 7) * 1) := by
    refine lt_of_le_of_lt
      (hd.trans ((add_le_add le_rfl (ENNReal.ofReal_le_ofReal hL1)).trans hdσk)) ?_
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  have hb' : b ≤ 1 / 200 := hbρ
  exact hsupK k (Tn k) (pT k) 1 hTfk (by linarith [hTn2 k]) (hsm k) hvolA (hnr k)
    (aSeed k) (haT k) (hclock k) (seedTrace k) v haS' hvTn hτw
    (tr.point ((KH k).toHistory.activeStage v) le_rfl ((KH k).toHistory.activeStage_mono hvt))
    hmem b hb0.le (by linarith) hctrl


/-- **consumer（`_J11S`）**：本结论 = driver `hkappaC` 槽文本（`Hs := fun k => (KH k).toHistory`，
`ts := σ`、`ys := y`、`ρnc := 1/200`；槽文本从 `P6DepthDriverAnyPosLocalP6DP4C2.lean` 抽取）。 -/
example (KH : ℕ → RetainedCoreHistory.{u}) (σ : ∀ k, Icc (0 : ℝ) (KH k).toHistory.horizon)
    (y : ∀ k, ((KH k).toHistory.stageAt (σ k)).Carrier) (R : ℕ → ℝ) (κ : ℝ)
    (X :
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
    (∀ᶠ n in map φ atTop, (KH n).toHistory.isTracedRegion (σ n) (y n)
      (2 * D / Real.sqrt (R n)) (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
    ∀ x ∈ riemannianBallOf ((KH n).toHistory.stageMetric ((KH n).toHistory.activeStage (σ n))
        (σ n)) (y n) (D / Real.sqrt (R n)),
    ∀ (v : Icc (0 : ℝ) (KH n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
    ∀ tr : BackwardPointTrace (KH n).toHistory ((KH n).toHistory.activeStage v)
      ((KH n).toHistory.activeStage (σ n)) ((KH n).toHistory.activeStage_mono hvt) x,
    ∀ r'' : ℝ, 0 < r'' → r'' ≤ (fun _ : ℕ => (1 : ℝ) / 200) n →
      (KH n).toHistory.isParabolicallyRmControlledBall v
        (tr.point ((KH n).toHistory.activeStage v) le_rfl
          ((KH n).toHistory.activeStage_mono hvt)) r'' →
      ENNReal.ofReal (κ * r'' ^ 3) ≤
        Geometry.Collapse.ballVolume ((KH n).toHistory.stageMetric
          ((KH n).toHistory.activeStage v) v)
          (tr.point ((KH n).toHistory.activeStage v) le_rfl
            ((KH n).toHistory.activeStage_mono hvt)) r'') :
    let Hs : ℕ → ObservedHistory.{u} := fun k => (KH k).toHistory
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (σ n))
          ((Hs n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ (fun _ : ℕ => (1 : ℝ) / 200) n →
          (Hs n).isParabolicallyRmControlledBall v
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'' := by
  intro Hs
  exact X

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
