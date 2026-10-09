import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J11InteriorStayJ11S
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HpinRescaledP6HI

/-!
# interior stay，driver records 包形（无 `hfamT`；O-CH11-J11STAY G4，后缀 `_J11S`）

lead 续令（1）（2）：
* `hstay_interior_body_cg_J11S`：G1 body 孪生——hgood 阈 `4` 参数化为 `Cg`（`Q_b ≥ max (max (9K) Cg) 1`；
  J8 槽 `8·R` 直接实例化）；records 量词 `T₀ ≤ aSeed` 收窄为 `T₀ ≤ σ − T/R`，`hscale` 收窄为窗形
  `σ − T/R < time e⁺`（DLW G4a 同法：原证明只在 trace 起点 `v ≥ σ − T/R` 之后的 event 用它）。
* `hstayK_of_drv_J11S`：塔层 stay（实例形，= G3b `hfpL_hPN_of_depthExt_J11S` 的 `hstayK` 输入）⇐ **driver
  records 包**（DEPTH4C2 anyPos driver 在同一中心的 `recordsK / hsep / hT₀ / hcanK / hacc / hrad / hord`
  逐字形，`r := 1`）+ pinching（`hpin_rescaled_of_records_P6HI`，任一全 records 族，`a₀ := 0`）。
  `hfamT` 不再需要：`hOld` = record 字段 `old_eq_retained`；`hfin` 不需（G3b 用槽自带 `hdistσ`）；
  budget ⇐ driver `hsep` 窗形（interior 形，无 `σ = time i⁺` 前提）。
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

/-- **interior stay 体（Cg + 窗形，`_J11S`，PROVED）**：G1 `hstay_interior_body_J11S` 孪生，hgood 阈 `Cg`，
records 量词 `T₀ ≤ σ − T/R`、`hscale` 窗 `σ − T/R < time e⁺`。 -/
theorem hstay_interior_body_cg_J11S :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg K Qb T ℓ Kℓ ρb : ℝ} (_ : 0 ≤ C2')
    (KH : RetainedCoreHistory.{u})
    {Tn aSeed σ : Icc (0 : ℝ) KH.toHistory.horizon} (haT : aSeed ≤ Tn)
    {pT : (KH.toHistory.stageAt Tn).Carrier} {r : ℝ}
    (_ : GC.LongTime.hasSmallParabolicCurvature KH.toHistory Tn pT r)
    (_ : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace KH.toHistory (KH.toHistory.activeStage aSeed)
      (KH.toHistory.activeStage Tn) (KH.toHistory.activeStage_mono haT) pT)
    {a₀ : ℝ} (_ : 0 ≤ a₀)
    (_ : ∀ (t : Icc (0 : ℝ) KH.toHistory.horizon) (x : (KH.toHistory.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (KH.toHistory.stageMetric (KH.toHistory.activeStage t) t)
        (a₀ + t) x)
    (hsT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (KH.toHistory.stageAt σ).Carrier) {R : ℝ} (L : ℝ)
    (_ : 0 < R)
    (_ : ∀ (v : Icc (0 : ℝ) KH.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (KH.toHistory.stageAt v).Carrier,
        riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v)
            (seedTrace.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono hav)
              (KH.toHistory.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
              (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
                (KH.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v) z →
        KH.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (_ : 0 ≤ K) (_ : max (max (9 * K) Cg) 1 ≤ Qb)
    (_ : (σ : ℝ) < KH.toHistory.horizon) (_ : 1 ≤ R * aSeed) (_ : T ≤ L ^ 2)
    (_ : 0 < ℓ) (_ : Kℓ * ℓ ^ 2 ≤ 1) (_ : ℓ ≤ r / 50) (_ : 1 / r ^ 2 ≤ Kℓ)
    (_ : 2 * Real.sqrt 3 * (6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4)) * R ≤ Kℓ)
    (_ : ℓ ≤ localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)))
    (_ : 2 * (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R))) ≤ L / 2 / Real.sqrt R)
    (_ : ρb / Real.sqrt R + 8 / ℓ * (T / R) < L / 2 / Real.sqrt R)
    {q : CutoffParameters} {T₀ : ℝ} (_ : T₀ ≤ (σ : ℝ) - T / R)
    (records : ∀ e : Fin KH.toHistory.eventCount, T₀ ≤ KH.toHistory.time e.succ →
      GeometricCutoffRecord KH.toHistory e q)
    (_ : ∀ e : Fin KH.toHistory.eventCount, T₀ ≤ KH.toHistory.time e.succ →
      (KH.toHistory.event e).old = (KH.toHistory.event e).transition.trace.retainedCore)
    (_ : ∀ (e : Fin KH.toHistory.eventCount) (he : T₀ ≤ KH.toHistory.time e.succ) b,
      ((records e he).static b).hasCanonicalWindow)
    (_ : StandardCap.transitionEnd + 10 < q.modelRadius)
    (_ : q.modelAccuracy ≤ ε₀) (_ : 2 ≤ q.modelOrder)
    (_ : ∀ (e : Fin KH.toHistory.eventCount) (he : T₀ ≤ KH.toHistory.time e.succ) b,
      (σ : ℝ) - T / R < KH.toHistory.time e.succ →
      2 * max (3 / r ^ 2) (2 * (Qb * R)) < ((records e he).static b).neck.scale)
    (_ : riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
        (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
          (KH.toHistory.activeStage_mono hsT)) y ≠ ⊤)
    (_ : KH.toHistory.isTracedRegion σ y (ρb / Real.sqrt R) (T / R) (K * R)),
    ∀ x ∈ riemannianBallOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ) y
        (ρb / Real.sqrt R),
    ∀ (v : Icc (0 : ℝ) KH.toHistory.horizon) (hvt : v ≤ σ), (σ : ℝ) - T / R ≤ v →
    ∀ (hav : aSeed ≤ v)
      (tr : BackwardPointTrace KH.toHistory (KH.toHistory.activeStage v)
        (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono hvt) x),
      riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v)
          (seedTrace.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono hav)
            (KH.toHistory.activeStage_mono (hvt.trans hsT)))
          (tr.point (KH.toHistory.activeStage v) le_rfl (KH.toHistory.activeStage_mono hvt)) <
        riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
            (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
              (KH.toHistory.activeStage_mono hsT)) y +
          ENNReal.ofReal (L / 2 / Real.sqrt R) := by
  obtain ⟨ε₀, hε₀, hnc0⟩ := exists_not_ageZeroCapPoint_of_scalar_lt_C11G.{u}
  refine ⟨min ε₀ (1 / 2), lt_min hε₀ (by norm_num), ?_⟩
  intro eps C1' C2' Ctime' Cg K Qb T ℓ Kℓ ρb hC2 KH Tn aSeed σ haT pT r hsmall hclock seedTrace
    a₀ ha₀ hpin hsT has y R L hR hgood hK hQb hσH hRa hTL hℓ hKℓ hℓr hKr hKC hℓρ hρL hnum
    q T₀ hT₀ records hOld hcan hDm hacc hm hscale hfin hTR x hx v hvt hvT hav tr
  have hnc : ∀ (e : Fin KH.toHistory.eventCount) (he : T₀ ≤ KH.toHistory.time e.succ)
      (w : (KH.toHistory.stage e.succ).Carrier),
      (∀ b, metricScalarAt (KH.toHistory.event e).outputMetric w <
        ((records e he).static b).neck.scale / 2) →
      ¬ ∃ (b : (KH.toHistory.event e).RetainedBoundaryIndex)
          (x : standardCapWindow q.modelRadius),
        w = ((records e he).static b).window x ∧ ‖x.val‖ < q.modelRadius := by
    intro e he w hw
    have h := hnc0 (records e he) (hacc.trans (min_le_left _ _)) hm (hcan e he)
      (Dcap := q.modelRadius - 1) (by linarith) w hw
    simpa only [sub_add_cancel] using h
  have hQ4 : max Cg 1 ≤ Qb := (max_le_max (le_max_right _ _) le_rfl).trans hQb
  have h9K : 9 * K * R ≤ 2 * (Qb * R) := by
    have h1 : 9 * K ≤ Qb := (le_max_left _ _).trans ((le_max_left _ _).trans hQb)
    have h2 : 0 ≤ Qb := le_trans (by norm_num) ((le_max_right _ _).trans hQb)
    nlinarith
  have hvT' : (σ : ℝ) - T / R ≤ v := hvT
  have hTR' : T / R ≤ L ^ 2 / R := div_le_div_of_nonneg_right hTL hR.le
  have haL : (σ : ℝ) - L ^ 2 / R ≤ v := by linarith
  have hdepth : (σ : ℝ) - v ≤ T / R := by linarith
  have hav' : (aSeed : ℝ) ≤ v := hav
  have hRv : 1 ≤ R * v := hRa.trans (mul_le_mul_of_nonneg_left hav' hR.le)
  have hscalC : ∀ (w : Icc (0 : ℝ) KH.toHistory.horizon) (haw : v ≤ w) (hwσ : w ≤ σ),
      (∀ (v' : Icc (0 : ℝ) KH.toHistory.horizon) (hav' : v ≤ v') (hv'σ : v' ≤ σ), (w : ℝ) ≤ v' →
        riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage v') v')
            (seedTrace.point (KH.toHistory.activeStage v')
              (KH.toHistory.activeStage_mono (hav.trans hav'))
              (KH.toHistory.activeStage_mono (hv'σ.trans hsT)))
            (tr.point (KH.toHistory.activeStage v') (KH.toHistory.activeStage_mono hav')
              (KH.toHistory.activeStage_mono hv'σ)) <
          riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
              (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
                (KH.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / 2 / Real.sqrt R)) →
      metricScalarAt (KH.toHistory.stageMetric (KH.toHistory.activeStage w) w)
        (tr.point (KH.toHistory.activeStage w) (KH.toHistory.activeStage_mono haw)
          (KH.toHistory.activeStage_mono hwσ)) ≤ 2 * (Qb * R) := by
    intro w haw hwσ _
    exact (KH.toHistory.hgrid_of_isTracedRegion_P6BB hR hK hTR hx hvt hvT tr w haw hwσ).trans h9K
  have hprotC := hprotC_scalC_CXJP KH haT hsmall hclock seedTrace hsT has y L hav hvt tr
    hscalC records hDm hnc (fun e he b hlt => hscale e he b (lt_of_le_of_lt hvT' hlt))
  exact hgoodV_scalC_CXJP hC2 KH haT hsmall hclock seedTrace ha₀ hpin hsT has y L hR hgood hQ4
    hav hvt (fun h => absurd h (ne_of_lt hσH)) haL hdepth hRv tr hscalC hℓ hKℓ hℓr hKr hKC hℓρ
    hρL (hT₀.trans hvT') records hOld hcan (hacc.trans (min_le_right _ _)) hDm hprotC hx hfin hnum
    v le_rfl hvt

/-- **塔层 stay ⇐ driver records 包（实例，`_J11S`，PROVED）**：结论 = G3b `hfpL_hPN_of_depthExt_J11S` 的
`hstayK` 输入形（`Kh k = (KH k).toHistory`）。records 包 = DEPTH4C2 anyPos driver 在中心 `(σ, y)` 的
`recordsK / hsep / hT₀ / hcanK / hacc / hrad / hord` 逐字形（种子半径 `r := 1`）；pinching `a₀ := 0`；
端点有限 `hfinE` 为 `∀ᶠ`（J11 槽由 top gate `hdistσ` 付）。 -/
theorem hstayK_of_drv_J11S {ε C1 C2 Cg : ℝ} {Ctime : ℝ≥0} (hC2 : 0 ≤ C2)
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
    (hfinE : ∀ᶠ k in atTop,
      riemannianEDistOf ((KH k).toHistory.stageMetric ((KH k).toHistory.activeStage (σ k)) (σ k))
          ((seedTrace k).point ((KH k).toHistory.activeStage (σ k))
            ((KH k).toHistory.activeStage_mono (has k))
            ((KH k).toHistory.activeStage_mono (hsT k))) (y k) ≠ ⊤)
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
    (hord : ∀ n : ℕ, n + 2 ≤ (q n).modelOrder) :
    ∀ T r : ℝ, 0 < T → 0 < r → ∀ K : ℝ, 0 ≤ K → ∀ᶠ k in atTop,
      (KH k).toHistory.isTracedRegion (σ k) (y k) (r / Real.sqrt (R k)) (T / R k) (K * R k) →
      ∀ x ∈ riemannianBallOf ((KH k).toHistory.stageMetric ((KH k).toHistory.activeStage (σ k))
          (σ k)) (y k) (r / Real.sqrt (R k)),
      ∀ (v : Icc (0 : ℝ) (KH k).toHistory.horizon) (hvt : v ≤ σ k), (σ k : ℝ) - T / R k ≤ v →
      ∀ (hav : aSeed k ≤ v)
        (tr : BackwardPointTrace (KH k).toHistory ((KH k).toHistory.activeStage v)
          ((KH k).toHistory.activeStage (σ k)) ((KH k).toHistory.activeStage_mono hvt) x),
        riemannianEDistOf ((KH k).toHistory.stageMetric ((KH k).toHistory.activeStage v) v)
            ((seedTrace k).point ((KH k).toHistory.activeStage v)
              ((KH k).toHistory.activeStage_mono hav)
              ((KH k).toHistory.activeStage_mono (hvt.trans (hsT k))))
            (tr.point ((KH k).toHistory.activeStage v) le_rfl
              ((KH k).toHistory.activeStage_mono hvt)) ≤
          riemannianEDistOf
              ((KH k).toHistory.stageMetric ((KH k).toHistory.activeStage (σ k)) (σ k))
              ((seedTrace k).point ((KH k).toHistory.activeStage (σ k))
                ((KH k).toHistory.activeStage_mono (has k))
                ((KH k).toHistory.activeStage_mono (hsT k))) (y k) +
            ENNReal.ofReal (L k / Real.sqrt (R k)) := by
  obtain ⟨ε₀, hε₀, hB⟩ := ObservedHistory.hstay_interior_body_cg_J11S.{u}
  intro T r hT hr K hK
  set Qb : ℝ := max (max (9 * K) Cg) 1 with hQbdef
  have hQ1 : (1 : ℝ) ≤ Qb := le_max_right _ _
  obtain ⟨cn, hcn, hnumF⟩ := crossSlab_numerics_P6JW (C2' := C2) hC2 hQ1 one_pos
  obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt hε₀
  have hTEpos := StandardCap.transitionEnd_pos
  obtain ⟨N₁, hN₁⟩ := exists_nat_ge (StandardCap.transitionEnd + 10)
  filter_upwards [hsep T hT (2 * Qb) (by linarith), hT₀ T hT, hfinE, eventually_ge_atTop N₀,
    eventually_ge_atTop (N₁ + 1), hL.eventually_ge_atTop (2 * (r + 8 * T / cn) + 1),
    hL.eventually_ge_atTop (4 * (localPropagationRadius C2 / Real.sqrt (2 * Qb))),
    hL.eventually_ge_atTop (T + 1)] with k hsepk hT₀k hfink hk0 hk1 hL1 hL2 hL3
  intro hTR x hx v hvt hvT hav tr
  have hRk := hRpos k
  have hR1 : (1 : ℝ) ≤ R k := by
    have h := hRr k
    have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  obtain ⟨ℓ, Kℓ, hℓ, hKℓ, hℓr, hKr, hKC, hℓρ, hρL, hnum⟩ :=
    hnumF (R := R k) (L := L k) (D := r) (T := T) hR1 (by linarith) (by linarith)
  have hTL : T ≤ L k ^ 2 := by nlinarith
  have hRa : 1 ≤ R k * aSeed k := by nlinarith [hone k]
  have hacck : (q k).modelAccuracy ≤ ε₀ := by
    refine (hacc k).trans (le_of_lt (lt_of_le_of_lt ?_ hN₀))
    have h1 : (N₀ : ℝ) ≤ k := by exact_mod_cast hk0
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hDm : StandardCap.transitionEnd + 10 < (q k).modelRadius := by
    have h1 : ((N₁ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk1
    push_cast at h1
    linarith [hrad k]
  have hm : 2 ≤ (q k).modelOrder := le_trans (by omega) (hord k)
  have hscale : ∀ (e : Fin (KH k).toHistory.eventCount) (he : T₀ k ≤ (KH k).toHistory.time e.succ)
      b, (σ k : ℝ) - T / R k < (KH k).toHistory.time e.succ →
      2 * max (3 / (1 : ℝ) ^ 2) (2 * (Qb * R k)) < ((recordsK k e he).static b).neck.scale := by
    intro e he b hlt
    refine lt_of_le_of_lt ?_ (hsepk e he b hlt)
    have h3 : (3 : ℝ) / 1 ^ 2 ≤ 3 / ((1 : ℝ) / 100) ^ 2 := by norm_num
    have h4 : 2 * (Qb * R k) = 2 * Qb * R k := by ring
    rw [h4]
    exact mul_le_mul_of_nonneg_left (max_le_max h3 le_rfl) (by norm_num)
  have hQbK : max (max (9 * K) Cg) 1 ≤ Qb := le_rfl
  exact hB hC2 (KH k) (haT k) (hsm k) (hclock k) (seedTrace k) le_rfl (hpin k) (hsT k) (has k)
    (y k) (L k) hRk (hgood k) hK hQbK (hσH k) hRa hTL hℓ hKℓ hℓr hKr hKC hℓρ hρL hnum hT₀k
    (recordsK k) (fun e he => (recordsK k e he).old_eq_retained) (hcanK k) hDm hacck hm hscale
    hfink hTR x hx v hvt hvT hav tr |>.le |>.trans (add_le_add le_rfl
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (by linarith)
        (Real.sqrt_nonneg _))))

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
