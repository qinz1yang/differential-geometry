import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6StayTRpcP6KA

/-!
# interior stay：hPN 中心自身的 traced region ⇒ 跨 slab footprint（O-CH11-J11STAY G1，后缀 `_J11S`）

hgap J11 的 footprint 半边与 driver 在 hPN 中心的 `hkappaC` 是同一件 interior stay（J8KAPPA 判定）。
crossing 帧孪生 `hstopE_deep_tower_pc_P6KA` 的中心是 `p′`（`t ↑ σ = time i⁺`），trace 从 `tt < σ` 出发，
要 no-shortcut 平移 + grid bootstrap；interior 中心 `(σ, y)` **自身**带 traced region，于是：
* `hscalC`（CXJP 的条件标量前提）**无条件**成立：`point_unique` ⇒ 任意 trace 即 traced region 的
  Rm-bounded trace，`hgrid_of_isTracedRegion_P6BB` 给沿 trace `R ≤ 9K·R ≤ Q_b·R`
  （`Q_b := max (max (9K) 4) 1`）；
* `hprotC` ⇐ `hprotC_scalC_CXJP`（records + C11G 的 cap 内区标量下界 + `hscale`）；
* 整窗定位 ⇐ `hgoodV_scalC_CXJP`（跨 event first-exit：I.8.3(b) + (D4) + `surgery_no_shortcut_C11D`），
  trace 起点取 `a := v` 本身；`hUSCtop` 由 `σ < horizon` 空真。
`hgood` 用 `4·R` 形（`Cg = 4`），与 J11 / driver 前提逐字；不涉 `Q_n`（traced-region 常数 `K` 是固定数）。
* `hstay_interior_body_J11S`（PROVED，单 history）；
* `hstay_interior_tower_J11S`（PROVED ⇐ `hfamT` 等，前提块 = `hstopE_deep_tower_pc_P6KA` 逐字去掉
  grid / ball 常数；中心换 interior：`σ < horizon`；traced region 常数 `K` 在 `∀ᶠ` 之前任取）。
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

/-- **interior stay 体（`_J11S`，PROVED）**：`(σ, y)` 的 traced region
`isTracedRegion σ y (ρb/√R) (T/R) (K·R)`
⇒ 从 `B_σ(y, ρb/√R)` 出发、起点 `v ∈ [σ − T/R, σ]` 的任意 trace 在 `v` 处
`d_v(O_v, tr(v)) < d_σ(O, y) + L/(2√R)`。 -/
theorem hstay_interior_body_J11S :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {K Qb T ℓ Kℓ ρb : ℝ} (_ : 0 ≤ C2')
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
        4 * R ≤ metricScalarAt (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v) z →
        KH.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (_ : 0 ≤ K) (_ : max (max (9 * K) 4) 1 ≤ Qb)
    (_ : (σ : ℝ) < KH.toHistory.horizon) (_ : 1 ≤ R * aSeed) (_ : T ≤ L ^ 2)
    (_ : 0 < ℓ) (_ : Kℓ * ℓ ^ 2 ≤ 1) (_ : ℓ ≤ r / 50) (_ : 1 / r ^ 2 ≤ Kℓ)
    (_ : 2 * Real.sqrt 3 * (6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4)) * R ≤ Kℓ)
    (_ : ℓ ≤ localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)))
    (_ : 2 * (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R))) ≤ L / 2 / Real.sqrt R)
    (_ : ρb / Real.sqrt R + 8 / ℓ * (T / R) < L / 2 / Real.sqrt R)
    {q : CutoffParameters} {T₀ : ℝ} (_ : T₀ ≤ (aSeed : ℝ))
    (records : ∀ e : Fin KH.toHistory.eventCount, T₀ ≤ KH.toHistory.time e.succ →
      GeometricCutoffRecord KH.toHistory e q)
    (_ : ∀ e : Fin KH.toHistory.eventCount, T₀ ≤ KH.toHistory.time e.succ →
      (KH.toHistory.event e).old = (KH.toHistory.event e).transition.trace.retainedCore)
    (_ : ∀ (e : Fin KH.toHistory.eventCount) (he : T₀ ≤ KH.toHistory.time e.succ) b,
      ((records e he).static b).hasCanonicalWindow)
    (_ : StandardCap.transitionEnd + 10 < q.modelRadius)
    (_ : q.modelAccuracy ≤ ε₀) (_ : 2 ≤ q.modelOrder)
    (_ : ∀ (e : Fin KH.toHistory.eventCount) (he : T₀ ≤ KH.toHistory.time e.succ) b,
      (aSeed : ℝ) < KH.toHistory.time e.succ →
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
  intro eps C1' C2' Ctime' K Qb T ℓ Kℓ ρb hC2 KH Tn aSeed σ haT pT r hsmall hclock seedTrace
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
  have hQ4 : max 4 1 ≤ Qb := (max_le_max (le_max_right _ _) le_rfl).trans hQb
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
    hscalC records hDm hnc (fun e he b hlt => hscale e he b (lt_of_le_of_lt hav' hlt))
  exact hgoodV_scalC_CXJP hC2 KH haT hsmall hclock seedTrace ha₀ hpin hsT has y L hR hgood hQ4
    hav hvt (fun h => absurd h (ne_of_lt hσH)) haL hdepth hRv tr hscalC hℓ hKℓ hℓr hKr hKC hℓρ
    hρL (hT₀.trans hav') records hOld hcan (hacc.trans (min_le_right _ _)) hDm hprotC hx hfin hnum
    v le_rfl hvt

end ObservedHistory

/-- **塔层 interior stay（`_J11S`，PROVED ⇐ `hfamT` + cap 参数）**：前提块 = `hstopE_deep_tower_pc_P6KA`
逐字（删 `Cball / Cgrid / β / Ktr` 与其约束）；中心换 interior（`σ k < horizon`，无 crossing `i`）。
`∀ T r > 0`、`∀ K ≥ 0`，`∀ᶠ k`：`(σ k, y k)` 的 traced region `(r/√R, T/R, K·R)` ⇒ 从 `B_σ(y, r/√R)`
出发、起点 `v ∈ [σ − T/R, σ]` 的任意 trace 在 `v` 处 `d_v(O_v, tr(v)) ≤ d_σ(O, y) + L/√R`。 -/
theorem hstay_interior_tower_J11S :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {qp : CutoffParameters},
    0 ≤ C2 → StandardCap.transitionEnd + 10 < qp.modelRadius → qp.modelAccuracy ≤ ε₀ →
    2 ≤ qp.modelOrder → Tendsto qp.delta atTop (𝓝 0) →
    (
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∃ (a₀ T₀ : ℕ → ℝ) (records : ∀ k (e : Fin (Kh k).eventCount),
            T₀ k ≤ (Kh k).time e.succ →
              GeometricCutoffRecord (Kh k) e (qp.rescale_P6N (c k) (hc k))),
          (∀ k, 0 ≤ a₀ k) ∧
          (∀ k (τ : Icc (0 : ℝ) (Kh k).horizon) (x : ((Kh k).stageAt τ).Carrier),
            InFixedHamiltonIveyRegion ((Kh k).stageMetric ((Kh k).activeStage τ) τ)
              (a₀ k + τ) x) ∧
          (∀ k, T₀ k ≤ (aSeed k : ℝ)) ∧
          (∀ k (e : Fin (Kh k).eventCount), T₀ k ≤ (Kh k).time e.succ →
            ((Kh k).event e).old = ((Kh k).event e).transition.trace.retainedCore) ∧
          (∀ k (e : Fin (Kh k).eventCount) (he : T₀ k ≤ (Kh k).time e.succ) b,
            ((records k e he).static b).hasCanonicalWindow) ∧
          (∀ k, riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) (y k) ≠ ⊤) ∧
          ∀ᶠ k in atTop, WindowNeckScaleBudget_P6HS (Kh k) (qp.rescale_P6N (c k) (hc k))
            (T₀ k) (aSeed k : ℝ) (R k)
    ) →
      ∀ (T r : ℝ), 0 < T → 0 < r →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        (∀ k, (σ k : ℝ) < (Kh k).horizon) →
        ∀ K : ℝ, 0 ≤ K → ∀ᶠ k in atTop,
          (Kh k).isTracedRegion (σ k) (y k) (r / Real.sqrt (R k)) (T / R k) (K * R k) →
          ∀ x ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)
              (r / Real.sqrt (R k)),
          ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hvt : v ≤ σ k), (σ k : ℝ) - T / R k ≤ v →
          ∀ (hav : aSeed k ≤ v)
            (tr : BackwardPointTrace (Kh k) ((Kh k).activeStage v) ((Kh k).activeStage (σ k))
              ((Kh k).activeStage_mono hvt) x),
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                  ((Kh k).activeStage_mono (hvt.trans (hsT k))))
                (tr.point ((Kh k).activeStage v) le_rfl ((Kh k).activeStage_mono hvt)) ≤
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k))
                    ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal (L k / Real.sqrt (R k)) := by
  obtain ⟨ε₀, hε₀, hB⟩ := ObservedHistory.hstay_interior_body_J11S.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F ε C1 C2 Ctime qp hC2 hDm hacc hm hδlim hfamT T r hT hr
    ind c hc Kh Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L hRdef hRpos hRr hL
    hsel hgood haS hTnS hroom hradii hσH K hK
  obtain ⟨a₀, T₀, records, ha₀, hpin, hT₀, hOld, hcan, hfin, hW⟩ := hfamT ind c hc Tn pT hTc
    aSeed haT hclock hone hsm seedTrace σ y R hsT has L hRdef hRpos hRr hL hsel hgood haS hTnS
    hroom hradii
  set Qb : ℝ := max (max (9 * K) 4) 1 with hQbdef
  have hQ1 : (1 : ℝ) ≤ Qb := le_max_right _ _
  have hRlim : Tendsto R atTop atTop :=
    tendsto_atTop_mono hRr (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hca : Tendsto (fun k => c k * (aSeed k : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_)
      ((tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).atTop_div_const
        (two_pos : (0 : ℝ) < 2))
    have h1 := hTc k
    have h2 := hclock k
    have h3 := hone k
    have h4 := hc k
    norm_num at h2
    have h5 : (Tn k : ℝ) ≤ 2 * (aSeed k : ℝ) := by linarith
    have h6 := mul_le_mul_of_nonneg_left h5 h4.le
    rw [div_le_iff₀ two_pos]
    nlinarith
  have hsc := hscale_eventually_rescale_P6HS Kh hc (a := fun k => (aSeed k : ℝ))
    (Qb := Qb) hQ1 records hδlim hca hRlim hW
  obtain ⟨cn, hcn, hnumF⟩ := crossSlab_numerics_P6JW (C2' := C2) hC2 hQ1 one_pos
  filter_upwards [hsc, hL.eventually_ge_atTop (2 * (r + 8 * T / cn) + 1),
    hL.eventually_ge_atTop (4 * (localPropagationRadius C2 / Real.sqrt (2 * Qb))),
    hL.eventually_ge_atTop (T + 1)] with k hsck hL1 hL2 hL3
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
  have hsT' : max (max (9 * K) 4) 1 ≤ Qb := le_rfl
  have h := hB hC2 ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)) (haT k) (hsm k)
    (hclock k) (seedTrace k) (ha₀ k) (hpin k) (hsT k) (has k) (y k) (L k) hRk (hgood k) hK hsT'
    (hσH k) hRa hTL hℓ hKℓ hℓr hKr hKC hℓρ hρL hnum (hT₀ k) (records k) (hOld k) (hcan k) hDm hacc
    hm hsck (hfin k) hTR x hx v hvt hvT hav tr
  have hsR : 0 < Real.sqrt (R k) := Real.sqrt_pos.2 hRk
  have hq : L k / 2 / Real.sqrt (R k) ≤ L k / Real.sqrt (R k) :=
    div_le_div_of_nonneg_right (by linarith) hsR.le
  exact h.le.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hq))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
