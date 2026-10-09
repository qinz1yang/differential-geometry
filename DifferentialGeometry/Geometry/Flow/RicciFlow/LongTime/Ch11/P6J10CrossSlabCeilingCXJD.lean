import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10FirstExitHstopCXJD

/-!
# 跨 slab `hstop` + 跨 slab ceiling（CX-J10DIST G4，后缀 `_CXJD`）

* `hstop_of_firstExit_CXJD`：G2 `edist_trace_le_of_firstExit_CXJD`（预算 `X = d_σ(O, y) + L/(2√R)`）+
  G3 `hRicC_of_hgood_ceiling_CXJD` + 余量（`z ∈ B_σ(y, D/√R)`、`D/√R + (8/ℓ)(T/R) < L/(2√R)`）⇒
  整窗 `[a, σ]` 的 `hstop`（`d_v(seed(v), A(v)) ≤ d_σ(O, y) + L/√R`，CXJT0 stopped ceiling 的前提形）。
* `scalar_le_two_mul_crossSlab_ceiling_CXJD`（consumer）：`hstop` 喂 CXJT0
  `scalar_le_two_mul_stopped_ceiling_CXJT0` ⇒ 跨 slab 沿 trace `R ≤ 2·Q_b·R`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

/-- **跨 slab `hstop`（`_CXJD`）**：first-exit bootstrap 的整窗定位。 -/
theorem hstop_of_firstExit_CXJD {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    {Cg Cball Qb T K ℓ D : ℝ} (hC2 : 0 ≤ C2') (H : ObservedHistory.{u})
    {Tn aSeed a σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn) {pT : (H.stageAt Tn).Carrier}
    {r : ℝ} (hsmall : GC.LongTime.hasSmallParabolicCurvature H Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a₀ + t) x)
    (hσT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (H.stageAt σ).Carrier) {R : ℝ} (L : ℝ) (hR : 0 < R)
    (hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hσT))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hσT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hQb : max (max Cball Cg) 1 ≤ Qb) (hstep : 2 * Ctime' * Qb * T ≤ 1)
    (haS : aSeed ≤ a) (haσ : a ≤ σ) (hσlast : H.activeStage σ < Fin.last H.eventCount)
    (haL : (σ : ℝ) - L ^ 2 / R ≤ a) (hdepth : (σ : ℝ) - a ≤ T / R) (hRa : 1 ≤ R * a)
    {z : (H.stageAt σ).Carrier}
    (hz : metricScalarAt (H.stageMetric (H.activeStage σ) σ) z ≤ Cball * R)
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage σ) (H.activeStage_mono haσ) z)
    (hℓ : 0 < ℓ) (hKℓ : K * ℓ ^ 2 ≤ 1) (hℓr : ℓ ≤ r / 50) (hKr : 1 / r ^ 2 ≤ K)
    (hKC : 2 * Real.sqrt 3 * (6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4)) * R ≤ K)
    (hℓρ : ℓ ≤ localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)))
    (hρL : 2 * (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R))) ≤ L / 2 / Real.sqrt R)
    {q : CutoffParameters} {T₀ : ℝ} (hT₀ : T₀ ≤ (a : ℝ))
    (records : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → GeometricCutoffRecord H e q)
    (hOld : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ →
      (H.event e).old = (H.event e).transition.trace.retainedCore)
    (hcan : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b,
      ((records e he).static b).hasCanonicalWindow)
    (hacc : q.modelAccuracy ≤ 1 / 2) (hDm : StandardCap.transitionEnd + 10 < q.modelRadius)
    (hprotC : ∀ (e : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ e.castSucc)
        (h2 : e.succ ≤ H.activeStage Tn) (h3 : H.activeStage a ≤ e.castSucc)
        (h4 : e.succ ≤ H.activeStage σ) (he : T₀ ≤ H.time e.succ),
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvσ : v ≤ σ), H.time e.succ ≤ (v : ℝ) →
          riemannianEDistOf (H.stageMetric (H.activeStage v) v)
              (seedTrace.point (H.activeStage v) (H.activeStage_mono (haS.trans hav))
                (H.activeStage_mono (hvσ.trans hσT)))
              (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvσ)) <
            riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
                (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                  (H.activeStage_mono hσT)) y +
              ENNReal.ofReal (L / 2 / Real.sqrt R)) → ∀ b,
        seedTrace.point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
            ((records e he).static b).window ''
              {w : standardCapWindow q.modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10} ∧
          A.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
            ((records e he).static b).window ''
              {w : standardCapWindow q.modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10})
    (hzy : z ∈ riemannianBallOf (H.stageMetric (H.activeStage σ) σ) y (D / Real.sqrt R))
    (hdσ : riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
        (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
          (H.activeStage_mono hσT)) y ≠ ⊤)
    (hnum : D / Real.sqrt R + 8 / ℓ * (T / R) < L / 2 / Real.sqrt R) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ σ),
      riemannianEDistOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono (haS.trans hav))
            (H.activeStage_mono ((hvt.trans le_rfl).trans hσT)))
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ≤
        riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
            (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
              (H.activeStage_mono hσT)) y +
          ENNReal.ofReal (L / Real.sqrt R) := by
  set dσ := riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
    (seedTrace.point (H.activeStage σ) (H.activeStage_mono has) (H.activeStage_mono hσT)) y
    with hdσdef
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hD0 : 0 < D / Real.sqrt R :=
    ENNReal.ofReal_pos.mp (lt_of_le_of_lt zero_le hzy)
  have h8 : 0 ≤ 8 / ℓ := (div_pos (by norm_num) hℓ).le
  have hTR : 0 ≤ T / R := ((sub_nonneg.mpr (show (a : ℝ) ≤ σ from haσ))).trans hdepth
  have hdrift : 8 / ℓ * ((σ : ℝ) - a) ≤ 8 / ℓ * (T / R) := mul_le_mul_of_nonneg_left hdepth h8
  have hmargin : riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
        (seedTrace.point (H.activeStage σ) (H.activeStage_mono (haS.trans haσ))
          (H.activeStage_mono hσT)) z +
      ENNReal.ofReal ((8 / ℓ) * ((σ : ℝ) - a)) < dσ + ENNReal.ofReal (L / 2 / Real.sqrt R) :=
    calc _ ≤ (dσ + riemannianEDistOf (H.stageMetric (H.activeStage σ) σ) y z) +
          ENNReal.ofReal (8 / ℓ * (T / R)) :=
          add_le_add (riemannianEDistOf_triangle _ _ _ _) (ENNReal.ofReal_le_ofReal hdrift)
      _ < (dσ + ENNReal.ofReal (D / Real.sqrt R)) + ENNReal.ofReal (8 / ℓ * (T / R)) :=
          ENNReal.add_lt_add_right ENNReal.ofReal_ne_top (ENNReal.add_lt_add_left hdσ hzy)
      _ = dσ + ENNReal.ofReal (D / Real.sqrt R + 8 / ℓ * (T / R)) := by
          rw [add_assoc, ← ENNReal.ofReal_add hD0.le (mul_nonneg h8 hTR)]
      _ ≤ dσ + ENNReal.ofReal (L / 2 / Real.sqrt R) :=
          add_le_add le_rfl (ENNReal.ofReal_le_ofReal hnum.le)
  have hL : L / 2 / Real.sqrt R ≤ L / Real.sqrt R := by
    have : 0 < L / 2 / Real.sqrt R := lt_trans (by positivity) hnum
    have hL0 : 0 < L := by
      by_contra hn
      have : L / 2 / Real.sqrt R ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hsR.le
      linarith
    exact div_le_div_of_nonneg_right (by linarith) hsR.le
  have hfe := H.edist_trace_le_of_firstExit_CXJD haT seedTrace haS haσ hσT hσlast A hℓ hT₀ records
    hOld hcan hacc hDm hprotC (hRicC_of_hgood_ceiling_CXJD hC2 H haT hsmall hclock seedTrace ha₀
      hpin hσT has y L hR hgood hQb hstep haS haσ hσlast haL hdepth hRa hz A hℓ hKℓ hℓr hKr hKC hℓρ
      hρL) hmargin
  intro v hav hvt
  have hv := hfe v hav hvt
  have hdv : 8 / ℓ * ((σ : ℝ) - v) ≤ 8 / ℓ * ((σ : ℝ) - a) :=
    mul_le_mul_of_nonneg_left (by linarith [show (a : ℝ) ≤ v from hav]) h8
  exact hv.trans ((add_le_add le_rfl (ENNReal.ofReal_le_ofReal hdv)).trans
    (hmargin.le.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hL))))

/-- **consumer：跨 slab ceiling（`_CXJD`）**：`hstop_of_firstExit_CXJD` 喂 CXJT0
`scalar_le_two_mul_stopped_ceiling_CXJT0` ⇒ 沿 trace `[a, σ]`（跨 slab）`R ≤ 2·Q_b·R`。 -/
theorem scalar_le_two_mul_crossSlab_ceiling_CXJD {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    {Cg Cball Qb T K ℓ D : ℝ} (hC2 : 0 ≤ C2') (H : ObservedHistory.{u})
    {Tn aSeed a σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn) {pT : (H.stageAt Tn).Carrier}
    {r : ℝ} (hsmall : GC.LongTime.hasSmallParabolicCurvature H Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a₀ + t) x)
    (hσT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (H.stageAt σ).Carrier) {R : ℝ} (L : ℝ) (hR : 0 < R)
    (hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hσT))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hσT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hQb : max (max Cball Cg) 1 ≤ Qb) (hstep : 2 * Ctime' * Qb * T ≤ 1)
    (haS : aSeed ≤ a) (haσ : a ≤ σ) (hσlast : H.activeStage σ < Fin.last H.eventCount)
    (haL : (σ : ℝ) - L ^ 2 / R ≤ a) (hdepth : (σ : ℝ) - a ≤ T / R) (hRa : 1 ≤ R * a)
    {z : (H.stageAt σ).Carrier}
    (hz : metricScalarAt (H.stageMetric (H.activeStage σ) σ) z ≤ Cball * R)
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage σ) (H.activeStage_mono haσ) z)
    (hℓ : 0 < ℓ) (hKℓ : K * ℓ ^ 2 ≤ 1) (hℓr : ℓ ≤ r / 50) (hKr : 1 / r ^ 2 ≤ K)
    (hKC : 2 * Real.sqrt 3 * (6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4)) * R ≤ K)
    (hℓρ : ℓ ≤ localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)))
    (hρL : 2 * (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R))) ≤ L / 2 / Real.sqrt R)
    {q : CutoffParameters} {T₀ : ℝ} (hT₀ : T₀ ≤ (a : ℝ))
    (records : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → GeometricCutoffRecord H e q)
    (hOld : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ →
      (H.event e).old = (H.event e).transition.trace.retainedCore)
    (hcan : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b,
      ((records e he).static b).hasCanonicalWindow)
    (hacc : q.modelAccuracy ≤ 1 / 2) (hDm : StandardCap.transitionEnd + 10 < q.modelRadius)
    (hprotC : ∀ (e : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ e.castSucc)
        (h2 : e.succ ≤ H.activeStage Tn) (h3 : H.activeStage a ≤ e.castSucc)
        (h4 : e.succ ≤ H.activeStage σ) (he : T₀ ≤ H.time e.succ),
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvσ : v ≤ σ), H.time e.succ ≤ (v : ℝ) →
          riemannianEDistOf (H.stageMetric (H.activeStage v) v)
              (seedTrace.point (H.activeStage v) (H.activeStage_mono (haS.trans hav))
                (H.activeStage_mono (hvσ.trans hσT)))
              (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvσ)) <
            riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
                (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                  (H.activeStage_mono hσT)) y +
              ENNReal.ofReal (L / 2 / Real.sqrt R)) → ∀ b,
        seedTrace.point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
            ((records e he).static b).window ''
              {w : standardCapWindow q.modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10} ∧
          A.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
            ((records e he).static b).window ''
              {w : standardCapWindow q.modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10})
    (hzy : z ∈ riemannianBallOf (H.stageMetric (H.activeStage σ) σ) y (D / Real.sqrt R))
    (hdσ : riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
        (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
          (H.activeStage_mono hσT)) y ≠ ⊤)
    (hnum : D / Real.sqrt R + 8 / ℓ * (T / R) < L / 2 / Real.sqrt R) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ σ),
      metricScalarAt (H.stageMetric (H.activeStage v) v)
        (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ≤
        2 * (Qb * R) :=
  scalar_le_two_mul_stopped_ceiling_CXJT0 H haT hσT has seedTrace y L hR hgood hQb hstep haσ le_rfl
    haS haL hdepth hz A (hstop_of_firstExit_CXJD hC2 H haT hsmall hclock seedTrace ha₀ hpin hσT
      has y L hR hgood hQb hstep haS haσ hσlast haL hdepth hRa hz A hℓ hKℓ hℓr hKr hKC hℓρ hρL hT₀
      records hOld hcan hacc hDm
      hprotC hzy hdσ hnum)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
