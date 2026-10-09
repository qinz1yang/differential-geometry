import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10TopCeilingCXJF2
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryExtendAt

/-!
# extendAt 上的 σ = horizon ceiling（CX-J10FIN2 G4，后缀 `_CXJF2`）

ch8 `hsurvive_noJ10_P6JC` 的消费形：`Hs = H.extendAt hend G hG hat hts`、
`σ = extendAtTime = horizon(Hs) = t`。
* `hUSCtop_extendAt_CXJF2`：extendAt 的 final slab = `G.closedPrefix t`（flow = `G.flow` 的时间限制），
  `t < s` 是
  `G` 的内部时刻 ⇒ 树内 `edist_lt_near_left_P6L4`（在 `G.flow` 上，`[lo, t] ⊆ G.regular`）给 horizon 处的左延拓。
  **不需要新事实**。
* `exists_extendAt_ceiling_CXJF2`：`exists_finalSlab_ceiling_CXJF` 结论逐字，`KH := H.extendAt …`，
  **无** `σ < horizon`（`σ ≤ horizon` 由 `σ : Icc 0 horizon` 自带）。
* consumer `example`：`σ := H.extendAtTime …`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

/-- **extendAt 的 horizon 左延拓（`_CXJF2`）**：final slab = `G.closedPrefix t`，`t < s` 为 `G` 内部。 -/
theorem hUSCtop_extendAt_CXJF2 (Hb : RetainedCoreHistory.{u})
    (hend : Hb.time (Fin.last Hb.eventCount) = Hb.horizon) {sb : ℝ}
    (Gb : (Hb.stage (Fin.last Hb.eventCount)).IncomingSlab (Hb.time (Fin.last Hb.eventCount)) sb)
    (hG : Gb.flow.base.metric (Hb.time (Fin.last Hb.eventCount)) =
      Hb.initialMetric (Fin.last Hb.eventCount))
    {tb : ℝ} (hat : Hb.time (Fin.last Hb.eventCount) < tb) (hts : tb < sb)
    (σ : Icc (0 : ℝ) (Hb.extendAt hend Gb hG hat hts).toHistory.horizon) :
    (σ : ℝ) = (Hb.extendAt hend Gb hG hat hts).toHistory.horizon →
      ∀ (hfT : (Hb.extendAt hend Gb hG hat hts).toHistory.time
          (Fin.last (Hb.extendAt hend Gb hG hat hts).toHistory.eventCount) <
          (Hb.extendAt hend Gb hG hat hts).toHistory.horizon)
      (p q : ((Hb.extendAt hend Gb hG hat hts).toHistory.stage
        (Fin.last (Hb.extendAt hend Gb hG hat hts).toHistory.eventCount)).Carrier) (X' : ℝ≥0∞),
      riemannianEDistOf (((Hb.extendAt hend Gb hG hat hts).toHistory.finalSlab hfT).flow.base.metric
        σ) p q < X' →
      ∃ s₁ : ℝ, s₁ < σ ∧ ∀ s' ∈ Icc s₁ (σ : ℝ),
        riemannianEDistOf (((Hb.extendAt hend Gb hG hat hts).toHistory.finalSlab
          hfT).flow.base.metric s') p q < X' := by
  intro hσ _ p q X' hX
  have hσt : (σ : ℝ) = tb := hσ
  have hlo : (Hb.time (Fin.last Hb.eventCount) + tb) / 2 < (σ : ℝ) := by rw [hσt]; linarith
  obtain ⟨s₁, -, hs₁, hnear⟩ := edist_lt_near_left_P6L4 Gb.flow Gb.equation hlo
    (fun r hr => ⟨lt_of_lt_of_le (by linarith) hr.1, lt_of_le_of_lt (hσt ▸ hr.2) hts⟩)
    p q hX
  exact ⟨s₁, hs₁, hnear⟩

/-- **extendAt 上的 ceiling（`_CXJF2`）**：`exists_finalSlab_ceiling_CXJF` 结论逐字，`KH := extendAt`，
无 `σ < horizon` 前提。 -/
theorem exists_extendAt_ceiling_CXJF2 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {eps C1' C2' : ℝ}
    {Ctime' : ℝ≥0}
    {Cg Cball Qb T K ℓ D : ℝ}
    (_ : 0 ≤ C2')
    (Hb : RetainedCoreHistory.{u})
    (hend : Hb.time (Fin.last Hb.eventCount) = Hb.horizon) {sb : ℝ}
    (Gb : (Hb.stage (Fin.last Hb.eventCount)).IncomingSlab (Hb.time (Fin.last Hb.eventCount)) sb)
    (hG : Gb.flow.base.metric (Hb.time (Fin.last Hb.eventCount)) = Hb.initialMetric (Fin.last
      Hb.eventCount))
    {tb : ℝ} (hat : Hb.time (Fin.last Hb.eventCount) < tb) (hts : tb < sb)
    {Tn aSeed a σ : Icc (0 : ℝ) (Hb.extendAt hend Gb hG hat hts).toHistory.horizon}
    (haT : aSeed
      ≤ Tn)
    {pT : ((Hb.extendAt hend Gb hG hat hts).toHistory.stageAt Tn).Carrier}
    {r : ℝ}
    (_ : GC.LongTime.hasSmallParabolicCurvature (Hb.extendAt hend Gb hG hat hts).toHistory Tn pT r)
    (_ : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace (Hb.extendAt hend Gb hG hat hts).toHistory ((Hb.extendAt hend
      Gb hG hat hts).toHistory.activeStage aSeed)
      ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage Tn)
      ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage_mono haT) pT)
    {a₀ : ℝ}
    (_ : 0 ≤ a₀)
    (_ : ∀ (t : Icc (0 : ℝ) (Hb.extendAt hend Gb hG hat hts).toHistory.horizon) (x : ((Hb.extendAt
      hend Gb hG hat hts).toHistory.stageAt t).Carrier),
      InFixedHamiltonIveyRegion ((Hb.extendAt hend Gb hG hat hts).toHistory.stageMetric
        ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage t) t) (a₀ + t)
        x)
    (hσT : σ ≤ Tn)
    (has : aSeed ≤ σ)
    (y : ((Hb.extendAt hend Gb hG hat hts).toHistory.stageAt σ).Carrier)
    {R : ℝ}
    (L : ℝ)
    (_ : 0
      < R)
    (_ : ∀ (v : Icc (0 : ℝ) (Hb.extendAt hend Gb hG hat hts).toHistory.horizon) (hav : aSeed ≤ v)
      (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : ((Hb.extendAt hend Gb hG hat hts).toHistory.stageAt v).Carrier,
        riemannianEDistOf ((Hb.extendAt hend Gb hG hat hts).toHistory.stageMetric ((Hb.extendAt
          hend Gb hG hat hts).toHistory.activeStage v) v)
            (seedTrace.point ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage v)
              ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage_mono hav)
              ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage_mono (hvs.trans hσT))) z ≤
          riemannianEDistOf ((Hb.extendAt hend Gb hG hat hts).toHistory.stageMetric ((Hb.extendAt
            hend Gb hG hat hts).toHistory.activeStage σ) σ)
              (seedTrace.point ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage σ)
                ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage_mono has)
                ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage_mono hσT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt ((Hb.extendAt hend Gb hG hat hts).toHistory.stageMetric
          ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage v) v) z →
        (Hb.extendAt hend Gb hG hat hts).toHistory.HasSpatialCanonicalTimeControl eps C1' C2'
          Ctime' v z)
    (_ : max (max Cball Cg) 1 ≤ Qb)
    (_ : 2 * Ctime' * Qb * T ≤ 1)
    (_ : aSeed ≤ a)
    (haσ : a ≤ σ)
    (_ : (σ : ℝ) - L ^ 2 / R ≤ a)
    (_ : (σ : ℝ) - a ≤ T / R)
    (_ : 1 ≤ R * a)
    {z : ((Hb.extendAt hend Gb hG hat hts).toHistory.stageAt σ).Carrier}
    (_ : metricScalarAt ((Hb.extendAt hend Gb hG hat hts).toHistory.stageMetric ((Hb.extendAt hend
      Gb hG hat hts).toHistory.activeStage σ) σ) z ≤ Cball * R)
    (A : BackwardPointTrace (Hb.extendAt hend Gb hG hat hts).toHistory ((Hb.extendAt hend Gb hG
      hat hts).toHistory.activeStage a) ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage σ)
      ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage_mono haσ) z)
    (_ : 0 < ℓ)
    (_ : K * ℓ ^ 2 ≤ 1)
    (_ : ℓ ≤ r / 50)
    (_ : 1 / r ^ 2 ≤ K)
    (_ : 2 * Real.sqrt 3 * (6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4)) * R ≤ K)
    (_ : ℓ ≤ localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)))
    (_ : 2 * (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R))) ≤ L / 2 / Real.sqrt R)
    {q : CutoffParameters}
    {T₀ : ℝ}
    (_ : T₀ ≤ (a : ℝ))
    (records : ∀ e : Fin (Hb.extendAt hend Gb hG hat hts).toHistory.eventCount, T₀ ≤ (Hb.extendAt
      hend Gb hG hat hts).toHistory.time e.succ →
      GeometricCutoffRecord (Hb.extendAt hend Gb hG hat hts).toHistory e q)
    (_ : ∀ e : Fin (Hb.extendAt hend Gb hG hat hts).toHistory.eventCount, T₀ ≤ (Hb.extendAt hend
      Gb hG hat hts).toHistory.time e.succ →
      ((Hb.extendAt hend Gb hG hat hts).toHistory.event e).old = ((Hb.extendAt hend Gb hG hat
        hts).toHistory.event e).transition.trace.retainedCore)
    (_ : ∀ (e : Fin (Hb.extendAt hend Gb hG hat hts).toHistory.eventCount) (he : T₀ ≤ (Hb.extendAt
      hend Gb hG hat hts).toHistory.time e.succ) b,
      ((records e he).static b).hasCanonicalWindow)
    (_ : StandardCap.transitionEnd + 10 < q.modelRadius)
    (_ : q.modelAccuracy ≤ ε₀)
    (_ : 2 ≤ q.modelOrder)
    (_ : ∀ (e : Fin (Hb.extendAt hend Gb hG hat hts).toHistory.eventCount) (he : T₀ ≤ (Hb.extendAt
      hend Gb hG hat hts).toHistory.time e.succ) b, (a : ℝ) <
      (Hb.extendAt hend Gb hG hat hts).toHistory.time e.succ →
      2 * max (3 / r ^ 2) (2 * (Qb * R)) < ((records e he).static b).neck.scale)
    (_ : z ∈ riemannianBallOf ((Hb.extendAt hend Gb hG hat hts).toHistory.stageMetric
      ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage σ) σ) y (D /
      Real.sqrt R))
    (_ : riemannianEDistOf ((Hb.extendAt hend Gb hG hat hts).toHistory.stageMetric ((Hb.extendAt
      hend Gb hG hat hts).toHistory.activeStage σ) σ)
        (seedTrace.point ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage σ) ((Hb.extendAt
          hend Gb hG hat hts).toHistory.activeStage_mono has)
          ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage_mono hσT)) y ≠ ⊤)
    (_ : D / Real.sqrt R + 8 / ℓ * (T / R) < L / 2 / Real.sqrt R),
      ∀ (v : Icc (0 : ℝ) (Hb.extendAt hend Gb hG hat hts).toHistory.horizon) (hav : a ≤ v) (hvt :
        v ≤ σ),
        metricScalarAt ((Hb.extendAt hend Gb hG hat hts).toHistory.stageMetric ((Hb.extendAt hend
          Gb hG hat hts).toHistory.activeStage v) v)
          (A.point ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage v) ((Hb.extendAt hend
            Gb hG hat hts).toHistory.activeStage_mono hav)
            ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage_mono hvt)) ≤
          2 * (Qb * R) := by
  obtain ⟨ε₀, hε₀, h⟩ := exists_top_ceiling_CXJF2.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro eps C1' C2' Ctime' Cg Cball Qb T K ℓ D hC2 Hb hend sb Gb hG tb hat hts Tn aSeed a σ haT pT
    r hsmall hclock seedTrace a₀ ha₀ hpin hσT has y R L hR hgood hQb hstep haS haσ haL hdepth hRa z
    hz A hℓ hKℓ hℓr hKr hKC hℓρ hρL q T₀ hT₀ records hOld hcan hDm hacc hm hscale hzy hdσ hnum
  exact h hC2 (Hb.extendAt hend Gb hG hat hts) haT hsmall hclock seedTrace ha₀ hpin hσT has y L hR
    hgood hQb hstep haS haσ (hUSCtop_extendAt_CXJF2 Hb hend Gb hG hat hts _) haL hdepth hRa hz A hℓ
    hKℓ hℓr hKr hKC hℓρ hρL hT₀ records hOld hcan hDm hacc hm hscale hzy hdσ hnum


/-- consumer（`_CXJF2` G4）：ch8 `hsurvive_noJ10_P6JC` 的形——`Hs = H.extendAt …`、`σ := H.extendAtTime …`
（= horizon(Hs)）处实例化 `exists_extendAt_ceiling_CXJF2`。 -/
example :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {eps C1' C2' : ℝ}
    {Ctime' : ℝ≥0}
    {Cg Cball Qb T K ℓ D : ℝ}
    (_ : 0 ≤ C2')
    (Hb : RetainedCoreHistory.{u})
    (hend : Hb.time (Fin.last Hb.eventCount) = Hb.horizon) {sb : ℝ}
    (Gb : (Hb.stage (Fin.last Hb.eventCount)).IncomingSlab (Hb.time (Fin.last Hb.eventCount)) sb)
    (hG : Gb.flow.base.metric (Hb.time (Fin.last Hb.eventCount)) = Hb.initialMetric (Fin.last
      Hb.eventCount))
    {tb : ℝ} (hat : Hb.time (Fin.last Hb.eventCount) < tb) (hts : tb < sb)
    {Tn aSeed a : Icc (0 : ℝ) (Hb.extendAt hend Gb hG hat hts).toHistory.horizon}
    (haT : aSeed
      ≤ Tn)
    {pT : ((Hb.extendAt hend Gb hG hat hts).toHistory.stageAt Tn).Carrier}
    {r : ℝ}
    (_ : GC.LongTime.hasSmallParabolicCurvature (Hb.extendAt hend Gb hG hat hts).toHistory Tn pT r)
    (_ : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace (Hb.extendAt hend Gb hG hat hts).toHistory ((Hb.extendAt hend
      Gb hG hat hts).toHistory.activeStage aSeed)
      ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage Tn)
      ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage_mono haT) pT)
    {a₀ : ℝ}
    (_ : 0 ≤ a₀)
    (_ : ∀ (t : Icc (0 : ℝ) (Hb.extendAt hend Gb hG hat hts).toHistory.horizon) (x : ((Hb.extendAt
      hend Gb hG hat hts).toHistory.stageAt t).Carrier),
      InFixedHamiltonIveyRegion ((Hb.extendAt hend Gb hG hat hts).toHistory.stageMetric
        ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage t) t) (a₀ + t)
        x)
    (hσT : (Hb.extendAtTime hend Gb hG hat hts) ≤ Tn)
    (has : aSeed ≤ (Hb.extendAtTime hend Gb hG hat hts))
    (y : ((Hb.extendAt hend Gb hG hat hts).toHistory.stageAt (Hb.extendAtTime hend Gb hG hat
      hts)).Carrier)
    {R : ℝ}
    (L : ℝ)
    (_ : 0
      < R)
    (_ : ∀ (v : Icc (0 : ℝ) (Hb.extendAt hend Gb hG hat hts).toHistory.horizon) (hav : aSeed ≤ v)
      (hvs : v ≤ (Hb.extendAtTime hend Gb hG hat hts)),
      ((Hb.extendAtTime hend Gb hG hat hts) : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : ((Hb.extendAt hend Gb hG hat hts).toHistory.stageAt v).Carrier,
        riemannianEDistOf ((Hb.extendAt hend Gb hG hat hts).toHistory.stageMetric ((Hb.extendAt
          hend Gb hG hat hts).toHistory.activeStage v) v)
            (seedTrace.point ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage v)
              ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage_mono hav)
              ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage_mono (hvs.trans hσT))) z ≤
          riemannianEDistOf ((Hb.extendAt hend Gb hG hat hts).toHistory.stageMetric ((Hb.extendAt
            hend Gb hG hat hts).toHistory.activeStage (Hb.extendAtTime hend Gb hG hat hts))
              (Hb.extendAtTime hend Gb hG hat hts))
              (seedTrace.point ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage
                (Hb.extendAtTime hend Gb hG hat hts))
                ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage_mono has)
                ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage_mono hσT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt ((Hb.extendAt hend Gb hG hat hts).toHistory.stageMetric
          ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage v) v) z →
        (Hb.extendAt hend Gb hG hat hts).toHistory.HasSpatialCanonicalTimeControl eps C1' C2'
          Ctime' v z)
    (_ : max (max Cball Cg) 1 ≤ Qb)
    (_ : 2 * Ctime' * Qb * T ≤ 1)
    (_ : aSeed ≤ a)
    (haσ : a ≤ (Hb.extendAtTime hend Gb hG hat hts))
    (_ : ((Hb.extendAtTime hend Gb hG hat hts) : ℝ) - L ^ 2 / R ≤ a)
    (_ : ((Hb.extendAtTime hend Gb hG hat hts) : ℝ) - a ≤ T / R)
    (_ : 1 ≤ R * a)
    {z : ((Hb.extendAt hend Gb hG hat hts).toHistory.stageAt (Hb.extendAtTime hend Gb hG hat
      hts)).Carrier}
    (_ : metricScalarAt ((Hb.extendAt hend Gb hG hat hts).toHistory.stageMetric ((Hb.extendAt hend
      Gb hG hat hts).toHistory.activeStage (Hb.extendAtTime hend Gb hG hat hts)) (Hb.extendAtTime
        hend Gb hG hat hts)) z ≤ Cball * R)
    (A : BackwardPointTrace (Hb.extendAt hend Gb hG hat hts).toHistory ((Hb.extendAt hend Gb hG
      hat hts).toHistory.activeStage a) ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage
        (Hb.extendAtTime hend Gb hG hat hts))
      ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage_mono haσ) z)
    (_ : 0 < ℓ)
    (_ : K * ℓ ^ 2 ≤ 1)
    (_ : ℓ ≤ r / 50)
    (_ : 1 / r ^ 2 ≤ K)
    (_ : 2 * Real.sqrt 3 * (6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4)) * R ≤ K)
    (_ : ℓ ≤ localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)))
    (_ : 2 * (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R))) ≤ L / 2 / Real.sqrt R)
    {q : CutoffParameters}
    {T₀ : ℝ}
    (_ : T₀ ≤ (a : ℝ))
    (records : ∀ e : Fin (Hb.extendAt hend Gb hG hat hts).toHistory.eventCount, T₀ ≤ (Hb.extendAt
      hend Gb hG hat hts).toHistory.time e.succ →
      GeometricCutoffRecord (Hb.extendAt hend Gb hG hat hts).toHistory e q)
    (_ : ∀ e : Fin (Hb.extendAt hend Gb hG hat hts).toHistory.eventCount, T₀ ≤ (Hb.extendAt hend
      Gb hG hat hts).toHistory.time e.succ →
      ((Hb.extendAt hend Gb hG hat hts).toHistory.event e).old = ((Hb.extendAt hend Gb hG hat
        hts).toHistory.event e).transition.trace.retainedCore)
    (_ : ∀ (e : Fin (Hb.extendAt hend Gb hG hat hts).toHistory.eventCount) (he : T₀ ≤ (Hb.extendAt
      hend Gb hG hat hts).toHistory.time e.succ) b,
      ((records e he).static b).hasCanonicalWindow)
    (_ : StandardCap.transitionEnd + 10 < q.modelRadius)
    (_ : q.modelAccuracy ≤ ε₀)
    (_ : 2 ≤ q.modelOrder)
    (_ : ∀ (e : Fin (Hb.extendAt hend Gb hG hat hts).toHistory.eventCount) (he : T₀ ≤ (Hb.extendAt
      hend Gb hG hat hts).toHistory.time e.succ) b, (a : ℝ) <
      (Hb.extendAt hend Gb hG hat hts).toHistory.time e.succ →
      2 * max (3 / r ^ 2) (2 * (Qb * R)) < ((records e he).static b).neck.scale)
    (_ : z ∈ riemannianBallOf ((Hb.extendAt hend Gb hG hat hts).toHistory.stageMetric
      ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage (Hb.extendAtTime hend Gb hG hat
        hts)) (Hb.extendAtTime hend Gb hG hat hts)) y (D /
      Real.sqrt R))
    (_ : riemannianEDistOf ((Hb.extendAt hend Gb hG hat hts).toHistory.stageMetric ((Hb.extendAt
      hend Gb hG hat hts).toHistory.activeStage (Hb.extendAtTime hend Gb hG hat hts))
        (Hb.extendAtTime hend Gb hG hat hts))
        (seedTrace.point ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage (Hb.extendAtTime
          hend Gb hG hat hts)) ((Hb.extendAt
          hend Gb hG hat hts).toHistory.activeStage_mono has)
          ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage_mono hσT)) y ≠ ⊤)
    (_ : D / Real.sqrt R + 8 / ℓ * (T / R) < L / 2 / Real.sqrt R),
      ∀ (v : Icc (0 : ℝ) (Hb.extendAt hend Gb hG hat hts).toHistory.horizon) (hav : a ≤ v) (hvt :
        v ≤ (Hb.extendAtTime hend Gb hG hat hts)),
        metricScalarAt ((Hb.extendAt hend Gb hG hat hts).toHistory.stageMetric ((Hb.extendAt hend
          Gb hG hat hts).toHistory.activeStage v) v)
          (A.point ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage v) ((Hb.extendAt hend
            Gb hG hat hts).toHistory.activeStage_mono hav)
            ((Hb.extendAt hend Gb hG hat hts).toHistory.activeStage_mono hvt)) ≤
          2 * (Qb * R) := by
  obtain ⟨ε₀, hε₀, h⟩ := exists_extendAt_ceiling_CXJF2.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro eps C1' C2' Ctime' Cg Cball Qb T K ℓ D hC2 Hb hend sb Gb hG tb hat hts Tn aSeed a haT pT r
    hsmall hclock seedTrace a₀ ha₀ hpin hσT has y R L hR hgood hQb hstep haS haσ haL hdepth hRa z
    hz A hℓ hKℓ hℓr hKr hKC hℓρ hρL q T₀ hT₀ records hOld hcan hDm hacc hm hscale hzy hdσ hnum
  exact h hC2 Hb hend Gb hG hat hts haT hsmall hclock seedTrace ha₀ hpin hσT has y L hR hgood hQb
    hstep haS haσ haL hdepth hRa hz A hℓ hKℓ hℓr hKr hKC hℓρ hρL hT₀ records hOld hcan hDm hacc hm
    hscale hzy hdσ hnum

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
