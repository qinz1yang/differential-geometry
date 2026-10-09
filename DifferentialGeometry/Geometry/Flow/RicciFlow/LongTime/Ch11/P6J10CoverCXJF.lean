import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10FinalSlabCeilingCXJF

/-!
# event 形 + final 形覆盖全部 σ（CX-J10FIN G4，后缀 `_CXJF`）

* `activeStage_lt_last_of_eventInterior_CXJF`：hgapJ 的 σ（`∃ j, time j⁻ < σ < time j⁺`）⇒
  `activeStage σ < Fin.last` 且 `σ < horizon`——CXJD event 形与 CXJF 通用形都适用。
* consumer `example`：按 `activeStage σ` 分类（`< last` 走 CXJD `exists_crossSlab_ceiling_CXJD`，
  `= last` 走 CXJF `exists_finalSlab_ceiling_CXJF`）⇒ 任意 `σ < horizon` 的跨 slab ceiling `R ≤ 2Q_bR`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

/-- **hgapJ 的 σ 在 event slab 内部（`_CXJF`）**。 -/
theorem activeStage_lt_last_of_eventInterior_CXJF (H : ObservedHistory.{u})
    (σ : Icc (0 : ℝ) H.horizon)
    (hj : ∃ j : Fin H.eventCount, H.time j.castSucc < (σ : ℝ) ∧ (σ : ℝ) < H.time j.succ) :
    H.activeStage σ < Fin.last H.eventCount ∧ (σ : ℝ) < H.horizon := by
  obtain ⟨j, h1, h2⟩ := hj
  have hact : H.activeStage σ = j.castSucc :=
    (H.mem_stageDomain_iff σ j.castSucc).mp (by
      simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
        (show (σ : ℝ) ∈ Ico (H.time j.castSucc) (H.time j.succ) from ⟨h1.le, h2⟩))
  refine ⟨hact ▸ Fin.castSucc_lt_last j, h2.trans_le ?_⟩
  exact (H.time_strictMono.monotone (Fin.le_last _)).trans H.time_le_horizon

/-- consumer（`_CXJF` G4）：event 形 + final 形按 `activeStage σ` 分类覆盖全部 `σ < horizon`。 -/
example :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg Cball Qb T K ℓ D : ℝ} (_ : 0 ≤ C2')
    (KH : RetainedCoreHistory.{u}) {Tn aSeed a σ : Icc (0 : ℝ) KH.toHistory.horizon} (haT : aSeed
      ≤ Tn)
    {pT : (KH.toHistory.stageAt Tn).Carrier} {r : ℝ}
    (_ : GC.LongTime.hasSmallParabolicCurvature KH.toHistory Tn pT r)
    (_ : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace KH.toHistory (KH.toHistory.activeStage aSeed)
      (KH.toHistory.activeStage Tn)
      (KH.toHistory.activeStage_mono haT) pT)
    {a₀ : ℝ} (_ : 0 ≤ a₀)
    (_ : ∀ (t : Icc (0 : ℝ) KH.toHistory.horizon) (x : (KH.toHistory.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (KH.toHistory.stageMetric (KH.toHistory.activeStage t) t) (a₀ + t)
        x)
    (hσT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (KH.toHistory.stageAt σ).Carrier) {R : ℝ} (L : ℝ) (_ : 0
      < R)
    (_ : ∀ (v : Icc (0 : ℝ) KH.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (KH.toHistory.stageAt v).Carrier,
        riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v)
            (seedTrace.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono hav)
              (KH.toHistory.activeStage_mono (hvs.trans hσT))) z ≤
          riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
              (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
                (KH.toHistory.activeStage_mono hσT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v) z →
        KH.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (_ : max (max Cball Cg) 1 ≤ Qb) (_ : 2 * Ctime' * Qb * T ≤ 1) (_ : aSeed ≤ a)
    (haσ : a ≤ σ) (_ : (σ : ℝ) < KH.toHistory.horizon)
    (_ : (σ : ℝ) - L ^ 2 / R ≤ a) (_ : (σ : ℝ) - a ≤ T / R) (_ : 1 ≤ R * a)
    {z : (KH.toHistory.stageAt σ).Carrier}
    (_ : metricScalarAt (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ) z ≤ Cball * R)
    (A : BackwardPointTrace KH.toHistory (KH.toHistory.activeStage a) (KH.toHistory.activeStage σ)
      (KH.toHistory.activeStage_mono haσ) z)
    (_ : 0 < ℓ) (_ : K * ℓ ^ 2 ≤ 1) (_ : ℓ ≤ r / 50) (_ : 1 / r ^ 2 ≤ K)
    (_ : 2 * Real.sqrt 3 * (6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4)) * R ≤ K)
    (_ : ℓ ≤ localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)))
    (_ : 2 * (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R))) ≤ L / 2 / Real.sqrt R)
    {q : CutoffParameters} {T₀ : ℝ} (_ : T₀ ≤ (a : ℝ))
    (records : ∀ e : Fin KH.toHistory.eventCount, T₀ ≤ KH.toHistory.time e.succ →
      GeometricCutoffRecord KH.toHistory e q)
    (_ : ∀ e : Fin KH.toHistory.eventCount, T₀ ≤ KH.toHistory.time e.succ →
      (KH.toHistory.event e).old = (KH.toHistory.event e).transition.trace.retainedCore)
    (_ : ∀ (e : Fin KH.toHistory.eventCount) (he : T₀ ≤ KH.toHistory.time e.succ) b,
      ((records e he).static b).hasCanonicalWindow)
    (_ : StandardCap.transitionEnd + 10 < q.modelRadius)
    (_ : q.modelAccuracy ≤ ε₀) (_ : 2 ≤ q.modelOrder)
    (_ : ∀ (e : Fin KH.toHistory.eventCount) (he : T₀ ≤ KH.toHistory.time e.succ) b, (a : ℝ) <
      KH.toHistory.time e.succ →
      2 * max (3 / r ^ 2) (2 * (Qb * R)) < ((records e he).static b).neck.scale)
    (_ : z ∈ riemannianBallOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ) y (D /
      Real.sqrt R))
    (_ : riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
        (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
          (KH.toHistory.activeStage_mono hσT)) y ≠ ⊤)
    (_ : D / Real.sqrt R + 8 / ℓ * (T / R) < L / 2 / Real.sqrt R),
      ∀ (v : Icc (0 : ℝ) KH.toHistory.horizon) (hav : a ≤ v) (hvt : v ≤ σ),
        metricScalarAt (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v)
          (A.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono hav)
            (KH.toHistory.activeStage_mono hvt)) ≤
          2 * (Qb * R) := by
  obtain ⟨ε₁, hε₁, hD⟩ := exists_crossSlab_ceiling_CXJD.{u}
  obtain ⟨ε₂, hε₂, hF⟩ := exists_finalSlab_ceiling_CXJF.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro eps C1' C2' Ctime' Cg Cball Qb T K ℓ D hC2 KH Tn aSeed a σ haT pT r hsmall hclock seedTrace
    a₀ ha₀ hpin hσT has y R L hR hgood hQb hstep haS haσ hσH haL hdepth hRa z hz A hℓ hKℓ hℓr hKr
    hKC hℓρ hρL q T₀ hT₀ records hOld hcan hDm hacc hm hscale hzy hdσ hnum
  rcases (Fin.le_last (KH.toHistory.activeStage σ)).lt_or_eq with hlt | _
  · -- event 形（CXJD，`activeStage σ < last`）
    exact hD hC2 KH.toHistory haT hsmall hclock seedTrace ha₀ hpin hσT has y L hR hgood hQb hstep
      haS haσ hlt haL hdepth hRa hz A hℓ hKℓ hℓr hKr hKC hℓρ hρL hT₀ records hOld hcan hDm
      (hacc.trans (min_le_left _ _)) hm hscale hzy hdσ hnum
  · -- final 形（CXJF，`activeStage σ = last`）
    exact hF hC2 KH haT hsmall hclock seedTrace ha₀ hpin hσT has y L hR hgood hQb hstep haS haσ hσH
      haL hdepth hRa hz A hℓ hKℓ hℓr hKr hKC hℓρ hρL hT₀ records hOld hcan hDm
      (hacc.trans (min_le_right _ _)) hm hscale hzy hdσ hnum

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
