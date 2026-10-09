import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10TopCeilingCXJF2
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison

/-!
# 一般 final ClosedSlab 在右端的 `hUSCtop`（CX-USCTOP G1，后缀 `_CXUT`）

`exists_top_ceiling_CXJF2` 的显式前提 `hUSCtop`（`σ = horizon` 时 final slab 度量距离左连续）
在**任意** `P.ClosedSlab a b` 上由树内事实内部付清，不需要 extendAt 的 incoming slab：
* `exists_abs_ricci_bound_P6L4`：`IsSolutionOn` 的 `ricciCont` ⇒ `Icc a b` 上 `|Ric| ≤ K g`；
* `metricPDE_Icc`：`closed a b` 的 `regular = Ioo a b` 加连续性 ⇒ `HasDerivWithinAt`
  （含右端点，经 `smoothMetric` / `ricciCont` 的 carrier 连续性）；
* `riemannianEDistOf_exp_bounds_of_abs_ricciTensor_le`：`d_s ≤ e^{K|s − b|} d_b`。
`smoothUpTo` 本身不需要：carrier 上的连续性已在 `IsSolutionOn` 内。
主定理 `hUSCtop_of_closedSlab_CXUT`（任意 slab）、`hUSCtop_of_finalClosedSlab_CXUT`
（`ObservedHistory` 形，逐字对齐 `hUSCtop` binder）、`exists_top_ceiling_general_CXUT`
（`exists_top_ceiling_CXJF2` 去掉 `hUSCtop` binder）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **ClosedSlab 右端距离左连续（`_CXUT`）**：`d_b(p, q) < X'` ⇒ 某 `s₁ < b`，`[s₁, b]` 上
`d_s(p, q) < X'`。 -/
theorem edist_lt_near_left_closedSlab_CXUT {P : OrientedThreeStage.{u}} {a b : ℝ}
    (G : P.ClosedSlab a b) (p q : P.Carrier) {X : ℝ≥0∞}
    (hX : riemannianEDistOf (G.flow.base.metric b) p q < X) :
    ∃ s₁ : ℝ, s₁ < b ∧ ∀ s ∈ Icc s₁ b, riemannianEDistOf (G.flow.base.metric s) p q < X := by
  have hcar : Icc a b ⊆ (RealTimeInterval.closed a b G.lt.le).carrier := subset_rfl
  have hreg : Ioo a b ⊆ (RealTimeInterval.closed a b G.lt.le).regular := subset_rfl
  obtain ⟨K, -, hric⟩ := exists_abs_ricci_bound_P6L4 G.flow G.equation (a := a) (b := b) hcar
  have hpde := metricPDE_Icc G.flow G.equation hcar hreg
  have hd : riemannianEDistOf (G.flow.base.metric b) p q ≠ ⊤ := ne_top_of_lt hX
  have hcont : Continuous fun s : ℝ => ENNReal.ofReal (Real.exp (K * |s - b|)) :=
    ENNReal.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const).abs))
  have hT : Tendsto (fun s : ℝ => ENNReal.ofReal (Real.exp (K * |s - b|)) *
      riemannianEDistOf (G.flow.base.metric b) p q) (𝓝 b)
      (𝓝 (ENNReal.ofReal (Real.exp (K * |b - b|)) *
        riemannianEDistOf (G.flow.base.metric b) p q)) :=
    ENNReal.Tendsto.mul_const (hcont.tendsto b) (Or.inr hd)
  have h1 : ENNReal.ofReal (Real.exp (K * |b - b|)) *
      riemannianEDistOf (G.flow.base.metric b) p q =
      riemannianEDistOf (G.flow.base.metric b) p q := by simp
  rw [h1] at hT
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hT.eventually_lt_const hX)
  refine ⟨max a (b - ε / 2), max_lt G.lt (by linarith), fun s hs => ?_⟩
  have hsI : s ∈ Icc a b := ⟨(le_max_left _ _).trans hs.1, hs.2⟩
  have hb : b ∈ Icc a b := ⟨G.lt.le, le_rfl⟩
  have hexp := (riemannianEDistOf_exp_bounds_of_abs_ricciTensor_le
    (fun u => G.flow.base.metric u) (fun r hr z v => hpde r hr z v v) hric hsI hb p q).2
  refine lt_of_le_of_lt hexp (hball ?_)
  have h2 : b - ε / 2 ≤ s := (le_max_right _ _).trans hs.1
  rw [Real.dist_eq, abs_of_nonpos (by linarith [hs.2])]
  linarith

/-- **`hUSCtop`（任意 ClosedSlab 形，`_CXUT`）**：`σ = b` 时的 `hUSCtop` 陈述。 -/
theorem hUSCtop_of_closedSlab_CXUT {P : OrientedThreeStage.{u}} {a b : ℝ}
    (G : P.ClosedSlab a b) {σ : ℝ} (hσ : σ = b) (p q : P.Carrier) (X' : ℝ≥0∞)
    (h : riemannianEDistOf (G.flow.base.metric σ) p q < X') :
    ∃ s₁ : ℝ, s₁ < σ ∧ ∀ s' ∈ Icc s₁ σ, riemannianEDistOf (G.flow.base.metric s') p q < X' := by
  subst hσ
  exact edist_lt_near_left_closedSlab_CXUT G p q h

namespace ObservedHistory

/-- **`hUSCtop`（一般 final ClosedSlab，`_CXUT`）**：逐字对齐 `exists_top_ceiling_CXJF2` 等的
`hUSCtop` binder，对任意 `ObservedHistory` 与任意 `finalSlab` 成立。 -/
theorem hUSCtop_of_finalClosedSlab_CXUT (H : ObservedHistory.{u})
    (σ : Icc (0 : ℝ) H.horizon) :
    (σ : ℝ) = H.horizon → ∀ (hfT : H.time (Fin.last H.eventCount) < H.horizon)
      (p q : (H.stage (Fin.last H.eventCount)).Carrier) (X' : ℝ≥0∞),
      riemannianEDistOf ((H.finalSlab hfT).flow.base.metric σ) p q < X' →
      ∃ s₁ : ℝ, s₁ < σ ∧ ∀ s' ∈ Icc s₁ (σ : ℝ),
        riemannianEDistOf ((H.finalSlab hfT).flow.base.metric s') p q < X' :=
  fun hσ hfT p q X' h => hUSCtop_of_closedSlab_CXUT (H.finalSlab hfT) hσ p q X' h

/-- **consumer**：`exists_top_ceiling_CXJF2` 去掉 `hUSCtop` binder（一般 final slab 内部付清）。 -/
theorem exists_top_ceiling_general_CXUT :
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
    (haσ : a ≤ σ)
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
  obtain ⟨ε₀, hε₀, h⟩ := exists_top_ceiling_CXJF2.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro eps C1' C2' Ctime' Cg Cball Qb T K ℓ D hC2 KH Tn aSeed a σ haT pT r hsmall hclock
    seedTrace a₀ ha₀ hpin hσT has y R L hR hgood hQb hstep haS haσ haL hdepth hRa z hz A hℓ hKℓ
    hℓr hKr hKC hℓρ hρL q T₀ hT₀ records hOld hcan hDm hacc hm hscale hzy hdσ hnum
  exact h hC2 KH haT hsmall hclock seedTrace ha₀ hpin hσT has y L hR hgood hQb hstep haS haσ
    (hUSCtop_of_finalClosedSlab_CXUT KH.toHistory σ) haL hdepth hRa hz A hℓ hKℓ hℓr hKr hKC
    hℓρ hρL hT₀ records hOld hcan hDm hacc hm hscale hzy hdσ hnum

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
