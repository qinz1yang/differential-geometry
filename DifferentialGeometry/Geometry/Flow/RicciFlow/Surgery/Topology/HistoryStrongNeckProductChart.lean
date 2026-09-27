import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeckClassSupply
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessProductChart

set_option autoImplicit false

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

variable {P₀ : OrientedThreeStage.{u}} (H : RetainedCoreHistory P₀)
  {F Hm N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace Hm] {J : ModelWithCorners ℝ F Hm} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace Hm N] [IsManifold J ∞ N]
  [T2Space N] [ConnectedSpace N] [SigmaCompactSpace N]

theorem historyStrongNeck_of_product_chart (k : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage k).IncomingSlab (H.time k) s) {ε ε₁ C1 C2 : ℝ}
    {y : (H.stage k).Carrier} {t : ℝ} (hε : ε ≤ 1 / 1000)
    (hcan : H.StronglyCanonicalAt k G ε ε₁ C1 C2 y t)
    (h : SmoothRiemannianMetric J N) (hdim : Module.finrank ℝ F = 2)
    (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens (H.stage k).Carrier)
    (Φ : O ≃ₘ⟮J.prod 𝓘(ℝ), I3⟯ V)
    (hcapture : riemannianBallOf (G.flow.base.metric t) y
      (2 * (C1 / Real.sqrt (metricScalarAt (G.flow.base.metric t) y))) ⊆ V)
    {eta : ℝ} (heta : eta ≤ 1 / 4)
    (hsmall : 720 * eta < C2⁻¹ * metricScalarAt (G.flow.base.metric t) y / 16)
    (hclose : ∀ z : V, z.val ∈ riemannianBallOf (G.flow.base.metric t) y
        (2 * (C1 / Real.sqrt (metricScalarAt (G.flow.base.metric t) y))) →
      ∀ m : ℕ, m ≤ 2 →
      metricDerivNorm m (Diffeomorph.pullbackMetricCross ((G.flow.base.metric t).restrictOpen V) Φ)
        ((h.prod (euclideanMetric (E := ℝ))).restrictOpen O)
        ((h.prod (euclideanMetric (E := ℝ))).restrictOpen O) (Φ.symm z) ≤ eta) :
    H.toHistory.HistoryStrongNeck k G ε₁ y t := by
  obtain ⟨W, hW, himp⟩ := hcan
  exact himp (W.exists_localNeck_of_ball_product_chart hW hε h hdim O V Φ hcapture heta hsmall
    hclose)

theorem hasStrongNeckAt_of_product_chart {ε ε₁ C1 C2 qcan : ℝ} (hε : ε ≤ 1 / 1000)
    (hclass : H.EventSlabsStronglyCanonical ε ε₁ C1 C2 qcan (Fin.last H.eventCount))
    (v : Icc (0 : ℝ) H.toHistory.horizon) (p : (H.toHistory.stageAt v).Carrier)
    (hev : H.time (H.toHistory.activeStage v) < v)
    (hterm : H.toHistory.activeStage v = Fin.last H.eventCount →
      ∃ (s : ℝ) (G : (H.stage (H.toHistory.activeStage v)).IncomingSlab
          (H.time (H.toHistory.activeStage v)) s),
        (v : ℝ) < s ∧
        (∀ τ ∈ Icc (H.time (H.toHistory.activeStage v)) (v : ℝ),
          G.flow.base.metric τ = H.toHistory.stageMetric (H.toHistory.activeStage v) τ) ∧
        H.StronglyCanonicalBefore (H.toHistory.activeStage v) G ε ε₁ C1 C2 qcan s)
    (hq : qcan < metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v) p)
    (h : SmoothRiemannianMetric J N) (hdim : Module.finrank ℝ F = 2)
    (O : TopologicalSpace.Opens (N × ℝ))
    (V : TopologicalSpace.Opens (H.toHistory.stageAt v).Carrier)
    (Φ : O ≃ₘ⟮J.prod 𝓘(ℝ), I3⟯ V)
    (hcapture : riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage v) v) p
      (2 * (C1 / Real.sqrt
        (metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v) p))) ⊆ V)
    {eta : ℝ} (heta : eta ≤ 1 / 4)
    (hsmall : 720 * eta <
      C2⁻¹ * metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v) p / 16)
    (hclose : ∀ z : V, z.val ∈ riemannianBallOf
        (H.toHistory.stageMetric (H.toHistory.activeStage v) v) p
        (2 * (C1 / Real.sqrt
          (metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v) p))) →
      ∀ m : ℕ, m ≤ 2 →
      metricDerivNorm m (Diffeomorph.pullbackMetricCross
          ((H.toHistory.stageMetric (H.toHistory.activeStage v) v).restrictOpen V) Φ)
        ((h.prod (euclideanMetric (E := ℝ))).restrictOpen O)
        ((h.prod (euclideanMetric (E := ℝ))).restrictOpen O) (Φ.symm z) ≤ eta) :
    H.toHistory.HasStrongNeckAt ε₁ v p := by
  obtain ⟨s, G, hvs, hG, hbefore⟩ := H.exists_currentSlab_stronglyCanonicalBefore hclass v hterm
  have hGv : G.flow.base.metric v = H.toHistory.stageMetric (H.toHistory.activeStage v) v :=
    hG v ⟨H.toHistory.activeStage_time_le v, le_rfl⟩
  rw [← hGv] at hq hcapture hsmall hclose
  exact ⟨s, G, hvs, hG, H.historyStrongNeck_of_product_chart _ G hε
    (hbefore p v ⟨hev, hvs⟩ hq) h hdim O V Φ hcapture heta hsmall hclose⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
