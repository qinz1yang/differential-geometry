import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComponentVolumeBridge
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff ENNReal
namespace GC.GeneralFlow
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem exists_ball_volume_from_kappa_model (κ Cm1 Cm2 Cs1 Cs2 : ℝ)
    (hκ : 0 < κ) (hCm2 : 0 < Cm2) :
    ∃ k : ℝ, 0 < k ∧ ∀ {P : OrientedThreeStage.{u}} {D : RealTimeInterval}
      {S : SolutionOn (I := I3) (M := P.Carrier) D}
      {δ εm εs : ℝ} {x : P.Carrier} {t : ℝ}
      (W : WindowedModelWitness δ κ S x t)
      (K : CanonicalWitness W.model.S εm Cm1 Cm2 W.model.basepoint 0)
      (V : SpatialCanonicalWitness (S.base.metric t) εs Cs1 Cs2 x),
      δ ≤ 1 / 2 → 2 * Cm1 ≤ modelRadius δ →
      K.domain.carrier = connectedComponent W.model.basepoint →
      V.domain.carrier = connectedComponent x →
      ∀ r : ℝ, 0 < r →
      r ^ 4 * normSq0S (S.base.metric t) x 4 (metricRm04At (S.base.metric t) x) ≤ 1 →
      ENNReal.ofReal (k * r ^ 3) ≤
        riemannianVolumeMeasure I3 P.Carrier (S.base.metric t)
          (riemannianBallOf (S.base.metric t) x r) := by
  have hν : 0 < κ * (Cm2⁻¹)^3 / 4 := by positivity
  obtain ⟨k,hk,hball⟩ :=
    exists_ball_volume_of_normalizedComponentVolume.{u} Cs1 Cs2 (κ * (Cm2⁻¹)^3 / 4) hν
  refine ⟨k,hk,?_⟩
  intro P D S δ εm εs x t W K V hδ hbuffer hwhole hVwhole r hr hcurv
  apply hball V hVwhole ?_ r hr hcurv
  rw [hVwhole]
  exact sourcedWholeComponentVolume W K hδ hbuffer hwhole

end GC.GeneralFlow
