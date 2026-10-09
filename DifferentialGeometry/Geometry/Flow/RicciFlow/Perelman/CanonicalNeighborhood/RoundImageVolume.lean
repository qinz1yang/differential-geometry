import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelBallVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RoundModelWitness
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff ENNReal
namespace GC.GeneralFlow
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem roundModelComponentVolume
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    {δ κ : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness δ κ S x t)
    (hround : IsShrinkingSphericalSpaceFormFlow W.model)
    (hδ : δ ≤ 1 / 2)
    (hbuffer : 2 * (2 * (Real.pi / Real.sqrt (1 / 6)) + 1) ≤ modelRadius δ) :
    ENNReal.ofReal ((κ / 32) / (S.scalar t x * Real.sqrt (S.scalar t x))) ≤
      riemannianVolumeMeasure I3 M (S.base.metric t) (connectedComponent x) := by
  obtain ⟨K,hKuniv⟩ := exists_canonicalWitness_univ_of_shrinkingSphericalSpaceFormFlow
    W.model hround W.model_scalar_base (eps := 1 / 2) (by norm_num) (by norm_num)
  let _ : ConnectedSpace W.model.M := W.model_ancient.connected
  have hwhole : K.domain.carrier = connectedComponent W.model.basepoint := by
    rw [hKuniv,PreconnectedSpace.connectedComponent_eq_univ]
  have hv := sourcedWholeComponentVolume W K hδ hbuffer hwhole
  have hcoef : κ * (2⁻¹ : ℝ)^3 / 4 = κ / 32 := by ring
  simpa only [hcoef] using hv

theorem roundModelBallConsumer (κ C1 C2 : ℝ) (hκ : 0 < κ) :
    ∃ k : ℝ, 0 < k ∧ ∀ {P : OrientedThreeStage.{u}} {D : RealTimeInterval}
      {S : SolutionOn (I := I3) (M := P.Carrier) D} {δ ε : ℝ} {x : P.Carrier} {t : ℝ}
      (W : WindowedModelWitness δ κ S x t)
      (V : SpatialCanonicalWitness (S.base.metric t) ε C1 C2 x),
      IsShrinkingSphericalSpaceFormFlow W.model → δ ≤ 1 / 2 →
      2 * (2 * (Real.pi / Real.sqrt (1 / 6)) + 1) ≤ modelRadius δ →
      V.domain.carrier = connectedComponent x →
      ∀ r : ℝ, 0 < r →
      r ^ 4 * normSq0S (S.base.metric t) x 4 (metricRm04At (S.base.metric t) x) ≤ 1 →
      ENNReal.ofReal (k * r^3) ≤
        riemannianVolumeMeasure I3 P.Carrier (S.base.metric t)
          (riemannianBallOf (S.base.metric t) x r) := by
  obtain ⟨k,hk,hball⟩ := exists_ball_volume_of_normalizedComponentVolume.{u} C1 C2 (κ/32)
    (by positivity)
  refine ⟨k,hk,?_⟩
  intro P D S δ ε x t W V hround hδ hbuffer hwhole r hr hcurv
  apply hball V hwhole ?_ r hr hcurv
  rw [hwhole]
  exact roundModelComponentVolume W hround hδ hbuffer

end GC.GeneralFlow
