import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.HeatTest
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalBounds

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData (I := I) D)

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem ancient_redLength_time_deriv_add_laplacian_lower_test_of_regular_base
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {T tau : ℝ} (hT : T < 0) (htau : 0 < tau)
    (p q : F.M) (phi : ℝ × F.M → ℝ) (d : ℝ)
    (hphi : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y => phi (tau, y)) q)
    (hdt : HasDerivAt (fun t => phi (t, q)) d tau)
    (hmin : IsLocalMin (fun z : ℝ × F.M => redLength F.S T p z.2 z.1 - phi z) (tau, q)) :
    d + laplacian (I := I) (LeviCivita (I := I) (F.S.base.metric (T - tau)))
        (F.S.base.metric (T - tau)) (fun y => phi (tau, y)) q ≤
      ((Module.finrank ℝ E : ℝ) / 2 - redLength F.S T p q tau) / tau := by
  let _ : ConnectedSpace F.M := hF.connected
  have hTc : T ∈ D.carrier := by simpa only [hF.carrier_eq, mem_Iic] using hT.le
  have hg : RiemannianMetricComplete (I := I) (F.S.base.metric T) := ⟨hF.complete T hTc⟩
  obtain ⟨K, hK⟩ := ancientKappa_rmNormSqBounded_finrank F hF
  apply redLength_time_deriv_add_laplacian_lower_test F.S F.isSolution K T (tau + 1) tau
    hg htau (by linarith) ?_ ?_ p q phi d hphi hdt hmin
  · intro t ht
    simpa only [hF.regular_eq, mem_Iio] using ht.2.trans_lt hT
  · intro t ht y
    exact hK t (by simpa only [hF.carrier_eq, mem_Iic] using ht.2.trans hT.le) y

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
