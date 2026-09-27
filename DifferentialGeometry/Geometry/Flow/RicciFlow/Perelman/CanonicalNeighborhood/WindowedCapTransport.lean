import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedDistanceComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalToleranceMonotone

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

theorem WindowedModelWitness.canonicalAlternative_cap_of_transported_necks
    {delta kappa epsm eps C rho : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    {U : Set W.model.M} (L : LocalCap W.model.S epsm W.model.basepoint 0 U)
    (hdelta : delta ≤ 1 / 4) (hrho : 0 ≤ rho) (hbuffer : 8 * rho ≤ modelRadius delta)
    (houter : U ⊆ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint rho)
    (heps : epsm ≤ eps) (hsmall : eps < 1 / 11)
    (necks : ∀ i, StrongNeck S eps (W.embedding (L.chain.centers i)) t)
    (hmap : ∀ i, (necks i).map = (L.chain.necks i).map.trans W.embedding)
    (hfar : ∀ y ∈ L.tube,
      20000 ≤ metricDistance (W.model.S.base.metric 0) W.model.basepoint y) :
    Nonempty (CanonicalAlternative S eps C x t (W.embedding '' U)) := by
  have hsource : U ⊆ W.embedding.source :=
    houter.trans ((riemannianClosedBallOf_mono _ _
      (by linarith : rho ≤ modelRadius delta + 1)).trans W.buffered_ball)
  have htube : L.tube ⊆ U := subset_union_right.trans L.union_eq.ge
  have hdeep : ∀ y ∈ W.embedding '' L.tube,
      10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y :=
    W.metricDistance_ge_on_image hdelta hrho hbuffer (htube.trans houter) (by
      intro y hy
      norm_num
      exact hfar y hy)
  exact canonicalAlternative_transport_cap_of_necks (L.mono_eps heps hsmall)
    W.embedding hsource necks hmap W.base_map hdeep

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
