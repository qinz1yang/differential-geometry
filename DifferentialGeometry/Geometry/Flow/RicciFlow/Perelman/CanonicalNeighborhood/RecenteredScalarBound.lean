import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedBoundedCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RecenteredFarField

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.DifferentialGeometry.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}





theorem recentered_source_bound {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ A D : ℝ, 0 ≤ D → ∃ C : ℝ,
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in Filter.atTop,
          ∀ s ∈ Set.Icc (-(X.depth i / 2)) 0, ∀ z y : (X.term i).M,
            (X.term i).S.scalar s z ≤ A →
            metricDistance ((X.term i).S.base.metric s) z y ≤ D →
              (X.term i).S.scalar s y ≤ C := by
  obtain ⟨epsBound, hBound, hbounded⟩ := exists_boundedAtDistance.{u} hkappa
  have hshell : BoundedAtDistanceShell.{u} kappa sigma Phi :=
    ⟨epsBound, hBound, fun eps heps hle X => hbounded eps heps hle sigma hsigma Phi hPhi X⟩
  obtain ⟨epsLocal, c, C, hLocal, hc, _, hprop⟩ :=
    canonical_neighborhood_local_propagation.{u} hkappa
  have hlocal : TerminalLocalPropagationBound.{u} kappa c := by
    refine ⟨epsLocal, hLocal, ?_⟩
    intro eps heps hle sigma hsigma Phi hPhi X
    filter_upwards [hprop eps heps hle sigma hsigma Phi hPhi X] with i hi
    intro s hs z
    exact ⟨(hi s hs z).1, fun y v hv => ((hi s hs z).2 y v hv).2.1⟩
  exact recentered_source_bound_of_boundedAtDistanceShell hsigma hPhi hc hlocal hshell


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
