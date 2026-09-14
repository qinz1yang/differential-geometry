import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RecenteredFarField
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalLocalPropagationOfHarnackCollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalSliceScalarTransfer

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem recentered_source_bound_of_harnackCollapseBound_and_boundedAtDistanceShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi)
    (hharnack : KappaSolutions.KLimHarnackCollapseBound.{u, 0, 0} (I := I3) kappa)
    (hshell : BoundedAtDistanceShell.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ A D : ℝ, 0 ≤ D → ∃ C : ℝ,
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in Filter.atTop,
          ∀ s ∈ Set.Icc (-(X.depth i / 2)) 0, ∀ z y : (X.term i).M,
            (X.term i).S.scalar s z ≤ A →
            metricDistance ((X.term i).S.base.metric s) z y ≤ D →
              (X.term i).S.scalar s y ≤ C := by
  obtain ⟨c, hc, hlocal⟩ :=
    exists_terminalLocalPropagationBound_of_harnackCollapseBound hharnack
  exact recentered_source_bound_of_boundedAtDistanceShell hsigma hPhi hc hlocal hshell

theorem uniform_moving_slice_propagation_of_harnackCollapseBound_and_boundedAtDistanceShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi)
    (hharnack : KappaSolutions.KLimHarnackCollapseBound.{u, 0, 0} (I := I3) kappa)
    (hshell : BoundedAtDistanceShell.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ A D : ℝ, 0 ≤ D → ∃ C : ℝ,
        ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
          (J : RealTimeInterval) (B : BackwardExtension L J),
          ∀ s ∈ J.carrier, ∀ z y : L.space.M,
            B.solution.scalar s z ≤ A →
            metricDistance (B.solution.base.metric s) z y ≤ D →
              B.solution.scalar s y ≤ C := by
  obtain ⟨c, hc, hlocal⟩ :=
    exists_terminalLocalPropagationBound_of_harnackCollapseBound hharnack
  exact uniform_moving_slice_propagation_of_recenteredSourceBound
    (recentered_source_bound_of_boundedAtDistanceShell hsigma hPhi hc hlocal hshell)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
