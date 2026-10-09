import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CompactAncientPositive
import DifferentialGeometry.Geometry.Curvature.PositiveRicciCover
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.SectionalRicci
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem exists_spherical_cover_of_compact_ancientKappa
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) [CompactSpace F.M] :
    (∃ p : DifferentialGeometry.Topology.SphereThree → F.M,
      IsCoveringMap p ∧ Function.Surjective p ∧ IsLocalDiffeomorph (𝓡 3) I3 ∞ p) ∧
      ∀ x : F.M, Finite (FundamentalGroup F.M x) := by
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hpos := ancientKappa_curvatureOperatorPositive_of_compact F hF hdim
  have hric : positiveRicciMetric (F.S.base.metric 0) := by
    intro x v hv
    rw [metricRicciAt_apply_eq_ricciTensor]
    apply DifferentialGeometry.Geometry.Riemannian.BonnetMyers.ricci_pos_of_sec
      (F.S.base.metric 0) x (by rw [hdim]; norm_num) ?_ hv
    intro a b ha hb hab
    apply (curvatureOperatorPositiveAt_iff_sectional (F.S.base.metric 0) x hdim).mp (hpos 0 le_rfl x)
    rw [hab, zero_pow (by norm_num), sub_zero]
    exact mul_pos ((F.S.base.metric 0).pos x a ha) ((F.S.base.metric 0).pos x b hb)
  exact DifferentialGeometry.Geometry.exists_spherical_cover_of_admits_positive_ricci
    ⟨inferInstance, hF.connected, inferInstance, hdim⟩ ⟨F.S.base.metric 0, hric⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
