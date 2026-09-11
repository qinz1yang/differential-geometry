import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RoundFlowMixedJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalScalarDifferentialBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalDerivativesJetBridge


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle


theorem exists_universal_scalarDifferentialBounds_unconditional :
    ∃ η : ℝ, 1 ≤ η ∧
      ∀ (kappa : ℝ) (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval),
        IsAncientKappaSolution (I := I3) kappa F → ScalarDifferentialBounds F η := by
  obtain ⟨C₀, _, h00⟩ := exists_universal_mixed_jet_bound_unconditional.{u} 0 0
  obtain ⟨C₁, _, h10⟩ := exists_universal_mixed_jet_bound_unconditional.{u} 1 0
  obtain ⟨C₂, _, h20⟩ := exists_universal_mixed_jet_bound_unconditional.{u} 2 0
  exact exists_universal_scalarDifferentialBounds h00 h10 h20


theorem ancientKappa_scalar_scale_comparison_universal :
    ∃ η : ℝ, 1 ≤ η ∧
      ∀ (kappa : ℝ) (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval),
        IsAncientKappaSolution (I := I3) kappa F → ∀ t ≤ (0 : ℝ),
          (∀ x y : F.M, riemannianEDistOf (I := I3) (F.S.base.metric t) x y ≤
              ENNReal.ofReal (η⁻¹ / Real.sqrt (F.S.scalar t x)) →
            4 / 9 * F.S.scalar t x ≤ F.S.scalar t y ∧
              F.S.scalar t y ≤ 4 * F.S.scalar t x) ∧
          (∀ x : F.M, ∀ s ∈ Icc (t - (2 * η * F.S.scalar t x)⁻¹) t,
            2 / 3 * F.S.scalar t x ≤ F.S.scalar s x ∧
              F.S.scalar s x ≤ F.S.scalar t x) := by
  obtain ⟨C₀, _, h00⟩ := exists_universal_mixed_jet_bound_unconditional.{u} 0 0
  obtain ⟨C₁, _, h10⟩ := exists_universal_mixed_jet_bound_unconditional.{u} 1 0
  obtain ⟨C₂, _, h20⟩ := exists_universal_mixed_jet_bound_unconditional.{u} 2 0
  exact ancientKappa_scalar_scale_comparison_of_universal h00 h10 h20


theorem exists_kappa_universal_derivatives (a b : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ kappa : ℝ, 0 < kappa →
      ∀ P : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval,
        IsAncientKappaSolution (I := I3) kappa P → PointedFlowScalarAtBase P 1 →
        ∀ J : MixedCurvatureJet P.S, J.norm a b 0 P.basepoint ≤ C := by
  obtain ⟨C₁, _, hround⟩ := exists_round_mixed_jet_bound.{u} a b
  exact exists_kappa_universal_derivatives_of_round a b hround

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
