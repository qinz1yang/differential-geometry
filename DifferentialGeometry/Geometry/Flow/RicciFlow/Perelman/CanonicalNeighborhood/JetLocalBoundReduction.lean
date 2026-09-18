import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureDerivativeEstimate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModelBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimHarnackCollapseBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimHarnackCollapseBoundReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RoundFlowMixedJets

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem exists_universal_mixed_jet_bound_unconditional_of_harnackCollapse (a b : ℕ)
    (hcollapse : KLimHarnackCollapseBound.{u, 0, 0} (I := I3) universalKappaConstant)
    (hgap : AncientKappaUniversalKappaGap.{u, 0, 0} (I := I3)) :
    ∃ C : ℝ, 0 < C ∧ UniversalMixedJetBound.{u} a b C := by
  obtain ⟨C₁, _, hround⟩ := exists_round_mixed_jet_bound.{u} a b
  exact exists_universal_mixed_jet_bound_of_localCurvatureBound.{u} a b hround
    (kLimLocalCurvatureBound_threeSpace_of_harnackCollapseBound hcollapse) hgap

theorem exists_kappa_universal_derivatives_of_harnackCollapse (a b : ℕ)
    (hcollapse : KLimHarnackCollapseBound.{u, 0, 0} (I := I3) universalKappaConstant)
    (hgap : AncientKappaUniversalKappaGap.{u, 0, 0} (I := I3)) :
    ∃ C : ℝ, 0 < C ∧ ∀ kappa : ℝ, 0 < kappa →
      ∀ P : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval,
        IsAncientKappaSolution (I := I3) kappa P → PointedFlowScalarAtBase (I := I3) P 1 →
        ∀ J : MixedCurvatureJet P.S, J.norm a b 0 P.basepoint ≤ C :=
  exists_kappa_universal_derivatives_of_localCurvatureBound.{u} a b
    (kLimLocalCurvatureBound_threeSpace_of_harnackCollapseBound hcollapse) hgap

theorem exists_ancientModelMixedBound_of_harnackCollapse (a b : ℕ)
    (hcollapse : KLimHarnackCollapseBound.{u, 0, 0} (I := I3) universalKappaConstant)
    (hgap : AncientKappaUniversalKappaGap.{u, 0, 0} (I := I3)) :
    ∃ C : ℝ, 0 < C ∧ AncientModelMixedBound.{u} a b C := by
  obtain ⟨C, hC, hU⟩ :=
    exists_universal_mixed_jet_bound_unconditional_of_harnackCollapse a b hcollapse hgap
  exact ⟨C, hC, ancientModelMixedBound_of_universalMixedJetBound a b hU⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Set
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open scoped Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem highCurvatureDerivativePullback_of_modelReduction (a b : ℕ) {C eta : ℝ}
    (h : HighCurvatureModelReduction.{u} a b C eta) :
    HighCurvatureDerivativePullback.{u} a b eta := by
  intro M _ _ _ _ _ _ _ T hT S hS o
  obtain ⟨Q0, hQ0, hmain⟩ := h M T hT S hS o
  refine ⟨Q0, hQ0, fun x t ht hQ y hy => ?_⟩
  obtain ⟨hpos, kappa, P, hk, hP, hbase, _hmodel, hle⟩ := hmain x t ht hQ y hy
  exact ⟨hpos, kappa, P, hk, hP, hbase, hle⟩

theorem highCurvatureModelReduction_iff_derivativePullback (a b : ℕ) {C eta : ℝ}
    (hM : AncientModelMixedBound.{u} a b C) :
    HighCurvatureModelReduction.{u} a b C eta ↔
      HighCurvatureDerivativePullback.{u} a b eta :=
  ⟨highCurvatureDerivativePullback_of_modelReduction a b,
    highCurvatureModelReduction_of_derivativePullback a b hM⟩

theorem highCurvatureDerivativePullback_of_eta_le (a b : ℕ) {eta eta' : ℝ} (heta : eta ≤ eta')
    (hpb : HighCurvatureDerivativePullback.{u} a b eta') :
    HighCurvatureDerivativePullback.{u} a b eta := by
  intro M _ _ _ _ _ _ _ T hT S hS o
  obtain ⟨Q0, hQ0, hmain⟩ := hpb M T hT S hS o
  refine ⟨Q0, hQ0, fun x t ht hQ y hy => hmain x t ht hQ y ?_⟩
  have hQpos : 0 < S.scalar t x := lt_of_lt_of_le hQ0 hQ
  have hroot : 0 < Real.sqrt (S.scalar t x) := Real.sqrt_pos.2 hQpos
  exact riemannianBallOf_mono (I := I3) (S.base.metric t) x
    (div_le_div_of_nonneg_right heta hroot.le) hy

theorem highCurvatureModelReduction_of_harnackCollapse (a b : ℕ)
    (hcollapse : KLimHarnackCollapseBound.{u, 0, 0} (I := I3) universalKappaConstant)
    (hgap : AncientKappaUniversalKappaGap.{u, 0, 0} (I := I3)) {eta : ℝ} (heta : 0 < eta)
    (hpb : HighCurvatureDerivativePullback.{u} a b eta) :
    ∃ C eta : ℝ, 0 < C ∧ 0 < eta ∧ HighCurvatureModelReduction.{u} a b C eta := by
  obtain ⟨C, hC, hM⟩ := exists_ancientModelMixedBound_of_harnackCollapse a b hcollapse hgap
  exact ⟨C, eta, hC, heta, highCurvatureModelReduction_of_derivativePullback a b hM hpb⟩

theorem exists_jetLocalBound_of_harnackCollapse (a b : ℕ)
    (hcollapse : KLimHarnackCollapseBound.{u, 0, 0} (I := I3) universalKappaConstant)
    (hgap : AncientKappaUniversalKappaGap.{u, 0, 0} (I := I3)) {eta : ℝ} (heta : 0 < eta)
    (hpb : HighCurvatureDerivativePullback.{u} a b eta) :
    ∃ C eta : ℝ, 0 < C ∧ 0 < eta ∧ JetLocalBound.{u} a b C eta := by
  obtain ⟨C, eta', hC, heta', hred⟩ :=
    highCurvatureModelReduction_of_harnackCollapse a b hcollapse hgap heta hpb
  exact high_curvature_derivatives_of_modelReduction a b hC heta' hred

private theorem jetLocalThreeSpace_finrank : Module.finrank ℝ ThreeSpace = 3 := by
  simp [ThreeSpace]

theorem exists_ancientModelMixedBound_of_seedCollapse (a b : ℕ)
    (hseed : KLimNormalizedSeedVolumeBound.{u, 0, 0} (I := I3) universalKappaConstant)
    (hcollapse : KLimThreeCollapseRadius.{u, 0, 0} (I := I3) universalKappaConstant)
    (hgap : AncientKappaUniversalKappaGap.{u, 0, 0} (I := I3)) :
    ∃ C : ℝ, 0 < C ∧ AncientModelMixedBound.{u} a b C :=
  exists_ancientModelMixedBound_of_harnackCollapse a b
    (kLimHarnackCollapseBound_of_normalizedSeedVolumeBound_and_threeCollapseRadius
      (I := I3) jetLocalThreeSpace_finrank hseed hcollapse) hgap

theorem exists_jetLocalBound_of_seedCollapse (a b : ℕ)
    (hseed : KLimNormalizedSeedVolumeBound.{u, 0, 0} (I := I3) universalKappaConstant)
    (hcollapse : KLimThreeCollapseRadius.{u, 0, 0} (I := I3) universalKappaConstant)
    (hgap : AncientKappaUniversalKappaGap.{u, 0, 0} (I := I3)) {eta : ℝ} (heta : 0 < eta)
    (hpb : HighCurvatureDerivativePullback.{u} a b eta) :
    ∃ C eta : ℝ, 0 < C ∧ 0 < eta ∧ JetLocalBound.{u} a b C eta :=
  exists_jetLocalBound_of_harnackCollapse a b
    (kLimHarnackCollapseBound_of_normalizedSeedVolumeBound_and_threeCollapseRadius
      (I := I3) jetLocalThreeSpace_finrank hseed hcollapse) hgap heta hpb

theorem highCurvatureDerivativePullback_of_scalar_nonpositive (a b : ℕ) {eta : ℝ}
    (heta : 0 < eta)
    (hneg : ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
      [T2Space (TangentBundle I3 M)] (T : ℝ) (hT : 0 < T)
      (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT)),
      ∀ t ∈ Set.Ioo 0 T, ∀ x : M, S.scalar t x ≤ 0) :
    HighCurvatureDerivativePullback.{u} a b eta := by
  intro M _ _ _ _ _ _ _ T hT S _ _
  obtain ⟨Q0, hQ0, hmain⟩ := derivativePullback_inner_of_nonpositive_scalar heta S
    (hneg M T hT S)
  exact ⟨Q0, hQ0, fun x t ht hQ y hy => by
    obtain ⟨hpos, kappa, P, hP, hbase, hle⟩ := hmain x t ht hQ y hy
    exact ⟨hpos, kappa, P, hP.kappa_pos, hP, hbase, hle⟩⟩

theorem highCurvatureModelReduction_of_scalar_nonpositive (a b : ℕ) {C eta : ℝ}
    (hneg : ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
      [T2Space (TangentBundle I3 M)] (T : ℝ) (hT : 0 < T)
      (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT)),
      ∀ t ∈ Set.Ioo 0 T, ∀ x : M, S.scalar t x ≤ 0) :
    HighCurvatureModelReduction.{u} a b C eta := by
  intro M _ _ _ _ _ _ _ T hT S _ _
  refine ⟨1, one_pos, fun x t ht hQ y _hy => ?_⟩
  exact absurd hQ (not_le.mpr (lt_of_le_of_lt (hneg M T hT S t ht x) zero_lt_one))

theorem jetLocalBound_of_scalar_nonpositive (a b : ℕ) {C eta : ℝ}
    (hneg : ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
      [T2Space (TangentBundle I3 M)] (T : ℝ) (hT : 0 < T)
      (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT)),
      ∀ t ∈ Set.Ioo 0 T, ∀ x : M, S.scalar t x ≤ 0) :
    JetLocalBound.{u} a b C eta := by
  intro M _ _ _ _ _ _ _ T hT S _ _
  refine ⟨1, one_pos, fun _J x t ht hQ _y _hy => ?_⟩
  exact absurd hQ (not_le.mpr (lt_of_le_of_lt (hneg M T hT S t ht x) zero_lt_one))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
