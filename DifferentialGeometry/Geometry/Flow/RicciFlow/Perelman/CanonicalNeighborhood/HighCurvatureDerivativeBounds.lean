import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModelExistenceClean
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.JetLocalBoundReduction

set_option autoImplicit false

noncomputable section

open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

def SubcriticalAncientKappaRoundness : Prop :=
  ∀ (kappa : ℝ), 0 < kappa → kappa < universalKappaConstant →
    ∀ F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval,
      IsAncientKappaSolution (I := I3) kappa F → IsShrinkingSphericalSpaceFormFlow (I := I3) F

theorem ancientKappaUniversalKappaGap_of_subcriticalAncientKappaRoundness
    (h : SubcriticalAncientKappaRoundness.{u}) :
    AncientKappaUniversalKappaGap.{u, 0, 0} (I := I3) := by
  intro kappa F hF
  by_cases hle : universalKappaConstant ≤ kappa
  · exact Or.inr
      (CanonicalNeighborhood.isAncientKappaSolution_of_kappa_le
        hF universalKappaConstant_pos hle)
  · exact Or.inl (h kappa hF.kappa_pos (lt_of_not_ge hle) F hF)

theorem exists_subcritical_kappa :
    ∃ kappa : ℝ, 0 < kappa ∧ kappa < universalKappaConstant :=
  ⟨universalKappaConstant / 2, half_pos universalKappaConstant_pos,
    half_lt_self universalKappaConstant_pos⟩

section RescaledBall

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

omit [T2Space M] [SigmaCompactSpace M] in
theorem riemannianBallOf_rescaledMetric {D : RealTimeInterval}
    (S : SolutionOn (I := I3) (M := M) D) {t : ℝ} {x : M} {eta : ℝ}
    (hR : 0 < S.scalar t x) :
    DifferentialGeometry.riemannianBallOf (I := I3) (S.base.metric t) x
        (eta / Real.sqrt (S.scalar t x)) =
      DifferentialGeometry.riemannianBallOf (I := I3)
        (rescaledMetric (I := I3) S t (S.scalar t x) hR 0) x eta := by
  have hsqrt : Real.sqrt (S.scalar t x) ≠ 0 := (Real.sqrt_pos.2 hR).ne'
  have hprod : Real.sqrt (S.scalar t x) * (eta / Real.sqrt (S.scalar t x)) = eta := by
    rw [mul_comm]
    exact div_mul_cancel₀ eta hsqrt
  have hset := DifferentialGeometry.riemannianBallOf_scaleMetric (I := I3)
    (S.scalar t x) hR (S.base.metric t) x (eta / Real.sqrt (S.scalar t x))
  rw [hprod] at hset
  rw [rescaledMetric, parabolicTime_zero]
  exact hset.symm

end RescaledBall

theorem high_curvature_derivatives_iff_jetLocalBound (a b : ℕ) :
    (∃ C eta : ℝ, 0 < C ∧ 0 < eta ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
        [T2Space (TangentBundle I3 M)] (T : ℝ) (hT : 0 < T)
        (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
        (_hS : IsSolutionOn S) (_o : TangentOrientationSection M),
        ∃ Q0 : ℝ, 0 < Q0 ∧ ∀ J : MixedCurvatureJet S, ∀ x t,
          t ∈ Set.Ioo 0 T → Q0 ≤ S.scalar t x →
          ∀ y ∈ riemannianBallOf (I := I3) (S.base.metric t) x
              (eta / Real.sqrt (S.scalar t x)),
            0 < S.scalar t y ∧ J.norm a b t y ≤
              C * Real.rpow (S.scalar t y) (1 + (a : ℝ) / 2 + b)) ↔
      ∃ C eta : ℝ, 0 < C ∧ 0 < eta ∧ JetLocalBound.{u} a b C eta :=
  ⟨fun h => h, fun h => h⟩

theorem high_curvature_derivatives_of_harnackCollapse (a b : ℕ)
    (hcollapse : KLimHarnackCollapseBound.{u, 0, 0} (I := I3) universalKappaConstant)
    (hgap : AncientKappaUniversalKappaGap.{u, 0, 0} (I := I3)) {eta : ℝ} (heta : 0 < eta)
    (hpb : HighCurvatureDerivativePullback.{u} a b eta) :
    ∃ C eta : ℝ, 0 < C ∧ 0 < eta ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
        [T2Space (TangentBundle I3 M)] (T : ℝ) (hT : 0 < T)
        (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
        (_hS : IsSolutionOn S) (_o : TangentOrientationSection M),
        ∃ Q0 : ℝ, 0 < Q0 ∧ ∀ J : MixedCurvatureJet S, ∀ x t,
          t ∈ Set.Ioo 0 T → Q0 ≤ S.scalar t x →
          ∀ y ∈ riemannianBallOf (I := I3) (S.base.metric t) x
              (eta / Real.sqrt (S.scalar t x)),
            0 < S.scalar t y ∧ J.norm a b t y ≤
              C * Real.rpow (S.scalar t y) (1 + (a : ℝ) / 2 + b) :=
  exists_jetLocalBound_of_harnackCollapse a b hcollapse hgap heta hpb

theorem high_curvature_derivatives_of_windowedWitnessJetTransfer (a b : ℕ)
    (hcollapse : KLimHarnackCollapseBound.{u, 0, 0} (I := I3) universalKappaConstant)
    (hgap : AncientKappaUniversalKappaGap.{u, 0, 0} (I := I3))
    (hmodel : HighCurvatureModelWitnessExistence.{u}) {eta : ℝ} (heta : 0 < eta)
    (htransfer : WindowedWitnessJetTransfer.{u} a b eta) :
    ∃ C eta : ℝ, 0 < C ∧ 0 < eta ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
        [T2Space (TangentBundle I3 M)] (T : ℝ) (hT : 0 < T)
        (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
        (_hS : IsSolutionOn S) (_o : TangentOrientationSection M),
        ∃ Q0 : ℝ, 0 < Q0 ∧ ∀ J : MixedCurvatureJet S, ∀ x t,
          t ∈ Set.Ioo 0 T → Q0 ≤ S.scalar t x →
          ∀ y ∈ riemannianBallOf (I := I3) (S.base.metric t) x
              (eta / Real.sqrt (S.scalar t x)),
            0 < S.scalar t y ∧ J.norm a b t y ≤
              C * Real.rpow (S.scalar t y) (1 + (a : ℝ) / 2 + b) :=
  high_curvature_derivatives_of_harnackCollapse a b hcollapse hgap heta
    (highCurvatureDerivativePullback_of_modelWitnessExistence_and_transfer hmodel htransfer)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
