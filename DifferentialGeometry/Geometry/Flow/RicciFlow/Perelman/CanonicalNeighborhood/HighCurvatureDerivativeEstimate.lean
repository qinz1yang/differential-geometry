import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureDerivativeFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureFlowBridge

set_option autoImplicit false

noncomputable section

open scoped Topology

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

def HighCurvatureDerivativePullbackCore (a b : ℕ) (eta : ℝ) : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [T2Space (TangentBundle I3 M)] (T : ℝ) (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (_ : IsSolutionOn S) (_ : TangentOrientationSection M),
    ∃ Q0 : ℝ, 0 < Q0 ∧ ∀ x t, t ∈ Set.Ioo 0 T → Q0 ≤ S.scalar t x →
      ∀ y ∈ riemannianBallOf (I := I3) (S.base.metric t) x
          (eta / Real.sqrt (S.scalar t x)),
        0 < S.scalar t y ∧
          ∃ (kappa : ℝ) (P : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval),
            IsAncientKappaSolution (I := I3) kappa P ∧
              PointedFlowScalarAtBase (I := I3) P 1 ∧
              mixedCurvatureNorm S a b t y ≤
                Real.rpow (S.scalar t y) (1 + (a : ℝ) / 2 + b) *
                  mixedCurvatureNorm P.S a b 0 P.basepoint

theorem derivativePullback_iff_core (a b : ℕ) (eta : ℝ) :
    HighCurvatureDerivativePullback.{u} a b eta ↔
      HighCurvatureDerivativePullbackCore.{u} a b eta := by
  constructor
  · intro h M _ _ _ _ _ _ _ T hT S hS o
    obtain ⟨Q0, hQ0, hmain⟩ := h M T hT S hS o
    exact ⟨Q0, hQ0, fun x t ht hQ y hy => by
      obtain ⟨hpos, kappa, P, _hk, hP, hbase, hle⟩ := hmain x t ht hQ y hy
      exact ⟨hpos, kappa, P, hP, hbase, hle⟩⟩
  · intro h M _ _ _ _ _ _ _ T hT S hS o
    obtain ⟨Q0, hQ0, hmain⟩ := h M T hT S hS o
    exact ⟨Q0, hQ0, fun x t ht hQ y hy => by
      obtain ⟨hpos, kappa, P, hP, hbase, hle⟩ := hmain x t ht hQ y hy
      exact ⟨hpos, kappa, P, hP.kappa_pos, hP, hbase, hle⟩⟩

def HighCurvatureDerivativePullbackInput (a b : ℕ) : Prop :=
  ∃ eta : ℝ, 0 < eta ∧ HighCurvatureDerivativePullback.{u} a b eta

theorem derivativePullbackInput_of_pullback {a b : ℕ} {eta : ℝ} (heta : 0 < eta)
    (h : HighCurvatureDerivativePullback.{u} a b eta) :
    HighCurvatureDerivativePullbackInput.{u} a b :=
  ⟨eta, heta, h⟩

theorem high_curvature_derivatives_of_derivativePullback_modelBound (a b : ℕ) {C eta : ℝ}
    (hC : 0 < C) (heta : 0 < eta) (hM : AncientModelMixedBound.{u} a b C)
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
              C * Real.rpow (S.scalar t y) (1 + (a : ℝ) / 2 + b) := by
  obtain ⟨C', eta', hC', heta', hJet⟩ :=
    exists_jetLocalBound_of_exists_mixedNormLocalBound a b
      ⟨C, eta, hC, heta, mixedNormLocalBound_of_derivativePullback a b hpb hM⟩
  exact ⟨C', eta', hC', heta', hJet⟩

theorem highCurvatureModelReduction_of_derivativePullback (a b : ℕ) {C eta : ℝ}
    (hM : AncientModelMixedBound.{u} a b C)
    (hpb : HighCurvatureDerivativePullback.{u} a b eta) :
    HighCurvatureModelReduction.{u} a b C eta := by
  intro M _ _ _ _ _ _ _ T hT S hS o
  obtain ⟨Q0, hQ0, hmain⟩ := hpb M T hT S hS o
  exact ⟨Q0, hQ0, fun x t ht hQ y hy => by
    obtain ⟨hpos, kappa, P, hk, hP, hbase, hle⟩ := hmain x t ht hQ y hy
    exact ⟨hpos, kappa, P, hk, hP, hbase, hM kappa hk P hP hbase, hle⟩⟩

section Vacuity

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem derivativePullback_inner_of_nonpositive_scalar {a b : ℕ} {eta : ℝ}
    (_heta : 0 < eta)
    (S : SolutionOn (I := I3) (M := M) D)
    (hneg : ∀ t ∈ D.regular, ∀ x : M, S.scalar t x ≤ 0) :
    ∃ Q0 : ℝ, 0 < Q0 ∧ ∀ x t, t ∈ D.regular → Q0 ≤ S.scalar t x →
      ∀ y ∈ riemannianBallOf (I := I3) (S.base.metric t) x
          (eta / Real.sqrt (S.scalar t x)),
        0 < S.scalar t y ∧
          ∃ (kappa : ℝ) (P : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval),
            IsAncientKappaSolution (I := I3) kappa P ∧
              PointedFlowScalarAtBase (I := I3) P 1 ∧
              mixedCurvatureNorm S a b t y ≤
                Real.rpow (S.scalar t y) (1 + (a : ℝ) / 2 + b) *
                  mixedCurvatureNorm P.S a b 0 P.basepoint := by
  refine ⟨1, one_pos, fun x t ht hQ => ?_⟩
  exact absurd hQ (not_le.mpr (lt_of_le_of_lt (hneg t ht x) zero_lt_one))

end Vacuity

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
