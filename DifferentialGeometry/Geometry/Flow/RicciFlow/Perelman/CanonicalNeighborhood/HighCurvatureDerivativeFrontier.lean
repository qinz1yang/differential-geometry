import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureFlowBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MixedCurvatureTerminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MixedCurvatureTimeDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalDerivativeEstimates

set_option autoImplicit false

noncomputable section

open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff

section TensorSucc

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

omit [SigmaCompactSpace M] in
theorem mixedCurvatureTensor_succ_apply (S : SolutionOn (I := I3) (M := M) D)
    (a b : ℕ) (t : ℝ) (x : M) (v : Fin (4 + a) → TangentSpace I3 x) :
    mixedCurvatureTensor S a (b + 1) t x v =
      derivWithin (fun s : ℝ => mixedCurvatureTensor S a b s x) D.carrier t v +
        ∑ j : Fin (4 + a), mixedCurvatureTensor S a b t x
          (Function.update v j (ricciSharp (I := I3) (S.base.metric t) x (v j))) := by
  simp only [mixedCurvatureTensor, iteratedMetricTimeDerivWithin_succ, metricTimeDerivWithin,
    Tensor0SSpace.add_apply, covariantEndomorphismAction0S_apply]

end TensorSucc

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

universe u

section JetEndpoint

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

theorem mixedCurvatureJet_norm_eq_of_regular (S : SolutionOn (I := I3) (M := M) D)
    (hS : IsSolutionOn S) (J J' : MixedCurvatureJet S) (a b : ℕ) (x : M) {t : ℝ}
    (ht : t ∈ D.regular) :
    J.norm a b t x = J'.norm a b t x :=
  (mixedCurvatureJet_norm_eq_mixedCurvatureNorm_of_regular S hS J a b x ht).trans
    (mixedCurvatureJet_norm_eq_mixedCurvatureNorm_of_regular S hS J' a b x ht).symm

omit [SigmaCompactSpace M] in
theorem mixedCurvatureJet_value_succ_leftEndpoint {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (J : MixedCurvatureJet S) (a b : ℕ) (x : M) (v : Fin (a + 4) → TangentSpace I3 x) :
    J.value a (b + 1) 0 x v =
      ∑ j : Fin (a + 4), J.value a b 0 x (Function.update v j
        (ricciEndAt (I := I3) (S.base.metric 0)
          (metricRicciAt (I := I3) (S.base.metric 0) x) (v j))) := by
  have hmem : (0 : ℝ) ∈ (RealTimeInterval.closedOpen 0 T hT).carrier := ⟨le_rfl, hT⟩
  have hzero := derivWithin_closedOpen_inter_Iic_leftEndpoint
    (fun s : ℝ => J.value a b s x v) hT
  have h := J.time a b 0 hmem x v
  rw [hzero, zero_add] at h
  exact h

end JetEndpoint

section Frontier

def HighCurvatureDerivativePullback (a b : ℕ) (eta : ℝ) : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [T2Space (TangentBundle I3 M)] (T : ℝ) (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (_ : IsSolutionOn S) (_ : TangentOrientationSection M),
    ∃ Q0 : ℝ, 0 < Q0 ∧ ∀ x t, t ∈ Set.Ioo 0 T → Q0 ≤ S.scalar t x →
      ∀ y ∈ DifferentialGeometry.riemannianBallOf (I := I3) (S.base.metric t) x
          (eta / Real.sqrt (S.scalar t x)),
        0 < S.scalar t y ∧
          ∃ (kappa : ℝ) (P : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval),
            0 < kappa ∧ IsAncientKappaSolution (I := I3) kappa P ∧
              PointedFlowScalarAtBase (I := I3) P 1 ∧
              mixedCurvatureNorm S a b t y ≤
                Real.rpow (S.scalar t y) (1 + (a : ℝ) / 2 + b) *
                  mixedCurvatureNorm P.S a b 0 P.basepoint

theorem ancientModelMixedBound_of_universalMixedJetBound (a b : ℕ) {C : ℝ}
    (h : UniversalMixedJetBound.{u} a b C) :
    AncientModelMixedBound.{u} a b C := by
  intro kappa _ P hP hbase
  have h0 := h kappa P hP 0 le_rfl P.basepoint
  rw [hbase, Real.one_rpow, mul_one] at h0
  exact h0

theorem mixedNormLocalBound_of_derivativePullback (a b : ℕ) {C eta : ℝ}
    (hpb : HighCurvatureDerivativePullback.{u} a b eta)
    (hM : AncientModelMixedBound.{u} a b C) :
    MixedNormLocalBound.{u} a b C eta := by
  intro M _ _ _ _ _ _ _ T hT S hS o
  obtain ⟨Q0, hQ0, hmain⟩ := hpb M T hT S hS o
  refine ⟨Q0, hQ0, fun x t ht hQ y hy => ?_⟩
  obtain ⟨hpos, kappa, P, hk, hP, hbase, hle⟩ := hmain x t ht hQ y hy
  refine ⟨hpos, ?_⟩
  have hR : 0 ≤ Real.rpow (S.scalar t y) (1 + (a : ℝ) / 2 + b) :=
    Real.rpow_nonneg hpos.le _
  calc mixedCurvatureNorm S a b t y
      ≤ Real.rpow (S.scalar t y) (1 + (a : ℝ) / 2 + b) *
          mixedCurvatureNorm P.S a b 0 P.basepoint := hle
    _ ≤ Real.rpow (S.scalar t y) (1 + (a : ℝ) / 2 + b) * C :=
        mul_le_mul_of_nonneg_left (hM kappa hk P hP hbase) hR
    _ = C * Real.rpow (S.scalar t y) (1 + (a : ℝ) / 2 + b) := by ring

theorem high_curvature_derivatives_of_derivativePullback (a b : ℕ) {C eta : ℝ}
    (hC : 0 < C) (heta : 0 < eta)
    (hpb : HighCurvatureDerivativePullback.{u} a b eta)
    (hU : UniversalMixedJetBound.{u} a b C) :
    ∃ C eta : ℝ, 0 < C ∧ 0 < eta ∧ JetLocalBound.{u} a b C eta :=
  exists_jetLocalBound_of_exists_mixedNormLocalBound a b
    ⟨C, eta, hC, heta,
      mixedNormLocalBound_of_derivativePullback a b hpb
        (ancientModelMixedBound_of_universalMixedJetBound a b hU)⟩

end Frontier

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
