import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MixedCurvatureTimeDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalDerivativeLocalCurvatureBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModelBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RoundFlowMixedJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalDerivativesJetBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MixedCurvatureScaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MixedCurvatureTerminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalDerivativeEstimates

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem mixedCurvatureWeight_eq_one_add (a b : ℕ) :
    mixedCurvatureWeight a b = 1 + (a : ℝ) / 2 + (b : ℝ) := rfl

theorem mixedCurvatureNorm_eq_rpow_mul_curvatureNormalized
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b : ℝ} (hcarrier : D.carrier = Set.Iic b) (hregular : D.regular = Set.Iio b)
    (t₀ Q : ℝ) (hQ : 0 < Q) (ht₀ : t₀ ∈ D.carrier) (p q : ℕ) (x : M) :
    mixedCurvatureNorm S p q t₀ x =
      Q ^ mixedCurvatureWeight p q *
        mixedCurvatureNorm (curvatureNormalizedSolution S t₀ Q hQ ht₀) p q 0 x := by
  have h := mixedCurvatureNorm_curvatureNormalizedSolution (I := I) (M := M) S hS
    hcarrier hregular t₀ Q hQ ht₀ p q (s := 0) le_rfl x
  rw [parabolicTime_zero] at h
  have hexp : (-(1 : ℝ) - (p : ℝ) / 2 - (q : ℝ)) = -mixedCurvatureWeight p q := by
    simp only [mixedCurvatureWeight]
    ring
  rw [hexp] at h
  have hpow : Q ^ mixedCurvatureWeight p q * Q ^ (-mixedCurvatureWeight p q) = 1 := by
    rw [← Real.rpow_add hQ, add_neg_cancel, Real.rpow_zero]
  calc mixedCurvatureNorm S p q t₀ x =
      (Q ^ mixedCurvatureWeight p q * Q ^ (-mixedCurvatureWeight p q)) *
          mixedCurvatureNorm S p q t₀ x := by
        rw [hpow, one_mul]
    _ = Q ^ mixedCurvatureWeight p q *
        (Q ^ (-mixedCurvatureWeight p q) * mixedCurvatureNorm S p q t₀ x) := by
        ring
    _ = Q ^ mixedCurvatureWeight p q *
        mixedCurvatureNorm (curvatureNormalizedSolution S t₀ Q hQ ht₀) p q 0 x := by
        rw [h]

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

def MixedNormLocalBound (a b : ℕ) (C eta : ℝ) : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [T2Space (TangentBundle I3 M)] (T : ℝ) (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (_ : IsSolutionOn S) (_ : TangentOrientationSection M),
    ∃ Q0 : ℝ, 0 < Q0 ∧ ∀ x t, t ∈ Set.Ioo 0 T → Q0 ≤ S.scalar t x →
      ∀ y ∈ DifferentialGeometry.riemannianBallOf (I := I3) (S.base.metric t) x
          (eta / Real.sqrt (S.scalar t x)),
        0 < S.scalar t y ∧ mixedCurvatureNorm S a b t y ≤
          C * Real.rpow (S.scalar t y) (1 + (a : ℝ) / 2 + b)

def JetLocalBound (a b : ℕ) (C eta : ℝ) : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [T2Space (TangentBundle I3 M)] (T : ℝ) (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (_ : IsSolutionOn S) (_ : TangentOrientationSection M),
    ∃ Q0 : ℝ, 0 < Q0 ∧ ∀ J : MixedCurvatureJet S, ∀ x t, t ∈ Set.Ioo 0 T →
      Q0 ≤ S.scalar t x →
      ∀ y ∈ DifferentialGeometry.riemannianBallOf (I := I3) (S.base.metric t) x
          (eta / Real.sqrt (S.scalar t x)),
        0 < S.scalar t y ∧ J.norm a b t y ≤
          C * Real.rpow (S.scalar t y) (1 + (a : ℝ) / 2 + b)

theorem exists_jetLocalBound_of_exists_mixedNormLocalBound (a b : ℕ)
    (h : ∃ C eta, 0 < C ∧ 0 < eta ∧ MixedNormLocalBound.{u} a b C eta) :
    ∃ C eta, 0 < C ∧ 0 < eta ∧ JetLocalBound.{u} a b C eta :=
  high_curvature_derivatives_of_mixedCurvatureNorm_bound.{u} a b h

def HighCurvatureModelReduction (a b : ℕ) (C eta : ℝ) : Prop :=
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
              mixedCurvatureNorm P.S a b 0 P.basepoint ≤ C ∧
              mixedCurvatureNorm S a b t y ≤
                Real.rpow (S.scalar t y) (1 + (a : ℝ) / 2 + b) *
                  mixedCurvatureNorm P.S a b 0 P.basepoint

theorem high_curvature_derivatives_of_modelReduction (a b : ℕ) {C eta : ℝ}
    (hC : 0 < C) (heta : 0 < eta) (h : HighCurvatureModelReduction.{u} a b C eta) :
    ∃ C eta, 0 < C ∧ 0 < eta ∧ JetLocalBound.{u} a b C eta := by
  refine exists_jetLocalBound_of_exists_mixedNormLocalBound a b ⟨C, eta, hC, heta, ?_⟩
  intro M _ _ _ _ _ _ _ T hT S hS o
  obtain ⟨Q0, hQ0, hmain⟩ := h M T hT S hS o
  refine ⟨Q0, hQ0, fun x t ht hQ y hy => ?_⟩
  obtain ⟨hpos, kappa, P, hk, hP, hbase, hmodel, hle⟩ := hmain x t ht hQ y hy
  refine ⟨hpos, ?_⟩
  have hR : 0 ≤ Real.rpow (S.scalar t y) (1 + (a : ℝ) / 2 + b) :=
    Real.rpow_nonneg hpos.le _
  calc mixedCurvatureNorm S a b t y
      ≤ Real.rpow (S.scalar t y) (1 + (a : ℝ) / 2 + b) *
          mixedCurvatureNorm P.S a b 0 P.basepoint := hle
    _ ≤ Real.rpow (S.scalar t y) (1 + (a : ℝ) / 2 + b) * C :=
        mul_le_mul_of_nonneg_left hmodel hR
    _ = C * Real.rpow (S.scalar t y) (1 + (a : ℝ) / 2 + b) := by ring

def AncientModelMixedBound (a b : ℕ) (C : ℝ) : Prop :=
  ∀ (kappa : ℝ), 0 < kappa →
    ∀ (P : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval),
      IsAncientKappaSolution (I := I3) kappa P → PointedFlowScalarAtBase (I := I3) P 1 →
        mixedCurvatureNorm P.S a b 0 P.basepoint ≤ C

def AncientJetInhabited : Prop :=
  ∀ (kappa : ℝ) (P : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval),
    IsAncientKappaSolution (I := I3) kappa P → PointedFlowScalarAtBase (I := I3) P 1 →
      Nonempty (MixedCurvatureJet P.S)

theorem ancientModelMixedBound_of_jetBound (a b : ℕ) {C : ℝ}
    (hjet : ∀ (kappa : ℝ), 0 < kappa →
      ∀ (P : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval),
        IsAncientKappaSolution (I := I3) kappa P → PointedFlowScalarAtBase (I := I3) P 1 →
          ∀ J : MixedCurvatureJet P.S, J.norm a b 0 P.basepoint ≤ C)
    (hne : AncientJetInhabited.{u}) :
    AncientModelMixedBound.{u} a b C := by
  intro kappa hk P hP hbase
  obtain ⟨J⟩ := hne kappa P hP hbase
  have hdiff : ∀ (q : ℕ) (t : ℝ), t ≤ 0 → DifferentiableWithinAt ℝ
      (fun s : ℝ => mixedCurvatureTensor P.S a q s P.basepoint) (Set.Iic 0) t :=
    fun q t ht =>
      ancientKappa_mixedCurvatureTensor_differentiableWithinAt_of_rmNormSqBounded P hP a q ht
  have hbridge : J.norm a b 0 P.basepoint = mixedCurvatureNorm P.S a b 0 P.basepoint :=
    mixedCurvatureJet_norm_eq P.S J a P.basepoint hdiff b le_rfl
  rw [← hbridge]
  exact hjet kappa hk P hP hbase J

theorem exists_ancientModelMixedBound_of_localCurvatureBound (a b : ℕ)
    (hlocal : KLimLocalCurvatureBound.{u, 0, 0} (I := I3) universalKappaConstant)
    (hgap : AncientKappaUniversalKappaGap.{u, 0, 0} (I := I3))
    (hne : AncientJetInhabited.{u}) :
    ∃ C : ℝ, 0 < C ∧ AncientModelMixedBound.{u} a b C := by
  obtain ⟨C, hC, hjet⟩ :=
    exists_kappa_universal_derivatives_of_localCurvatureBound.{u} a b hlocal hgap
  exact ⟨C, hC, ancientModelMixedBound_of_jetBound a b hjet hne⟩

theorem exists_roundShrinker_roundMixedJetBound (a b : ℕ) :
    ∃ C : ℝ, 0 < C ∧ RoundMixedJetBound.{u} a b C :=
  exists_round_mixed_jet_bound.{u} a b

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
