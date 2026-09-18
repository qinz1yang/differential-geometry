import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientModelClassification
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureDerivativeFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalLocalPropagationOfHarnackCollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedSourceCurvature
import DifferentialGeometry.Tensor.Metric.ScaleNorm

set_option autoImplicit false

noncomputable section

open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

def HighCurvatureModelExistence : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [T2Space (TangentBundle I3 M)] (T : ℝ) (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (_ : IsSolutionOn S) (_ : TangentOrientationSection M),
    ∃ kappa : ℝ, 0 < kappa ∧ ∃ Q0 : ℝ, 0 < Q0 ∧ ∀ x t, t ∈ Set.Ico 0 T →
      Q0 ≤ S.scalar t x →
        ∃ P : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval,
          IsAncientKappaSolution (I := I3) kappa P ∧
            PointedFlowScalarAtBase (I := I3) P 1

def HighCurvatureModelWitnessExistence : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [T2Space (TangentBundle I3 M)] (T : ℝ) (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (_ : IsSolutionOn S) (o : TangentOrientationSection M),
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ eps : ℝ, 0 < eps → eps < 1 →
      ∃ Q0 : ℝ, 0 < Q0 ∧ ∀ x t, t ∈ Set.Ico 0 T → Q0 ≤ S.scalar t x →
        OrientedWitness S o eps kappa x t

def WindowedWitnessJetTransfer (a b : ℕ) (eta : ℝ) : Prop :=
  ∀ (kappa : ℝ) (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [T2Space (TangentBundle I3 M)] (T : ℝ) (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (_ : IsSolutionOn S) (_ : TangentOrientationSection M),
    ∃ Q0 : ℝ, 0 < Q0 ∧ ∀ (eps : ℝ) (x : M) (t : ℝ)
      (W : WindowedModelWitness eps kappa S x t),
      t ∈ Set.Ioo 0 T → Q0 ≤ S.scalar t x →
        ∀ y ∈ DifferentialGeometry.riemannianBallOf (I := I3) (S.base.metric t) x
            (eta / Real.sqrt (S.scalar t x)),
          0 < S.scalar t y ∧
            mixedCurvatureNorm S a b t y ≤
              Real.rpow (S.scalar t y) (1 + (a : ℝ) / 2 + b) *
                mixedCurvatureNorm W.model.S a b 0 W.model.basepoint

theorem modelCurvatureBoundNearBase_of_kappa_le {kappa kappa' : ℝ} (hkappa : 0 < kappa)
    (hle : kappa ≤ kappa') (h : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa' := by
  obtain ⟨K, hK, hbound⟩ := h
  refine ⟨K, hK, fun L hL hbase s hs y hy => ?_⟩
  exact hbound L (CanonicalNeighborhood.isAncientKappaSolution_of_kappa_le hL hkappa hle)
    hbase s hs y hy

theorem highCurvatureModelExistence_of_modelWitnessExistence
    (h : HighCurvatureModelWitnessExistence.{u}) :
    HighCurvatureModelExistence.{u} := by
  intro M _ _ _ _ _ _ _ T hT S hS o
  obtain ⟨kappa, hkappa, hforall⟩ := h M T hT S hS o
  obtain ⟨Q0, hQ0, hwit⟩ := hforall (1 / 2) (by norm_num) (by norm_num)
  refine ⟨kappa, hkappa, Q0, hQ0, fun x t ht hx => ?_⟩
  obtain ⟨W, _⟩ := hwit x t ht hx
  exact ⟨W.model, W.model_ancient, W.model_scalar_base⟩

theorem highCurvatureDerivativePullback_of_modelWitnessExistence_and_transfer
    {a b : ℕ} {eta : ℝ} (hmodel : HighCurvatureModelWitnessExistence.{u})
    (htransfer : WindowedWitnessJetTransfer.{u} a b eta) :
    HighCurvatureDerivativePullback.{u} a b eta := by
  intro M _ _ _ _ _ _ _ T hT S hS o
  obtain ⟨kappa, hkappa, hforall⟩ := hmodel M T hT S hS o
  obtain ⟨Q0, hQ0, hmain⟩ := htransfer kappa M T hT S hS o
  obtain ⟨Q1, hQ1, hwit⟩ := hforall (1 / 2) (by norm_num) (by norm_num)
  refine ⟨max Q0 Q1, lt_max_of_lt_left hQ0, fun x t ht hQ y hy => ?_⟩
  obtain ⟨W, _⟩ := hwit x t ⟨ht.1.le, ht.2⟩ (le_trans (le_max_right _ _) hQ)
  obtain ⟨hypos, hbound⟩ := hmain (1 / 2) x t W ht (le_trans (le_max_left _ _) hQ) y hy
  exact ⟨hypos, kappa, W.model, hkappa, W.model_ancient, W.model_scalar_base, hbound⟩

theorem mixedNormLocalBound_of_modelWitnessExistence_and_transfer {a b : ℕ} {C eta : ℝ}
    (hmodel : HighCurvatureModelWitnessExistence.{u})
    (htransfer : WindowedWitnessJetTransfer.{u} a b eta)
    (hbound : AncientModelMixedBound.{u} a b C) :
    MixedNormLocalBound.{u} a b C eta :=
  mixedNormLocalBound_of_derivativePullback a b
    (highCurvatureDerivativePullback_of_modelWitnessExistence_and_transfer hmodel htransfer)
    hbound

theorem exists_jetLocalBound_of_modelWitnessExistence_and_transfer {a b : ℕ} {C eta : ℝ}
    (hC : 0 < C) (heta : 0 < eta) (hmodel : HighCurvatureModelWitnessExistence.{u})
    (htransfer : WindowedWitnessJetTransfer.{u} a b eta)
    (hbound : AncientModelMixedBound.{u} a b C) :
    ∃ C eta : ℝ, 0 < C ∧ 0 < eta ∧ JetLocalBound.{u} a b C eta :=
  exists_jetLocalBound_of_exists_mixedNormLocalBound a b
    ⟨C, eta, hC, heta,
      mixedNormLocalBound_of_modelWitnessExistence_and_transfer hmodel htransfer hbound⟩

theorem windowedWitnessJetTransfer_of_eta_le {a b : ℕ} {eta eta' : ℝ} (hle : eta ≤ eta')
    (h : WindowedWitnessJetTransfer.{u} a b eta') :
    WindowedWitnessJetTransfer.{u} a b eta := by
  intro kappa M _ _ _ _ _ _ _ T hT S hS o
  obtain ⟨Q0, hQ0, hmain⟩ := h kappa M T hT S hS o
  refine ⟨Q0, hQ0, fun eps x t W ht hQ => ?_⟩
  intro y hy
  exact hmain eps x t W ht hQ y
    (DifferentialGeometry.riemannianBallOf_mono (I := I3) (S.base.metric t) x
      (div_le_div_of_nonneg_right hle (Real.sqrt_nonneg _)) hy)

theorem highCurvatureModelWitnessExistence_of_scalar_nonpositive
    (h : ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
      [T2Space (TangentBundle I3 M)] (T : ℝ) (hT : 0 < T)
      (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
      (x : M) (t : ℝ), S.scalar t x ≤ 0) :
    HighCurvatureModelWitnessExistence.{u} := by
  intro M _ _ _ _ _ _ _ T hT S hS o
  refine ⟨1, one_pos, fun eps _ _ => ⟨1, one_pos, fun x t _ hx => ?_⟩⟩
  exact absurd (h M T hT S x t) (by linarith)

theorem windowedWitnessJetTransfer_of_scalar_nonpositive (a b : ℕ) (eta : ℝ)
    (h : ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
      [T2Space (TangentBundle I3 M)] (T : ℝ) (hT : 0 < T)
      (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
      (x : M) (t : ℝ), S.scalar t x ≤ 0) :
    WindowedWitnessJetTransfer.{u} a b eta := by
  intro kappa M _ _ _ _ _ _ _ T hT S hS o
  refine ⟨1, one_pos, fun eps x t W _ hx => ?_⟩
  exact absurd (h M T hT S x t) (by linarith)

section SourceCurvatureTransfer

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

omit [SigmaCompactSpace M] in
private theorem mixedCurvatureNorm_zero_zero_eq (t : ℝ) (y : M) :
    mixedCurvatureNorm S 0 0 t y = Real.sqrt (normSq0S (I := I3) (S.base.metric t) y 4
      (metricRm04At (I := I3) (S.base.metric t) y)) := rfl

omit [SigmaCompactSpace M] in
private theorem iterCov_metricRm04_zero (g : SmoothRiemannianMetric I3 M) (x : M) :
    (iterCov (I := I3) g 4 (metricRm04 (I := I3) g) 0) x =
      metricRm04At (I := I3) g x := rfl

omit [SigmaCompactSpace M] in
private theorem curvatureNormScale (g : SmoothRiemannianMetric I3 M) (h : ℝ) (hh : 0 < h)
    (x : M) :
    Real.sqrt (normSq0S (I := I3) (scaleMetric (I := I3) (h ^ 2) (pow_pos hh 2) g) x 4
        (metricRm04At (I := I3) (scaleMetric (I := I3) (h ^ 2) (pow_pos hh 2) g) x)) =
      (h ^ 2)⁻¹ * Real.sqrt (normSq0S (I := I3) g x 4 (metricRm04At (I := I3) g x)) := by
  have hmain :=
    DifferentialGeometry.Geometry.Tensor.sqrt_normSq0S_iterCov_metricRm04_scaleMetric_sq
      (I := I3) g h hh 0 x
  rw [iterCov_metricRm04_zero (scaleMetric (I := I3) (h ^ 2) (pow_pos hh 2) g) x,
    iterCov_metricRm04_zero g x] at hmain
  simpa only [Nat.add_zero, pow_two, ← mul_inv] using hmain

omit [SigmaCompactSpace M] in
theorem mixedCurvatureNorm_zero_zero_le_of_windowedModelWitness {eps kappa K eta : ℝ} {x : M}
    {t : ℝ} (W : WindowedModelWitness eps kappa S x t) (heps4 : eps ≤ 1 / 4)
    (hK : 0 ≤ K)
    (hmodel : ∀ s ∈ Set.Icc (-(4 : ℝ)) 0, ∀ y ∈
      DifferentialGeometry.riemannianClosedBallOf (I := I3) (W.model.S.base.metric 0)
        W.model.basepoint 2, W.model.rmNormSq s y ≤ K ^ 2)
    (heta : eta ≤ 1)
    {y : M} (hy : y ∈ DifferentialGeometry.riemannianBallOf (I := I3) (S.base.metric t) x
      (eta / Real.sqrt (S.scalar t x))) :
    mixedCurvatureNorm S 0 0 t y ≤ sourceCurvatureBound 3 K * S.scalar t x := by
  have hR : 0 < S.scalar t x := W.scalar_pos
  have hsqrt : 0 < Real.sqrt (S.scalar t x) := Real.sqrt_pos.2 hR
  have hsq : (Real.sqrt (S.scalar t x)) ^ 2 = S.scalar t x := Real.sq_sqrt hR.le
  obtain ⟨-, hbound⟩ :=
    W.unitBall_compact_curvature_bound heps4 hK hmodel (a := 0) (by norm_num)
  have hres : rescaledMetric S t (S.scalar t x) W.scalar_pos 0 =
      scaleMetric (I := I3) (S.scalar t x) W.scalar_pos (S.base.metric t) := by
    simp only [rescaledMetric, parabolicTime, zero_div, add_zero]
  have hmetric : rescaledMetric S t (S.scalar t x) W.scalar_pos 0 =
      scaleMetric (I := I3) (Real.sqrt (S.scalar t x) ^ 2) (pow_pos hsqrt 2)
        (S.base.metric t) := by
    simp only [rescaledMetric, parabolicTime, zero_div, add_zero, hsq]
  have hmemBase : y ∈ DifferentialGeometry.riemannianClosedBallOf (I := I3)
      (scaleMetric (I := I3) (S.scalar t x) W.scalar_pos (S.base.metric t)) x 1 := by
    have hone : Real.sqrt (S.scalar t x) * (1 / Real.sqrt (S.scalar t x)) = 1 := by
      rw [mul_one_div, div_self (ne_of_gt hsqrt)]
    rw [← hone,
      DifferentialGeometry.riemannianClosedBallOf_scaleMetric (I := I3) (S.scalar t x)
        W.scalar_pos (S.base.metric t) x (1 / Real.sqrt (S.scalar t x))]
    refine (DifferentialGeometry.riemannianClosedBallOf_mono (I := I3) (S.base.metric t) x
      (div_le_div_of_nonneg_right heta hsqrt.le)) ?_
    change DifferentialGeometry.riemannianEDistOf (I := I3) (S.base.metric t) x y <
      ENNReal.ofReal (eta / Real.sqrt (S.scalar t x)) at hy
    change DifferentialGeometry.riemannianEDistOf (I := I3) (S.base.metric t) x y ≤
      ENNReal.ofReal (eta / Real.sqrt (S.scalar t x))
    exact hy.le
  have hmem : y ∈ DifferentialGeometry.riemannianClosedBallOf (I := I3)
      (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) x 1 := by
    rw [hres]
    exact hmemBase
  have hcurv := hbound 0 (by norm_num) y hmem
  rw [hmetric] at hcurv
  have hstep : (Real.sqrt (S.scalar t x) ^ 2)⁻¹ * mixedCurvatureNorm S 0 0 t y ≤
      sourceCurvatureBound 3 K := by
    have hs := Real.sqrt_le_sqrt hcurv
    rw [curvatureNormScale (S.base.metric t) (Real.sqrt (S.scalar t x)) hsqrt y,
      ← mixedCurvatureNorm_zero_zero_eq (S := S) t y] at hs
    exact hs.trans_eq (Real.sqrt_sq (sourceCurvatureBound_pos 3 hK).le)
  have hpos2 : 0 < (Real.sqrt (S.scalar t x)) ^ 2 := pow_pos hsqrt 2
  have hmul := mul_le_mul_of_nonneg_left hstep hpos2.le
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos2), one_mul] at hmul
  simpa only [hsq, mul_comm] using hmul

omit [SigmaCompactSpace M] in
theorem exists_sourceCurvatureBound_of_modelCurvatureBound {eps kappa eta : ℝ} {x : M} {t : ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa)
    (W : WindowedModelWitness eps kappa S x t) (heps4 : eps ≤ 1 / 4) (heta : eta ≤ 1)
    {y : M} (hy : y ∈ DifferentialGeometry.riemannianBallOf (I := I3) (S.base.metric t) x
      (eta / Real.sqrt (S.scalar t x))) :
    ∃ K : ℝ, 0 ≤ K ∧
      mixedCurvatureNorm S 0 0 t y ≤ sourceCurvatureBound 3 K * S.scalar t x := by
  obtain ⟨K, hK, hmodel⟩ := hmod
  refine ⟨K, hK, ?_⟩
  refine mixedCurvatureNorm_zero_zero_le_of_windowedModelWitness W heps4 hK ?_ heta hy
  intro s hs y hy
  exact hmodel W.model W.model_ancient W.model_scalar_base s hs y
    (DifferentialGeometry.riemannianClosedBallOf_mono (I := I3) (W.model.S.base.metric 0)
      W.model.basepoint (by norm_num : (2 : ℝ) ≤ 3) hy)

omit [SigmaCompactSpace M] in
theorem exists_sourceCurvatureBound_of_harnackCollapseBound {eps kappa eta : ℝ} {x : M} {t : ℝ}
    (hcollapse : KLimHarnackCollapseBound.{u, 0, 0} (I := I3) kappa)
    (W : WindowedModelWitness eps kappa S x t) (heps4 : eps ≤ 1 / 4) (heta : eta ≤ 1)
    {y : M} (hy : y ∈ DifferentialGeometry.riemannianBallOf (I := I3) (S.base.metric t) x
      (eta / Real.sqrt (S.scalar t x))) :
    ∃ K : ℝ, 0 ≤ K ∧
      mixedCurvatureNorm S 0 0 t y ≤ sourceCurvatureBound 3 K * S.scalar t x :=
  exists_sourceCurvatureBound_of_modelCurvatureBound
    (modelCurvatureBoundNearBase_of_harnackCollapseBound (I := I3) (by simp [ThreeSpace])
      hcollapse) W heps4 heta hy

end SourceCurvatureTransfer

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
