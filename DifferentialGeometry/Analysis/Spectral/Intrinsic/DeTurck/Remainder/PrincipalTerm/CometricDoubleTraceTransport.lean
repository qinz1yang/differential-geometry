import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.Defs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearity.Basic
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalCometric.Extraction
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalTerm.SpectralGarding
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.HigherOrderTame
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.Reconstruction.TensorHilbertSobolev
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.PartitionOfUnityNormComparison
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.InverseCometricMultiplier
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.CovariantOrderCoefficient.ReindexingNorm
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.ConnectionLaplacian.CommutatorCoefficientTame
import DifferentialGeometry.Analysis.Sobolev.Embedding.Tensor.SharpC0JetSum
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.Garding.ChartSobolevBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.Weitzenbock.IntegratedCovariantTensor
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Bounds.FiberNormJets
import DifferentialGeometry.Analysis.Integration.L2.FiberNormBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Bounds.HomFieldActionJets
import DifferentialGeometry.Analysis.Integration.L2.FiniteProductHolderFiberNorm
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.ResolventFactorization
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.Weitzenbock.IntegratedMixedTensor
import DifferentialGeometry.Geometry.Curvature.RoughLaplacian.Commutator.Pointwise
import DifferentialGeometry.Geometry.Curvature.RoughLaplacian.Commutator.HomFieldJetDecomposition
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
    [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
private lemma tangentSpaceModel_cons_cons (x : M) {s : ℕ}
    (a b : TangentSpace I x) (m : Fin s → TangentSpace I x) :
    (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x
      ((Fin.cons a (Fin.cons b m) : Fin (s + 2) → TangentSpace I x) i)) =
      (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x a)
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x b)
          (fun i : Fin s => tangentSpaceModelContinuousLinearEquiv (I := I) x (m i))) :
            Fin (s + 2) → E) := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> rfl

section BalLadder

variable (g₀ : SmoothRiemannianMetric I M)

open DifferentialGeometry.Tensor0SBundle in
omit [CompactSpace M] in
omit [SigmaCompactSpace M] in
private lemma rawTensorConnLap_frame_sum_apply (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (x : M) (D : Tensor0SSpace r I x)
    (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.eval
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          (rawTensorConnLapSmooth (I := I) g r s Φ).toSection x) D) m =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.eval
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 2) I x from
            (iteratedCovGrad (I := I) g r s 2 Φ).toSection x) D)
          (Fin.cons (smoothOrthoFrame (I := I) g x i x)
            (Fin.cons (smoothOrthoFrame (I := I) g x i x) m)) := by
  classical
  have hsec : (rawTensorConnLapSmooth (I := I) g r s Φ).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun z : M => Φ.toSection z) x) := by
    rw [rawTensorConnLapSmooth_toSection_apply (I := I) g r s Φ x,
      rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g r s
        (fun z : M => Φ.toSection z) x]
  have happ : (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      (rawTensorConnLapSmooth (I := I) g r s Φ).toSection x) D =
      ∑ i : Fin (Module.finrank ℝ E),
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun z : M => Φ.toSection z) x) D := by
    rw [hsec, sum_apply]
  rw [happ, Tensor0SSpace.eval_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show (iteratedCovGrad (I := I) g r s 2 Φ).toSection x =
      (covGrad (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s Φ)).toSection x from rfl]
  exact (secondCovGrad_eval_eq_tensorSecondCovDeriv (I := I) g r s Φ
    (smoothOrthoFrame_smooth (I := I) g x i) (smoothOrthoFrame_smooth (I := I) g x i)
    x D m).symm

open DifferentialGeometry.Tensor0SBundle in
omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma operatorFieldComposition_cometricDoubleTrace_apply (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (K : SmoothCcTensor g r (s + 2)) (x : M) (D : Tensor0SSpace r I x)
    (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.eval
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          (ccOperatorFieldComp (I := I) (M := M) g r (s + 2) s
            (DeTurck.cometricDoubleTraceField (I := I) g s) K).toSection x) D) m =
      ∑ k : Fin (Module.finrank ℝ E),
        Tensor0SSpace.eval
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 2) I x from
            K.toSection x) D)
          (Fin.cons ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
              (DeTurck.cometricLmodel (I := I) g x
                (modelCovectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))))
            (Fin.cons ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
              ((Module.finBasis ℝ E) k)) m)) := by
  rw [show (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        (ccOperatorFieldComp (I := I) (M := M) g r (s + 2) s
          (DeTurck.cometricDoubleTraceField (I := I) g s) K).toSection x) D =
      DeTurck.cometricDoubleTraceFib (I := I) g s x
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 2) I x from
          K.toSection x) D) from rfl]
  rw [← Tensor0SSpace.toModel_apply_tangent]
  rw [DeTurck.cometricDoubleTraceFib_toModel]
  simp only [← Tensor0SSpace.toModel_apply_tangent]
  simpa only [tangentSpaceModel_cons_cons, Fin.cons_zero, Fin.cons_succ,
    ContinuousLinearEquiv.apply_symm_apply] using
    DeTurck.modelDoubleTrace_apply (E := E) s (DeTurck.cometricLmodel (I := I) g x)
      (Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 2) I x from
          K.toSection x) D))
      (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (m i))

open DifferentialGeometry.Tensor0SBundle in
omit [SigmaCompactSpace M] in
private lemma rawTensorConnLap_toSection_eq_cometricDoubleTrace (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (x : M) :
    (rawTensorConnLapSmooth (I := I) g r s Φ).toSection x =
      (ccOperatorFieldComp (I := I) (M := M) g r (s + 2) s
        (DeTurck.cometricDoubleTraceField (I := I) g s)
        (iteratedCovGrad (I := I) g r s 2 Φ)).toSection x := by
  classical
  apply tensorRS_eq_of_eval_eq
  intro D m
  refine (rawTensorConnLap_frame_sum_apply (I := I) g r s Φ x D m).trans ?_
  refine Eq.trans ?_ (operatorFieldComposition_cometricDoubleTrace_apply (I := I) g r s
    (iteratedCovGrad (I := I) g r s 2 Φ) x D m).symm
  simp only [← Tensor0SSpace.toModel_apply_tangent]
  simpa only [tangentSpaceModel_cons_cons, Fin.cons_zero, Fin.cons_succ,
    ContinuousLinearEquiv.apply_symm_apply] using
    (DeTurck.cometric_dualTrace_eq_orthoFrame_diag (I := I) g (s := s) x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 2) I x from
          (iteratedCovGrad (I := I) g r s 2 Φ).toSection x) D))
        (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (m i))).symm

omit [SigmaCompactSpace M] in
theorem rawTensorConnLapSmooth_eq_operatorFieldComposition_cometricDoubleTrace_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (Φ : SmoothCcTensor g r s) :
    rawTensorConnLapSmooth (I := I) g r s Φ =
      ccOperatorFieldComp (I := I) (M := M) g r (s + 2) s
        (DeTurck.cometricDoubleTraceField (I := I) g s)
        (iteratedCovGrad (I := I) g r s 2 Φ) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  exact rawTensorConnLap_toSection_eq_cometricDoubleTrace (I := I) g r s Φ x

omit [SigmaCompactSpace M] in
omit [CompactSpace M] [I.Boundaryless] in
lemma oneMinusConnLapSmoothIter_sub (g : SmoothRiemannianMetric I M) (r s : ℕ) (q : ℕ)
    (A B : SmoothCcTensor g r s) :
    oneMinusConnLapSmoothIter (I := I) g r s q (A - B) =
      oneMinusConnLapSmoothIter (I := I) g r s q A -
        oneMinusConnLapSmoothIter (I := I) g r s q B := by
  induction q with
  | zero => simp only [oneMinusConnLapSmoothIter_zero]
  | succ k ih =>
    rw [oneMinusConnLapSmoothIter_succ, oneMinusConnLapSmoothIter_succ,
      oneMinusConnLapSmoothIter_succ, ih]
    unfold oneMinusConnLapSmooth
    rw [rawTensorConnLapSmooth_sub]
    abel

omit [SigmaCompactSpace M] in
omit [CompactSpace M] [I.Boundaryless] in
private lemma rawTensorConnLap_add (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g r s) :
    rawTensorConnLapSmooth (I := I) g r s (A + B) =
      rawTensorConnLapSmooth (I := I) g r s A + rawTensorConnLapSmooth (I := I) g r s B := by
  have h0 : rawTensorConnLapSmooth (I := I) g r s (0 : SmoothCcTensor g r s) = 0 := by
    have := rawTensorConnLapSmooth_sub (I := I) (M := M) g r s A A
    rw [sub_self, sub_self] at this
    exact this
  have hneg : rawTensorConnLapSmooth (I := I) g r s (-B) =
      -rawTensorConnLapSmooth (I := I) g r s B := by
    have := rawTensorConnLapSmooth_sub (I := I) (M := M) g r s 0 B
    rw [zero_sub, h0, zero_sub] at this
    exact this
  have := rawTensorConnLapSmooth_sub (I := I) (M := M) g r s A (-B)
  rw [sub_neg_eq_add, hneg, sub_neg_eq_add] at this
  exact this

omit [SigmaCompactSpace M] in
omit [CompactSpace M] [I.Boundaryless] in
private lemma commutatorCorrection_add (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g r s) :
    oneMinusConnLapSmooth (I := I) g r s (A + B) =
      oneMinusConnLapSmooth (I := I) g r s A + oneMinusConnLapSmooth (I := I) g r s B := by
  unfold oneMinusConnLapSmooth
  rw [rawTensorConnLap_add]
  abel

omit [SigmaCompactSpace M] in
private lemma operatorFieldApplication_connLap_commutator (Φ : SmoothCcTensor g₀ 2 2) (W : SmoothCcTensor g₀ 0 2) :
    oneMinusConnLapSmooth (I := I) g₀ 0 2 (operatorFieldApply (I := I) (M := M) g₀ 2 2 Φ W) =
      operatorFieldApply (I := I) (M := M) g₀ 2 2 (oneMinusConnLapSmooth (I := I) g₀ 2 2 Φ) W +
        (-(operatorFieldApply (I := I) (M := M) g₀ 2 2 Φ (rawTensorConnLapSmooth (I := I) g₀ 0 2 W))
          - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
            (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                (slotExtend (I := I) (M := M) g₀ 2 (2 + 1) (covGrad (I := I) (M := M) g₀ 2 2 Φ))
                (covGrad (I := I) (M := M) g₀ 0 2 W))
          - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
            (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                  (slotExtend (I := I) (M := M) g₀ 2 2 Φ))
                (covGrad (I := I) (M := M) g₀ 0 2 W))) := by
  have hlap : operatorFieldApply (I := I) (M := M) g₀ 2 2 (rawTensorConnLapSmooth (I := I) g₀ 2 2 Φ)
    W =
      operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
        (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
        (operatorFieldApply (I := I) (M := M) g₀ 2 (2 + 2)
          (covGrad (I := I) (M := M) g₀ 2 (2 + 1) (covGrad (I := I) (M := M) g₀ 2 2 Φ)) W) := by
    rw [rawTensorConnLapSmooth_eq_operatorFieldComposition_cometricDoubleTrace_rs (I := I) (M := M) g₀ 2 2 Φ]
    rw [show iteratedCovGrad (I := I) g₀ 2 2 2 Φ =
        covGrad (I := I) (M := M) g₀ 2 (2 + 1) (covGrad (I := I) (M := M) g₀ 2 2 Φ) from rfl]
    exact (SmoothCcTensor.ext_iff.mpr rfl).symm
  have hpeel := rawTensorConnLap_operatorFieldApplication_comm_of_rank (I := I) g₀ 2 2 Φ W
  unfold oneMinusConnLapSmooth
  rw [hpeel, operatorFieldApplication_sub_left (I := I) (M := M) g₀ 2 2 Φ
    (rawTensorConnLapSmooth (I := I) g₀ 2 2 Φ) W, hlap]
  abel

omit [SigmaCompactSpace M] in
lemma DeTurckRemainderPrincipalTerm.connLapIterate_operatorFieldApplication_decomposition (Φ : SmoothCcTensor g₀ 2 2) (W : SmoothCcTensor g₀ 0 2) (p : ℕ) :
    oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p (operatorFieldApply (I := I) (M := M) g₀ 2 2 Φ W) =
      operatorFieldApply (I := I) (M := M) g₀ 2 2 (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p Φ) W
        +
        ∑ q ∈ Finset.range p, oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p - 1 - q)
          (-(operatorFieldApply (I := I) (M := M) g₀ 2 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q Φ)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 W))
            - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
              (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                    (covGrad (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q Φ)))
                  (covGrad (I := I) (M := M) g₀ 0 2 W))
            - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
              (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                    (slotExtend (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q Φ)))
                  (covGrad (I := I) (M := M) g₀ 0 2 W))) := by
  classical
  set Efun : ℕ → SmoothCcTensor g₀ 0 2 := fun q =>
    -(operatorFieldApply (I := I) (M := M) g₀ 2 2 (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q Φ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 W))
      - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
        (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
          (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
            (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
              (covGrad (I := I) (M := M) g₀ 2 2
                (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q Φ)))
            (covGrad (I := I) (M := M) g₀ 0 2 W))
      - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
        (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
          (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
            (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
              (slotExtend (I := I) (M := M) g₀ 2 2
                (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q Φ)))
            (covGrad (I := I) (M := M) g₀ 0 2 W)) with hEfun
  induction p with
  | zero =>
    simp only [oneMinusConnLapSmoothIter_zero, Finset.range_zero, Finset.sum_empty, add_zero]
  | succ p ih =>
    have hPhom : ∀ (A B : SmoothCcTensor g₀ 0 2),
        oneMinusConnLapSmooth (I := I) g₀ 0 2 (A + B) =
          oneMinusConnLapSmooth (I := I) g₀ 0 2 A +
            oneMinusConnLapSmooth (I := I) g₀ 0 2 B :=
      fun A B => commutatorCorrection_add (I := I) (M := M) g₀ 0 2 A B
    have hpeelp := operatorFieldApplication_connLap_commutator (I := I) (M := M) g₀
      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p Φ) W
    calc oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p + 1)
          (operatorFieldApply (I := I) (M := M) g₀ 2 2 Φ W) = oneMinusConnLapSmooth (I := I) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p
              (operatorFieldApply (I := I) (M := M) g₀ 2 2 Φ W)) := by
          rw [oneMinusConnLapSmoothIter_succ]
      _ = oneMinusConnLapSmooth (I := I) g₀ 0 2
            (operatorFieldApply (I := I) (M := M) g₀ 2 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p Φ) W +
              ∑ q ∈ Finset.range p,
                oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p - 1 - q) (Efun q)) := by
          rw [ih]
      _ = oneMinusConnLapSmooth (I := I) g₀ 0 2
            (operatorFieldApply (I := I) (M := M) g₀ 2 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p Φ) W) +
            ∑ q ∈ Finset.range p,
              oneMinusConnLapSmooth (I := I) g₀ 0 2
                (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p - 1 - q) (Efun q)) := by
          rw [hPhom]
          congr 1
          exact map_sum (AddMonoidHom.mk' (oneMinusConnLapSmooth (I := I) g₀ 0 2)
            (fun A B => hPhom A B)) (fun q => oneMinusConnLapSmoothIter (I := I) g₀ 0 2
              (p - 1 - q) (Efun q)) (Finset.range p)
      _ = (operatorFieldApply (I := I) (M := M) g₀ 2 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 (p + 1) Φ) W + Efun p) +
            ∑ q ∈ Finset.range p,
              oneMinusConnLapSmooth (I := I) g₀ 0 2
                (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p - 1 - q) (Efun q)) := by
          rw [hpeelp, ← oneMinusConnLapSmoothIter_succ (I := I) g₀ 2 2 p Φ]
      _ = (operatorFieldApply (I := I) (M := M) g₀ 2 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 (p + 1) Φ) W + Efun p) +
            ∑ q ∈ Finset.range p,
              oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p + 1 - 1 - q) (Efun q) := by
          congr 1
          refine Finset.sum_congr rfl (fun q hq => ?_)
          have hqlt : q < p := Finset.mem_range.mp hq
          rw [← oneMinusConnLapSmoothIter_succ (I := I) g₀ 0 2 (p - 1 - q) (Efun q),
            show p - 1 - q + 1 = p + 1 - 1 - q from by omega]
      _ = operatorFieldApply (I := I) (M := M) g₀ 2 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 (p + 1) Φ) W +
            ∑ q ∈ Finset.range (p + 1),
              oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p + 1 - 1 - q) (Efun q) := by
          rw [Finset.sum_range_succ,
            show p + 1 - 1 - p = 0 from by omega, oneMinusConnLapSmoothIter_zero]
          abel

end BalLadder

end Spectral
end Analysis
end DifferentialGeometry

end
