import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RemainderAction
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2H3Principal
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SecondCovariantDerivativeApplication
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Inclusion
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SmoothCcDense

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private noncomputable def secondOrderActionCore
    (g : SmoothRiemannianMetric I M) (A : LowerScaleActionCoefficients g)
    (σ : ℝ) :
    SmoothCcTensor g 0 2 →ₗ[ℝ]
      TensorHs (I := I) (M := M) g 0 2 σ where
  toFun := fun W =>
    ccTensorToHs (I := I) (M := M) g 2 σ
      (A.secondOrderAction (I := I) (M := M) W)
  map_add' := fun W V => by
    simp only [LowerScaleActionCoefficients.secondOrderAction, iteratedCovGrad_add,
      operatorFieldApplication_add_right, ccTensorToHs_add]
  map_smul' := fun c W => by
    simp only [RingHom.id_apply, LowerScaleActionCoefficients.secondOrderAction,
      iteratedCovGrad_smul, operatorFieldApplication_smul_right, ccTensorToHs_smul]

noncomputable def LowerScaleActionCoefficients.secondOrderActionFourthToSecondOrder
    {g : SmoothRiemannianMetric I M} (A : LowerScaleActionCoefficients g) :
    TensorHs (I := I) (M := M) g 0 2 (4 : ℝ) →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 (2 : ℝ) :=
  secondCovariantDerivativeApplication (I := I) (M := M) g 2 2 A.secondOrderCoefficient

noncomputable def LowerScaleActionCoefficients.secondOrderActionThirdToFirstOrder
    {g : SmoothRiemannianMetric I M} (A : LowerScaleActionCoefficients g) :
    TensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 (1 : ℝ) :=
  (secondOrderActionCore (I := I) (M := M) g A (1 : ℝ)).extendOfNorm
    (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ))

theorem secondOrderAction_sobolev_extension_bounds
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : LowerScaleActionCoefficients g) (B : ℝ), 0 ≤ B →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 4 2 x
              (A.secondOrderCoefficient.toSection x) ≤ B ^ 2) →
        covariantJetNormSq (I := I) (M := M) g 2 A.secondOrderCoefficient ≤ B ^ 2 →
        ‖A.secondOrderActionFourthToSecondOrder (I := I) (M := M)‖ ≤ C * B ∧
        ‖A.secondOrderActionThirdToFirstOrder (I := I) (M := M)‖ ≤ C * B ∧
        (∀ W : SmoothCcTensor g 0 2,
          A.secondOrderActionFourthToSecondOrder (I := I) (M := M)
              (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) W) =
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
              (A.secondOrderAction (I := I) (M := M) W)) ∧
        (∀ W : SmoothCcTensor g 0 2,
          A.secondOrderActionThirdToFirstOrder (I := I) (M := M)
              (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W) =
            ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
              (A.secondOrderAction (I := I) (M := M) W)) ∧
        (tensorHsInclusion (I := I) (M := M) (g := g)
            (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
              (A.secondOrderActionFourthToSecondOrder (I := I) (M := M)) =
          (A.secondOrderActionThirdToFirstOrder (I := I) (M := M)).comp
            (tensorHsInclusion (I := I) (M := M) (g := g)
              (r := 0) (s := 2) (show (3 : ℝ) ≤ 4 by norm_num)) := by
  obtain ⟨Ch, hCh, hhigh⟩ :=
    secondCovariantDerivativeApplication_norm (I := I) (M := M) hDim g 2 2
  obtain ⟨Cl, hCl, hlow⟩ :=
    operatorFieldApplication_h2_h3_h1 (I := I) (M := M) hDim g 2 2
  let C : ℝ := Ch + Cl
  refine ⟨C, add_nonneg hCh hCl, ?_⟩
  intro A B hB hsup hjet
  have hdense4 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (4 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hdense3 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hlowMap :
      ∀ W : SmoothCcTensor g 0 2,
        ‖secondOrderActionCore (I := I) (M := M) g A (1 : ℝ) W‖ ≤
          (Cl * B) *
            ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W‖ := by
    intro W
    change ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
      (operatorFieldApply (I := I) (M := M) g 4 2 A.secondOrderCoefficient
        (iteratedCovGrad (I := I) g 0 2 2 W))‖ ≤ _
    simpa only [covariantJetNormSq, Nat.reduceAdd] using
      hlow A.secondOrderCoefficient W B hB hsup hjet
  have hHiNorm :
      ‖A.secondOrderActionFourthToSecondOrder (I := I) (M := M)‖ ≤ Ch * B := by
    simpa only [LowerScaleActionCoefficients.secondOrderActionFourthToSecondOrder, covariantJetNormSq] using
      hhigh A.secondOrderCoefficient B hB hjet
  have hLoNorm :
      ‖A.secondOrderActionThirdToFirstOrder (I := I) (M := M)‖ ≤ Cl * B := by
    unfold LowerScaleActionCoefficients.secondOrderActionThirdToFirstOrder
    exact LinearMap.opNorm_extendOfNorm_le
      hdense3 (mul_nonneg hCl hB) hlowMap
  have hHiCore (W : SmoothCcTensor g 0 2) :
      A.secondOrderActionFourthToSecondOrder (I := I) (M := M)
          (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) W) =
        ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (A.secondOrderAction (I := I) (M := M) W) := by
    simpa only [LowerScaleActionCoefficients.secondOrderActionFourthToSecondOrder, LowerScaleActionCoefficients.secondOrderAction] using
      secondCovariantDerivativeApplication_ccTensorToHs (I := I) (M := M) hDim g 2 2 A.secondOrderCoefficient W
  have hLoCore (W : SmoothCcTensor g 0 2) :
      A.secondOrderActionThirdToFirstOrder (I := I) (M := M)
          (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W) =
        ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
          (A.secondOrderAction (I := I) (M := M) W) := by
    change
      ((secondOrderActionCore (I := I) (M := M) g A (1 : ℝ)).extendOfNorm
          (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)))
          ((ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) W) =
        (secondOrderActionCore (I := I) (M := M) g A (1 : ℝ)) W
    apply LinearMap.extendOfNorm_eq hdense3
    exact ⟨Cl * B, hlowMap⟩
  have hHiNorm' :
      ‖A.secondOrderActionFourthToSecondOrder (I := I) (M := M)‖ ≤ C * B :=
    hHiNorm.trans
      (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right hCl) hB)
  have hLoNorm' :
      ‖A.secondOrderActionThirdToFirstOrder (I := I) (M := M)‖ ≤ C * B :=
    hLoNorm.trans
      (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left hCh) hB)
  refine ⟨hHiNorm', hLoNorm', hHiCore, hLoCore, ?_⟩
  let L :=
    (tensorHsInclusion (I := I) (M := M) (g := g)
      (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
        (A.secondOrderActionFourthToSecondOrder (I := I) (M := M))
  let R :=
    (A.secondOrderActionThirdToFirstOrder (I := I) (M := M)).comp
      (tensorHsInclusion (I := I) (M := M) (g := g)
        (r := 0) (s := 2) (show (3 : ℝ) ≤ 4 by norm_num))
  have hfun : (L : _ → _) = R :=
    hdense4.equalizer L.continuous R.continuous (by
      funext W
      simp only [Function.comp_apply, L, R, ccToHsLin_apply,
        ContinuousLinearMap.comp_apply]
      rw [hHiCore]
      have hin :
          tensorHsInclusion (I := I) (M := M) (g := g)
              (r := 0) (s := 2) (show (3 : ℝ) ≤ 4 by norm_num)
              (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) W) =
            ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W := by
        apply TensorHs.ext
        funext i
        simp only [tensorHsInclusion_coeff_apply, ccTensorToHs_coeff]
      rw [hin, hLoCore]
      apply TensorHs.ext
      funext i
      simp only [tensorHsInclusion_coeff_apply, ccTensorToHs_coeff])
  apply ContinuousLinearMap.ext
  intro W
  exact congrFun hfun W

private noncomputable def secondOrderCoefficientDifference
    {g : SmoothRiemannianMetric I M}
    (A B : LowerScaleActionCoefficients g) : LowerScaleActionCoefficients g where
  zeroOrderCoefficient := 0
  firstOrderCoefficient := 0
  secondOrderCoefficient := A.secondOrderCoefficient - B.secondOrderCoefficient

theorem secondOrderActionFourthToSecondOrder_ccTensorToHs
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A : LowerScaleActionCoefficients g)
    (W : SmoothCcTensor g 0 2) :
    A.secondOrderActionFourthToSecondOrder (I := I) (M := M)
        (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) W) =
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (A.secondOrderAction (I := I) (M := M) W) := by
  simpa only [LowerScaleActionCoefficients.secondOrderActionFourthToSecondOrder, LowerScaleActionCoefficients.secondOrderAction] using
    secondCovariantDerivativeApplication_ccTensorToHs (I := I) (M := M) hDim g 2 2 A.secondOrderCoefficient W

theorem secondOrderActionThirdToFirstOrder_ccTensorToHs
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A : LowerScaleActionCoefficients g)
    (W : SmoothCcTensor g 0 2) :
    A.secondOrderActionThirdToFirstOrder (I := I) (M := M)
        (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W) =
      ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
        (A.secondOrderAction (I := I) (M := M) W) := by
  obtain ⟨C, hC, hpair⟩ := secondOrderAction_sobolev_extension_bounds (I := I) (M := M) hDim g
  obtain ⟨K, hK, hpoint⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g 4 2 A.secondOrderCoefficient
  let J : ℝ := covariantJetNormSq (I := I) (M := M) g 2 A.secondOrderCoefficient
  let B : ℝ := Real.sqrt (K + J)
  have hJ : 0 ≤ J := by
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsum : 0 ≤ K + J := add_nonneg hK hJ
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = K + J := by
    simpa only [B] using Real.sq_sqrt hsum
  have hpointB : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          (A.secondOrderCoefficient.toSection x) ≤ B ^ 2 := by
    intro x
    rw [hBsq]
    exact (hpoint x).trans (le_add_of_nonneg_right hJ)
  have hjetB :
      covariantJetNormSq (I := I) (M := M) g 2 A.secondOrderCoefficient ≤ B ^ 2 := by
    rw [hBsq]
    exact le_add_of_nonneg_left hK
  exact (hpair A B hB hpointB hjetB).2.2.2.1 W

theorem secondOrderAction_sobolev_extensions_commute
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A : LowerScaleActionCoefficients g) :
    (tensorHsInclusion (I := I) (M := M) (g := g)
        (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
          (A.secondOrderActionFourthToSecondOrder (I := I) (M := M)) =
      (A.secondOrderActionThirdToFirstOrder (I := I) (M := M)).comp
        (tensorHsInclusion (I := I) (M := M) (g := g)
          (r := 0) (s := 2) (show (3 : ℝ) ≤ 4 by norm_num)) := by
  let L :=
    (tensorHsInclusion (I := I) (M := M) (g := g)
      (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
        (A.secondOrderActionFourthToSecondOrder (I := I) (M := M))
  let R :=
    (A.secondOrderActionThirdToFirstOrder (I := I) (M := M)).comp
      (tensorHsInclusion (I := I) (M := M) (g := g)
        (r := 0) (s := 2) (show (3 : ℝ) ≤ 4 by norm_num))
  have hdense4 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (4 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hfun : (L : _ → _) = R :=
    hdense4.equalizer L.continuous R.continuous (by
      funext W
      simp only [Function.comp_apply, L, R, ccToHsLin_apply,
        ContinuousLinearMap.comp_apply]
      rw [secondOrderActionFourthToSecondOrder_ccTensorToHs (I := I) (M := M) hDim g A]
      have hin :
          tensorHsInclusion (I := I) (M := M) (g := g)
              (r := 0) (s := 2) (show (3 : ℝ) ≤ 4 by norm_num)
              (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) W) =
            ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W := by
        apply TensorHs.ext
        funext i
        simp only [tensorHsInclusion_coeff_apply, ccTensorToHs_coeff]
      rw [hin, secondOrderActionThirdToFirstOrder_ccTensorToHs (I := I) (M := M) hDim g A]
      apply TensorHs.ext
      funext i
      simp only [tensorHsInclusion_coeff_apply, ccTensorToHs_coeff])
  apply ContinuousLinearMap.ext
  intro W
  exact congrFun hfun W

theorem secondOrderAction_sobolev_extension_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A B : LowerScaleActionCoefficients g) (R : ℝ), 0 ≤ R →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 4 2 x
              ((A.secondOrderCoefficient - B.secondOrderCoefficient).toSection x) ≤ R ^ 2) →
        covariantJetNormSq (I := I) (M := M) g 2 (A.secondOrderCoefficient - B.secondOrderCoefficient) ≤ R ^ 2 →
        ‖A.secondOrderActionFourthToSecondOrder (I := I) (M := M) -
            B.secondOrderActionFourthToSecondOrder (I := I) (M := M)‖ ≤ C * R ∧
        ‖A.secondOrderActionThirdToFirstOrder (I := I) (M := M) -
            B.secondOrderActionThirdToFirstOrder (I := I) (M := M)‖ ≤ C * R := by
  obtain ⟨C, hC, hpair⟩ := secondOrderAction_sobolev_extension_bounds (I := I) (M := M) hDim g
  refine ⟨C, hC, ?_⟩
  intro A B R hR hpoint hjet
  let D : LowerScaleActionCoefficients g := secondOrderCoefficientDifference A B
  have hDpoint : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          (D.secondOrderCoefficient.toSection x) ≤ R ^ 2 := by
    simpa only [D, secondOrderCoefficientDifference] using hpoint
  have hDjet :
      covariantJetNormSq (I := I) (M := M) g 2 D.secondOrderCoefficient ≤ R ^ 2 := by
    simpa only [D, secondOrderCoefficientDifference] using hjet
  obtain ⟨hDhi, hDlo, hDhiCore, hDloCore, _⟩ :=
    hpair D R hR hDpoint hDjet
  have hdense4 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (4 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hdense3 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hHi :
      D.secondOrderActionFourthToSecondOrder (I := I) (M := M) =
        A.secondOrderActionFourthToSecondOrder (I := I) (M := M) -
          B.secondOrderActionFourthToSecondOrder (I := I) (M := M) := by
    let L := D.secondOrderActionFourthToSecondOrder (I := I) (M := M)
    let Q := A.secondOrderActionFourthToSecondOrder (I := I) (M := M) -
      B.secondOrderActionFourthToSecondOrder (I := I) (M := M)
    have hfun : (L : _ → _) = Q :=
      hdense4.equalizer L.continuous Q.continuous (by
        funext W
        simp only [Function.comp_apply, L, Q, ccToHsLin_apply,
          sub_apply]
        rw [hDhiCore,
          secondOrderActionFourthToSecondOrder_ccTensorToHs (I := I) (M := M) hDim g A W,
          secondOrderActionFourthToSecondOrder_ccTensorToHs (I := I) (M := M) hDim g B W]
        simp only [D, secondOrderCoefficientDifference, LowerScaleActionCoefficients.secondOrderAction, operatorFieldApplication_sub_left]
        simpa only [ccToHsLin_apply] using
          map_sub (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ))
            (operatorFieldApply (I := I) (M := M) g 4 2 A.secondOrderCoefficient
              (iteratedCovGrad (I := I) g 0 2 2 W))
            (operatorFieldApply (I := I) (M := M) g 4 2 B.secondOrderCoefficient
              (iteratedCovGrad (I := I) g 0 2 2 W)))
    apply ContinuousLinearMap.ext
    intro W
    exact congrFun hfun W
  have hLo :
      D.secondOrderActionThirdToFirstOrder (I := I) (M := M) =
        A.secondOrderActionThirdToFirstOrder (I := I) (M := M) -
          B.secondOrderActionThirdToFirstOrder (I := I) (M := M) := by
    let L := D.secondOrderActionThirdToFirstOrder (I := I) (M := M)
    let Q := A.secondOrderActionThirdToFirstOrder (I := I) (M := M) -
      B.secondOrderActionThirdToFirstOrder (I := I) (M := M)
    have hfun : (L : _ → _) = Q :=
      hdense3.equalizer L.continuous Q.continuous (by
        funext W
        simp only [Function.comp_apply, L, Q, ccToHsLin_apply,
          sub_apply]
        rw [hDloCore,
          secondOrderActionThirdToFirstOrder_ccTensorToHs (I := I) (M := M) hDim g A W,
          secondOrderActionThirdToFirstOrder_ccTensorToHs (I := I) (M := M) hDim g B W]
        simp only [D, secondOrderCoefficientDifference, LowerScaleActionCoefficients.secondOrderAction, operatorFieldApplication_sub_left]
        simpa only [ccToHsLin_apply] using
          map_sub (ccToHsLin (I := I) (M := M) g 2 (1 : ℝ))
            (operatorFieldApply (I := I) (M := M) g 4 2 A.secondOrderCoefficient
              (iteratedCovGrad (I := I) g 0 2 2 W))
            (operatorFieldApply (I := I) (M := M) g 4 2 B.secondOrderCoefficient
              (iteratedCovGrad (I := I) g 0 2 2 W)))
    apply ContinuousLinearMap.ext
    intro W
    exact congrFun hfun W
  constructor
  · rwa [← hHi]
  · rwa [← hLo]

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
