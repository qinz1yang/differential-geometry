import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Action.Remainder
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.SmoothCompactSupportDense
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.Inclusion
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJet.Interpolation

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
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private theorem exists_firstOrderAction_thirdToSecondOrder_spectralSobolev_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : LowerScaleActionCoefficients g) (Q : ℝ), 0 ≤ Q →
        (∀ W : SmoothCcTensor g 0 2,
          covariantJetNormSq (I := I) (M := M) g 2
              (A.firstOrderAction (I := I) (M := M) W) ≤
            Q * covariantJetNormSq (I := I) (M := M) g 3 W) →
        ∀ W : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
              (A.firstOrderAction (I := I) (M := M) W)‖ ≤
            C * Real.sqrt Q *
              ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W‖ := by
  obtain ⟨Co, hCo, hout⟩ := exists_spectralSobolevNorm_le_of_covariantJetNormSq_le_sq (I := I) (M := M) g 2 2
  obtain ⟨Ci, hCi, hin⟩ := exists_covariantJetNormSq_le_spectralSobolevNorm_sq (I := I) (M := M) g 2 3
  refine ⟨Co * Ci, mul_nonneg hCo hCi, ?_⟩
  intro A Q hQ hact W
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W‖
  let D : ℝ := Ci * N
  let R : ℝ := Real.sqrt Q * D
  have hN : 0 ≤ N := norm_nonneg _
  have hD : 0 ≤ D := mul_nonneg hCi hN
  have hR : 0 ≤ R := mul_nonneg (Real.sqrt_nonneg _) hD
  have hR2 : R ^ 2 = Q * D ^ 2 := by
    simp only [R]
    rw [mul_pow, Real.sq_sqrt hQ]
  have hY :
      covariantJetNormSq (I := I) (M := M) g 2
          (A.firstOrderAction (I := I) (M := M) W) ≤ R ^ 2 := by
    calc
      _ ≤ Q * covariantJetNormSq (I := I) (M := M) g 3 W := hact W
      _ ≤ Q * D ^ 2 :=
        mul_le_mul_of_nonneg_left
          (by
            have hinW := hin W
            rw [show ((3 : ℕ) : ℝ) = (3 : ℝ) by norm_num] at hinW
            simpa only [D, N] using hinW) hQ
      _ = R ^ 2 := hR2.symm
  have hbound :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (A.firstOrderAction (I := I) (M := M) W)‖ ≤ Co * R := by
    simpa only [Nat.cast_ofNat] using
      hout (A.firstOrderAction (I := I) (M := M) W) R hR hY
  calc
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (A.firstOrderAction (I := I) (M := M) W)‖ ≤ Co * R := hbound
    _ = (Co * Ci) * Real.sqrt Q *
        ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W‖ := by
      simp only [R, D, N]
      ring

theorem exists_firstOrderAction_secondToFirstOrder_spectralSobolev_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : LowerScaleActionCoefficients g) (Q : ℝ), 0 ≤ Q →
        (∀ W : SmoothCcTensor g 0 2,
          covariantJetNormSq (I := I) (M := M) g 1
              (A.firstOrderAction (I := I) (M := M) W) ≤
            Q * covariantJetNormSq (I := I) (M := M) g 2 W) →
        ∀ W : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
              (A.firstOrderAction (I := I) (M := M) W)‖ ≤
            C * Real.sqrt Q *
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W‖ := by
  obtain ⟨Co, hCo, hout⟩ := exists_spectralSobolevNorm_le_of_covariantJetNormSq_le_sq (I := I) (M := M) g 2 1
  obtain ⟨Ci, hCi, hin⟩ := exists_covariantJetNormSq_le_spectralSobolevNorm_sq (I := I) (M := M) g 2 2
  refine ⟨Co * Ci, mul_nonneg hCo hCi, ?_⟩
  intro A Q hQ hact W
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W‖
  let D : ℝ := Ci * N
  let R : ℝ := Real.sqrt Q * D
  have hN : 0 ≤ N := norm_nonneg _
  have hD : 0 ≤ D := mul_nonneg hCi hN
  have hR : 0 ≤ R := mul_nonneg (Real.sqrt_nonneg _) hD
  have hR2 : R ^ 2 = Q * D ^ 2 := by
    simp only [R]
    rw [mul_pow, Real.sq_sqrt hQ]
  have hY :
      covariantJetNormSq (I := I) (M := M) g 1
          (A.firstOrderAction (I := I) (M := M) W) ≤ R ^ 2 := by
    calc
      _ ≤ Q * covariantJetNormSq (I := I) (M := M) g 2 W := hact W
      _ ≤ Q * D ^ 2 :=
        mul_le_mul_of_nonneg_left
          (by
            have hinW := hin W
            rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num] at hinW
            simpa only [D, N] using hinW) hQ
      _ = R ^ 2 := hR2.symm
  have hbound :
      ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
          (A.firstOrderAction (I := I) (M := M) W)‖ ≤ Co * R := by
    have hboundNat :=
      hout (A.firstOrderAction (I := I) (M := M) W) R hR hY
    rw [show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num] at hboundNat
    exact hboundNat
  calc
    ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
        (A.firstOrderAction (I := I) (M := M) W)‖ ≤ Co * R := hbound
    _ = (Co * Ci) * Real.sqrt Q *
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W‖ := by
      simp only [R, D, N]
      ring

private noncomputable def firstOrderActionCore
    (g : SmoothRiemannianMetric I M) (A : LowerScaleActionCoefficients g)
    (σ : ℝ) :
    SmoothCcTensor g 0 2 →ₗ[ℝ]
      TensorHs (I := I) (M := M) g 0 2 σ where
  toFun := fun W =>
    ccTensorToHs (I := I) (M := M) g 2 σ
      (A.firstOrderAction (I := I) (M := M) W)
  map_add' := fun W V => by
    simp only [LowerScaleActionCoefficients.firstOrderAction, iteratedCovGrad_add,
      operatorFieldApplication_add_right, ccTensorToHs_add]
    module
  map_smul' := fun c W => by
    simp only [RingHom.id_apply, LowerScaleActionCoefficients.firstOrderAction,
      iteratedCovGrad_smul, operatorFieldApplication_smul_right, ccTensorToHs_add,
      ccTensorToHs_smul, smul_add]

noncomputable def LowerScaleActionCoefficients.firstOrderActionThirdToSecondOrder
    {g : SmoothRiemannianMetric I M} (A : LowerScaleActionCoefficients g) :
    TensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 (2 : ℝ) :=
  (firstOrderActionCore (I := I) (M := M) g A (2 : ℝ)).extendOfNorm
    (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ))

noncomputable def LowerScaleActionCoefficients.firstOrderActionSecondToFirstOrder
    {g : SmoothRiemannianMetric I M} (A : LowerScaleActionCoefficients g) :
    TensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 (1 : ℝ) :=
  (firstOrderActionCore (I := I) (M := M) g A (1 : ℝ)).extendOfNorm
    (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ))

theorem exists_firstOrderAction_spectralSobolev_extensions
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : LowerScaleActionCoefficients g) (Q : ℝ), 0 ≤ Q →
        (∀ W : SmoothCcTensor g 0 2,
          covariantJetNormSq (I := I) (M := M) g 2
              (A.firstOrderAction (I := I) (M := M) W) ≤
            Q * covariantJetNormSq (I := I) (M := M) g 3 W) →
        (∀ W : SmoothCcTensor g 0 2,
          covariantJetNormSq (I := I) (M := M) g 1
              (A.firstOrderAction (I := I) (M := M) W) ≤
            Q * covariantJetNormSq (I := I) (M := M) g 2 W) →
        ‖A.firstOrderActionThirdToSecondOrder (I := I) (M := M)‖ ≤ C * Real.sqrt Q ∧
        ‖A.firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤ C * Real.sqrt Q ∧
        (∀ W : SmoothCcTensor g 0 2,
          A.firstOrderActionThirdToSecondOrder (I := I) (M := M)
              (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W) =
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
              (A.firstOrderAction (I := I) (M := M) W)) ∧
        (∀ W : SmoothCcTensor g 0 2,
          A.firstOrderActionSecondToFirstOrder (I := I) (M := M)
              (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W) =
            ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
              (A.firstOrderAction (I := I) (M := M) W)) ∧
        (tensorHsInclusion (I := I) (M := M) (g := g)
            (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
              (A.firstOrderActionThirdToSecondOrder (I := I) (M := M)) =
          (A.firstOrderActionSecondToFirstOrder (I := I) (M := M)).comp
            (tensorHsInclusion (I := I) (M := M) (g := g)
              (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num)) := by
  obtain ⟨Ch, hCh, hhigh⟩ := exists_firstOrderAction_thirdToSecondOrder_spectralSobolev_bound (I := I) (M := M) g
  obtain ⟨Cl, hCl, hlow⟩ := exists_firstOrderAction_secondToFirstOrder_spectralSobolev_bound (I := I) (M := M) g
  refine ⟨Ch + Cl, add_nonneg hCh hCl, ?_⟩
  intro A Q hQ hHi hLo
  have hdense3 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hdense2 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hhi := hhigh A Q hQ hHi
  have hlo := hlow A Q hQ hLo
  have hHiNorm :
      ‖A.firstOrderActionThirdToSecondOrder (I := I) (M := M)‖ ≤ Ch * Real.sqrt Q := by
    unfold LowerScaleActionCoefficients.firstOrderActionThirdToSecondOrder
    exact LinearMap.opNorm_extendOfNorm_le
      hdense3 (mul_nonneg hCh (Real.sqrt_nonneg _)) hhi
  have hLoNorm :
      ‖A.firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤ Cl * Real.sqrt Q := by
    unfold LowerScaleActionCoefficients.firstOrderActionSecondToFirstOrder
    exact LinearMap.opNorm_extendOfNorm_le
      hdense2 (mul_nonneg hCl (Real.sqrt_nonneg _)) hlo
  have hHiCore (W : SmoothCcTensor g 0 2) :
      A.firstOrderActionThirdToSecondOrder (I := I) (M := M)
          (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W) =
        ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (A.firstOrderAction (I := I) (M := M) W) := by
    change
      ((firstOrderActionCore (I := I) (M := M) g A (2 : ℝ)).extendOfNorm
          (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)))
          ((ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) W) =
        (firstOrderActionCore (I := I) (M := M) g A (2 : ℝ)) W
    apply LinearMap.extendOfNorm_eq hdense3
    exact ⟨Ch * Real.sqrt Q, hhi⟩
  have hLoCore (W : SmoothCcTensor g 0 2) :
      A.firstOrderActionSecondToFirstOrder (I := I) (M := M)
          (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W) =
        ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
          (A.firstOrderAction (I := I) (M := M) W) := by
    change
      ((firstOrderActionCore (I := I) (M := M) g A (1 : ℝ)).extendOfNorm
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)))
          ((ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) W) =
        (firstOrderActionCore (I := I) (M := M) g A (1 : ℝ)) W
    apply LinearMap.extendOfNorm_eq hdense2
    exact ⟨Cl * Real.sqrt Q, hlo⟩
  have hHiNorm' :
      ‖A.firstOrderActionThirdToSecondOrder (I := I) (M := M)‖ ≤
        (Ch + Cl) * Real.sqrt Q :=
    hHiNorm.trans
      (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right hCl) (Real.sqrt_nonneg _))
  have hLoNorm' :
      ‖A.firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤
        (Ch + Cl) * Real.sqrt Q :=
    hLoNorm.trans
      (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left hCh) (Real.sqrt_nonneg _))
  refine ⟨hHiNorm', hLoNorm', hHiCore, hLoCore, ?_⟩
  let L :=
    (tensorHsInclusion (I := I) (M := M) (g := g)
      (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
        (A.firstOrderActionThirdToSecondOrder (I := I) (M := M))
  let R :=
    (A.firstOrderActionSecondToFirstOrder (I := I) (M := M)).comp
      (tensorHsInclusion (I := I) (M := M) (g := g)
        (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num))
  have hfun : (L : _ → _) = R :=
    hdense3.equalizer L.continuous R.continuous (by
      funext W
      simp only [Function.comp_apply, L, R, ccToHsLin_apply,
        ContinuousLinearMap.comp_apply]
      rw [hHiCore]
      have hin :
          tensorHsInclusion (I := I) (M := M) (g := g)
              (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num)
              (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W) =
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W := by
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

noncomputable def LowerScaleActionCoefficients.firstOrderCoefficientDifference
    {g : SmoothRiemannianMetric I M}
    (A B : LowerScaleActionCoefficients g) : LowerScaleActionCoefficients g where
  zeroOrderCoefficient := A.zeroOrderCoefficient - B.zeroOrderCoefficient
  firstOrderCoefficient := A.firstOrderCoefficient - B.firstOrderCoefficient
  secondOrderCoefficient := 0

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem LowerScaleActionCoefficients.firstOrderCoefficientDifference_firstOrderAction
    {g : SmoothRiemannianMetric I M}
    (A B : LowerScaleActionCoefficients g) (W : SmoothCcTensor g 0 2) :
    (A.firstOrderCoefficientDifference B).firstOrderAction (I := I) (M := M) W =
      A.firstOrderAction (I := I) (M := M) W -
        B.firstOrderAction (I := I) (M := M) W := by
  simp only [LowerScaleActionCoefficients.firstOrderCoefficientDifference,
    LowerScaleActionCoefficients.firstOrderAction, operatorFieldApplication_sub_left]
  module

private theorem firstOrderActionThirdToSecondOrder_apply_ccTensorToHs
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A : LowerScaleActionCoefficients g)
    (W : SmoothCcTensor g 0 2) :
    A.firstOrderActionThirdToSecondOrder (I := I) (M := M)
        (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W) =
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (A.firstOrderAction (I := I) (M := M) W) := by
  obtain ⟨Ca, _, haction⟩ :=
    exists_lowerScaleFirstOrderAction_thirdToSecondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨Cs, _, hspec⟩ :=
    exists_firstOrderAction_thirdToSecondOrder_spectralSobolev_bound (I := I) (M := M) g
  let J : ℝ :=
    covariantJetNormSq (I := I) (M := M) g 2 A.zeroOrderCoefficient +
      covariantJetNormSq (I := I) (M := M) g 2 A.firstOrderCoefficient
  let B : ℝ := Real.sqrt J
  let Q : ℝ := (Ca * B) ^ 2
  have hJ : 0 ≤ J := by
    exact add_nonneg
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = J := by
    simpa only [B] using Real.sq_sqrt hJ
  have hQ : 0 ≤ Q := sq_nonneg _
  have hact : ∀ V : SmoothCcTensor g 0 2,
      covariantJetNormSq (I := I) (M := M) g 2
          (A.firstOrderAction (I := I) (M := M) V) ≤
        Q * covariantJetNormSq (I := I) (M := M) g 3 V := by
    intro V
    let D : ℝ :=
      Real.sqrt (covariantJetNormSq (I := I) (M := M) g 3 V)
    have hV : 0 ≤ covariantJetNormSq (I := I) (M := M) g 3 V :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hD : 0 ≤ D := Real.sqrt_nonneg _
    have hDsq :
        D ^ 2 = covariantJetNormSq (I := I) (M := M) g 3 V := by
      simpa only [D] using Real.sq_sqrt hV
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (A.firstOrderAction (I := I) (M := M) V) ≤
          (Ca * B * D) ^ 2 := by
        apply haction A V B D hB hD
        · rw [hBsq]
        · rw [hDsq]
      _ = Q * covariantJetNormSq (I := I) (M := M) g 3 V := by
        rw [show (Ca * B * D) ^ 2 = (Ca * B) ^ 2 * D ^ 2 by ring,
          hDsq]
  have hdense3 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  change
    ((firstOrderActionCore (I := I) (M := M) g A (2 : ℝ)).extendOfNorm
        (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)))
        ((ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) W) =
      (firstOrderActionCore (I := I) (M := M) g A (2 : ℝ)) W
  apply LinearMap.extendOfNorm_eq hdense3
  exact ⟨Cs * Real.sqrt Q, hspec A Q hQ hact⟩

theorem firstOrderActionSecondToFirstOrder_apply_ccTensorToHs
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A : LowerScaleActionCoefficients g)
    (W : SmoothCcTensor g 0 2) :
    A.firstOrderActionSecondToFirstOrder (I := I) (M := M)
        (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W) =
      ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
        (A.firstOrderAction (I := I) (M := M) W) := by
  obtain ⟨Ca, _, haction⟩ :=
    exists_lowerScaleFirstOrderAction_secondToFirstOrder_bound (I := I) (M := M) hDim g
  obtain ⟨Cs, _, hspec⟩ :=
    exists_firstOrderAction_secondToFirstOrder_spectralSobolev_bound (I := I) (M := M) g
  let J : ℝ :=
    covariantJetNormSq (I := I) (M := M) g 2 A.zeroOrderCoefficient +
      covariantJetNormSq (I := I) (M := M) g 2 A.firstOrderCoefficient
  let B : ℝ := Real.sqrt J
  let Q : ℝ := (Ca * B) ^ 2
  have hJ : 0 ≤ J := by
    exact add_nonneg
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = J := by
    simpa only [B] using Real.sq_sqrt hJ
  have hQ : 0 ≤ Q := sq_nonneg _
  have hact : ∀ V : SmoothCcTensor g 0 2,
      covariantJetNormSq (I := I) (M := M) g 1
          (A.firstOrderAction (I := I) (M := M) V) ≤
        Q * covariantJetNormSq (I := I) (M := M) g 2 V := by
    intro V
    let D : ℝ :=
      Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 V)
    have hV : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 V :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hD : 0 ≤ D := Real.sqrt_nonneg _
    have hDsq :
        D ^ 2 = covariantJetNormSq (I := I) (M := M) g 2 V := by
      simpa only [D] using Real.sq_sqrt hV
    calc
      covariantJetNormSq (I := I) (M := M) g 1
          (A.firstOrderAction (I := I) (M := M) V) ≤
          (Ca * B * D) ^ 2 := by
        apply haction A V B D hB hD
        · rw [hBsq]
        · rw [hDsq]
      _ = Q * covariantJetNormSq (I := I) (M := M) g 2 V := by
        rw [show (Ca * B * D) ^ 2 = (Ca * B) ^ 2 * D ^ 2 by ring,
          hDsq]
  have hdense2 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  change
    ((firstOrderActionCore (I := I) (M := M) g A (1 : ℝ)).extendOfNorm
        (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)))
        ((ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) W) =
      (firstOrderActionCore (I := I) (M := M) g A (1 : ℝ)) W
  apply LinearMap.extendOfNorm_eq hdense2
  exact ⟨Cs * Real.sqrt Q, hspec A Q hQ hact⟩

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem covariantJetNormSq_iteratedCovGrad_one_le
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (W : SmoothCcTensor g 0 s) :
    covariantJetNormSq (I := I) (M := M) g 1
        (iteratedCovGrad (I := I) g 0 s 1 W) ≤
      covariantJetNormSq (I := I) (M := M) g 2 W := by
  have h0 := iteratedCovGrad_comp_norm (I := I) (M := M) g s 1 0 W
  have h1 := iteratedCovGrad_comp_norm (I := I) (M := M) g s 1 1 W
  unfold covariantJetNormSq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h0 h1 ⊢
  rw [h0, h1]
  nlinarith [sq_nonneg ‖W‖]

theorem exists_firstOrderActionSecondToFirstOrder_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A B : LowerScaleActionCoefficients g) (R0 R1 : ℝ),
        0 ≤ R0 → 0 ≤ R1 →
        covariantJetNormSq (I := I) (M := M) g 1 (A.zeroOrderCoefficient - B.zeroOrderCoefficient) ≤ R0 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (A.firstOrderCoefficient - B.firstOrderCoefficient) ≤ R1 ^ 2 →
        ‖A.firstOrderActionSecondToFirstOrder (I := I) (M := M) -
            B.firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤ C * (R0 + R1) := by
  obtain ⟨C0, hC0, happ0⟩ :=
    operator_field_composition_h1_h2_to_h1_bound (I := I) (M := M) hDim g 0 2 2
  obtain ⟨C1, hC1, happ1⟩ :=
    operator_field_composition_h2_h1_to_h1_bound (I := I) (M := M) hDim g 0 3 2
  obtain ⟨Cs, hCs, hspec⟩ :=
    exists_firstOrderAction_secondToFirstOrder_spectralSobolev_bound (I := I) (M := M) g
  let Ca : ℝ := 2 * (C0 + C1)
  let C : ℝ := Cs * Ca
  have hCa : 0 ≤ Ca :=
    mul_nonneg (by norm_num) (add_nonneg hC0 hC1)
  refine ⟨C, mul_nonneg hCs hCa, ?_⟩
  intro A B R0 R1 hR0 hR1 hA0 hA1
  let D : LowerScaleActionCoefficients g := A.firstOrderCoefficientDifference B
  let R : ℝ := R0 + R1
  let Q : ℝ := (Ca * R) ^ 2
  have hR : 0 ≤ R := add_nonneg hR0 hR1
  have hQ : 0 ≤ Q := sq_nonneg _
  have hD0 :
      covariantJetNormSq (I := I) (M := M) g 1 D.zeroOrderCoefficient ≤ R0 ^ 2 := by
    simpa only [D, LowerScaleActionCoefficients.firstOrderCoefficientDifference] using hA0
  have hD1 :
      covariantJetNormSq (I := I) (M := M) g 2 D.firstOrderCoefficient ≤ R1 ^ 2 := by
    simpa only [D, LowerScaleActionCoefficients.firstOrderCoefficientDifference] using hA1
  have hact : ∀ W : SmoothCcTensor g 0 2,
      covariantJetNormSq (I := I) (M := M) g 1
          (D.firstOrderAction (I := I) (M := M) W) ≤
        Q * covariantJetNormSq (I := I) (M := M) g 2 W := by
    intro W
    let S : ℝ :=
      Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 W)
    let Y0 : SmoothCcTensor g 0 2 :=
      operatorFieldApply (I := I) (M := M) g 2 2 D.zeroOrderCoefficient W
    let Y1 : SmoothCcTensor g 0 2 :=
      operatorFieldApply (I := I) (M := M) g 3 2 D.firstOrderCoefficient
        (iteratedCovGrad (I := I) g 0 2 1 W)
    have hW : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 W :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hS : 0 ≤ S := Real.sqrt_nonneg _
    have hSsq :
        S ^ 2 = covariantJetNormSq (I := I) (M := M) g 2 W := by
      simpa only [S] using Real.sq_sqrt hW
    have hGW :
        covariantJetNormSq (I := I) (M := M) g 1
            (iteratedCovGrad (I := I) g 0 2 1 W) ≤ S ^ 2 := by
      rw [hSsq]
      exact covariantJetNormSq_iteratedCovGrad_one_le (I := I) (M := M) g W
    have hY0 :
        ‖(⟨Y0⟩ : SmoothCcTensorH1 g 0 2)‖ ≤
          C0 * R0 * S := by
      simpa only [Y0, operatorFieldComposition_zero_eq_operatorFieldApply, covariantJetNormSq,
        Nat.reduceAdd] using
        happ0 D.zeroOrderCoefficient W R0 S hR0 hS
          (by simpa only [covariantJetNormSq, Nat.reduceAdd] using hD0)
          (by
            rw [hSsq])
    have hY1 :
        ‖(⟨Y1⟩ : SmoothCcTensorH1 g 0 2)‖ ≤
          C1 * R1 * S := by
      simpa only [Y1, operatorFieldComposition_zero_eq_operatorFieldApply, covariantJetNormSq,
        Nat.reduceAdd] using
        happ1 D.firstOrderCoefficient
          (iteratedCovGrad (I := I) g 0 2 1 W)
          R1 S hR1 hS
          (by simpa only [covariantJetNormSq, Nat.reduceAdd] using hD1)
          (by simpa only [covariantJetNormSq, Nat.reduceAdd] using hGW)
    have hsum :
        ‖(⟨Y0 + Y1⟩ : SmoothCcTensorH1 g 0 2)‖ ≤
          Ca * R * S := by
      calc
        ‖(⟨Y0 + Y1⟩ : SmoothCcTensorH1 g 0 2)‖ ≤
            ‖(⟨Y0⟩ : SmoothCcTensorH1 g 0 2)‖ +
              ‖(⟨Y1⟩ : SmoothCcTensorH1 g 0 2)‖ := norm_add_le _ _
        _ ≤ C0 * R0 * S + C1 * R1 * S := add_le_add hY0 hY1
        _ ≤ Ca * R * S := by
          simp only [Ca, R]
          nlinarith [mul_nonneg hC0 hR0, mul_nonneg hC1 hR1,
            mul_nonneg hC0 hR1, mul_nonneg hC1 hR0]
    have hsq := pow_le_pow_left₀
      (norm_nonneg (⟨Y0 + Y1⟩ : SmoothCcTensorH1 g 0 2))
      hsum 2
    rw [smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M) g 0 2 (Y0 + Y1)] at hsq
    have hjet :
        covariantJetNormSq (I := I) (M := M) g 1 (Y0 + Y1) ≤
          (Ca * R * S) ^ 2 := by
      simpa only [covariantJetNormSq, Finset.sum_range_succ,
        Finset.sum_range_zero, zero_add, Nat.reduceAdd,
        iteratedCovGrad_zero, iteratedCovGrad_succ] using hsq
    change covariantJetNormSq (I := I) (M := M) g 1 (Y0 + Y1) ≤ _
    calc
      covariantJetNormSq (I := I) (M := M) g 1 (Y0 + Y1) ≤
          (Ca * R * S) ^ 2 := hjet
      _ = Q * covariantJetNormSq (I := I) (M := M) g 2 W := by
        rw [show (Ca * R * S) ^ 2 = (Ca * R) ^ 2 * S ^ 2 by ring,
          hSsq]
  have hdense2 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hDlo :
      ‖D.firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤
        Cs * Real.sqrt Q := by
    unfold LowerScaleActionCoefficients.firstOrderActionSecondToFirstOrder
    exact LinearMap.opNorm_extendOfNorm_le
      hdense2 (mul_nonneg hCs (Real.sqrt_nonneg _))
        (hspec D Q hQ hact)
  have hsqrtQ : Real.sqrt Q = Ca * R := by
    rw [show Q = (Ca * R) ^ 2 by rfl, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (mul_nonneg hCa hR)]
  have hbound :
      ‖D.firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤ C * (R0 + R1) := by
    calc
      ‖D.firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤
          Cs * Real.sqrt Q := hDlo
      _ = C * (R0 + R1) := by
        rw [hsqrtQ]
        simp only [C, R]
        ring
  have hLo :
      D.firstOrderActionSecondToFirstOrder (I := I) (M := M) =
        A.firstOrderActionSecondToFirstOrder (I := I) (M := M) -
          B.firstOrderActionSecondToFirstOrder (I := I) (M := M) := by
    let L := D.firstOrderActionSecondToFirstOrder (I := I) (M := M)
    let P := A.firstOrderActionSecondToFirstOrder (I := I) (M := M) -
      B.firstOrderActionSecondToFirstOrder (I := I) (M := M)
    have hfun : (L : _ → _) = P :=
      hdense2.equalizer L.continuous P.continuous (by
        funext W
        simp only [Function.comp_apply, L, P, ccToHsLin_apply,
          sub_apply]
        rw [firstOrderActionSecondToFirstOrder_apply_ccTensorToHs (I := I) (M := M) hDim g D W,
          firstOrderActionSecondToFirstOrder_apply_ccTensorToHs (I := I) (M := M) hDim g A W,
          firstOrderActionSecondToFirstOrder_apply_ccTensorToHs (I := I) (M := M) hDim g B W,
          LowerScaleActionCoefficients.firstOrderCoefficientDifference_firstOrderAction (I := I) (M := M) A B W]
        simpa only [ccToHsLin_apply] using
          map_sub (ccToHsLin (I := I) (M := M) g 2 (1 : ℝ))
            (A.firstOrderAction (I := I) (M := M) W)
            (B.firstOrderAction (I := I) (M := M) W))
    apply ContinuousLinearMap.ext
    intro W
    exact congrFun hfun W
  rwa [← hLo]

theorem exists_firstOrderAction_spectralSobolev_difference_bounds
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A B : LowerScaleActionCoefficients g) (R : ℝ), 0 ≤ R →
        covariantJetNormSq (I := I) (M := M) g 2 (A.zeroOrderCoefficient - B.zeroOrderCoefficient) +
            covariantJetNormSq (I := I) (M := M) g 2 (A.firstOrderCoefficient - B.firstOrderCoefficient) ≤ R ^ 2 →
        ‖A.firstOrderActionThirdToSecondOrder (I := I) (M := M) -
            B.firstOrderActionThirdToSecondOrder (I := I) (M := M)‖ ≤ C * R ∧
        ‖A.firstOrderActionSecondToFirstOrder (I := I) (M := M) -
            B.firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤ C * R := by
  obtain ⟨Cp, hCp, hpair⟩ := exists_firstOrderAction_spectralSobolev_extensions (I := I) (M := M) g
  obtain ⟨Ch, hCh, hhigh⟩ :=
    exists_lowerScaleFirstOrderAction_thirdToSecondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨Cl, hCl, hlow⟩ :=
    exists_lowerScaleFirstOrderAction_secondToFirstOrder_bound (I := I) (M := M) hDim g
  let Ca : ℝ := Ch + Cl
  let C : ℝ := Cp * Ca
  refine ⟨C, mul_nonneg hCp (add_nonneg hCh hCl), ?_⟩
  intro A B R hR hcoeff
  let D : LowerScaleActionCoefficients g := A.firstOrderCoefficientDifference B
  let Q : ℝ := (Ca * R) ^ 2
  have hCa : 0 ≤ Ca := add_nonneg hCh hCl
  have hQ : 0 ≤ Q := sq_nonneg _
  have hDcoeff :
      covariantJetNormSq (I := I) (M := M) g 2 D.zeroOrderCoefficient +
          covariantJetNormSq (I := I) (M := M) g 2 D.firstOrderCoefficient ≤ R ^ 2 := by
    simpa only [D, LowerScaleActionCoefficients.firstOrderCoefficientDifference] using hcoeff
  have hHiAct : ∀ W : SmoothCcTensor g 0 2,
      covariantJetNormSq (I := I) (M := M) g 2
          (D.firstOrderAction (I := I) (M := M) W) ≤
        Q * covariantJetNormSq (I := I) (M := M) g 3 W := by
    intro W
    let S : ℝ :=
      Real.sqrt (covariantJetNormSq (I := I) (M := M) g 3 W)
    have hW : 0 ≤ covariantJetNormSq (I := I) (M := M) g 3 W :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hS : 0 ≤ S := Real.sqrt_nonneg _
    have hSsq :
        S ^ 2 = covariantJetNormSq (I := I) (M := M) g 3 W := by
      simpa only [S] using Real.sq_sqrt hW
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (D.firstOrderAction (I := I) (M := M) W) ≤
          (Ch * R * S) ^ 2 :=
        hhigh D W R S hR hS hDcoeff (by rw [hSsq])
      _ ≤ (Ca * R * S) ^ 2 := by
        exact pow_le_pow_left₀
          (mul_nonneg (mul_nonneg hCh hR) hS)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_right hCl) hR) hS) 2
      _ = Q * covariantJetNormSq (I := I) (M := M) g 3 W := by
        rw [show (Ca * R * S) ^ 2 = (Ca * R) ^ 2 * S ^ 2 by ring,
          hSsq]
  have hLoAct : ∀ W : SmoothCcTensor g 0 2,
      covariantJetNormSq (I := I) (M := M) g 1
          (D.firstOrderAction (I := I) (M := M) W) ≤
        Q * covariantJetNormSq (I := I) (M := M) g 2 W := by
    intro W
    let S : ℝ :=
      Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 W)
    have hW : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 W :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hS : 0 ≤ S := Real.sqrt_nonneg _
    have hSsq :
        S ^ 2 = covariantJetNormSq (I := I) (M := M) g 2 W := by
      simpa only [S] using Real.sq_sqrt hW
    calc
      covariantJetNormSq (I := I) (M := M) g 1
          (D.firstOrderAction (I := I) (M := M) W) ≤
          (Cl * R * S) ^ 2 :=
        hlow D W R S hR hS hDcoeff (by rw [hSsq])
      _ ≤ (Ca * R * S) ^ 2 := by
        exact pow_le_pow_left₀
          (mul_nonneg (mul_nonneg hCl hR) hS)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_left hCh) hR) hS) 2
      _ = Q * covariantJetNormSq (I := I) (M := M) g 2 W := by
        rw [show (Ca * R * S) ^ 2 = (Ca * R) ^ 2 * S ^ 2 by ring,
          hSsq]
  obtain ⟨hDhi, hDlo, hDhiCore, hDloCore, _⟩ :=
    hpair D Q hQ hHiAct hLoAct
  have hsqrtQ : Real.sqrt Q = Ca * R := by
    rw [show Q = (Ca * R) ^ 2 by rfl, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (mul_nonneg hCa hR)]
  have hDhi' :
      ‖D.firstOrderActionThirdToSecondOrder (I := I) (M := M)‖ ≤ C * R := by
    calc
      ‖D.firstOrderActionThirdToSecondOrder (I := I) (M := M)‖ ≤ Cp * Real.sqrt Q := hDhi
      _ = C * R := by rw [hsqrtQ]; simp only [C]; ring
  have hDlo' :
      ‖D.firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤ C * R := by
    calc
      ‖D.firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤ Cp * Real.sqrt Q := hDlo
      _ = C * R := by rw [hsqrtQ]; simp only [C]; ring
  have hdense3 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hdense2 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hHi :
      D.firstOrderActionThirdToSecondOrder (I := I) (M := M) =
        A.firstOrderActionThirdToSecondOrder (I := I) (M := M) -
          B.firstOrderActionThirdToSecondOrder (I := I) (M := M) := by
    let L := D.firstOrderActionThirdToSecondOrder (I := I) (M := M)
    let P := A.firstOrderActionThirdToSecondOrder (I := I) (M := M) -
      B.firstOrderActionThirdToSecondOrder (I := I) (M := M)
    have hfun : (L : _ → _) = P :=
      hdense3.equalizer L.continuous P.continuous (by
        funext W
        simp only [Function.comp_apply, L, P, ccToHsLin_apply,
          sub_apply]
        rw [hDhiCore,
          firstOrderActionThirdToSecondOrder_apply_ccTensorToHs (I := I) (M := M) hDim g A W,
          firstOrderActionThirdToSecondOrder_apply_ccTensorToHs (I := I) (M := M) hDim g B W,
          LowerScaleActionCoefficients.firstOrderCoefficientDifference_firstOrderAction (I := I) (M := M) A B W]
        simpa only [ccToHsLin_apply] using
          map_sub (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ))
            (A.firstOrderAction (I := I) (M := M) W)
            (B.firstOrderAction (I := I) (M := M) W))
    apply ContinuousLinearMap.ext
    intro W
    exact congrFun hfun W
  have hLo :
      D.firstOrderActionSecondToFirstOrder (I := I) (M := M) =
        A.firstOrderActionSecondToFirstOrder (I := I) (M := M) -
          B.firstOrderActionSecondToFirstOrder (I := I) (M := M) := by
    let L := D.firstOrderActionSecondToFirstOrder (I := I) (M := M)
    let P := A.firstOrderActionSecondToFirstOrder (I := I) (M := M) -
      B.firstOrderActionSecondToFirstOrder (I := I) (M := M)
    have hfun : (L : _ → _) = P :=
      hdense2.equalizer L.continuous P.continuous (by
        funext W
        simp only [Function.comp_apply, L, P, ccToHsLin_apply,
          sub_apply]
        rw [hDloCore,
          firstOrderActionSecondToFirstOrder_apply_ccTensorToHs (I := I) (M := M) hDim g A W,
          firstOrderActionSecondToFirstOrder_apply_ccTensorToHs (I := I) (M := M) hDim g B W,
          LowerScaleActionCoefficients.firstOrderCoefficientDifference_firstOrderAction (I := I) (M := M) A B W]
        simpa only [ccToHsLin_apply] using
          map_sub (ccToHsLin (I := I) (M := M) g 2 (1 : ℝ))
            (A.firstOrderAction (I := I) (M := M) W)
            (B.firstOrderAction (I := I) (M := M) W))
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
