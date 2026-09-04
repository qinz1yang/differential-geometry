import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Action.LowerScaleSobolevExtensions

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

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private theorem jetNN
    (g : SmoothRiemannianMetric I M) {r s m : ℕ}
    (S : SmoothCcTensor g r s) :
    0 ≤ covariantJetNormSq (I := I) (M := M) g m S :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem firstOrderAction_jet_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A : LowerScaleActionCoefficients g) :
    ∃ Q : ℝ, 0 ≤ Q ∧
      (∀ W : SmoothCcTensor g 0 2,
        covariantJetNormSq (I := I) (M := M) g 2
            (A.firstOrderAction (I := I) (M := M) W) ≤
          Q * covariantJetNormSq (I := I) (M := M) g 3 W) ∧
      (∀ W : SmoothCcTensor g 0 2,
        covariantJetNormSq (I := I) (M := M) g 1
            (A.firstOrderAction (I := I) (M := M) W) ≤
          Q * covariantJetNormSq (I := I) (M := M) g 2 W) := by
  obtain ⟨Ch, hCh, hhigh⟩ :=
    exists_lowerScaleFirstOrderAction_thirdToSecondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨Cl, hCl, hlow⟩ :=
    exists_lowerScaleFirstOrderAction_secondToFirstOrder_bound (I := I) (M := M) hDim g
  let J : ℝ :=
    covariantJetNormSq (I := I) (M := M) g 2 A.zeroOrderCoefficient +
      covariantJetNormSq (I := I) (M := M) g 2 A.firstOrderCoefficient
  let B : ℝ := Real.sqrt J
  let C : ℝ := Ch + Cl
  let Q : ℝ := (C * B) ^ 2
  have hJ : 0 ≤ J := by
    exact add_nonneg
      (jetNN (I := I) (M := M) g A.zeroOrderCoefficient)
      (jetNN (I := I) (M := M) g A.firstOrderCoefficient)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = J := by
    simpa only [B] using Real.sq_sqrt hJ
  have hC : 0 ≤ C := add_nonneg hCh hCl
  have hQ : 0 ≤ Q := sq_nonneg _
  have hcoeff :
      covariantJetNormSq (I := I) (M := M) g 2 A.zeroOrderCoefficient +
          covariantJetNormSq (I := I) (M := M) g 2 A.firstOrderCoefficient ≤ B ^ 2 := by
    rw [hBsq]
  have hHi : ∀ W : SmoothCcTensor g 0 2,
      covariantJetNormSq (I := I) (M := M) g 2
          (A.firstOrderAction (I := I) (M := M) W) ≤
        Q * covariantJetNormSq (I := I) (M := M) g 3 W := by
    intro W
    let D : ℝ :=
      Real.sqrt (covariantJetNormSq (I := I) (M := M) g 3 W)
    have hW : 0 ≤ covariantJetNormSq (I := I) (M := M) g 3 W :=
      jetNN (I := I) (M := M) g W
    have hD : 0 ≤ D := Real.sqrt_nonneg _
    have hDsq :
        D ^ 2 = covariantJetNormSq (I := I) (M := M) g 3 W := by
      simpa only [D] using Real.sq_sqrt hW
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (A.firstOrderAction (I := I) (M := M) W) ≤
        (Ch * B * D) ^ 2 :=
          hhigh A W B D hB hD hcoeff (by rw [hDsq])
      _ ≤ (C * B * D) ^ 2 := by
        exact pow_le_pow_left₀
          (mul_nonneg (mul_nonneg hCh hB) hD)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_right hCl) hB) hD) 2
      _ = Q * covariantJetNormSq (I := I) (M := M) g 3 W := by
        rw [show (C * B * D) ^ 2 = (C * B) ^ 2 * D ^ 2 by ring,
          hDsq]
  have hLo : ∀ W : SmoothCcTensor g 0 2,
      covariantJetNormSq (I := I) (M := M) g 1
          (A.firstOrderAction (I := I) (M := M) W) ≤
        Q * covariantJetNormSq (I := I) (M := M) g 2 W := by
    intro W
    let D : ℝ :=
      Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 W)
    have hW : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 W :=
      jetNN (I := I) (M := M) g W
    have hD : 0 ≤ D := Real.sqrt_nonneg _
    have hDsq :
        D ^ 2 = covariantJetNormSq (I := I) (M := M) g 2 W := by
      simpa only [D] using Real.sq_sqrt hW
    calc
      covariantJetNormSq (I := I) (M := M) g 1
          (A.firstOrderAction (I := I) (M := M) W) ≤
        (Cl * B * D) ^ 2 :=
          hlow A W B D hB hD hcoeff (by rw [hDsq])
      _ ≤ (C * B * D) ^ 2 := by
        exact pow_le_pow_left₀
          (mul_nonneg (mul_nonneg hCl hB) hD)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_left hCh) hB) hD) 2
      _ = Q * covariantJetNormSq (I := I) (M := M) g 2 W := by
        rw [show (C * B * D) ^ 2 = (C * B) ^ 2 * D ^ 2 by ring,
          hDsq]
  exact ⟨Q, hQ, hHi, hLo⟩

theorem first_order_action_sobolev_extensions_commute
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A : LowerScaleActionCoefficients g) :
    (tensorHsInclusion (I := I) (M := M) (g := g)
        (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
          (A.firstOrderActionThirdToSecondOrder (I := I) (M := M)) =
      (A.firstOrderActionSecondToFirstOrder (I := I) (M := M)).comp
        (tensorHsInclusion (I := I) (M := M) (g := g)
          (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num)) := by
  obtain ⟨_, _, hpair⟩ := exists_firstOrderAction_spectralSobolev_extensions (I := I) (M := M) g
  obtain ⟨Q, hQ, hHi, hLo⟩ := firstOrderAction_jet_bound (I := I) (M := M) hDim g A
  exact (hpair A Q hQ hHi hLo).2.2.2.2

theorem firstOrderActionThirdToSecondOrder_apply
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A : LowerScaleActionCoefficients g)
    (W : SmoothCcTensor g 0 2) :
    A.firstOrderActionThirdToSecondOrder (I := I) (M := M)
        (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W) =
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (A.firstOrderAction (I := I) (M := M) W) := by
  obtain ⟨_, _, hpair⟩ := exists_firstOrderAction_spectralSobolev_extensions (I := I) (M := M) g
  obtain ⟨Q, hQ, hHi, hLo⟩ := firstOrderAction_jet_bound (I := I) (M := M) hDim g A
  exact (hpair A Q hQ hHi hLo).2.2.1 W

theorem firstOrderActionSecondToFirstOrder_apply
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A : LowerScaleActionCoefficients g)
    (W : SmoothCcTensor g 0 2) :
    A.firstOrderActionSecondToFirstOrder (I := I) (M := M)
        (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W) =
      ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
        (A.firstOrderAction (I := I) (M := M) W) := by
  obtain ⟨_, _, hpair⟩ := exists_firstOrderAction_spectralSobolev_extensions (I := I) (M := M) g
  obtain ⟨Q, hQ, hHi, hLo⟩ := firstOrderAction_jet_bound (I := I) (M := M) hDim g A
  exact (hpair A Q hQ hHi hLo).2.2.2.1 W

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem firstOrderAction_add_core
    (g : SmoothRiemannianMetric I M) (A B F : LowerScaleActionCoefficients g)
    (h0 : F.zeroOrderCoefficient = A.zeroOrderCoefficient + B.zeroOrderCoefficient) (h1 : F.firstOrderCoefficient = A.firstOrderCoefficient + B.firstOrderCoefficient)
    (W : SmoothCcTensor g 0 2) :
    F.firstOrderAction (I := I) (M := M) W =
      A.firstOrderAction (I := I) (M := M) W + B.firstOrderAction (I := I) (M := M) W := by
  simp only [LowerScaleActionCoefficients.firstOrderAction, h0, h1, operatorFieldApplication_add_left]
  abel

theorem firstOrderActionThirdToSecondOrder_add
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A B F : LowerScaleActionCoefficients g)
    (h0 : F.zeroOrderCoefficient = A.zeroOrderCoefficient + B.zeroOrderCoefficient) (h1 : F.firstOrderCoefficient = A.firstOrderCoefficient + B.firstOrderCoefficient) :
    F.firstOrderActionThirdToSecondOrder (I := I) (M := M) =
      A.firstOrderActionThirdToSecondOrder (I := I) (M := M) + B.firstOrderActionThirdToSecondOrder (I := I) (M := M) := by
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by norm_num)
  apply ContinuousLinearMap.ext
  intro x
  refine hdense.induction_on x
    (isClosed_eq (F.firstOrderActionThirdToSecondOrder (I := I) (M := M)).continuous
      (A.firstOrderActionThirdToSecondOrder (I := I) (M := M) +
        B.firstOrderActionThirdToSecondOrder (I := I) (M := M)).continuous) ?_
  intro W
  rw [ccToHsLin_apply, add_apply,
    firstOrderActionThirdToSecondOrder_apply (I := I) (M := M) hDim g F W,
    firstOrderActionThirdToSecondOrder_apply (I := I) (M := M) hDim g A W,
    firstOrderActionThirdToSecondOrder_apply (I := I) (M := M) hDim g B W,
    firstOrderAction_add_core (I := I) (M := M) g A B F h0 h1 W,
    ccTensorToHs_add]

theorem firstOrderActionSecondToFirstOrder_add
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A B F : LowerScaleActionCoefficients g)
    (h0 : F.zeroOrderCoefficient = A.zeroOrderCoefficient + B.zeroOrderCoefficient) (h1 : F.firstOrderCoefficient = A.firstOrderCoefficient + B.firstOrderCoefficient) :
    F.firstOrderActionSecondToFirstOrder (I := I) (M := M) =
      A.firstOrderActionSecondToFirstOrder (I := I) (M := M) + B.firstOrderActionSecondToFirstOrder (I := I) (M := M) := by
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by norm_num)
  apply ContinuousLinearMap.ext
  intro x
  refine hdense.induction_on x
    (isClosed_eq (F.firstOrderActionSecondToFirstOrder (I := I) (M := M)).continuous
      (A.firstOrderActionSecondToFirstOrder (I := I) (M := M) +
        B.firstOrderActionSecondToFirstOrder (I := I) (M := M)).continuous) ?_
  intro W
  rw [ccToHsLin_apply, add_apply,
    firstOrderActionSecondToFirstOrder_apply (I := I) (M := M) hDim g F W,
    firstOrderActionSecondToFirstOrder_apply (I := I) (M := M) hDim g A W,
    firstOrderActionSecondToFirstOrder_apply (I := I) (M := M) hDim g B W,
    firstOrderAction_add_core (I := I) (M := M) g A B F h0 h1 W,
    ccTensorToHs_add]

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
