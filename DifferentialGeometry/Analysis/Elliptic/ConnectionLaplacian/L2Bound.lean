import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapSecondOrderGardingSobolevCurv
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.CurvatureDefect
import DifferentialGeometry.Analysis.Sobolev.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge
import DifferentialGeometry.Analysis.Sobolev.RiemannianFiberNormSq.PointwiseToL2Packaging
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.Tensor3rdCurvFiberNormBound
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature


noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

section NormedL2Bounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private lemma sum_three_sq_le_sq_sum
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a ^ 2 + b ^ 2 + c ^ 2 ≤ (a + b + c) ^ 2 := by
  nlinarith [mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]

private lemma scale_sum_three_sq_le
    {C a b c : ℝ}
    (h : a ^ 2 + b ^ 2 + c ^ 2 ≤ (a + b + c) ^ 2) :
    C ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≤ (C * (a + b + c)) ^ 2 := by
  calc
    C ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≤ C ^ 2 * (a + b + c) ^ 2 :=
      mul_le_mul_of_nonneg_left h (sq_nonneg C)
    _ = (C * (a + b + c)) ^ 2 := by ring

private lemma nonneg_le_of_sq_le_sq
    {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) :
    a ≤ b := by
  nlinarith [sq_nonneg (a - b)]


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorL2Norm_le_of_pointwise_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (Curv : SmoothCcTensor g 0 3) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x (Curv.toSection x) ≤
        C₀ ^ 2 *
          (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
              ((covGrad (I := I) (M := M) g 0 3
                (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x))) :
    tensorL2Norm (I := I) (M := M) g 0 3 Curv.toFun ≤
      C₀ * (tensorL2Norm (I := I) (M := M) g 0 2 T₀.toFun +
        tensorL2Norm (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀).toFun +
        tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
          (covGrad (I := I) (M := M) g 0 3
            (covGrad (I := I) (M := M) g 0 2 T₀)).toFun) := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  set S : SmoothCcTensor g 0 3 := covGrad (I := I) (M := M) g 0 2 T₀ with hS_def
  set Hess : SmoothCcTensor g 0 (3 + 1) :=
    covGrad (I := I) (M := M) g 0 3 (covGrad (I := I) (M := M) g 0 2 T₀) with hHess_def
  set nT : ℝ := tensorL2Norm (I := I) (M := M) g 0 2 T₀.toFun with hnT_def
  set nGrad : ℝ := tensorL2Norm (I := I) (M := M) g 0 3 S.toFun with hnGrad_def
  set nHess : ℝ := tensorL2Norm (I := I) (M := M) g 0 (3 + 1) Hess.toFun with hnHess_def
  set nCurv : ℝ := tensorL2Norm (I := I) (M := M) g 0 3 Curv.toFun with hnCurv_def
  have hnT_nn : 0 ≤ nT := tensorL2Norm_nonneg (I := I) (M := M) g 0 2 _
  have hnGrad_nn : 0 ≤ nGrad := tensorL2Norm_nonneg (I := I) (M := M) g 0 3 _
  have hnHess_nn : 0 ≤ nHess := tensorL2Norm_nonneg (I := I) (M := M) g 0 (3 + 1) _
  have hnCurv_nn : 0 ≤ nCurv := tensorL2Norm_nonneg (I := I) (M := M) g 0 3 _
  have hbridgeT : nT ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) ∂μ := by
    rw [hnT_def, hμ_def]
    have hfun : T₀.toFun = fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := 0) (s := 2) (x := x) (T₀.toSection x) := rfl
    rw [hfun]
    exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g 0 2 _
  have hbridgeGrad : nGrad ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 3 x (S.toSection x) ∂μ := by
    rw [hnGrad_def, hμ_def]
    have hfun : S.toFun = fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := 0) (s := 3) (x := x) (S.toSection x) := rfl
    rw [hfun]
    exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g 0 3 _
  have hbridgeHess : nHess ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x (Hess.toSection x) ∂μ := by
    rw [hnHess_def, hμ_def]
    have hfun : Hess.toFun = fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := 0) (s := 3 + 1) (x := x) (Hess.toSection x) := rfl
    rw [hfun]
    exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) _
  have hbridgeCurv : nCurv ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 3 x (Curv.toSection x) ∂μ := by
    rw [hnCurv_def, hμ_def]
    have hfun : Curv.toFun = fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := 0) (s := 3) (x := x) (Curv.toSection x) := rfl
    rw [hfun]
    exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g 0 3 _
  have hintT := integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 2 T₀
  have hintGrad := integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 3 S
  have hintHess := integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 (3 + 1) Hess
  set RHS : M → ℝ := fun x =>
    C₀ ^ 2 *
      (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) +
        riemannianFiberNormSq (I := I) (M := M) g 0 3 x (S.toSection x) +
        riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x (Hess.toSection x))
    with hRHS_def
  have hRHS_int : MeasureTheory.Integrable RHS μ := by
    rw [hRHS_def, hμ_def]
    exact ((hintT.add hintGrad).add hintHess).const_mul (C₀ ^ 2)
  have hpt' : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x (Curv.toSection x) ≤ RHS x := by
    intro x
    rw [hRHS_def, hS_def, hHess_def]
    exact hpt x
  have hcurv_nn : (0 : M → ℝ) ≤ᵐ[μ]
      (fun x => riemannianFiberNormSq (I := I) (M := M) g 0 3 x (Curv.toSection x)) :=
    Filter.Eventually.of_forall (fun x =>
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 3 x _)
  have hint_le :
      (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 3 x (Curv.toSection x) ∂μ) ≤
        ∫ x, RHS x ∂μ :=
    MeasureTheory.integral_mono_of_nonneg hcurv_nn hRHS_int
      (Filter.Eventually.of_forall hpt')
  have hRHS_integral :
      (∫ x, RHS x ∂μ) =
        C₀ ^ 2 *
          ((∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) ∂μ) +
            (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 3 x (S.toSection x) ∂μ) +
            (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
              (Hess.toSection x) ∂μ)) := by
    rw [hRHS_def]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    have hsplit12 :
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x (S.toSection x)) ∂μ) =
          (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) ∂μ) +
            (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 3 x (S.toSection x) ∂μ) :=
      MeasureTheory.integral_add hintT hintGrad
    have hsplit123 :
        (∫ x, ((riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 3 x (S.toSection x)) +
            riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x (Hess.toSection x)) ∂μ) =
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 3 x (S.toSection x)) ∂μ) +
            (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
              (Hess.toSection x) ∂μ) :=
      MeasureTheory.integral_add (hintT.add hintGrad) hintHess
    rw [hsplit123, hsplit12]
  have hsq_bound : nCurv ^ 2 ≤ C₀ ^ 2 * (nT ^ 2 + nGrad ^ 2 + nHess ^ 2) := by
    rw [hbridgeCurv, hbridgeT, hbridgeGrad, hbridgeHess]
    calc (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 3 x (Curv.toSection x) ∂μ)
        ≤ ∫ x, RHS x ∂μ := hint_le
      _ = C₀ ^ 2 *
            ((∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) ∂μ) +
              (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 3 x (S.toSection x) ∂μ) +
              (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
                (Hess.toSection x) ∂μ)) := hRHS_integral
  clear_value nT nGrad nHess nCurv
  have hy_nn : 0 ≤ C₀ * (nT + nGrad + nHess) :=
    mul_nonneg hC₀ (by linarith [hnT_nn, hnGrad_nn, hnHess_nn])
  have hfinal_sq : nCurv ^ 2 ≤ (C₀ * (nT + nGrad + nHess)) ^ 2 := by
    exact hsq_bound.trans
      (scale_sum_three_sq_le (sum_three_sq_le_sq_sum hnT_nn hnGrad_nn hnHess_nn))
  exact nonneg_le_of_sq_le_sq hy_nn hfinal_sq

end NormedL2Bounds

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩


theorem secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) ≤
        C₀ ^ 2 *
          (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
              ((covGrad (I := I) (M := M) g 0 3
                (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x))) :
    tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
        (covGrad (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀)).toFun ^ 2 ≤
      (2 + 3 * C₀ + 2 * C₀ ^ 2) *
        (tensorL2Norm (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth (I := I) g 0 2 T₀).toFun ^ 2 +
          tensorL2Norm (I := I) (M := M) g 0 2 T₀.toFun ^ 2) := by
  refine secondCovGrad_l2NormSq_le_rawConnLap_gen (I := I) (M := M) g T₀
    (covGradRoughLapCurv (I := I) (M := M) g T₀) C₀ hC₀
    (covGradRoughLap_commutator_eq (I := I) (M := M) g T₀) ?_
  exact tensorL2Norm_le_of_pointwise_fiberNormSq_bound (I := I) (M := M) g T₀
    (covGradRoughLapCurv (I := I) (M := M) g T₀) C₀ hC₀ hpt

end Elliptic
end Analysis
end DifferentialGeometry

end
