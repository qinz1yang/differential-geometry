import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalArmEnergyPairing
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.InverseMetricRaisedEndomorphismJetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBound

/-!
# Boundary Ricci--DeTurck difference energy

This file isolates the genuinely small highest-order term in the difference of two
Ricci--DeTurck equations.  The carrier metric is fixed.  If the moving metric is
`g₀ + T`, then differentiation of its inverse metric contributes one factor of
`∇T`; pairing the resulting first-order residual with `T` contributes the small
`C⁰` factor.  Consequently the principal arm is bounded by `O(δ) ‖∇T‖²`, with no
high-jet bound on the moving endpoint.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem edge_rfns_neg (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (x : M) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise
      (I := I) (M := M) g r s x (-v),
    riemannianFiberNormSq_eq_tensorInnerPointwise
      (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_neg]
  rw [← neg_one_smul ℝ
    (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
      (r := r) (s := s) (x := x) v),
    tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

/-- The differentiated inverse-metric coefficient in the boundary energy
identity is pointwise linear in the first covariant derivative of the metric
difference.  The constant depends only on the fixed carrier metric. -/
theorem edgeCoeff_rfns (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ}, δ < 1 / 2 → 0 ≤ δ →
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ T y v w) →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((edgeArmCoeff (I := I) (M := M) g₀ g₁).toSection x) ≤
            C ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
                ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x) := by
  classical
  let Φ : SmoothCcTensor g₀ 4 2 :=
    DeTurck.cometricDoubleTraceField (I := I) g₀ 2
  obtain ⟨K, hK0, hK⟩ :=
    exists_uniform_riemannianFiberNormSq_appCcRS_le
      (I := I) (M := M) g₀ 3 4 2 Φ
  obtain ⟨A, hA0, hA⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ (show (1 / 2 : ℝ) < 1 by norm_num)
  let fr : ℝ := Module.finrank ℝ E
  let B : ℝ := K * (fr ^ 2 * A 1)
  have hfr0 : 0 ≤ fr := by
    dsimp [fr]
    positivity
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg hK0 (mul_nonneg (sq_nonneg fr) (hA0 1))
  refine ⟨Real.sqrt B, Real.sqrt_nonneg _, ?_⟩
  intro g₁ T δ hδ hδ0 htie hbound x
  let Λ := gInvDiffRaisedEndoField (I := I) (M := M) g₀ g₁
  let W : SmoothCcTensor g₀ 3 4 :=
    covGrad (I := I) (M := M) g₀ 3 3
      (slotInsertEndoCc (I := I) (M := M) g₀ 2 Λ)
  have hgrid := hA g₁ T htie (le_of_lt hδ) hδ0 hbound 1 x
  have hgrid' :
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
          ((covGrad (I := I) (M := M) g₀ 1 1
            (slotInsertEndoCc (I := I) (M := M) g₀ 0 Λ)).toSection x) ≤
        A 1 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
          ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x) := by
    simpa [Λ, Finset.sum_range_succ, Finset.sum_range_one] using hgrid
  have hslot := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo
    (I := I) (M := M) g₀ 2 Λ 1 x
  have hW :
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
          (W.toSection x) ≤
        fr ^ 2 * A 1 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x) := by
    have hslot' :
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
            (W.toSection x) ≤
          fr ^ 2 *
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
              ((covGrad (I := I) (M := M) g₀ 1 1
                (slotInsertEndoCc (I := I) (M := M) g₀ 0 Λ)).toSection x) := by
      simpa [W, fr] using hslot
    calc
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x (W.toSection x)
          ≤ fr ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
                ((covGrad (I := I) (M := M) g₀ 1 1
                  (slotInsertEndoCc (I := I) (M := M) g₀ 0 Λ)).toSection x) := hslot'
      _ ≤ fr ^ 2 *
          (A 1 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x)) :=
        mul_le_mul_of_nonneg_left hgrid' (sq_nonneg fr)
      _ = fr ^ 2 * A 1 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x) := by ring
  have happ := hK W x
  rw [edgeArmCoeff, SmoothCcTensor.toSection_neg]
  change riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
      (-((appCcRS (I := I) (M := M) g₀ 3 4 2 Φ W).toSection x)) ≤ _
  rw [edge_rfns_neg (I := I) (M := M) g₀ 3 2 x]
  calc
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
        ((appCcRS (I := I) (M := M) g₀ 3 4 2 Φ W).toSection x)
        ≤ K * riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
          (W.toSection x) := happ
    _ ≤ K * (fr ^ 2 * A 1 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x)) :=
      mul_le_mul_of_nonneg_left hW hK0
    _ = B * riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
          ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x) := by
      simp only [B]
      ring
    _ = (Real.sqrt B) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
          ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x) := by
      rw [Real.sq_sqrt hB0]

private theorem edgePair_point_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {C δ : ℝ}
    (hC0 : 0 ≤ C) (hδ0 : 0 ≤ δ)
    (hT : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          ((symmS (I := I) (M := M) g₀ T).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * δ ^ 2)
    (hF : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
          ((edgeArmCoeff (I := I) (M := M) g₀ g₁).toSection x) ≤
        C ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
          ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x))
    (x : M) :
    |tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
        ((symmS (I := I) (M := M) g₀ T).toFun x)
        ((appCc (I := I) (M := M) g₀ 3 2
          (edgeArmCoeff (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 1 T)).toFun x)| ≤
      (Module.finrank ℝ E : ℝ) * C * δ *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
          ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x) := by
  classical
  let S := (symmS (I := I) (M := M) g₀ T).toSection x
  let D := (iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x
  let F := (edgeArmCoeff (I := I) (M := M) g₀ g₁).toSection x
  let U :=
    (appCc (I := I) (M := M) g₀ 3 2
      (edgeArmCoeff (I := I) (M := M) g₀ g₁)
      (iteratedCovGrad (I := I) g₀ 0 2 1 T)).toSection x
  let d : ℝ := Module.finrank ℝ E
  let q : ℝ := riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x D
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hq0 : 0 ≤ q :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 3 x D
  have hS0 :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x S ≤ d ^ 2 * δ ^ 2 := by
    simpa [S, d] using hT x
  have hU0 :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x U ≤ C ^ 2 * q ^ 2 := by
    have happ :
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x U ≤
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x F * q := by
      dsimp only [U, F, q]
      rw [appCc_toSection]
      exact riemannianFiberNormSq_comp_le_mul
        (I := I) (M := M) g₀ 3 2 x _ _
    calc
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x U
          ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x F * q := happ
      _ ≤ (C ^ 2 * q) * q :=
        mul_le_mul_of_nonneg_right (by simpa [F, q, D] using hF x) hq0
      _ = C ^ 2 * q ^ 2 := by ring
  have hcs := tensorInnerPointwise_sq_le_mul
    (I := I) (M := M) g₀ 0 2 x
      (TensorRSSpace.toModel S) (TensorRSSpace.toModel U)
  have hcs' :
      (tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
        (TensorRSSpace.toModel S) (TensorRSSpace.toModel U)) ^ 2 ≤
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x S *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x U := by
    simpa [riemannianFiberNormSq_eq_tensorInnerPointwise] using hcs
  have hprod :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x S *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x U ≤
        (d * C * δ * q) ^ 2 := by
    calc
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x S *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x U
          ≤ (d ^ 2 * δ ^ 2) * (C ^ 2 * q ^ 2) :=
        mul_le_mul hS0 hU0
          (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x U)
          (by positivity)
      _ = (d * C * δ * q) ^ 2 := by ring
  have hsq := hcs'.trans hprod
  have hrhs0 : 0 ≤ d * C * δ * q := by positivity
  change |tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
      (TensorRSSpace.toModel S) (TensorRSSpace.toModel U)| ≤ d * C * δ * q
  nlinarith [sq_abs (tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
    (TensorRSSpace.toModel S) (TensorRSSpace.toModel U)),
    abs_nonneg (tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
      (TensorRSSpace.toModel S) (TensorRSSpace.toModel U))]

/-- The first-order residual in the principal-arm integration-by-parts
identity is `O(δ) ‖∇T‖²`. -/
theorem edgeArm_resid_le (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ}, δ < 1 / 2 → 0 ≤ δ →
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ T y v w) →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ →
        symmS (I := I) (M := M) g₀ T = T →
        |tensorL2Inner (I := I) (M := M) g₀ 0 2 T.toFun
          (appCc (I := I) (M := M) g₀ 3 2
            (edgeArmCoeff (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 1 T)).toFun| ≤
          C * δ *
            ‖SmoothCcTensor.toL2
              (iteratedCovGrad (I := I) g₀ 0 2 1 T)‖ ^ 2 := by
  classical
  obtain ⟨C₀, hC₀0, hC₀⟩ := edgeCoeff_rfns (I := I) (M := M) g₀
  let C : ℝ := (Module.finrank ℝ E : ℝ) * C₀
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC0, ?_⟩
  intro g₁ T δ hδ hδ0 htie hbound hsymm
  let U : SmoothCcTensor g₀ 0 2 :=
    appCc (I := I) (M := M) g₀ 3 2
      (edgeArmCoeff (I := I) (M := M) g₀ g₁)
      (iteratedCovGrad (I := I) g₀ 0 2 1 T)
  let μ := riemannianVolumeMeasure (I := I) (M := M) g₀
  have hTpt := symmC0_rfns_le (I := I) (M := M) g₀ T hδ0 hbound
  have hFpt := hC₀ g₁ T hδ hδ0 htie hbound
  have hpt : ∀ x : M,
      |tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
        (T.toFun x) (U.toFun x)| ≤
      C * δ * riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x) := by
    intro x
    have h := edgePair_point_le (I := I) (M := M) g₀ g₁ T
      hC₀0 hδ0 hTpt hFpt x
    rw [hsymm] at h
    simpa [U, C] using h
  have hcross :=
    DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) T U
  have hsqint :=
    integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g₀ 0 3
        (iteratedCovGrad (I := I) g₀ 0 2 1 T)
  have hrhsint : Integrable
      (fun x => C * δ *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
          ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x)) μ :=
    hsqint.const_mul (C * δ)
  unfold tensorL2Inner
  calc
    |∫ x, tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
        (T.toFun x) (U.toFun x) ∂μ|
        ≤ ∫ x, |tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
          (T.toFun x) (U.toFun x)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, C * δ *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
          ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x) ∂μ := by
      exact integral_mono hcross.abs hrhsint hpt
    _ = C * δ * ∫ x,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
          ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x) ∂μ := by
      rw [integral_const_mul]
    _ = C * δ *
        ‖SmoothCcTensor.toL2
          (iteratedCovGrad (I := I) g₀ 0 2 1 T)‖ ^ 2 := by
      rw [← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g₀ 0 3
          (iteratedCovGrad (I := I) g₀ 0 2 1 T)]
      change C * δ *
        ‖iteratedCovGrad (I := I) g₀ 0 2 1 T‖ ^ 2 = _
      rw [SmoothCcTensor.norm_toL2]

/-- The entire variable-cometric principal arm is a small perturbation of
the fixed connection Laplacian in the boundary `L²` energy. -/
theorem edgeArm_energy_le [Nonempty M]
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ}, δ < 1 / 2 → 0 ≤ δ →
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ T y v w) →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ →
        symmS (I := I) (M := M) g₀ T = T →
        tensorL2Inner (I := I) (M := M) g₀ 0 2 T.toFun
            (deTurckPrincipalCometricArm
              (I := I) (M := M) g₀ g₁ T).toFun ≤
          (δ / (1 - δ) + C * δ) *
            ‖SmoothCcTensor.toL2
              (iteratedCovGrad (I := I) g₀ 0 2 1 T)‖ ^ 2 := by
  obtain ⟨C, hC0, hres⟩ := edgeArm_resid_le (I := I) (M := M) g₀
  refine ⟨C, hC0, ?_⟩
  intro g₁ T δ hδ hδ0 htie hbound hsymm
  have hslot := edgeArm_slot_le (I := I) (M := M) g₀ g₁ 0
    (ccTensorBilinSymm (I := I) g₀ T) htie (by linarith) hδ0 hbound T
  have hibp := edgeArm_ibp (I := I) (M := M) g₀ g₁ T
  have hres0 := hres g₁ T hδ hδ0 htie hbound hsymm
  have hinner :
      (⟪iteratedCovGrad (I := I) g₀ 0 2 0 T,
          appCc (I := I) (M := M) g₀ 3 2
            (edgeArmCoeff (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 1 T)⟫_ℝ : ℝ) =
        tensorL2Inner (I := I) (M := M) g₀ 0 2 T.toFun
          (appCc (I := I) (M := M) g₀ 3 2
            (edgeArmCoeff (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 1 T)).toFun := by
    simpa only [iteratedCovGrad_zero] using
      SmoothCcTensor.inner_def (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 0 T)
      (appCc (I := I) (M := M) g₀ 3 2
        (edgeArmCoeff (I := I) (M := M) g₀ g₁)
        (iteratedCovGrad (I := I) g₀ 0 2 1 T))
  rw [hinner] at hibp
  have hresle :
      tensorL2Inner (I := I) (M := M) g₀ 0 2 T.toFun
          (appCc (I := I) (M := M) g₀ 3 2
            (edgeArmCoeff (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 1 T)).toFun ≤
        C * δ *
          ‖SmoothCcTensor.toL2
            (iteratedCovGrad (I := I) g₀ 0 2 1 T)‖ ^ 2 :=
    le_trans (le_abs_self _) hres0
  simp only [oneMinusConnLapSmoothIter_zero] at hibp
  nlinarith [hslot, hresle]

/-- If the fixed-carrier `C⁰` radius is chosen so that the two principal
error coefficients total at most `1/2`, the fixed Laplacian absorbs them and
leaves half of the Dirichlet energy. -/
theorem edgePrincipal_half [Nonempty M]
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ}, δ < 1 / 2 → 0 ≤ δ →
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ T y v w) →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ →
        symmS (I := I) (M := M) g₀ T = T →
        δ / (1 - δ) + C * δ ≤ 1 / 2 →
        tensorL2Inner (I := I) (M := M) g₀ 0 2 T.toFun
          ((rawTensorConnLapSmooth (I := I) g₀ 0 2 T) +
            deTurckPrincipalCometricArm
              (I := I) (M := M) g₀ g₁ T).toFun ≤
          -(1 / 2 : ℝ) *
            ‖SmoothCcTensor.toL2
              (iteratedCovGrad (I := I) g₀ 0 2 1 T)‖ ^ 2 := by
  obtain ⟨C, hC0, harm⟩ := edgeArm_energy_le (I := I) (M := M) g₀
  refine ⟨C, hC0, ?_⟩
  intro g₁ T δ hδ hδ0 htie hbound hsymm hsmall
  have ha := harm g₁ T hδ hδ0 htie hbound hsymm
  have hgreen :=
    tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
      (I := I) (M := M) g₀ 0 2 T T
  have hsym := tensorL2Inner_symm (I := I) (M := M) g₀ 0 2
    (rawTensorConnLapSmooth (I := I) g₀ 0 2 T).toFun T.toFun
  have hlap :
      tensorL2Inner (I := I) (M := M) g₀ 0 2 T.toFun
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T).toFun =
        -‖SmoothCcTensor.toL2
          (iteratedCovGrad (I := I) g₀ 0 2 1 T)‖ ^ 2 := by
    have hgrad :
        tensorL2Inner (I := I) (M := M) g₀ 0 3
            (covGrad (I := I) (M := M) g₀ 0 2 T).toFun
            (covGrad (I := I) (M := M) g₀ 0 2 T).toFun =
          ‖SmoothCcTensor.toL2
            (covGrad (I := I) (M := M) g₀ 0 2 T)‖ ^ 2 := by
      rw [← DifferentialGeometry.Integral.L2.SmoothCcTensor.inner_def
        (I := I) (M := M)
          (covGrad (I := I) (M := M) g₀ 0 2 T)
          (covGrad (I := I) (M := M) g₀ 0 2 T)]
      rw [real_inner_self_eq_norm_sq, SmoothCcTensor.norm_toL2]
    rw [hgrad, hsym] at hgreen
    have hlap' :
        tensorL2Inner (I := I) (M := M) g₀ 0 2 T.toFun
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 T).toFun =
          -‖SmoothCcTensor.toL2
            (covGrad (I := I) (M := M) g₀ 0 2 T)‖ ^ 2 := by
      linarith
    simpa only [iteratedCovGrad_succ, iteratedCovGrad_zero, Nat.add_zero] using hlap'
  have hadd :
      tensorL2Inner (I := I) (M := M) g₀ 0 2 T.toFun
          ((rawTensorConnLapSmooth (I := I) g₀ 0 2 T) +
            deTurckPrincipalCometricArm
              (I := I) (M := M) g₀ g₁ T).toFun =
        tensorL2Inner (I := I) (M := M) g₀ 0 2 T.toFun
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 T).toFun +
          tensorL2Inner (I := I) (M := M) g₀ 0 2 T.toFun
            (deTurckPrincipalCometricArm
              (I := I) (M := M) g₀ g₁ T).toFun := by
    rw [SmoothCcTensor.toFun_add]
    exact tensorL2Inner_add_right (I := I) (M := M) g₀ 0 2 T.toFun
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 T).toFun
      (deTurckPrincipalCometricArm
        (I := I) (M := M) g₀ g₁ T).toFun
      (DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
        (I := I) (M := M) T
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T))
      (DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
        (I := I) (M := M) T
          (deTurckPrincipalCometricArm
            (I := I) (M := M) g₀ g₁ T))
  rw [hadd, hlap]
  have hnorm0 : 0 ≤
      ‖SmoothCcTensor.toL2
        (iteratedCovGrad (I := I) g₀ 0 2 1 T)‖ ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hsmall hnorm0]

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
