import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciTopOrderCoefficientBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.CoefficientDeviationSecondOrderBounds

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Topology DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem secondOrderCoefficient_fibre_bound_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ ρ K : ℝ, 0 < ρ ∧ 0 ≤ K ∧
      ∀ {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        {R : ℝ}, 0 ≤ R → R ≤ ρ →
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T : SmoothCcTensor g 0 2)
          (hT : ∀ (x : M) (u v : TangentSpace I x),
            ccTensorBilin (I := I) g T x u v =
              ccTensorBilin (I := I) g T x v u)
          (hδ : gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g T) δ)
            (hδZ : gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g
                (0 : SmoothCcTensor g 0 2)) δ),
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
          ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g 4 2 x
                ((lowerScaleActionCoefficients (I := I) (M := M) g gBase T
                  (lt_of_le_of_lt hδ_le (by norm_num)) hδ hδZ).secondOrderCoefficient.toSection x) ≤
              (K * (δ / (1 - δ) ^ 2 + R)) ^ 2 := by
  classical
  obtain ⟨Ktop, hKtop, htop⟩ :=
    RicciDeTurckLowOrder.exists_topOrderKernel_path_riemannianFiberNormSq_le (I := I) (M := M)
  obtain ⟨ρ, Cdev, hρ, hCdev, hdev⟩ :=
    phi_dev_h2_uniform (I := I) (M := M) hDim gBase hΛ
  let K : ℝ := 2 * (Ktop + Cdev)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨ρ, K, hρ, hK, ?_⟩
  intro δ hδ_le hδ0 R hR0 hRρ g hEq hjet T hT hδ hδZ hT2 x
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  let Φ := rhsDecompositionTop (I := I) (M := M) g T hδ hδZ
  let Ψ := RicciDeTurckLowOrder.ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M) g T hδ hδZ
  let C := deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      metricPerturbationPathDomain (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hΦ := rhsDecompositionTop_joint (I := I) (M := M) g T hδ_lt hδ hδZ
  have hΨ := RicciDeTurckLowOrder.selfTop_joint (I := I) (M := M) g T hδ hδZ
  have hC := covariantJetJoint_const (I := I) (M := M) g (δ := δ) (δ' := δ) C
  have hKern := covariantJetJoint_sub (I := I) (M := M) g _ _
    (covariantJetJoint_add (I := I) (M := M) g _ _ hΦ hΨ) hC
  rw [RicciDeTurckLowOrder.secondOrderCoefficient_eq (I := I) (M := M) g gBase T hδ_lt hδ hδZ]
  apply path_add_sub_cap (I := I) (M := M) g 4 hSI Φ Ψ C
    hΦ hΨ hKern x (K * (δ / (1 - δ) ^ 2 + R))
    (mul_nonneg hK (add_nonneg (div_nonneg hδ0 (sq_nonneg _)) hR0))
  intro s hs
  let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
  let Dtop : SmoothCcTensor g 4 2 :=
    lieDecomposition2 (I := I) (M := M) g T hδ hδZ s +
      (-2 * s : ℝ) • RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T
  let Ddev : SmoothCcTensor g 4 2 :=
    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gm -
      deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
  let r : ℝ := δ / (1 - δ) ^ 2
  let A : ℝ := Ktop * r
  let B : ℝ := Cdev * R
  let S : ℝ := (Ktop + Cdev) * (r + R)
  have hr : 0 ≤ r := div_nonneg hδ0 (sq_nonneg _)
  have hA : 0 ≤ A := mul_nonneg hKtop hr
  have hB : 0 ≤ B := mul_nonneg hCdev hR0
  have hS : 0 ≤ S := mul_nonneg (add_nonneg hKtop hCdev) (add_nonneg hr hR0)
  have htopS : riemannianFiberNormSq (I := I) (M := M) g 4 2 x
      (Dtop.toSection x) ≤ A ^ 2 := by
    simpa only [Dtop, gm, A, r] using
      htop g T hT hδ_le hδ0 hδ hδZ hs x
  have hzero : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
      (0 : SmoothCcTensor g 0 2)‖ ≤ R := by
    rw [show (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
      ccTensorToHs_smul, zero_smul, norm_zero]
    exact hR0
  have hdevS : riemannianFiberNormSq (I := I) (M := M) g 4 2 x
      (Ddev.toSection x) ≤ B ^ 2 := by
    simpa only [Ddev, gm, B] using
      (hdev g hEq hjet T (0 : SmoothCcTensor g 0 2)
        hδ_lt hδ hδ_lt hδZ hR0 hRρ hT2 hzero hs.1 hs.2).1 x
  have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g 4 2 x
    (Dtop.toSection x) (Ddev.toSection x)
  have hsplit : Φ s + Ψ s - C = Dtop + Ddev := by
    rw [RicciDeTurckLowOrder.topKernel_eq (I := I) (M := M) g T hδ hδZ s]
    dsimp only [Dtop, Ddev, gm]
    module
  rw [hsplit]
  have hAS : A + B ≤ S := by
    dsimp only [A, B, S]
    nlinarith [mul_nonneg hKtop hR0, mul_nonneg hCdev hr]
  have hsq : (A + B) ^ 2 ≤ S ^ 2 :=
    pow_le_pow_left₀ (add_nonneg hA hB) hAS 2
  have hbound : 2 * A ^ 2 + 2 * B ^ 2 ≤ (2 * S) ^ 2 := by
    nlinarith [sq_nonneg (A - B), sq_nonneg S]
  have hraw : riemannianFiberNormSq (I := I) (M := M) g 4 2 x
      ((Dtop + Ddev).toSection x) ≤ 2 * A ^ 2 + 2 * B ^ 2 := by
    simp only [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply] at hadd ⊢
    linarith
  calc
    riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        ((Dtop + Ddev).toSection x) ≤ 2 * A ^ 2 + 2 * B ^ 2 := hraw
    _ ≤ (2 * S) ^ 2 := hbound
    _ = (K * (δ / (1 - δ) ^ 2 + R)) ^ 2 := by
      simp only [K, S, r]
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
