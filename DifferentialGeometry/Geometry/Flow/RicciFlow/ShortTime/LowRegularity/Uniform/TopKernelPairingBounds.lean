import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciTopOrderCoefficientBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.MoserTameBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.SecondDerivativePairing.ZeroOrderCoefficient
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.SecondDerivativePairing.FirstOrderCoefficient
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Morrey
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.ConvexJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.TopOrderCoefficientH3Bounds

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

theorem bcD2_pair_h4_uniform
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T : SmoothCcTensor g 0 2)
          (_hT : ∀ (x : M) (u v : TangentSpace I x),
            ccTensorBilin (I := I) g T x u v =
              ccTensorBilin (I := I) g T x v u)
          {δ : ℝ}, δ ≤ 1 / 3 → 0 ≤ δ →
          ∀ (hδ : gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g T) δ)
            (hδZ : gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g
                (0 : SmoothCcTensor g 0 2)) δ)
            {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
          ∀ U : SmoothCcTensor g 0 2,
          let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
          let Φ :=
            lieDecomposition2 (I := I) (M := M) g T hδ hδZ s +
              (-2 * s : ℝ) •
                RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T
          |tensorL2Inner (I := I) (M := M) g 0 2
              (oneMinusConnLapSmooth (I := I) g 0 2
                (oneMinusConnLapSmooth (I := I) g 0 2 U)).toFun
              (operatorFieldApply (I := I) (M := M) g 4 2 Φ
                (iteratedCovGrad (I := I) g 0 2 2
                  (oneMinusConnLapSmooth (I := I) g 0 2 U))).toFun| ≤
            C * (δ / (1 - δ) ^ 2) *
              ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2 := by
  obtain ⟨Ktop, hKtop0, htop⟩ :=
    RicciDeTurckLowOrder.exists_topOrderKernel_path_riemannianFiberNormSq_le (I := I) (M := M)
  obtain ⟨Kcurv, hKcurv⟩ :=
    exists_uniform_curvature_action_parameters (I := I) (M := M) gBase hΛ
  let C : ℝ := Ktop * h2CovsumC Kcurv.rankTwo
  refine ⟨C, mul_nonneg hKtop0 (h2CovsumC_nonneg Kcurv.rankTwo), ?_⟩
  intro g hEq hjet T hT δ hδ_le hδ0 hδ hδZ s hs U
  dsimp only
  let r : ℝ := δ / (1 - δ) ^ 2
  let Φ : SmoothCcTensor g 4 2 :=
    lieDecomposition2 (I := I) (M := M) g T hδ hδZ s +
      (-2 * s : ℝ) •
        RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ s) T
  have hr : 0 ≤ r := div_nonneg hδ0 (sq_nonneg _)
  have hΦ : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          (Φ.toSection x) ≤ (Ktop * r) ^ 2 := by
    intro x
    simpa only [Φ, r] using
      htop g T hT hδ_le hδ0 hδ hδZ hs x
  have hact : IsCurvAction0 (I := I) (M := M) g 2 Kcurv.rankTwo :=
    (hKcurv.bounds g hEq hjet).1
  have hpair := operator_field_application_second_covariant_derivative_pairing_h4_bound (I := I) (M := M) g hact
    (mul_nonneg hKtop0 hr) Φ hΦ U
  change
    |tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmooth (I := I) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2 U)).toFun
        (operatorFieldApply (I := I) (M := M) g 4 2 Φ
          (iteratedCovGrad (I := I) g 0 2 2
            (oneMinusConnLapSmooth (I := I) g 0 2 U))).toFun| ≤
      C * r * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2
  calc
    _ ≤ (Ktop * r) * h2CovsumC Kcurv.rankTwo *
        ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2 := hpair
    _ = C * r *
        ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2 := by
      simp only [C]
      ring

theorem bcD2_pair_abs_uniform
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∀ {η : ℝ}, 0 < η →
      ∃ δ₂ : ℝ, 0 < δ₂ ∧ δ₂ ≤ 1 / 3 ∧
        ∀ g : SmoothRiemannianMetric I M,
          MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
          (∀ a : ℕ, a ≤ 3 →
            MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
          ∀ (T : SmoothCcTensor g 0 2)
            (_hT : ∀ (x : M) (u v : TangentSpace I x),
              ccTensorBilin (I := I) g T x u v =
                ccTensorBilin (I := I) g T x v u)
            {δ : ℝ}, δ ≤ δ₂ → 0 ≤ δ →
            ∀ (hδ : gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g T) δ)
              (hδZ : gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g
                  (0 : SmoothCcTensor g 0 2)) δ)
              {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
            ∀ U : SmoothCcTensor g 0 2,
            let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
            let Φ :=
              lieDecomposition2 (I := I) (M := M) g T hδ hδZ s +
                (-2 * s : ℝ) •
                  RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T
            2 * |tensorL2Inner (I := I) (M := M) g 0 2
                (oneMinusConnLapSmooth (I := I) g 0 2
                  (oneMinusConnLapSmooth (I := I) g 0 2 U)).toFun
                (operatorFieldApply (I := I) (M := M) g 4 2 Φ
                  (iteratedCovGrad (I := I) g 0 2 2
                    (oneMinusConnLapSmooth (I := I) g 0 2 U))).toFun| ≤
              η * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2 := by
  intro η hη
  obtain ⟨C, hC0, hpair⟩ := bcD2_pair_h4_uniform
    (I := I) (M := M) gBase hΛ
  let δ₂ : ℝ := min (1 / 4 : ℝ) (η / (4 * (C + 1)))
  have hCp : 0 < C + 1 := by linarith
  have hδ₂0 : 0 < δ₂ := lt_min (by norm_num)
    (div_pos hη (mul_pos (by norm_num) hCp))
  have hδ₂third : δ₂ ≤ 1 / 3 :=
    (min_le_left _ _).trans (by norm_num)
  refine ⟨δ₂, hδ₂0, hδ₂third, ?_⟩
  intro g hEq hjet T hT δ hδ_le hδ0 hδ hδZ s hs U
  dsimp only
  let r : ℝ := δ / (1 - δ) ^ 2
  let Φ : SmoothCcTensor g 4 2 :=
    lieDecomposition2 (I := I) (M := M) g T hδ hδZ s +
      (-2 * s : ℝ) •
        RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ s) T
  have hδ_quarter : δ ≤ 1 / 4 :=
    hδ_le.trans (min_le_left _ _)
  have hδ_third : δ ≤ 1 / 3 := hδ_le.trans hδ₂third
  have hbase : 0 < 1 - δ := by linarith
  have hsq : (1 / 2 : ℝ) ≤ (1 - δ) ^ 2 := by
    nlinarith [sq_nonneg δ]
  have hr : r ≤ 2 * δ := by
    dsimp only [r]
    rw [div_le_iff₀ (sq_pos_of_pos hbase)]
    nlinarith [mul_le_mul_of_nonneg_left hsq hδ0]
  have hδ_frac : δ ≤ η / (4 * (C + 1)) :=
    hδ_le.trans (min_le_right _ _)
  have hδ_scaled : δ * (4 * (C + 1)) ≤ η :=
    (le_div_iff₀ (mul_pos (by norm_num) hCp)).mp hδ_frac
  have hcoef : 4 * C * δ ≤ η := by
    calc
      4 * C * δ ≤ 4 * (C + 1) * δ := by
        apply mul_le_mul_of_nonneg_right _ hδ0
        nlinarith
      _ ≤ η := by
        nlinarith
  have hpair' :
      |tensorL2Inner (I := I) (M := M) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2
            (oneMinusConnLapSmooth (I := I) g 0 2 U)).toFun
          (operatorFieldApply (I := I) (M := M) g 4 2 Φ
            (iteratedCovGrad (I := I) g 0 2 2
              (oneMinusConnLapSmooth (I := I) g 0 2 U))).toFun| ≤
        C * r *
          ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2 := by
    simpa only [Φ, r] using
      hpair g hEq hjet T hT hδ_third hδ0 hδ hδZ hs U
  have hCr : 2 * C * r ≤ 4 * C * δ := by
    calc
      2 * C * r ≤ 2 * C * (2 * δ) :=
        mul_le_mul_of_nonneg_left hr (mul_nonneg (by norm_num) hC0)
      _ = 4 * C * δ := by ring
  calc
    2 * |tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmooth (I := I) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2 U)).toFun
        (operatorFieldApply (I := I) (M := M) g 4 2 Φ
          (iteratedCovGrad (I := I) g 0 2 2
            (oneMinusConnLapSmooth (I := I) g 0 2 U))).toFun| ≤
      2 * (C * r *
        ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hpair' (by norm_num)
    _ = (2 * C * r) *
        ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2 := by ring
    _ ≤ (4 * C * δ) *
        ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hCr (sq_nonneg _)
    _ ≤ η * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem iterated_covgrad_comp_l2_sq
    (g : SmoothRiemannianMetric I M) (r s l m : ℕ)
    (S : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g r (s + l) m
        (iteratedCovGrad (I := I) g r s l S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s (l + m) S‖ ^ 2 := by
  simp only [SmoothCcTensor.norm_def]
  rw [tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g r ((s + l) + m),
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g r (s + (l + m))]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simpa only [Nat.add_assoc] using
    riemannianFiberNormSq_iteratedCovGrad_comp
      (I := I) (M := M) g r s l m S x

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem covgrad_jet_three_le_four
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g r (s + 1) j
        (covGrad (I := I) (M := M) g r s S)‖ ^ 2) ≤
      ∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g r s j S‖ ^ 2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    iteratedCovGrad_zero]
  change ‖iteratedCovGrad (I := I) g r s 1 S‖ ^ 2 +
      ‖iteratedCovGrad (I := I) g r (s + 1) 1
        (covGrad (I := I) (M := M) g r s S)‖ ^ 2 +
      ‖iteratedCovGrad (I := I) g r (s + 1) 2
        (covGrad (I := I) (M := M) g r s S)‖ ^ 2 ≤ _
  rw [show ‖iteratedCovGrad (I := I) g r (s + 1) 1
      (covGrad (I := I) (M := M) g r s S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s 2 S‖ ^ 2 by
        exact iterated_covgrad_comp_l2_sq
          (I := I) (M := M) g r s 1 1 S,
    show ‖iteratedCovGrad (I := I) g r (s + 1) 2
      (covGrad (I := I) (M := M) g r s S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s 3 S‖ ^ 2 by
        exact iterated_covgrad_comp_l2_sq
          (I := I) (M := M) g r s 1 2 S]
  norm_num

theorem top_ker_grad_h3_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T : SmoothCcTensor g 0 2)
          (_hT : ∀ (x : M) (u v : TangentSpace I x),
            ccTensorBilin (I := I) g T x u v =
              ccTensorBilin (I := I) g T x v u)
          {δ : ℝ}, δ ≤ 1 / 3 → 0 ≤ δ →
          ∀ (hδ : gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g T) δ)
            (hδZ : gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g
                (0 : SmoothCcTensor g 0 2)) δ),
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
          ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
          ∀ p : M,
          let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
          let Φ := lieDecomposition2 (I := I) (M := M) g T hδ hδZ s +
            (-2 * s : ℝ) •
              RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T
          riemannianFiberNormSq (I := I) (M := M) g 4 3 p
              ((covGrad (I := I) (M := M) g 4 2 Φ).toSection p) ≤
            (C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖) ^ 2 := by
  classical
  obtain ⟨ρB, CB, hρB, hCB, hedge⟩ :=
    ricciDeTurckTopOrderCoefficient_h3_uniform_bound (I := I) (M := M) hDim gBase hΛ
  obtain ⟨ρP, CP, hρP, hCP, hphi⟩ :=
    phi_dev_h3_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Cmor, hCmor, hmor⟩ :=
    morreyRS_uniform (I := I) (M := M) hDim gBase hΛ 4 3
  let Cjet : ℝ := Real.sqrt (2 * (CB ^ 2 + CP ^ 2))
  let Cgrad : ℝ := Cmor * Cjet
  have hCjet : 0 ≤ Cjet := Real.sqrt_nonneg _
  have hCgrad : 0 ≤ Cgrad := mul_nonneg hCmor hCjet
  refine ⟨min ρB ρP, Cgrad, lt_min hρB hρP, hCgrad, ?_⟩
  intro g hEq hjet T hT δ hδle hδ0 hδ hδZ hT2 s hs p
  let gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδ hδZ s
  let P : SmoothCcTensor g 4 2 :=
    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gm -
      deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
  let B : SmoothCcTensor g 4 2 :=
    lieDecomposition2 (I := I) (M := M) g T hδ hδZ s + P +
      (-2 * s : ℝ) •
        RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T
  let Φ : SmoothCcTensor g 4 2 := B - P
  let x : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  have hx : 0 ≤ x := norm_nonneg _
  have hδlt : δ < 1 := lt_of_le_of_lt hδle (by norm_num)
  have hT2B : x ≤ ρB := hT2.trans (min_le_left _ _)
  have hT2P : x ≤ ρP := hT2.trans (min_le_right _ _)
  have hzero2 :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (0 : SmoothCcTensor g 0 2)‖ ≤ x := by
    rw [show (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
      ccTensorToHs_smul, zero_smul, norm_zero]
    exact hx
  have hzero3 :
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ)
        (0 : SmoothCcTensor g 0 2)‖ = 0 := by
    rw [show (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
      ccTensorToHs_smul, zero_smul, norm_zero]
  have hBjet : covariantJetNormSq (I := I) (M := M) g 3 B ≤ (CB * y) ^ 2 := by
    simpa only [covariantJetNormSq, B, P, gm, y] using
      hedge g hEq hjet T hT hδle hδ0 hδ hδZ hT2B hs
  have hPjet : covariantJetNormSq (I := I) (M := M) g 3 P ≤ (CP * y) ^ 2 := by
    obtain ⟨_, h⟩ := hphi g hEq hjet T (0 : SmoothCcTensor g 0 2)
      hδlt hδ hδlt hδZ hx hT2P le_rfl hzero2 hs.1 hs.2
    simpa only [covariantJetNormSq, P, gm, y, hzero3, add_zero] using h
  have hΦjet : covariantJetNormSq (I := I) (M := M) g 3 Φ ≤ (Cjet * y) ^ 2 := by
    refine (covariantJetNormSq_sub_le (I := I) (M := M) g 3 B P).trans ?_
    calc
      2 * (covariantJetNormSq (I := I) (M := M) g 3 B +
          covariantJetNormSq (I := I) (M := M) g 3 P) ≤
          2 * ((CB * y) ^ 2 + (CP * y) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hBjet hPjet) (by norm_num)
      _ = 2 * (CB ^ 2 + CP ^ 2) * y ^ 2 := by ring
      _ = Cjet ^ 2 * y ^ 2 := by
        rw [show Cjet ^ 2 = 2 * (CB ^ 2 + CP ^ 2) by
          exact Real.sq_sqrt (by positivity)]
      _ = (Cjet * y) ^ 2 := by ring
  let DΦ : SmoothCcTensor g 4 3 :=
    covGrad (I := I) (M := M) g 4 2 Φ
  have hDΦjet :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 4 3 j DΦ‖ ^ 2) ≤
        (Cjet * y) ^ 2 :=
    (covgrad_jet_three_le_four
      (I := I) (M := M) g 4 2 Φ).trans hΦjet
  have hjet1 := hjet 1 (by norm_num)
  have hjet2 := hjet 2 (by norm_num)
  have hpoint :
      riemannianFiberNormSq (I := I) (M := M) g 4 3 p
          (DΦ.toSection p) ≤ (Cgrad * y) ^ 2 := by
    calc
      _ ≤ Cmor ^ 2 * ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 4 3 j DΦ‖ ^ 2 :=
        hmor g hEq hjet1 hjet2 DΦ p
      _ ≤ Cmor ^ 2 * (Cjet * y) ^ 2 :=
        mul_le_mul_of_nonneg_left hDΦjet (sq_nonneg Cmor)
      _ = (Cgrad * y) ^ 2 := by dsimp only [Cgrad]; ring
  have hΦeq : Φ = lieDecomposition2 (I := I) (M := M) g T hδ hδZ s +
      (-2 * s : ℝ) •
        RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T := by
    dsimp only [Φ, B, P]
    module
  simpa only [hΦeq, DΦ, gm, y] using hpoint

theorem bcD2_pair_h5_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ ρ C4 Cmix C5 : ℝ,
      0 < ρ ∧ 0 ≤ C4 ∧ 0 ≤ Cmix ∧ 0 ≤ C5 ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T : SmoothCcTensor g 0 2)
          (_hT : ∀ (x : M) (u v : TangentSpace I x),
            ccTensorBilin (I := I) g T x u v =
              ccTensorBilin (I := I) g T x v u)
          {δ : ℝ}, δ ≤ 1 / 3 → 0 ≤ δ →
          ∀ (hδ : gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g T) δ)
            (hδZ : gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g
                (0 : SmoothCcTensor g 0 2)) δ),
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
          ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
          ∀ U : SmoothCcTensor g 0 2,
          let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
          let Φ := lieDecomposition2 (I := I) (M := M) g T hδ hδZ s +
            (-2 * s : ℝ) •
              RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T
          |tensorL2Inner (I := I) (M := M) g 0 2
              (oneMinusConnLapSmooth (I := I) g 0 2
                (oneMinusConnLapSmooth (I := I) g 0 2
                  (oneMinusConnLapSmooth (I := I) g 0 2 U))).toFun
              (operatorFieldApply (I := I) (M := M) g 4 2 Φ
                (iteratedCovGrad (I := I) g 0 2 2
                  (oneMinusConnLapSmooth (I := I) g 0 2 U))).toFun| ≤
            C4 * (δ / (1 - δ) ^ 2) *
                ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2 +
              Cmix * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ *
                ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) U‖ *
                ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ +
              C5 * (δ / (1 - δ) ^ 2) *
                ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) U‖ ^ 2 := by
  classical
  obtain ⟨Ktop, hKtop, htop⟩ :=
    RicciDeTurckLowOrder.exists_topOrderKernel_path_riemannianFiberNormSq_le (I := I) (M := M)
  obtain ⟨ρ, Cgrad, hρ, hCgrad, hgrad⟩ :=
    top_ker_grad_h3_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Kcurv, hKcurv⟩ :=
    exists_uniform_curvature_action_parameters (I := I) (M := M) gBase hΛ
  let C4 : ℝ := Ktop * h2CovsumC Kcurv.rankTwo
  let Cmix : ℝ := Cgrad * h2CovsumC Kcurv.rankTwo
  let C5 : ℝ := Real.sqrt (Module.finrank ℝ E) * Ktop *
    h3CovsumC Kcurv.rankTwo Kcurv.rankThree
  have hC4 : 0 ≤ C4 :=
    mul_nonneg hKtop (h2CovsumC_nonneg _)
  have hCmix : 0 ≤ Cmix :=
    mul_nonneg hCgrad (h2CovsumC_nonneg _)
  have hC5 : 0 ≤ C5 :=
    mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) hKtop)
      (h3CovsumC_nonneg _ _)
  refine ⟨ρ, C4, Cmix, C5, hρ, hC4, hCmix, hC5, ?_⟩
  intro g hEq hjet T hT δ hδle hδ0 hδ hδZ hT2 s hs U
  let gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδ hδZ s
  let Φ : SmoothCcTensor g 4 2 :=
    lieDecomposition2 (I := I) (M := M) g T hδ hδZ s +
      (-2 * s : ℝ) •
        RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T
  let W : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 U
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let r : ℝ := δ / (1 - δ) ^ 2
  have hy : 0 ≤ y := norm_nonneg _
  have hr : 0 ≤ r := div_nonneg hδ0 (sq_nonneg _)
  let DΦ : SmoothCcTensor g 4 3 :=
    covGrad (I := I) (M := M) g 4 2 Φ
  have hDΦpoint : ∀ p : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 3 p
          (DΦ.toSection p) ≤ (Cgrad * y) ^ 2 := by
    intro p
    simpa only [DΦ, Φ, gm, y] using
      hgrad g hEq hjet T hT hδle hδ0 hδ hδZ hT2 hs p
  have hΦpoint : ∀ p : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 p
          (Φ.toSection p) ≤ (Ktop * r) ^ 2 := by
    intro p
    have hraw := htop g T hT hδle hδ0 hδ hδZ hs p
    simpa only [Φ, gm, r] using hraw
  obtain ⟨hact2, hact3⟩ := hKcurv.bounds g hEq hjet
  have hpair := operator_field_application_second_covariant_derivative_pairing_h3_bound (I := I) (M := M) g hact2 hact3
    (mul_nonneg hKtop hr) (mul_nonneg hCgrad hy)
    Φ hΦpoint (by simpa only [DΦ] using hDΦpoint) W
  have hshift4 :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W‖ =
        ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ := by
    rw [norm_ccHs_eq_smoothHs, norm_ccHs_eq_smoothHs]
    exact (smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap
      (I := I) (M := M) g 2 U).symm
  have hshift5 :
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W‖ =
        ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) U‖ := by
    rw [norm_ccHs_eq_smoothHs, norm_ccHs_eq_smoothHs]
    exact (smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap
      (I := I) (M := M) g 3 U).symm
  change
    |tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmooth (I := I) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2 W)).toFun
        (operatorFieldApply (I := I) (M := M) g 4 2 Φ
          (iteratedCovGrad (I := I) g 0 2 2 W)).toFun| ≤ _
  calc
    _ ≤ (Ktop * r) * h2CovsumC Kcurv.rankTwo *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W‖ ^ 2 +
        (Cgrad * y) * h2CovsumC Kcurv.rankTwo *
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W‖ *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W‖ +
        Real.sqrt (Module.finrank ℝ E) * (Ktop * r) *
          h3CovsumC Kcurv.rankTwo Kcurv.rankThree *
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W‖ ^ 2 := hpair
    _ = C4 * r *
          ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2 +
        Cmix * y *
          ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) U‖ *
          ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ +
        C5 * r *
          ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) U‖ ^ 2 := by
      rw [hshift4, hshift5]
      dsimp only [C4, Cmix, C5]
      ring
    _ = _ := by rfl

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
