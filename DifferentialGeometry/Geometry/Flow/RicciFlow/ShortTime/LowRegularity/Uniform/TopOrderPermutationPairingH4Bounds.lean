import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.TopOrderPathPairingBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.VectorBundleTerm
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.OperatorFieldApplicationLpProduct
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2PointwiseUnif
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.H1Jet
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralNormLIterateLadder
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.H1L6
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.FiberLpThreeSixComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Morrey
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.ConvexJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

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
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem fiber_cont
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) : Continuous (fiberLpFun g r s S) := by
  apply Real.continuous_sqrt.comp
  have h := SmoothCcTensor.continuous_inner_self (I := I) (M := M) S
  refine h.congr (fun x => ?_)
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise
    (I := I) (M := M) g r s x (S.toSection x),
    ← SmoothCcTensor.toFun_apply (I := I) (M := M) S x]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem fiber_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M) :
    0 ≤ fiberLpFun g r s S x := Real.sqrt_nonneg _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem inner_fiber_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Q B : SmoothCcTensor g r s)
    (rA sA rC sC : ℕ)
    (A : SmoothCcTensor g rA sA) (C : SmoothCcTensor g rC sC)
    (K : ℝ)
    (hQ : ∀ x : M,
      fiberLpFun g r s Q x ≤
        K * fiberLpFun g rA sA A x * fiberLpFun g rC sC C x) :
    |Inner.inner ℝ Q B| ≤
      K * ∫ x, fiberLpFun g rA sA A x * fiberLpFun g r s B x *
          fiberLpFun g rC sC C x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hinner : Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g r s x
        (Q.toFun x) (B.toFun x)) μ :=
    SmoothCcTensor.integrable_inner_cross (I := I) (M := M) Q B
  have hprod : Integrable
      (fun x => K * (fiberLpFun g rA sA A x * fiberLpFun g r s B x *
        fiberLpFun g rC sC C x)) μ := by
    have hc : Continuous
        (fun x => K * (fiberLpFun g rA sA A x * fiberLpFun g r s B x *
          fiberLpFun g rC sC C x)) :=
      continuous_const.mul
        (((fiber_cont (I := I) (M := M) g rA sA A).mul
          (fiber_cont (I := I) (M := M) g r s B)).mul
          (fiber_cont (I := I) (M := M) g rC sC C))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpoint : ∀ x : M,
      |tensorInnerPointwise (I := I) (M := M) g r s x
          (Q.toFun x) (B.toFun x)| ≤
        K * (fiberLpFun g rA sA A x * fiberLpFun g r s B x *
          fiberLpFun g rC sC C x) := by
    intro x
    have hcs := abs_tensorInnerPointwise_le_mul
      (I := I) (M := M) g r s x (Q.toFun x) (B.toFun x)
    have hcs' :
        |tensorInnerPointwise (I := I) (M := M) g r s x
            (Q.toFun x) (B.toFun x)| ≤
          fiberLpFun g r s Q x * fiberLpFun g r s B x := by
      simpa only [fiberLpFun, tensorPointwiseNorm,
        riemannianFiberNormSq_eq_tensorInnerPointwise,
        SmoothCcTensor.toFun_apply] using hcs
    calc
      _ ≤ fiberLpFun g r s Q x * fiberLpFun g r s B x := hcs'
      _ ≤ (K * fiberLpFun g rA sA A x * fiberLpFun g rC sC C x) *
          fiberLpFun g r s B x :=
        mul_le_mul_of_nonneg_right (hQ x)
          (fiber_nonneg (I := I) (M := M) g r s B x)
      _ = K * (fiberLpFun g rA sA A x * fiberLpFun g r s B x *
          fiberLpFun g rC sC C x) := by ring
  rw [SmoothCcTensor.inner_def]
  unfold tensorL2Inner
  calc
    |∫ x, tensorInnerPointwise (I := I) (M := M) g r s x
        (Q.toFun x) (B.toFun x) ∂μ| ≤
        ∫ x, |tensorInnerPointwise (I := I) (M := M) g r s x
          (Q.toFun x) (B.toFun x)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, K * (fiberLpFun g rA sA A x * fiberLpFun g r s B x *
          fiberLpFun g rC sC C x) ∂μ :=
      integral_mono hinner.abs hprod hpoint
    _ = K * ∫ x, fiberLpFun g rA sA A x * fiberLpFun g r s B x *
          fiberLpFun g rC sC C x ∂μ := by rw [integral_const_mul]

theorem top_order_path_pairing_permuted_h4_uniform_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_half : δ₀ ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T : SmoothCcTensor g 0 2)
          (hδ : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T) δ₀)
          (hδZ : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g
              (0 : SmoothCcTensor g 0 2)) δ₀)
          (qA qB : Fin 4 → Equiv.Perm (Fin 4))
          (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → ℝ),
          (∀ i, |epsilon i| ≤ 1) →
          ∀ {R : ℝ}, 0 ≤ R →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
          let LT := oneMinusConnLapSmooth (I := I) g 0 2 T
          let V := oneMinusConnLapSmooth (I := I) g 0 2 LT
          let YTL := operatorFieldApply (I := I) (M := M) g 2 2
            (ricciDeTurckTopOrderPathIntegralCoefficient (I := I) (M := M) g T T
              (lt_of_le_of_lt hδ₀_half (by norm_num)) hδ hδZ
              qA qB q epsilon) LT
          let YLT := operatorFieldApply (I := I) (M := M) g 2 2
            (ricciDeTurckTopOrderPathIntegralCoefficient (I := I) (M := M) g T LT
              (lt_of_le_of_lt hδ₀_half (by norm_num)) hδ hδZ
              qA qB q epsilon) T
          2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
              (YTL + YLT).toFun| ≤
            C * R *
              ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 := by
  classical
  obtain ⟨Kedge, hKedge, hedge⟩ :=
    ricciDeTurckTopOrderPathIntegral_zero_uniform_bound (I := I) (M := M)
  obtain ⟨C6two, hC6two, h6two⟩ :=
    h1Lp6RS_uniform (I := I) (M := M) hDim gBase hΛ 0 2
  obtain ⟨C6four, hC6four, h6four⟩ :=
    h1Lp6RS_uniform (I := I) (M := M) hDim gBase hΛ 0 4
  obtain ⟨C63, hC63, h63⟩ :=
    fiber_lp_three_le_uniform_constant_mul_lp_six (I := I) (M := M) gBase Λ
  obtain ⟨Cmor, hCmor, hmor⟩ :=
    morreyRS_uniform (I := I) (M := M) hDim gBase hΛ 0 2
  obtain ⟨Kcurv, hKcurv⟩ :=
    exists_uniform_curvature_action_parameters (I := I) (M := M) gBase hΛ
  let C2 : ℝ := h2CovsumC Kcurv.rankTwo
  let C3 : ℝ := h3CovsumC Kcurv.rankTwo Kcurv.rankThree
  let A : ℝ := Kedge * C6two * C63 * C6four * C3
  let B : ℝ := Kedge * Cmor * C2 ^ 2
  let C : ℝ := 2 * (A + B)
  have hC2 : 0 ≤ C2 := by
    dsimp only [C2]
    exact h2CovsumC_nonneg _
  have hC3 : 0 ≤ C3 := by
    dsimp only [C3]
    exact h3CovsumC_nonneg _ _
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro g hEq hjet T hδ hδZ qA qB q epsilon hepsilon R hR hT2
  let hδ₀_lt : δ₀ < 1 := lt_of_le_of_lt hδ₀_half (by norm_num)
  let LT : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 T
  let V : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 LT
  let YTL : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2
      (ricciDeTurckTopOrderPathIntegralCoefficient (I := I) (M := M) g T T hδ₀_lt hδ hδZ
        qA qB q epsilon) LT
  let YLT : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2
      (ricciDeTurckTopOrderPathIntegralCoefficient (I := I) (M := M) g T LT hδ₀_lt hδ hδZ
        qA qB q epsilon) T
  let D2T : SmoothCcTensor g 0 4 :=
    iteratedCovGrad (I := I) g 0 2 2 T
  let D3T : SmoothCcTensor g 0 5 :=
    iteratedCovGrad (I := I) g 0 2 3 T
  let D2LT : SmoothCcTensor g 0 4 :=
    iteratedCovGrad (I := I) g 0 2 2 LT
  let QTL : SmoothCcTensor g 0 4 :=
    ricciDeTurckTopOrderPathIntegralAdjoint (I := I) (M := M) g T LT V hδ₀_lt
      hδ hδZ qA qB q epsilon
  let QLT : SmoothCcTensor g 0 4 :=
    ricciDeTurckTopOrderPathIntegralAdjoint (I := I) (M := M) g T T V hδ₀_lt
      hδ hδZ qA qB q epsilon
  let x : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let z : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  have hx : 0 ≤ x := norm_nonneg _
  have hy : 0 ≤ y := norm_nonneg _
  have hz : 0 ≤ z := norm_nonneg _
  have hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ :=
    hjet 1 (by norm_num)
  have hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ :=
    hjet 2 (by norm_num)
  obtain ⟨hact2, hact3⟩ := hKcurv.bounds g hEq hjet
  have hshift1 :
      ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) LT‖ = y := by
    dsimp only [LT, y]
    rw [norm_ccHs_eq_smoothHs, norm_ccHs_eq_smoothHs]
    calc
      _ = ‖smoothCcToTensorHs (I := I) (M := M) g ((1 : ℕ) : ℝ)
            (oneMinusConnLapSmooth (I := I) g 0 2 T)‖ :=
        congrArg (fun sigma : ℝ =>
          ‖smoothCcToTensorHs (I := I) (M := M) g sigma
            (oneMinusConnLapSmooth (I := I) g 0 2 T)‖) (by norm_num)
      _ = ‖smoothCcToTensorHs (I := I) (M := M) g ((1 + 2 : ℕ) : ℝ) T‖ :=
        (smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap
          (I := I) (M := M) g 1 T).symm
      _ = _ := congrArg (fun sigma : ℝ =>
        ‖smoothCcToTensorHs (I := I) (M := M) g sigma T‖) (by norm_num)
  have hshift2 :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) LT‖ = z := by
    dsimp only [LT, z]
    rw [norm_ccHs_eq_smoothHs, norm_ccHs_eq_smoothHs]
    calc
      _ = ‖smoothCcToTensorHs (I := I) (M := M) g ((2 : ℕ) : ℝ)
            (oneMinusConnLapSmooth (I := I) g 0 2 T)‖ :=
        congrArg (fun sigma : ℝ =>
          ‖smoothCcToTensorHs (I := I) (M := M) g sigma
            (oneMinusConnLapSmooth (I := I) g 0 2 T)‖) (by norm_num)
      _ = ‖smoothCcToTensorHs (I := I) (M := M) g ((2 + 2 : ℕ) : ℝ) T‖ :=
        (smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap
          (I := I) (M := M) g 2 T).symm
      _ = _ := congrArg (fun sigma : ℝ =>
        ‖smoothCcToTensorHs (I := I) (M := M) g sigma T‖) (by norm_num)
  have hVnorm : ‖V‖ = z := by
    have heven := smoothCcToTensorHs_even_norm_eq_toL2_iter
      (I := I) (M := M) g 2 T
    change ‖smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) T‖ =
      ‖SmoothCcTensor.toL2 V‖ at heven
    rw [SmoothCcTensor.norm_toL2] at heven
    simpa only [z, norm_ccHs_eq_smoothHs] using heven.symm
  have hspec (W : SmoothCcTensor g 0 2) :
      ‖(⟨W⟩ : SmoothCcTensorH1 g 0 2)‖ =
        ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) W‖ := by
    have hspectral := cc_h1_jet_sq (I := I) (M := M) g W
    have hintrinsic := smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M) g 0 2 W
    nlinarith [
      norm_nonneg (ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) W),
      norm_nonneg (⟨W⟩ : SmoothCcTensorH1 g 0 2)]
  have hLT6 :
      lpNorm (fiberLpFun g 0 2 LT) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        C6two * y := by
    calc
      _ ≤ C6two * ‖(⟨LT⟩ : SmoothCcTensorH1 g 0 2)‖ := by
        simpa only [fiberLpFun] using h6two g hEq hjet1
          (⟨LT⟩ : SmoothCcTensorH1 g 0 2)
      _ = C6two * y := by rw [hspec LT, hshift1]
  have hcompD2 :
      ‖covGrad (I := I) (M := M) g 0 4 D2T‖ = ‖D3T‖ := by
    change ‖iteratedCovGrad (I := I) g 0 (2 + 2) 1
        (iteratedCovGrad (I := I) g 0 2 2 T)‖ =
      ‖iteratedCovGrad (I := I) g 0 2 (2 + 1) T‖
    exact iteratedCovGrad_comp_norm (I := I) (M := M) g 2 2 1 T
  have hD2H1root :
      ‖(⟨D2T⟩ : SmoothCcTensorH1 g 0 4)‖ ≤ ‖D2T‖ + ‖D3T‖ := by
    have hsq : ‖(⟨D2T⟩ : SmoothCcTensorH1 g 0 4)‖ ^ 2 =
        ‖D2T‖ ^ 2 + ‖covGrad (I := I) (M := M) g 0 4 D2T‖ ^ 2 := by
      rw [smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M)]
    refine le_of_sq_le_sq ?_
      (add_nonneg (norm_nonneg D2T) (norm_nonneg D3T))
    rw [hsq, hcompD2]
    nlinarith [mul_nonneg (norm_nonneg D2T) (norm_nonneg D3T)]
  have hsum3 :
      (∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 0 2 j T‖) ≤ C3 * y := by
    simpa only [C3, y] using
      (covsum_hs_three (I := I) (M := M) g 2 hact2 hact3 T)
  have hD2tail : ‖D2T‖ + ‖D3T‖ ≤
      ∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 0 2 j T‖ := by
    dsimp only [D2T, D3T]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      iteratedCovGrad_zero, Nat.reduceAdd]
    nlinarith [norm_nonneg T,
      norm_nonneg (iteratedCovGrad (I := I) g 0 2 1 T)]
  have hD2H1 :
      ‖(⟨D2T⟩ : SmoothCcTensorH1 g 0 4)‖ ≤ C3 * y :=
    hD2H1root.trans (hD2tail.trans hsum3)
  have hD2T6 :
      lpNorm (fiberLpFun g 0 4 D2T) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        C6four * (C3 * y) := by
    calc
      _ ≤ C6four * ‖(⟨D2T⟩ : SmoothCcTensorH1 g 0 4)‖ := by
        simpa only [fiberLpFun] using h6four g hEq hjet1
          (⟨D2T⟩ : SmoothCcTensorH1 g 0 4)
      _ ≤ C6four * (C3 * y) :=
        mul_le_mul_of_nonneg_left hD2H1 hC6four
  have hD2T3 :
      lpNorm (fiberLpFun g 0 4 D2T) 3
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        C63 * (C6four * (C3 * y)) := by
    calc
      _ ≤ C63 * lpNorm (fiberLpFun g 0 4 D2T) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) :=
        h63 g hEq 0 4 D2T
      _ ≤ C63 * (C6four * (C3 * y)) :=
        mul_le_mul_of_nonneg_left hD2T6 hC63
  have hD2LT : ‖D2LT‖ ≤ C2 * z := by
    calc
      _ ≤ ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j LT‖ := by
        dsimp only [D2LT]
        exact Finset.single_le_sum (s := Finset.range 3)
          (f := fun j : ℕ => ‖iteratedCovGrad (I := I) g 0 2 j LT‖)
          (fun j _ => norm_nonneg _) (show 2 ∈ Finset.range 3 by norm_num)
      _ ≤ C2 * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) LT‖ := by
        simpa only [C2] using
          (covsum_hs_two (I := I) (M := M) g 2 hact2 LT)
      _ = C2 * z := by rw [hshift2]
  have hsumT :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 2 j T‖) ≤ C2 * x := by
    simpa only [C2, x] using
      (covsum_hs_two (I := I) (M := M) g 2 hact2 T)
  have hTcap : ∀ p : M,
      fiberLpFun g 0 2 T p ≤ Cmor * C2 * R := by
    intro p
    have hmor0 := hmor g hEq hjet1 hjet2 T p
    have hsum_to_R :
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖) ≤ C2 * R :=
      hsumT.trans (mul_le_mul_of_nonneg_left hT2 hC2)
    have hsqsum :
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) ≤
            (C2 * R) ^ 2 :=
      (Finset.sum_sq_le_sq_sum_of_nonneg
        (fun j _ => norm_nonneg
          (iteratedCovGrad (I := I) g 0 2 j T))).trans
        (pow_le_pow_left₀
          (Finset.sum_nonneg (fun j _ => norm_nonneg
            (iteratedCovGrad (I := I) g 0 2 j T))) hsum_to_R 2)
    have hriemannianFiberNormSq :
        riemannianFiberNormSq (I := I) (M := M) g 0 2 p
            (T.toSection p) ≤ (Cmor * C2 * R) ^ 2 := by
      calc
        _ ≤ Cmor ^ 2 * ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 := hmor0
        _ ≤ Cmor ^ 2 * (C2 * R) ^ 2 :=
          mul_le_mul_of_nonneg_left hsqsum (sq_nonneg Cmor)
        _ = (Cmor * C2 * R) ^ 2 := by ring
    have hcap_nonneg : 0 ≤ Cmor * C2 * R := by positivity
    have hroot := Real.sqrt_le_sqrt hriemannianFiberNormSq
    simpa only [fiberLpFun, Real.sqrt_sq hcap_nonneg] using hroot
  have hQTL : ∀ p : M,
      fiberLpFun g 0 4 QTL p ≤
        Kedge * fiberLpFun g 0 2 LT p * fiberLpFun g 0 2 V p := by
    intro p
    simpa only [QTL] using
      (hedge g T LT V hδ₀_nonneg hδ₀_half hδ₀_lt hδ hδZ
        qA qB q epsilon hepsilon p)
  have hQLT : ∀ p : M,
      fiberLpFun g 0 4 QLT p ≤
        Kedge * fiberLpFun g 0 2 T p * fiberLpFun g 0 2 V p := by
    intro p
    simpa only [QLT] using
      (hedge g T T V hδ₀_nonneg hδ₀_half hδ₀_lt hδ hδZ
        qA qB q epsilon hepsilon p)
  have hpathTL : Inner.inner ℝ V YTL = Inner.inner ℝ QTL D2T := by
    simpa only [YTL, QTL, D2T] using
      (ricciDeTurckTopOrderPathIntegral_inner (I := I) (M := M) g T LT T V hδ₀_lt
        hδ hδZ qA qB q epsilon)
  have hpathLT : Inner.inner ℝ V YLT = Inner.inner ℝ QLT D2LT := by
    simpa only [YLT, QLT, D2LT] using
      (ricciDeTurckTopOrderPathIntegral_inner (I := I) (M := M) g T T LT V hδ₀_lt
        hδ hδZ qA qB q epsilon)
  have hholderTL := fiber_mul3_l632 (I := I) (M := M) g
    0 2 0 4 0 2 LT D2T V
  have htermTL : |Inner.inner ℝ V YTL| ≤ A * y ^ 2 * z := by
    calc
      _ = |Inner.inner ℝ QTL D2T| := congrArg abs hpathTL
      _ ≤ Kedge * ∫ p,
          fiberLpFun g 0 2 LT p * fiberLpFun g 0 4 D2T p *
            fiberLpFun g 0 2 V p
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
        inner_fiber_le (I := I) (M := M) g 0 4 QTL D2T
          0 2 0 2 LT V Kedge hQTL
      _ ≤ Kedge *
          (lpNorm (fiberLpFun g 0 2 LT) 6
              (riemannianVolumeMeasure (I := I) (M := M) g) *
            lpNorm (fiberLpFun g 0 4 D2T) 3
              (riemannianVolumeMeasure (I := I) (M := M) g) * ‖V‖) :=
        mul_le_mul_of_nonneg_left hholderTL hKedge
      _ ≤ Kedge *
          ((C6two * y) *
            lpNorm (fiberLpFun g 0 4 D2T) 3
              (riemannianVolumeMeasure (I := I) (M := M) g) * ‖V‖) := by
        apply mul_le_mul_of_nonneg_left _ hKedge
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg V)
        exact mul_le_mul_of_nonneg_right hLT6 lpNorm_nonneg
      _ ≤ Kedge *
          ((C6two * y) * (C63 * (C6four * (C3 * y))) * ‖V‖) := by
        apply mul_le_mul_of_nonneg_left _ hKedge
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg V)
        exact mul_le_mul_of_nonneg_left hD2T3 (mul_nonneg hC6two hy)
      _ = A * y ^ 2 * z := by
        rw [hVnorm]
        dsimp only [A]
        ring
  have hcap_nonneg : 0 ≤ Cmor * C2 * R := by positivity
  have hholderLT := fiber_mul3_linf22 (I := I) (M := M) g
    0 2 0 4 0 2 T D2LT V (Cmor * C2 * R) hcap_nonneg hTcap
  have htermLT : |Inner.inner ℝ V YLT| ≤ B * R * z ^ 2 := by
    calc
      _ = |Inner.inner ℝ QLT D2LT| := congrArg abs hpathLT
      _ ≤ Kedge * ∫ p,
          fiberLpFun g 0 2 T p * fiberLpFun g 0 4 D2LT p *
            fiberLpFun g 0 2 V p
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
        inner_fiber_le (I := I) (M := M) g 0 4 QLT D2LT
          0 2 0 2 T V Kedge hQLT
      _ ≤ Kedge * ((Cmor * C2 * R) * ‖D2LT‖ * ‖V‖) :=
        mul_le_mul_of_nonneg_left hholderLT hKedge
      _ ≤ Kedge * ((Cmor * C2 * R) * (C2 * z) * ‖V‖) := by
        apply mul_le_mul_of_nonneg_left _ hKedge
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg V)
        exact mul_le_mul_of_nonneg_left hD2LT hcap_nonneg
      _ = B * R * z ^ 2 := by
        rw [hVnorm]
        dsimp only [B]
        ring
  have hinterp : y ^ 2 ≤ x * z := by
    dsimp only [x, y, z]
    exact ccTensorToHs_norm_three_sq_le_norm_two_mul_norm_four
      (I := I) (M := M) g 2 T
  have hy2Rz : y ^ 2 ≤ R * z :=
    hinterp.trans (mul_le_mul_of_nonneg_right hT2 hz)
  have hsum : |Inner.inner ℝ V (YTL + YLT)| ≤
      A * y ^ 2 * z + B * R * z ^ 2 := by
    calc
      _ = |Inner.inner ℝ V YTL + Inner.inner ℝ V YLT| := by
        rw [inner_add_right]
      _ ≤ |Inner.inner ℝ V YTL| + |Inner.inner ℝ V YLT| :=
        abs_add_le _ _
      _ ≤ A * y ^ 2 * z + B * R * z ^ 2 :=
        add_le_add htermTL htermLT
  change 2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
      (YTL + YLT).toFun| ≤ C * R * z ^ 2
  rw [show tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
      (YTL + YLT).toFun = Inner.inner ℝ V (YTL + YLT) from
    (SmoothCcTensor.inner_def (I := I) (M := M) V (YTL + YLT)).symm]
  calc
    2 * |Inner.inner ℝ V (YTL + YLT)| ≤
        2 * (A * y ^ 2 * z + B * R * z ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ ≤ 2 * (A * (R * z) * z + B * R * z ^ 2) := by
      gcongr
    _ = C * R * z ^ 2 := by
      dsimp only [C]
      ring

theorem top_order_path_pairing_diagonal_h4_uniform_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_half : δ₀ ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T : SmoothCcTensor g 0 2)
          (hδ : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T) δ₀)
          (hδZ : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g
              (0 : SmoothCcTensor g 0 2)) δ₀)
          (qA qB : Fin 4 → Equiv.Perm (Fin 4))
          (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → ℝ),
          (∀ i, |epsilon i| ≤ 1) →
          ∀ {R : ℝ}, 0 ≤ R →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
          let LT := oneMinusConnLapSmooth (I := I) g 0 2 T
          let V := oneMinusConnLapSmooth (I := I) g 0 2 LT
          let QTT := operatorFieldApply (I := I) (M := M) g 2 2
            (ricciDeTurckTopOrderPathIntegralCoefficient (I := I) (M := M) g T T
              (lt_of_le_of_lt hδ₀_half (by norm_num)) hδ hδZ
              qA qB q epsilon) T
          2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun QTT.toFun| ≤
            C * R *
              ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ *
              ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ := by
  classical
  obtain ⟨Kedge, hKedge, hedge⟩ :=
    ricciDeTurckTopOrderPathIntegral_zero_uniform_bound (I := I) (M := M)
  obtain ⟨Cmor, hCmor, hmor⟩ :=
    morreyRS_uniform (I := I) (M := M) hDim gBase hΛ 0 2
  obtain ⟨Kcurv, hKcurv⟩ :=
    exists_uniform_curvature_action_parameters (I := I) (M := M) gBase hΛ
  let C2 : ℝ := h2CovsumC Kcurv.rankTwo
  let C3 : ℝ := h3CovsumC Kcurv.rankTwo Kcurv.rankThree
  let C : ℝ := 2 * Kedge * Cmor * C2 * C3
  have hC2 : 0 ≤ C2 := by
    dsimp only [C2]
    exact h2CovsumC_nonneg _
  have hC3 : 0 ≤ C3 := by
    dsimp only [C3]
    exact h3CovsumC_nonneg _ _
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro g hEq hjet T hδ hδZ qA qB q epsilon hepsilon R hR hT2
  let hδ₀_lt : δ₀ < 1 := lt_of_le_of_lt hδ₀_half (by norm_num)
  let LT : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 T
  let V : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 LT
  let QTT : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2
      (ricciDeTurckTopOrderPathIntegralCoefficient (I := I) (M := M) g T T hδ₀_lt hδ hδZ
        qA qB q epsilon) T
  let D2T : SmoothCcTensor g 0 4 :=
    iteratedCovGrad (I := I) g 0 2 2 T
  let PTT : SmoothCcTensor g 0 4 :=
    ricciDeTurckTopOrderPathIntegralAdjoint (I := I) (M := M) g T T V hδ₀_lt
      hδ hδZ qA qB q epsilon
  let x : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let z : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  have hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ :=
    hjet 1 (by norm_num)
  have hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ :=
    hjet 2 (by norm_num)
  obtain ⟨hact2, hact3⟩ := hKcurv.bounds g hEq hjet
  have hVnorm : ‖V‖ = z := by
    have heven := smoothCcToTensorHs_even_norm_eq_toL2_iter
      (I := I) (M := M) g 2 T
    change ‖smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) T‖ =
      ‖SmoothCcTensor.toL2 V‖ at heven
    rw [SmoothCcTensor.norm_toL2] at heven
    simpa only [z, norm_ccHs_eq_smoothHs] using heven.symm
  have hD2T : ‖D2T‖ ≤ C3 * y := by
    calc
      _ ≤ ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ := by
        dsimp only [D2T]
        exact Finset.single_le_sum (s := Finset.range 4)
          (f := fun j : ℕ => ‖iteratedCovGrad (I := I) g 0 2 j T‖)
          (fun j _ => norm_nonneg _) (show 2 ∈ Finset.range 4 by norm_num)
      _ ≤ C3 * y := by
        simpa only [C3, y] using
          (covsum_hs_three (I := I) (M := M) g 2 hact2 hact3 T)
  have hsumT :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 2 j T‖) ≤ C2 * x := by
    simpa only [C2, x] using
      (covsum_hs_two (I := I) (M := M) g 2 hact2 T)
  have hTcap : ∀ p : M,
      fiberLpFun g 0 2 T p ≤ Cmor * C2 * R := by
    intro p
    have hmor0 := hmor g hEq hjet1 hjet2 T p
    have hsum_to_R :
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖) ≤ C2 * R :=
      hsumT.trans (mul_le_mul_of_nonneg_left hT2 hC2)
    have hsqsum :
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) ≤
            (C2 * R) ^ 2 :=
      (Finset.sum_sq_le_sq_sum_of_nonneg
        (fun j _ => norm_nonneg
          (iteratedCovGrad (I := I) g 0 2 j T))).trans
        (pow_le_pow_left₀
          (Finset.sum_nonneg (fun j _ => norm_nonneg
            (iteratedCovGrad (I := I) g 0 2 j T))) hsum_to_R 2)
    have hriemannianFiberNormSq :
        riemannianFiberNormSq (I := I) (M := M) g 0 2 p
            (T.toSection p) ≤ (Cmor * C2 * R) ^ 2 := by
      calc
        _ ≤ Cmor ^ 2 * ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 := hmor0
        _ ≤ Cmor ^ 2 * (C2 * R) ^ 2 :=
          mul_le_mul_of_nonneg_left hsqsum (sq_nonneg Cmor)
        _ = (Cmor * C2 * R) ^ 2 := by ring
    have hcap_nonneg : 0 ≤ Cmor * C2 * R := by positivity
    have hroot := Real.sqrt_le_sqrt hriemannianFiberNormSq
    simpa only [fiberLpFun, Real.sqrt_sq hcap_nonneg] using hroot
  have hPTT : ∀ p : M,
      fiberLpFun g 0 4 PTT p ≤
        Kedge * fiberLpFun g 0 2 T p * fiberLpFun g 0 2 V p := by
    intro p
    simpa only [PTT] using
      (hedge g T T V hδ₀_nonneg hδ₀_half hδ₀_lt hδ hδZ
        qA qB q epsilon hepsilon p)
  have hpath : Inner.inner ℝ V QTT = Inner.inner ℝ PTT D2T := by
    simpa only [QTT, PTT, D2T] using
      (ricciDeTurckTopOrderPathIntegral_inner (I := I) (M := M) g T T T V hδ₀_lt
        hδ hδZ qA qB q epsilon)
  have hcap_nonneg : 0 ≤ Cmor * C2 * R := by positivity
  have hholder := fiber_mul3_linf22 (I := I) (M := M) g
    0 2 0 4 0 2 T D2T V (Cmor * C2 * R) hcap_nonneg hTcap
  have hpair : |Inner.inner ℝ V QTT| ≤
      Kedge * ((Cmor * C2 * R) * (C3 * y) * z) := by
    calc
      _ = |Inner.inner ℝ PTT D2T| := congrArg abs hpath
      _ ≤ Kedge * ∫ p,
          fiberLpFun g 0 2 T p * fiberLpFun g 0 4 D2T p *
            fiberLpFun g 0 2 V p
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
        inner_fiber_le (I := I) (M := M) g 0 4 PTT D2T
          0 2 0 2 T V Kedge hPTT
      _ ≤ Kedge * ((Cmor * C2 * R) * ‖D2T‖ * ‖V‖) :=
        mul_le_mul_of_nonneg_left hholder hKedge
      _ ≤ Kedge * ((Cmor * C2 * R) * (C3 * y) * ‖V‖) := by
        apply mul_le_mul_of_nonneg_left _ hKedge
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg V)
        exact mul_le_mul_of_nonneg_left hD2T hcap_nonneg
      _ = Kedge * ((Cmor * C2 * R) * (C3 * y) * z) := by
        rw [hVnorm]
  change 2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun QTT.toFun| ≤
    C * R * y * z
  rw [show tensorL2Inner (I := I) (M := M) g 0 2 V.toFun QTT.toFun =
      Inner.inner ℝ V QTT from
    (SmoothCcTensor.inner_def (I := I) (M := M) V QTT).symm]
  calc
    2 * |Inner.inner ℝ V QTT| ≤
        2 * (Kedge * ((Cmor * C2 * R) * (C3 * y) * z)) :=
      mul_le_mul_of_nonneg_left hpair (by norm_num)
    _ = C * R * y * z := by
      dsimp only [C]
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
