import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.TopOrderCoefficientH3Bounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.TopOrderPermutationPairingH4Bounds

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
    [I.Boundaryless] [SigmaCompactSpace M] in
private theorem fiber_app_app_le
    (g : SmoothRiemannianMetric I M)
    (a b c d : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (Tr : SmoothCcTensor g c d) (A : SmoothCcTensor g b c)
    (W : SmoothCcTensor g a b)
    (hTr : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g c d x
        (Tr.toSection x) ≤ K ^ 2) :
    ∀ x : M,
      fiberLpFun g a d
          (ccOperatorFieldComp (I := I) (M := M) g a c d Tr
            (ccOperatorFieldComp (I := I) (M := M) g a b c A W)) x ≤
        K * fiberLpFun g b c A x * fiberLpFun g a b W x := by
  intro x
  have houter := riemannianFiberNormSq_compRS_le_mul
    (I := I) (M := M) g a c d x (Tr.toSection x)
      ((ccOperatorFieldComp (I := I) (M := M) g a b c A W).toSection x)
  have hinner := riemannianFiberNormSq_compRS_le_mul
    (I := I) (M := M) g a b c x (A.toSection x) (W.toSection x)
  have hsq : riemannianFiberNormSq (I := I) (M := M) g a d x
      ((ccOperatorFieldComp (I := I) (M := M) g a c d Tr
        (ccOperatorFieldComp (I := I) (M := M) g a b c A W)).toSection x) ≤
      (K * fiberLpFun g b c A x * fiberLpFun g a b W x) ^ 2 := by
    calc
      _ ≤ riemannianFiberNormSq (I := I) (M := M) g c d x
          (Tr.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g a c x
          ((ccOperatorFieldComp (I := I) (M := M) g a b c A W).toSection x) := by
            simpa only [operatorFieldComposition_toSection] using houter
      _ ≤ K ^ 2 *
          (riemannianFiberNormSq (I := I) (M := M) g b c x
              (A.toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g a b x
              (W.toSection x)) := by
        exact mul_le_mul (hTr x) hinner
          (riemannianFiberNormSq_nonneg (I := I) (M := M) g a c x _)
          (sq_nonneg K)
      _ = (K * fiberLpFun g b c A x * fiberLpFun g a b W x) ^ 2 := by
        dsimp only [fiberLpFun, tensorPointwiseNorm]
        calc
          _ = K ^ 2 *
              Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g b c x
                (A.toSection x)) ^ 2 *
              Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g a b x
                (W.toSection x)) ^ 2 := by
            rw [Real.sq_sqrt
              (riemannianFiberNormSq_nonneg (I := I) (M := M) g b c x _),
              Real.sq_sqrt
              (riemannianFiberNormSq_nonneg (I := I) (M := M) g a b x _)]
            ring
          _ = _ := by ring
  have hsqrt := Real.sqrt_le_sqrt hsq
  simpa only [fiberLpFun, tensorPointwiseNorm,
    Real.sqrt_sq (mul_nonneg (mul_nonneg hK (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _))] using hsqrt

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem fiber_cont
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) : Continuous (fiberLpFun g r s S) := by
  apply Real.continuous_sqrt.comp
  have h := SmoothCcTensor.continuous_inner_self (I := I) (M := M) S
  refine h.congr (fun x => ?_)
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise
    (I := I) (M := M) g r s x (S.toSection x),
    ← SmoothCcTensor.toFun_apply (I := I) (M := M) S x]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [BoundarylessManifold I M] in
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
  let mu := riemannianVolumeMeasure (I := I) (M := M) g
  let _ : IsFiniteMeasure mu := by
    dsimp only [mu]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hinner : Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g r s x
        (Q.toFun x) (B.toFun x)) mu :=
    SmoothCcTensor.integrable_inner_cross (I := I) (M := M) Q B
  have hprod : Integrable
      (fun x => K * (fiberLpFun g rA sA A x * fiberLpFun g r s B x *
        fiberLpFun g rC sC C x)) mu := by
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
        mul_le_mul_of_nonneg_right (hQ x) (Real.sqrt_nonneg _)
      _ = K * (fiberLpFun g rA sA A x * fiberLpFun g r s B x *
          fiberLpFun g rC sC C x) := by ring
  rw [SmoothCcTensor.inner_def]
  unfold tensorL2Inner
  calc
    |∫ x, tensorInnerPointwise (I := I) (M := M) g r s x
        (Q.toFun x) (B.toFun x) ∂mu| ≤
        ∫ x, |tensorInnerPointwise (I := I) (M := M) g r s x
          (Q.toFun x) (B.toFun x)| ∂mu := abs_integral_le_integral_abs
    _ ≤ ∫ x, K * (fiberLpFun g rA sA A x * fiberLpFun g r s B x *
          fiberLpFun g rC sC C x) ∂mu :=
      integral_mono hinner.abs hprod hpoint
    _ = K * ∫ x, fiberLpFun g rA sA A x * fiberLpFun g r s B x *
          fiberLpFun g rC sC C x ∂mu := by rw [integral_const_mul]

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
        exact iterated_covgrad_comp_l2_sq (I := I) (M := M) g r s 1 1 S,
    show ‖iteratedCovGrad (I := I) g r (s + 1) 2
      (covGrad (I := I) (M := M) g r s S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s 3 S‖ ^ 2 by
        exact iterated_covgrad_comp_l2_sq (I := I) (M := M) g r s 1 2 S]
  norm_num

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem iter_two_h1_le_jet_four
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    ‖(⟨iteratedCovGrad (I := I) g r s 2 S⟩ :
        SmoothCcTensorH1 g r (s + 2))‖ ^ 2 ≤
      ∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g r s j S‖ ^ 2 := by
  rw [smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M)]
  rw [show ‖covGrad (I := I) (M := M) g r (s + 2)
      (iteratedCovGrad (I := I) g r s 2 S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s 3 S‖ ^ 2 by
        exact iterated_covgrad_comp_l2_sq (I := I) (M := M) g r s 2 1 S]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    iteratedCovGrad_zero]
  nlinarith [sq_nonneg ‖S‖,
    sq_nonneg ‖iteratedCovGrad (I := I) g r s 1 S‖]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [BoundarylessManifold I M] in
private theorem inner_fiber_l632_le
    (g : SmoothRiemannianMetric I M) (r s rA sA rC sC : ℕ)
    (Q V : SmoothCcTensor g r s)
    (A : SmoothCcTensor g rA sA) (C : SmoothCcTensor g rC sC)
    (K : ℝ) (hK : 0 ≤ K)
    (hQ : ∀ p : M,
      fiberLpFun g r s Q p ≤
        K * fiberLpFun g rA sA A p * fiberLpFun g rC sC C p) :
    |Inner.inner ℝ V Q| ≤
      K * (lpNorm (fiberLpFun g rA sA A) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) *
        lpNorm (fiberLpFun g rC sC C) 3
          (riemannianVolumeMeasure (I := I) (M := M) g) * ‖V‖) := by
  have hholder := fiber_mul3_l632 (I := I) (M := M) g
    rA sA rC sC r s A C V
  calc
    _ = |Inner.inner ℝ Q V| := congrArg abs (real_inner_comm Q V)
    _ ≤ K * ∫ p,
        fiberLpFun g rA sA A p * fiberLpFun g r s V p *
          fiberLpFun g rC sC C p
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      inner_fiber_le (I := I) (M := M) g r s Q V
        rA sA rC sC A C K hQ
    _ = K * ∫ p,
        fiberLpFun g rA sA A p * fiberLpFun g rC sC C p *
          fiberLpFun g r s V p
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      congr 1
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => by ring)
    _ ≤ _ := mul_le_mul_of_nonneg_left hholder hK

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [BoundarylessManifold I M] in
private theorem inner_fiber_linf22_le
    (g : SmoothRiemannianMetric I M) (r s rA sA rC sC : ℕ)
    (Q V : SmoothCcTensor g r s)
    (A : SmoothCcTensor g rA sA) (C : SmoothCcTensor g rC sC)
    (K KA : ℝ) (hK : 0 ≤ K) (hKA : 0 ≤ KA)
    (hQ : ∀ p : M,
      fiberLpFun g r s Q p ≤
        K * fiberLpFun g rA sA A p * fiberLpFun g rC sC C p)
    (hA : ∀ p : M, fiberLpFun g rA sA A p ≤ KA) :
    |Inner.inner ℝ V Q| ≤ K * (KA * ‖V‖ * ‖C‖) := by
  have hholder := fiber_mul3_linf22 (I := I) (M := M) g
    rA sA r s rC sC A V C KA hKA hA
  calc
    _ = |Inner.inner ℝ Q V| := congrArg abs (real_inner_comm Q V)
    _ ≤ K * ∫ p,
        fiberLpFun g rA sA A p * fiberLpFun g r s V p *
          fiberLpFun g rC sC C p
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      inner_fiber_le (I := I) (M := M) g r s Q V
        rA sA rC sC A C K hQ
    _ ≤ _ := mul_le_mul_of_nonneg_left hholder hK

theorem mixed_derivative_action_pairing_h4_uniform_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ rho C : ℝ, 0 < rho ∧ 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ b : ℕ, b ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ b g gBase Λ) →
        ∀ (T : SmoothCcTensor g 0 2)
          (_hTsymm : ∀ (x : M) (u v : TangentSpace I x),
            ccTensorBilin (I := I) g T x u v =
              ccTensorBilin (I := I) g T x v u)
          {delta : ℝ}, delta ≤ 1 / 3 → 0 ≤ delta →
          ∀ (hdelta : gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g T) delta)
            (hdeltaZ : gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g
                (0 : SmoothCcTensor g 0 2)) delta),
          ∀ {a : ℝ}, a ∈ Set.Icc (0 : ℝ) 1 →
          ∀ {R : ℝ}, 0 ≤ R → R ≤ rho →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
          let gm := DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricPerturbationPath
            (I := I) g T 0 hdelta hdeltaZ a
          let B : SmoothCcTensor g 4 2 :=
            lieDecomposition2 (I := I) (M := M) g T hdelta hdeltaZ a +
              (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gm -
                deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g) +
              (-2 * a : ℝ) •
                RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T
          let HT : SmoothCcTensor g 0 4 :=
            iteratedCovGrad (I := I) g 0 2 2 T
          let V : SmoothCcTensor g 0 2 :=
            oneMinusConnLapSmooth (I := I) g 0 2
              (oneMinusConnLapSmooth (I := I) g 0 2 T)
          let Tr : SmoothCcTensor g 4 2 :=
            DeTurck.cometricDoubleTraceField (I := I) g 2
          let P20 : SmoothCcTensor g 0 2 :=
            operatorFieldApply (I := I) (M := M) g 4 2 Tr
              (operatorFieldApply (I := I) (M := M) g 4 4
                (covGrad (I := I) (M := M) g 4 3
                  (covGrad (I := I) (M := M) g 4 2 B)) HT)
          let P11L : SmoothCcTensor g 0 2 :=
            operatorFieldApply (I := I) (M := M) g 4 2 Tr
              (operatorFieldApply (I := I) (M := M) g 5 4
                (slotExtend (I := I) (M := M) g 4 3
                  (covGrad (I := I) (M := M) g 4 2 B))
                (covGrad (I := I) (M := M) g 0 4 HT))
          let P11R : SmoothCcTensor g 0 2 :=
            operatorFieldApply (I := I) (M := M) g 4 2 Tr
              (operatorFieldApply (I := I) (M := M) g 5 4
                (covGrad (I := I) (M := M) g 5 3
                  (slotExtend (I := I) (M := M) g 4 2 B))
                (covGrad (I := I) (M := M) g 0 4 HT))
          2 * (|tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P20.toFun| +
              |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11L.toFun| +
              |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11R.toFun|) ≤
            C * R *
              ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 := by
  classical
  obtain ⟨rhoB, CB, hrhoB, hCB, hedge⟩ :=
    ricciDeTurckTopOrderCoefficient_h3_uniform_bound (I := I) (M := M) hDim gBase hΛ
  obtain ⟨rhoTr, Cp, Cj, hrhoTr, hCp, hCj, hpure⟩ :=
    pureTrace_h3_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨C6B, hC6B, h6B⟩ :=
    h1Lp6RS_uniform (I := I) (M := M) hDim gBase hΛ 4 4
  obtain ⟨C6T, hC6T, h6T⟩ :=
    h1Lp6RS_uniform (I := I) (M := M) hDim gBase hΛ 0 4
  obtain ⟨C63, hC63, h63⟩ :=
    fiber_lp_three_le_uniform_constant_mul_lp_six (I := I) (M := M) gBase Λ
  obtain ⟨Cmor, hCmor, hmor⟩ :=
    morreyRS_uniform (I := I) (M := M) hDim gBase hΛ 4 3
  obtain ⟨Kcurv, hKcurv⟩ :=
    exists_uniform_curvature_action_parameters (I := I) (M := M) gBase hΛ
  let C3 : ℝ := h3CovsumC Kcurv.rankTwo Kcurv.rankThree
  let n : ℝ := Module.finrank ℝ E
  let Kn : ℝ := Real.sqrt n
  let C20 : ℝ := Cp * C6B * CB * C63 * C6T * C3
  let C11 : ℝ := Cp * Kn * Cmor * CB * C3
  let C : ℝ := 2 * (C20 + 2 * C11)
  have hC3 : 0 ≤ C3 := by
    dsimp only [C3]
    exact h3CovsumC_nonneg _ _
  have hn : 0 ≤ n := by dsimp only [n]; positivity
  have hKn : 0 ≤ Kn := by dsimp only [Kn]; positivity
  have hC20 : 0 ≤ C20 := by dsimp only [C20]; positivity
  have hC11 : 0 ≤ C11 := by dsimp only [C11]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨min rhoB rhoTr, C, lt_min hrhoB hrhoTr, hC, ?_⟩
  intro g hEq hjet T hTsymm delta hdelta_le hdelta0 hdelta hdeltaZ
    a ha R hR hRrho hT2
  let gm : SmoothRiemannianMetric I M :=
    DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricPerturbationPath
      (I := I) g T 0 hdelta hdeltaZ a
  let B : SmoothCcTensor g 4 2 :=
    lieDecomposition2 (I := I) (M := M) g T hdelta hdeltaZ a +
      (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gm -
        deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g) +
      (-2 * a : ℝ) • RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient
        (I := I) (M := M) g gm T
  let HT : SmoothCcTensor g 0 4 :=
    iteratedCovGrad (I := I) g 0 2 2 T
  let D3T : SmoothCcTensor g 0 5 :=
    covGrad (I := I) (M := M) g 0 4 HT
  let A20 : SmoothCcTensor g 4 4 :=
    covGrad (I := I) (M := M) g 4 3
      (covGrad (I := I) (M := M) g 4 2 B)
  let A11 : SmoothCcTensor g 4 3 :=
    covGrad (I := I) (M := M) g 4 2 B
  let A11L : SmoothCcTensor g 5 4 :=
    slotExtend (I := I) (M := M) g 4 3 A11
  let A11R : SmoothCcTensor g 5 4 :=
    covGrad (I := I) (M := M) g 5 3
      (slotExtend (I := I) (M := M) g 4 2 B)
  let V : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2
      (oneMinusConnLapSmooth (I := I) g 0 2 T)
  let Tr : SmoothCcTensor g 4 2 :=
    DeTurck.cometricDoubleTraceField (I := I) g 2
  let P20 : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 4 2 Tr
      (operatorFieldApply (I := I) (M := M) g 4 4 A20 HT)
  let P11L : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 4 2 Tr
      (operatorFieldApply (I := I) (M := M) g 5 4 A11L D3T)
  let P11R : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 4 2 Tr
      (operatorFieldApply (I := I) (M := M) g 5 4 A11R D3T)
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
  have hsum3 :
      (∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 0 2 j T‖) ≤ C3 * y := by
    simpa only [C3, y] using
      (covsum_hs_three (I := I) (M := M) g 2 hact2 hact3 T)
  have hT2B :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ rhoB :=
    hT2.trans (hRrho.trans (min_le_left _ _))
  have hBjet :
      (∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 4 2 j B‖ ^ 2) ≤
          (CB * y) ^ 2 := by
    simpa only [B, gm, y] using
      hedge g hEq hjet T hTsymm hdelta_le hdelta0 hdelta hdeltaZ hT2B ha
  have hzero2 :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (0 : SmoothCcTensor g 0 2)‖ ≤ rhoTr := by
    rw [show (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
      ccTensorToHs_smul, zero_smul, norm_zero]
    exact le_of_lt hrhoTr
  have hzeroTie : ∀ (p : M) (u v : TangentSpace I p),
      g.inner p u v = g.inner p u v +
        ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2) p u v := by
    intro p u v
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight,
      ccTensorBilin_zero_weight]
    ring
  have hTrpure : Tr = pureTrace (I := I) (M := M) g g 2 := by
    apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro x
    rw [pureTrace_toSection,
      DifferentialGeometry.Analysis.Spectral.DeTurck.cometricDoubleTraceField_toSection]
  have hTr : ∀ p : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 p
        (Tr.toSection p) ≤ Cp ^ 2 := by
    have hp := hpure g hEq hjet (0 : SmoothCcTensor g 0 2) g
      hdelta_le hdelta0 hdeltaZ hzero2 hzeroTie
    rw [hTrpure]
    exact hp.1
  have hA20H1sq :
      ‖(⟨A20⟩ : SmoothCcTensorH1 g 4 4)‖ ^ 2 ≤ (CB * y) ^ 2 := by
    have hshift := iter_two_h1_le_jet_four
      (I := I) (M := M) g 4 2 B
    simpa only [A20, iteratedCovGrad_succ, iteratedCovGrad_zero,
      Nat.zero_add] using hshift.trans hBjet
  have hA20H1 :
      ‖(⟨A20⟩ : SmoothCcTensorH1 g 4 4)‖ ≤ CB * y :=
    le_of_sq_le_sq hA20H1sq (mul_nonneg hCB hy)
  have hA20L6 :
      lpNorm (fiberLpFun g 4 4 A20) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        C6B * (CB * y) := by
    calc
      _ ≤ C6B * ‖(⟨A20⟩ : SmoothCcTensorH1 g 4 4)‖ := by
        change lpNorm (fun x => Real.sqrt
          (riemannianFiberNormSq (I := I) (M := M) g 4 4 x (A20.toSection x))) 6
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          C6B * ‖(⟨A20⟩ : SmoothCcTensorH1 g 4 4)‖
        exact h6B g hEq hjet1 (⟨A20⟩ : SmoothCcTensorH1 g 4 4)
      _ ≤ C6B * (CB * y) :=
        mul_le_mul_of_nonneg_left hA20H1 hC6B
  have hHTH1root :
      ‖(⟨HT⟩ : SmoothCcTensorH1 g 0 4)‖ ≤ ‖HT‖ + ‖D3T‖ := by
    have hsq : ‖(⟨HT⟩ : SmoothCcTensorH1 g 0 4)‖ ^ 2 =
        ‖HT‖ ^ 2 + ‖D3T‖ ^ 2 := by
      rw [smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M)]
    refine le_of_sq_le_sq ?_
      (add_nonneg (norm_nonneg HT) (norm_nonneg D3T))
    rw [hsq]
    nlinarith [mul_nonneg (norm_nonneg HT) (norm_nonneg D3T)]
  have hHTtail : ‖HT‖ + ‖D3T‖ ≤
      ∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 0 2 j T‖ := by
    dsimp only [HT, D3T]
    rw [show covGrad (I := I) (M := M) g 0 4
        (iteratedCovGrad (I := I) g 0 2 2 T) =
          iteratedCovGrad (I := I) g 0 2 3 T by rfl]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      iteratedCovGrad_zero, Nat.reduceAdd]
    nlinarith [norm_nonneg T,
      norm_nonneg (iteratedCovGrad (I := I) g 0 2 1 T)]
  have hHTH1 :
      ‖(⟨HT⟩ : SmoothCcTensorH1 g 0 4)‖ ≤ C3 * y :=
    hHTH1root.trans (hHTtail.trans hsum3)
  have hHTL6 :
      lpNorm (fiberLpFun g 0 4 HT) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        C6T * (C3 * y) := by
    calc
      _ ≤ C6T * ‖(⟨HT⟩ : SmoothCcTensorH1 g 0 4)‖ := by
        change lpNorm (fun x => Real.sqrt
          (riemannianFiberNormSq (I := I) (M := M) g 0 4 x (HT.toSection x))) 6
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          C6T * ‖(⟨HT⟩ : SmoothCcTensorH1 g 0 4)‖
        exact h6T g hEq hjet1 (⟨HT⟩ : SmoothCcTensorH1 g 0 4)
      _ ≤ C6T * (C3 * y) :=
        mul_le_mul_of_nonneg_left hHTH1 hC6T
  have hHTL3 :
      lpNorm (fiberLpFun g 0 4 HT) 3
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        C63 * (C6T * (C3 * y)) := by
    calc
      _ ≤ C63 * lpNorm (fiberLpFun g 0 4 HT) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) :=
        h63 g hEq 0 4 HT
      _ ≤ C63 * (C6T * (C3 * y)) :=
        mul_le_mul_of_nonneg_left hHTL6 hC63
  have hA11jet :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 4 3 j A11‖ ^ 2) ≤
          (CB * y) ^ 2 := by
    have hshift := covgrad_jet_three_le_four
      (I := I) (M := M) g 4 2 B
    simpa only [A11] using hshift.trans hBjet
  have hA11riemannianFiberNormSq : ∀ p : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 3 p
          (A11.toSection p) ≤ (Cmor * CB * y) ^ 2 := by
    intro p
    calc
      _ ≤ Cmor ^ 2 * ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 4 3 j A11‖ ^ 2 :=
        hmor g hEq hjet1 hjet2 A11 p
      _ ≤ Cmor ^ 2 * (CB * y) ^ 2 :=
        mul_le_mul_of_nonneg_left hA11jet (sq_nonneg Cmor)
      _ = (Cmor * CB * y) ^ 2 := by ring
  have hKnSq : Kn ^ 2 = n := by
    dsimp only [Kn]
    exact Real.sq_sqrt hn
  have hA11LriemannianFiberNormSq : ∀ p : M,
      riemannianFiberNormSq (I := I) (M := M) g 5 4 p
          (A11L.toSection p) ≤ (Kn * Cmor * CB * y) ^ 2 := by
    intro p
    rw [show riemannianFiberNormSq (I := I) (M := M) g 5 4 p
        (A11L.toSection p) = n *
          riemannianFiberNormSq (I := I) (M := M) g 4 3 p
            (A11.toSection p) by
      simpa only [A11L, n] using
        riemannianFiberNormSq_slotExtend_eq (I := I) (M := M) g 4 3 A11 p]
    calc
      _ ≤ n * (Cmor * CB * y) ^ 2 :=
        mul_le_mul_of_nonneg_left (hA11riemannianFiberNormSq p) hn
      _ = (Kn * Cmor * CB * y) ^ 2 := by rw [← hKnSq]; ring
  have hA11RriemannianFiberNormSq : ∀ p : M,
      riemannianFiberNormSq (I := I) (M := M) g 5 4 p
          (A11R.toSection p) ≤ (Kn * Cmor * CB * y) ^ 2 := by
    intro p
    rw [show riemannianFiberNormSq (I := I) (M := M) g 5 4 p
        (A11R.toSection p) =
          riemannianFiberNormSq (I := I) (M := M) g 5 4 p
            ((slotExtend (I := I) (M := M) g 4 3 A11).toSection p) by
      simpa only [A11R, A11] using
        riemannianFiberNormSq_covGrad_slotExtend_eq (I := I) (M := M) g 4 2 B p]
    exact hA11LriemannianFiberNormSq p
  have hA11Lcap : ∀ p : M,
      fiberLpFun g 5 4 A11L p ≤ Kn * Cmor * CB * y := by
    intro p
    have hsqrt := Real.sqrt_le_sqrt (hA11LriemannianFiberNormSq p)
    simpa only [fiberLpFun, tensorPointwiseNorm,
      Real.sqrt_sq (mul_nonneg
        (mul_nonneg (mul_nonneg hKn hCmor) hCB) hy)] using hsqrt
  have hA11Rcap : ∀ p : M,
      fiberLpFun g 5 4 A11R p ≤ Kn * Cmor * CB * y := by
    intro p
    have hsqrt := Real.sqrt_le_sqrt (hA11RriemannianFiberNormSq p)
    simpa only [fiberLpFun, tensorPointwiseNorm,
      Real.sqrt_sq (mul_nonneg
        (mul_nonneg (mul_nonneg hKn hCmor) hCB) hy)] using hsqrt
  have hD3T : ‖D3T‖ ≤ C3 * y := by
    calc
      _ ≤ ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ := by
        dsimp only [D3T, HT]
        rw [show covGrad (I := I) (M := M) g 0 4
            (iteratedCovGrad (I := I) g 0 2 2 T) =
              iteratedCovGrad (I := I) g 0 2 3 T by rfl]
        exact Finset.single_le_sum (s := Finset.range 4)
          (f := fun j : ℕ => ‖iteratedCovGrad (I := I) g 0 2 j T‖)
          (fun j _ => norm_nonneg _) (show 3 ∈ Finset.range 4 by norm_num)
      _ ≤ C3 * y := hsum3
  have hVnorm : ‖V‖ = z := by
    have heven := smoothCcToTensorHs_even_norm_eq_toL2_iter
      (I := I) (M := M) g 2 T
    change ‖smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) T‖ =
      ‖SmoothCcTensor.toL2 V‖ at heven
    rw [SmoothCcTensor.norm_toL2] at heven
    simpa only [z, norm_ccHs_eq_smoothHs] using heven.symm
  have hP20point : ∀ p : M,
      fiberLpFun g 0 2 P20 p ≤
        Cp * fiberLpFun g 4 4 A20 p * fiberLpFun g 0 4 HT p := by
    simpa only [P20, operatorFieldComposition_zero_eq_operatorFieldApply] using
      fiber_app_app_le (I := I) (M := M) g 0 4 4 2 Cp hCp
        Tr A20 HT hTr
  have hP11Lpoint : ∀ p : M,
      fiberLpFun g 0 2 P11L p ≤
        Cp * fiberLpFun g 5 4 A11L p * fiberLpFun g 0 5 D3T p := by
    simpa only [P11L, operatorFieldComposition_zero_eq_operatorFieldApply] using
      fiber_app_app_le (I := I) (M := M) g 0 5 4 2 Cp hCp
        Tr A11L D3T hTr
  have hP11Rpoint : ∀ p : M,
      fiberLpFun g 0 2 P11R p ≤
        Cp * fiberLpFun g 5 4 A11R p * fiberLpFun g 0 5 D3T p := by
    simpa only [P11R, operatorFieldComposition_zero_eq_operatorFieldApply] using
      fiber_app_app_le (I := I) (M := M) g 0 5 4 2 Cp hCp
        Tr A11R D3T hTr
  have hbase20 := inner_fiber_l632_le (I := I) (M := M) g
    0 2 4 4 0 4 P20 V A20 HT Cp hCp hP20point
  have hterm20 : |Inner.inner ℝ V P20| ≤ C20 * y ^ 2 * z := by
    calc
      _ ≤ Cp *
          (lpNorm (fiberLpFun g 4 4 A20) 6
              (riemannianVolumeMeasure (I := I) (M := M) g) *
            lpNorm (fiberLpFun g 0 4 HT) 3
              (riemannianVolumeMeasure (I := I) (M := M) g) * ‖V‖) :=
        hbase20
      _ ≤ Cp *
          ((C6B * (CB * y)) *
            lpNorm (fiberLpFun g 0 4 HT) 3
              (riemannianVolumeMeasure (I := I) (M := M) g) * ‖V‖) := by
        apply mul_le_mul_of_nonneg_left _ hCp
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg V)
        exact mul_le_mul_of_nonneg_right hA20L6 lpNorm_nonneg
      _ ≤ Cp *
          ((C6B * (CB * y)) * (C63 * (C6T * (C3 * y))) * ‖V‖) := by
        apply mul_le_mul_of_nonneg_left _ hCp
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg V)
        exact mul_le_mul_of_nonneg_left hHTL3
          (mul_nonneg hC6B (mul_nonneg hCB hy))
      _ = C20 * y ^ 2 * z := by
        rw [hVnorm]
        dsimp only [C20]
        ring
  have hcap11 : 0 ≤ Kn * Cmor * CB * y := by positivity
  have hbase11L := inner_fiber_linf22_le (I := I) (M := M) g
    0 2 5 4 0 5 P11L V A11L D3T Cp (Kn * Cmor * CB * y)
      hCp hcap11 hP11Lpoint hA11Lcap
  have hbase11R := inner_fiber_linf22_le (I := I) (M := M) g
    0 2 5 4 0 5 P11R V A11R D3T Cp (Kn * Cmor * CB * y)
      hCp hcap11 hP11Rpoint hA11Rcap
  have hterm11L : |Inner.inner ℝ V P11L| ≤ C11 * y ^ 2 * z := by
    calc
      _ ≤ Cp * ((Kn * Cmor * CB * y) * ‖V‖ * ‖D3T‖) :=
        hbase11L
      _ ≤ Cp * ((Kn * Cmor * CB * y) * ‖V‖ * (C3 * y)) := by
        apply mul_le_mul_of_nonneg_left _ hCp
        exact mul_le_mul_of_nonneg_left hD3T
          (mul_nonneg hcap11 (norm_nonneg V))
      _ = C11 * y ^ 2 * z := by
        rw [hVnorm]
        dsimp only [C11]
        ring
  have hterm11R : |Inner.inner ℝ V P11R| ≤ C11 * y ^ 2 * z := by
    calc
      _ ≤ Cp * ((Kn * Cmor * CB * y) * ‖V‖ * ‖D3T‖) :=
        hbase11R
      _ ≤ Cp * ((Kn * Cmor * CB * y) * ‖V‖ * (C3 * y)) := by
        apply mul_le_mul_of_nonneg_left _ hCp
        exact mul_le_mul_of_nonneg_left hD3T
          (mul_nonneg hcap11 (norm_nonneg V))
      _ = C11 * y ^ 2 * z := by
        rw [hVnorm]
        dsimp only [C11]
        ring
  have hinterp : y ^ 2 ≤ x * z := by
    dsimp only [x, y, z]
    exact ccTensorToHs_norm_three_sq_le_norm_two_mul_norm_four
      (I := I) (M := M) g 2 T
  have hy2Rz : y ^ 2 ≤ R * z :=
    hinterp.trans (mul_le_mul_of_nonneg_right hT2 hz)
  change 2 * (|tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P20.toFun| +
      |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11L.toFun| +
      |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11R.toFun|) ≤
        C * R * z ^ 2
  rw [show tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P20.toFun =
      Inner.inner ℝ V P20 from
        (SmoothCcTensor.inner_def (I := I) (M := M) V P20).symm,
    show tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11L.toFun =
      Inner.inner ℝ V P11L from
        (SmoothCcTensor.inner_def (I := I) (M := M) V P11L).symm,
    show tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11R.toFun =
      Inner.inner ℝ V P11R from
        (SmoothCcTensor.inner_def (I := I) (M := M) V P11R).symm]
  calc
    2 * (|Inner.inner ℝ V P20| + |Inner.inner ℝ V P11L| +
        |Inner.inner ℝ V P11R|) ≤
      2 * (C20 * y ^ 2 * z + C11 * y ^ 2 * z + C11 * y ^ 2 * z) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (add_le_add hterm20 hterm11L) hterm11R) (by norm_num)
    _ ≤ 2 * (C20 * (R * z) * z + C11 * (R * z) * z +
        C11 * (R * z) * z) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hy2Rz hC20) hz)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hy2Rz hC11) hz))
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hy2Rz hC11) hz)
    _ = C * R * z ^ 2 := by
      dsimp only [C]
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
