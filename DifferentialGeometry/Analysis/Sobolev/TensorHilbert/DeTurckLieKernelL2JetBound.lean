import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBoundPairTrace
open DifferentialGeometry.Tensor.Auxiliary
open DifferentialGeometry.Combinatorics
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle
    ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev
    DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (connectionDifferenceCovDerivBiContrFib deTurckLieConnectionDifferenceDerivativeBiContrFib_contMDiff deTurckLieCovariantDerivativeInsertionFib deTurckLieCovariantDerivativeInsertionFib_contMDiff
    deTurckLieFib deTurckLieCoeffField deTurckLieCoeffField_toSection
    deTurckConnectionDifferenceCovDeriv connectionDifference_pairing_mdiffAt connectionDifferenceCovDerivOp deTurckLieConnectionDifferenceDerivativeCovKernel_apply_extend)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (metricPerturbationPath convexPerturbation metricPerturbationPath_inner_of_mem convexPerturbation_gFibreOpBound_abs
    abs_convex_smallConstant_lt_one metricPerturbationPathDomain)
open DifferentialGeometry.Analysis.Laplacian
  (metric_inner_self_nonneg metric_inner_cauchy_schwarz_sq)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (covGrad connectionDifference_gFibreNorm_le_iteratedCovGrad_of_lt_one deTurckLieConnectionDifferenceDerivativeBiContrFibFixedFrame_toModel)
open DifferentialGeometry.Geometry.Curvature
  (exists_covDerivConnectionDifference_gQuadratic_le_of_jetEnvelope
    abs_tensor_one_three_flat_eval_le_fibreNorm_mul_sqrt)
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
  (g0FlatCLM cotangentToDual_g0FlatCLM g0FlatCLM_apply)

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

section DeTurckLieConnectionDifferenceDerivativeGridBrick

open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

theorem riemannianFiberNormSq_iteratedCovGrad_deTurckLieConnectionDifferenceDerivCoeffField_diagonalProductGrid_le
    (g₀ g_bg : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T)
          δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨CPT, hCPT_nn, hCPT⟩ := exists_deTurckLieConnectionDifferenceDerivativePairTraceOperator_fiberNormSq_antidiagonalTupleGrid_bound (I := I) (M := M) g₀ hδ₀
  obtain ⟨CX, hCX_nn, hCX⟩ := exists_riemannianFiberNormSq_deTurckLieConnectionDifferenceDerivativeSym_tgrid (I := I) (M := M) g₀ g_bg hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => diagonalGridGrowthFactor (E := E) i * ∑ i' ∈ Finset.range (i + 1),
      CPT i' * ∑ l ∈ Finset.range (i + 1 - i'),
        (fr * (fr * CX l)) * antidiagonalTuplePairCount (i' + 1) (l + 3),
    fun i => mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun i' _ => mul_nonneg (hCPT_nn i')
        (Finset.sum_nonneg fun l _ => mul_nonneg
          (mul_nonneg hfr_nn (mul_nonneg hfr_nn (hCX_nn l))) (antidiagonalTuplePairCount_nonneg _ _))), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set W : ℝ := antidiagonalTupleGridPartialSum b (i + 3) with hW_def
  have hW_nn : 0 ≤ W := antidiagonalTupleGridPartialSum_nonneg b hb (i + 3)
  have hXtower : ∀ l, l ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (deTurckLieConnectionDifferenceDerivativeSymCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) ≤
      CX l * antidiagonalTupleGridPartialSum b (l + 3) := by
    intro l _
    exact hCX g₁ T htie hδ_le hδ0 hbound l x
  have hWtower : ∀ l, l ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 deTurckLieConnectionDifferenceDerivativeInputPermutation
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (deTurckLieConnectionDifferenceDerivativeSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x) ≤
      (fr * (fr * CX l)) * antidiagonalTupleGridPartialSum b (l + 3) := by
    intro l hl
    have hperm : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 deTurckLieConnectionDifferenceDerivativeInputPermutation
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (deTurckLieConnectionDifferenceDerivativeSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (deTurckLieConnectionDifferenceDerivativeSymCc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) :=
      riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 2 6
        deTurckLieConnectionDifferenceDerivativeInputPermutation
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (deTurckLieConnectionDifferenceDerivativeSymCc (I := I) (M := M) g₀ T g₁ g_bg))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 deTurckLieConnectionDifferenceDerivativeInputPermutation
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (deTurckLieConnectionDifferenceDerivativeSymCc (I := I) (M := M) g₀ T g₁ g_bg)))
        (fun y d => by
          rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) l x
    rw [hperm]
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (deTurckLieConnectionDifferenceDerivativeSymCc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) ≤
        fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 5 l
            (slotExtendIter (I := I) (M := M) g₀ 0 4 1
              (deTurckLieConnectionDifferenceDerivativeSymCc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) :=
      riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
        (slotExtendIter (I := I) (M := M) g₀ 0 4 1
          (deTurckLieConnectionDifferenceDerivativeSymCc (I := I) (M := M) g₀ T g₁ g_bg)) l x
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 5 l
          (slotExtendIter (I := I) (M := M) g₀ 0 4 1
            (deTurckLieConnectionDifferenceDerivativeSymCc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) ≤
        fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (deTurckLieConnectionDifferenceDerivativeSymCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) :=
      riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4
        (deTurckLieConnectionDifferenceDerivativeSymCc (I := I) (M := M) g₀ T g₁ g_bg) l x
    have h3 := hXtower l hl
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (deTurckLieConnectionDifferenceDerivativeSymCc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x)
        ≤ fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 5 l
              (slotExtendIter (I := I) (M := M) g₀ 0 4 1
                (deTurckLieConnectionDifferenceDerivativeSymCc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) := h1
      _ ≤ fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (deTurckLieConnectionDifferenceDerivativeSymCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x)) :=
          mul_le_mul_of_nonneg_left h2 hfr_nn
      _ ≤ fr * (fr * (CX l * antidiagonalTupleGridPartialSum b (l + 3))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hfr_nn) hfr_nn
      _ = (fr * (fr * CX l)) * antidiagonalTupleGridPartialSum b (l + 3) := by ring
  have hlift : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (deTurckLieConnectionDifferenceDerivativePairTraceOperator (I := I) (M := M) g₀ g₁)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 deTurckLieConnectionDifferenceDerivativeInputPermutation
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (deTurckLieConnectionDifferenceDerivativeSymCc (I := I) (M := M) g₀ T g₁ g_bg))))).toSection x) := by
    rw [deTurckLieConnectionDifferenceDerivCoeffField_eq_pairTrace (I := I) (M := M) g₀ g_bg g₁ T htie]
    rw [iteratedCovGrad_smul]
    rw [show (((-1 : ℝ) • iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (deTurckLieConnectionDifferenceDerivativePairTraceOperator (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 deTurckLieConnectionDifferenceDerivativeInputPermutation
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (deTurckLieConnectionDifferenceDerivativeSymCc (I := I) (M := M) g₀ T g₁ g_bg))))).toSection x) =
        (-1 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (deTurckLieConnectionDifferenceDerivativePairTraceOperator (I := I) (M := M) g₀ g₁)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 deTurckLieConnectionDifferenceDerivativeInputPermutation
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (deTurckLieConnectionDifferenceDerivativeSymCc (I := I) (M := M) g₀ T g₁ g_bg))))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]
      rfl]
    rw [riemannianFiberNormSq_smul_deTurckLieConnectionDifferenceDerivative (I := I) (M := M) g₀ 2 (2 + i) x]
    ring
  rw [hlift]
  refine le_trans
    (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ i 2 6 2
    (deTurckLieConnectionDifferenceDerivativePairTraceOperator (I := I) (M := M) g₀ g₁)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 deTurckLieConnectionDifferenceDerivativeInputPermutation
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (deTurckLieConnectionDifferenceDerivativeSymCc (I := I) (M := M) g₀ T g₁ g_bg))) x) ?_
  have hcell : ∀ i' ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + i') x
          ((iteratedCovGrad (I := I) g₀ 6 2 i'
            (deTurckLieConnectionDifferenceDerivativePairTraceOperator (I := I) (M := M) g₀ g₁)).toSection x) *
        ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 6 l
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 deTurckLieConnectionDifferenceDerivativeInputPermutation
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (deTurckLieConnectionDifferenceDerivativeSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x) ≤
      (CPT i' * ∑ l ∈ Finset.range (i + 1 - i'),
        (fr * (fr * CX l)) * antidiagonalTuplePairCount (i' + 1) (l + 3)) * W := by
    intro i' hi'
    rw [Finset.mem_range] at hi'
    have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 6 2 i'
          (deTurckLieConnectionDifferenceDerivativePairTraceOperator (I := I) (M := M) g₀ g₁)).toSection x) ≤
        CPT i' * antidiagonalTupleGridPartialSum b (i' + 1) :=
      hCPT g₁ T htie hδ_le hδ0 hbound i' x
    have hA2 : (∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 deTurckLieConnectionDifferenceDerivativeInputPermutation
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (deTurckLieConnectionDifferenceDerivativeSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x)) ≤
        ∑ l ∈ Finset.range (i + 1 - i'), (fr * (fr * CX l)) * antidiagonalTupleGridPartialSum b
          (l + 3) := by
      refine Finset.sum_le_sum fun l hl => ?_
      rw [Finset.mem_range] at hl
      exact hWtower l (by omega)
    have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 deTurckLieConnectionDifferenceDerivativeInputPermutation
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (deTurckLieConnectionDifferenceDerivativeSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + l) x _
    have hA1_rhs_nn : 0 ≤ CPT i' * antidiagonalTupleGridPartialSum b (i' + 1) :=
      mul_nonneg (hCPT_nn i') (antidiagonalTupleGridPartialSum_nonneg b hb (i' + 1))
    refine le_trans (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn) ?_
    rw [Finset.mul_sum]
    rw [show (CPT i' * ∑ l ∈ Finset.range (i + 1 - i'),
        (fr * (fr * CX l)) * antidiagonalTuplePairCount (i' + 1) (l + 3)) * W =
        ∑ l ∈ Finset.range (i + 1 - i'),
          (CPT i' * ((fr * (fr * CX l)) * antidiagonalTuplePairCount (i' + 1) (l + 3))) * W from by
      rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [Finset.mem_range] at hl
    have hpair : antidiagonalTupleGridPartialSum b (i' + 1) * antidiagonalTupleGridPartialSum b
      (l + 3) ≤
        antidiagonalTuplePairCount (i' + 1) (l + 3) * antidiagonalTupleGridPartialSum b (i + 3) :=
      antidiagonalTupleGridPartialSum_mul_le b hb (i' + 1) (l + 3) (i + 3) (by omega)
    calc CPT i' * antidiagonalTupleGridPartialSum b (i' + 1) *
           ((fr * (fr * CX l)) * antidiagonalTupleGridPartialSum b (l + 3))
        = (CPT i' * (fr * (fr * CX l))) *
            (antidiagonalTupleGridPartialSum b (i' + 1) * antidiagonalTupleGridPartialSum b (l + 3))
              := by ring
      _ ≤ (CPT i' * (fr * (fr * CX l))) *
            (antidiagonalTuplePairCount (i' + 1) (l + 3) * antidiagonalTupleGridPartialSum b
              (i + 3)) := by
          refine mul_le_mul_of_nonneg_left hpair ?_
          exact mul_nonneg (hCPT_nn i')
            (mul_nonneg hfr_nn (mul_nonneg hfr_nn (hCX_nn l)))
      _ = (CPT i' * ((fr * (fr * CX l)) * antidiagonalTuplePairCount (i' + 1) (l + 3))) * W := by
          rw [hW_def]
          ring
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
    (operatorFieldApplicationGdiag_nonneg (E := E) i)) ?_
  rw [← Finset.sum_mul, ← mul_assoc]
  beta_reduce
  rw [hW_def]
  rfl

open DifferentialGeometry.PDE.DeTurck.RicciLinearization (Icc_subset_metricPerturbationPathDomain) in
theorem deTurckLieConnectionDifferenceDerivCoeffField_metricPerturbationPath_jetL2_perOrder_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieConnectionDifferenceDerivCoeffField (I := I) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤ P i := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_nn : 0 ≤ δ₁ := le_max_right _ _
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  obtain ⟨C, hC_nn, hC⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_deTurckLieConnectionDifferenceDerivCoeffField_diagonalProductGrid_le
      (I := I) (M := M) g₀ g_bg hδ₁_lt
  obtain ⟨K, hK_nn, hK⟩ :=
    antidiagonalTupleGrid_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => C i * ∑ k ∈ Finset.range (i + 3),
      K k * (1 + ((a + 3 : ℕ) : ℝ) * R ^ 2),
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg fun k _ =>
      mul_nonneg (hK_nn k) (by positivity)), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set g₁ : SmoothRiemannianMetric I M := metricPerturbationPath (I := I) g₀ T T' hδ hδ' s with hg₁_def
  set Pc : SmoothCcTensor g₀ 0 2 := convexPerturbation (I := I) g₀ T T' s with hPc_def
  have hδs_raw : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ Pc)
      (|1 - s| * δ' + |s| * δ) := by
    rw [hPc_def]
    exact convexPerturbation_gFibreOpBound_abs (I := I) g₀ T T' hδ hδ' s
  set δP : ℝ := max (|1 - s| * δ' + |s| * δ) 0 with hδP_def
  have hδP_nn : 0 ≤ δP := le_max_right _ _
  have hδP_bound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ Pc)
    δP :=
    gFibreOpBound_mono_of_le (I := I) (M := M) g₀ _ (le_max_left _ _) hδs_raw
  have hδP_le : δP ≤ δ₁ := by
    refine max_le ?_ hδ₁_nn
    rw [abs_of_nonneg h1ms, abs_of_nonneg hs0]
    have h1 : δ' ≤ δ₁ := le_trans hδ'_le (le_max_left _ _)
    have h2 : δ ≤ δ₁ := le_trans hδ_le (le_max_left _ _)
    nlinarith only [h1, h2, hs0, h1ms]
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ Pc y v w := by
    intro y v w
    rw [hg₁_def, hPc_def]
    exact metricPerturbationPath_inner_of_mem (I := I) g₀ T T' hδ hδ'
      (Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt hs) y v w
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j Pc‖ ≤ R := by
    intro j hj
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j Pc
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [hPc_def]
      rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, iteratedCovGrad_smul, iteratedCovGrad_smul]
    rw [heq]
    calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
            + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
        ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
      _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg h1ms, abs_of_nonneg hs0]
      _ ≤ (1 - s) * R + s * R :=
          add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
            (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
      _ = R := by ring
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        C i * ∑ k ∈ Finset.range (i + 3),
          ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) Pc).toSection x) :=
    fun x => hC g₁ Pc htie hδP_le hδP_nn hδP_bound i x
  have hint_k : ∀ k ∈ Finset.range (i + 3), MeasureTheory.Integrable
      (fun x => ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) Pc).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    fun k _ => (hK Pc hPball k).1
  have hint : MeasureTheory.Integrable
      (fun x => C i * ∑ k ∈ Finset.range (i + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) Pc).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (MeasureTheory.integrable_finset_sum (Finset.range (i + 3)) hint_k).const_mul (C i)
  have hnorm := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
    (iteratedCovGrad (I := I) g₀ 2 2 i
      (deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg))
    (fun x => C i * ∑ k ∈ Finset.range (i + 3),
      ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) Pc).toSection x))
    hint hpt
  refine le_trans hnorm ?_
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_finset_sum (Finset.range (i + 3)) hint_k]
  refine mul_le_mul_of_nonneg_left ?_ (hC_nn i)
  refine Finset.sum_le_sum fun k hk => ?_
  rw [Finset.mem_range] at hk
  refine le_trans (hK Pc hPball k).2 ?_
  refine mul_le_mul_of_nonneg_left ?_ (hK_nn k)
  have hsum_le : (∑ j ∈ Finset.range (k + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j Pc‖ ^ 2) ≤ ((a + 3 : ℕ) : ℝ) * R ^ 2 := by
    calc (∑ j ∈ Finset.range (k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j Pc‖ ^ 2)
        ≤ ∑ j ∈ Finset.range (k + 1), R ^ 2 := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [Finset.mem_range] at hj
          have hjle : j ≤ a + 2 := by omega
          have h := hPball j hjle
          nlinarith only [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j Pc), h, hR]
      _ = ((k + 1 : ℕ) : ℝ) * R ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ((a + 3 : ℕ) : ℝ) * R ^ 2 := by
          have hcast : ((k + 1 : ℕ) : ℝ) ≤ ((a + 3 : ℕ) : ℝ) := by
            exact_mod_cast (by omega : k + 1 ≤ a + 3)
          exact mul_le_mul_of_nonneg_right hcast (sq_nonneg R)
  linarith [hsum_le]

namespace DeTurckLieConnectionDifferenceDerivativeUniformInternal

noncomputable abbrev deTurckLieConnectionDifferenceDerivativeKernel := @deTurckLieConnectionDifferenceDerivativeKernelRaisedCc
noncomputable abbrev deTurckLieConnectionDifferenceDerivativeLowered := @deTurckLieConnectionDifferenceDerivativeLoweredCc
noncomputable abbrev deTurckLieConnectionDifferenceDerivativeQuad := @deTurckLieConnectionDifferenceDerivativeQuadCc
noncomputable abbrev deTurckLieConnectionDifferenceDerivativePerturb := @deTurckLieConnectionDifferenceDerivativePerturbSharpEndoField
noncomputable abbrev deTurckLieConnectionDifferenceDerivativeLoweredPerturb := @deTurckLieConnectionDifferenceDerivativeLoweredPerturbCc
noncomputable abbrev deTurckLieConnectionDifferenceDerivativeLoweredG1 := @deTurckLieConnectionDifferenceDerivativeLoweredG1Cc
noncomputable abbrev deTurckLieConnectionDifferenceDerivativeSym := @deTurckLieConnectionDifferenceDerivativeSymCc
noncomputable abbrev deTurckLieConnectionDifferenceDerivativePairTrace := @deTurckLieConnectionDifferenceDerivativePairTraceOperator
abbrev deTurckLieConnectionDifferenceDerivativeSigma := @deTurckLieConnectionDifferenceDerivativeInputPermutation

theorem pair_nonneg (m1 m2 : ℕ) : 0 ≤ antidiagonalTuplePairCount m1 m2 :=
  antidiagonalTuplePairCount_nonneg m1 m2

theorem grid_mul_le (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (m1 m2 m3 : ℕ)
    (h3 : m1 + m2 ≤ m3 + 1) :
    antidiagonalTupleGridPartialSum b m1 * antidiagonalTupleGridPartialSum b m2 ≤
      antidiagonalTuplePairCount m1 m2 * antidiagonalTupleGridPartialSum b m3 :=
  antidiagonalTupleGridPartialSum_mul_le b hb m1 m2 m3 h3

theorem quad_tower
    (g₀ ga gb : SmoothRiemannianMetric I M)
    (j : ℕ) (x : M) (b : ℕ → ℝ) (hb : ∀ l, 0 ≤ b l)
    (Ba Bb : ℕ → ℝ) (hBa_nn : ∀ i, 0 ≤ Ba i) (hBb_nn : ∀ l, 0 ≤ Bb l)
    (harm : ∀ i, i ≤ j →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 2 i
          (connectionDifferenceSection (I := I) ga g₀)).toSection x) ≤
      Ba i * antidiagonalTupleGridPartialSum b (i + 2))
    (hin : ∀ l, l ≤ j →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 2 l
          (connectionDifferenceSection (I := I) gb g₀)).toSection x) ≤
      Bb l * antidiagonalTupleGridPartialSum b (l + 2)) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + j) x
        ((iteratedCovGrad (I := I) g₀ 1 3 j
          (deTurckLieConnectionDifferenceDerivativeQuad (I := I) (M := M) g₀ ga gb)).toSection x) ≤
      (operatorFieldApplicationGdiag (E := E) j * ∑ i ∈ Finset.range (j + 1),
        (Module.finrank ℝ E : ℝ) * Ba i *
          ∑ l ∈ Finset.range (j + 1 - i),
            Bb l * antidiagonalTuplePairCount (i + 2) (l + 2)) *
        antidiagonalTupleGridPartialSum b (j + 3) :=
  deTurckLieConnectionDifferenceDerivativeQuad_tower_of_factors (I := I) (M := M) g₀ ga gb j x b hb
    Ba Bb hBa_nn hBb_nn harm hin

omit [NeZero (Module.finrank ℝ E)] in
theorem lower_raise (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    cometricRaiseSlot0Field (I := I) (M := M) g₀ 2
        (deTurckLieConnectionDifferenceDerivativeLowered (I := I) (M := M) g₀ g₁ g_bg) =
      deTurckLieConnectionDifferenceDerivativeKernel (I := I) (M := M) g₀ g₁ g_bg :=
  deTurckLieConnectionDifferenceDerivativeLoweredCc_raise_repr (I := I) (M := M) g₀ g₁ g_bg

theorem insert_riemannianFiberNormSq (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + j) x
        ((iteratedCovGrad (I := I) g₀ 4 4 j
          (slotInsertEndoCc (I := I) (M := M) g₀ 3
            (deTurckLieConnectionDifferenceDerivativePerturb (I := I) (M := M) g₀ T))).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j
            (symmS (I := I) (M := M) g₀ T)).toSection x) :=
  riemannianFiberNormSq_iteratedCovGrad_slotInsert3_deTurckLieConnectionDifferenceDerivativePerturb_le (I := I) (M := M) g₀ T j x

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (c : ℝ)
    (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v :=
  riemannianFiberNormSq_smul_deTurckLieConnectionDifferenceDerivative
    (I := I) (M := M) g r s x c v

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem pair_trace_def (g₀ g₁ : SmoothRiemannianMetric I M) :
    deTurckLieConnectionDifferenceDerivativePairTrace (I := I) (M := M) g₀ g₁ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 6 4 2
        (pureTrace (I := I) (M := M) g₀ g₁ 2)
        (pureTrace (I := I) (M := M) g₀ g₁ 4) := by
  rfl

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem deTurckLieConnectionDifferenceDerivativeCoefficient_eq_pairTrace
    (g₀ g_bg g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w) :
    deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg =
      (-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (deTurckLieConnectionDifferenceDerivativePairTrace (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6
          deTurckLieConnectionDifferenceDerivativeSigma
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (deTurckLieConnectionDifferenceDerivativeSym (I := I) (M := M) g₀ T g₁ g_bg))) :=
  deTurckLieConnectionDifferenceDerivCoeffField_eq_pairTrace (I := I) (M := M) g₀ g_bg g₁ T htie

end DeTurckLieConnectionDifferenceDerivativeUniformInternal

end DeTurckLieConnectionDifferenceDerivativeGridBrick

end DifferentialGeometry.Analysis.Sobolev

end
