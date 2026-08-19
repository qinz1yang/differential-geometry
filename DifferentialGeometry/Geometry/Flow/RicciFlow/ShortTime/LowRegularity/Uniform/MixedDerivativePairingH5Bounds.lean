import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.MixedDerivativePairingH4Bounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.MixedTensorApplicationFirstSecondOrderBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.SecondDerivativePairing.FirstOrderCoefficient

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic
  (integrable_riemannianFiberNormSq_toSection riemannianFiberNormSq)
open DifferentialGeometry.Analysis.Sobolev
  (iteratedCovGrad iteratedCovGrad_succ iteratedCovGrad_zero
   normSq_le_integral_of_pointwise_fiberNormSq_le_rs
   riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongr_both_eq rsDomDomCongrSection
   rsDomDomCongrSection_toSection tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs)
open DifferentialGeometry.Analysis.Spectral
  (operatorFieldApply operatorFieldComposition_zero_eq_operatorFieldApply ccTensorToHs ccTensorToHs_smul cc_h1_jet_sq deTurckMetricPrincipalDefectTotal smooth_cc_tensor_h1_norm_sq_eq_covariant_jet
   hsJet_le norm_ccHs_eq_smoothHs oneMinusConnLapSmooth one_minus_connection_laplacian_squared_pairing_h3_h1_bound pureTrace pureTrace_toSection
   riemannianFiberNormSq_iteratedCovGrad_slotExtend_le riemannianFiberNormSq_iteratedCovGrad_comp
   slotExtend smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap)
open DifferentialGeometry.Analysis.Spectral.CurvatureCoefficientDifferenceJetTower
  (covGrad_slotExtend_toSection_rsDomDomCongr_b)
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

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem iterated_covgrad_comp_l2_sq_h5
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

omit [BoundarylessManifold I M] in
private theorem slot_extend_sq_h5
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (A : SmoothCcTensor g r s) (j : ℕ) :
    ‖iteratedCovGrad (I := I) g (r + 1) (s + 1) j
        (slotExtend (I := I) (M := M) g r s A)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 := by
  classical
  let F : M → ℝ := fun x => (Module.finrank ℝ E : ℝ) *
    riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
      ((iteratedCovGrad (I := I) g r s j A).toSection x)
  have hFint : Integrable F (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g r (s + j)
        (iteratedCovGrad (I := I) g r s j A)).const_mul _
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (r + 1) ((s + 1) + j)
      (iteratedCovGrad (I := I) g (r + 1) (s + 1) j
        (slotExtend (I := I) (M := M) g r s A)) F hFint
      (riemannianFiberNormSq_iteratedCovGrad_slotExtend_le
        (I := I) (M := M) g r s A j)
  have hint :
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
          ((iteratedCovGrad (I := I) g r s j A).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g r (s + j)]
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  exact hsq

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem iter_two_jet_two_le_four_h5
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g r (s + 2) j
        (iteratedCovGrad (I := I) g r s 2 S)‖ ^ 2) ≤
      ∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g r s j S‖ ^ 2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    iteratedCovGrad_zero]
  rw [show ‖iteratedCovGrad (I := I) g r (s + 2) 1
      (iteratedCovGrad (I := I) g r s 2 S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s 3 S‖ ^ 2 by
        exact iterated_covgrad_comp_l2_sq_h5
          (I := I) (M := M) g r s 2 1 S]
  nlinarith [sq_nonneg ‖S‖,
    sq_nonneg ‖iteratedCovGrad (I := I) g r s 1 S‖]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem iter_two_jet_three_le_five_h5
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g r (s + 2) j
        (iteratedCovGrad (I := I) g r s 2 S)‖ ^ 2) ≤
      (∑ j ∈ Finset.range 5,
        ‖iteratedCovGrad (I := I) g r s j S‖) ^ 2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    iteratedCovGrad_zero]
  rw [show ‖iteratedCovGrad (I := I) g r (s + 2) 1
      (iteratedCovGrad (I := I) g r s 2 S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s 3 S‖ ^ 2 by
        exact iterated_covgrad_comp_l2_sq_h5
          (I := I) (M := M) g r s 2 1 S,
    show ‖iteratedCovGrad (I := I) g r (s + 2) 2
      (iteratedCovGrad (I := I) g r s 2 S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s 4 S‖ ^ 2 by
        exact iterated_covgrad_comp_l2_sq_h5
          (I := I) (M := M) g r s 2 2 S]
  nlinarith [norm_nonneg S,
    norm_nonneg (iteratedCovGrad (I := I) g r s 1 S),
    norm_nonneg (iteratedCovGrad (I := I) g r s 2 S),
    norm_nonneg (iteratedCovGrad (I := I) g r s 3 S),
    norm_nonneg (iteratedCovGrad (I := I) g r s 4 S)]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem iter_three_jet_two_le_five_h5
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g r (s + 3) j
        (iteratedCovGrad (I := I) g r s 3 S)‖ ^ 2) ≤
      (∑ j ∈ Finset.range 5,
        ‖iteratedCovGrad (I := I) g r s j S‖) ^ 2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    iteratedCovGrad_zero]
  rw [show ‖iteratedCovGrad (I := I) g r (s + 3) 1
      (iteratedCovGrad (I := I) g r s 3 S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s 4 S‖ ^ 2 by
        exact iterated_covgrad_comp_l2_sq_h5
          (I := I) (M := M) g r s 3 1 S]
  nlinarith [norm_nonneg S,
    norm_nonneg (iteratedCovGrad (I := I) g r s 1 S),
    norm_nonneg (iteratedCovGrad (I := I) g r s 2 S),
    norm_nonneg (iteratedCovGrad (I := I) g r s 3 S),
    norm_nonneg (iteratedCovGrad (I := I) g r s 4 S)]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covgrad_slot_extend_eq_reindex_h5
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    covGrad (I := I) (M := M) g (r + 1) (s + 1)
        (slotExtend (I := I) (M := M) g r s S) =
      rsDomDomCongrSection (I := I) (M := M) g (r + 1) (s + 1 + 1)
        (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
        (slotExtend (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s S)) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [covGrad_slotExtend_toSection_rsDomDomCongr_b
      (I := I) (M := M) g r s S x,
    rsDomDomCongrSection_toSection]

omit [BoundarylessManifold I M] in
private theorem rs_dom_iterated_norm_sq_h5
    (g : SmoothRiemannianMetric I M) (r s i : ℕ)
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g r s i
        (rsDomDomCongrSection (I := I) (M := M) g r s σ S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s i S‖ ^ 2 := by
  simp only [SmoothCcTensor.norm_def]
  rw [tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g r (s + i),
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g r (s + i)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  have h := riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongr_both_eq
    (I := I) (M := M) g r s (Equiv.refl (Fin r)) σ S i x
  simpa using h

omit [BoundarylessManifold I M] in
private theorem slot_covgrad_jet_three_le_four_h5
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g (r + 1) (s + 2) j
        (slotExtend (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s S))‖ ^ 2) ≤
      (Module.finrank ℝ E : ℝ) *
        ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g r s j S‖ ^ 2 := by
  let DS : SmoothCcTensor g r (s + 1) :=
    covGrad (I := I) (M := M) g r s S
  have h0 := slot_extend_sq_h5 (I := I) (M := M) g DS 0
  have h1 := slot_extend_sq_h5 (I := I) (M := M) g DS 1
  have h2 := slot_extend_sq_h5 (I := I) (M := M) g DS 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    iteratedCovGrad_zero]
  dsimp only [DS] at h0 h1 h2 ⊢
  rw [show ‖iteratedCovGrad (I := I) g r (s + 1) 1
      (covGrad (I := I) (M := M) g r s S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s 2 S‖ ^ 2 by
        exact iterated_covgrad_comp_l2_sq_h5
          (I := I) (M := M) g r s 1 1 S] at h1
  rw [show ‖iteratedCovGrad (I := I) g r (s + 1) 2
      (covGrad (I := I) (M := M) g r s S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s 3 S‖ ^ 2 by
        exact iterated_covgrad_comp_l2_sq_h5
          (I := I) (M := M) g r s 1 2 S] at h2
  simp only [iteratedCovGrad_zero] at h0
  have h0' :
      ‖slotExtend (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s S)‖ ^ 2 ≤
        (Module.finrank ℝ E : ℝ) *
          ‖iteratedCovGrad (I := I) g r s 1 S‖ ^ 2 := by
    simpa only [iteratedCovGrad_succ, iteratedCovGrad_zero, Nat.zero_add] using h0
  nlinarith [h0', sq_nonneg ‖S‖,
    (Nat.cast_nonneg (Module.finrank ℝ E) :
      0 ≤ (Module.finrank ℝ E : ℝ))]

omit [BoundarylessManifold I M] in
private theorem covgrad_slot_jet_three_le_four_h5
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g (r + 1) (s + 2) j
        (covGrad (I := I) (M := M) g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s S))‖ ^ 2) ≤
      (Module.finrank ℝ E : ℝ) *
        ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g r s j S‖ ^ 2 := by
  rw [covgrad_slot_extend_eq_reindex_h5
    (I := I) (M := M) g r s S]
  simpa only [rs_dom_iterated_norm_sq_h5 (I := I) (M := M)] using
    slot_covgrad_jet_three_le_four_h5
      (I := I) (M := M) g r s S

set_option backward.isDefEq.respectTransparency false in
private theorem edge_corner_inner_h1_of_jets_h5
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (g : SmoothRiemannianMetric I M)
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ)
    (hjet : ∀ b : ℕ, b ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ b g gBase Λ)
    (CB : ℝ) (hCB : 0 ≤ CB) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g 0 2) (B : SmoothCcTensor g 4 2),
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 4 2 j B‖ ^ 2) ≤
            (CB * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖) ^ 2 →
        let HT : SmoothCcTensor g 0 4 :=
          iteratedCovGrad (I := I) g 0 2 2 T
        let D3T : SmoothCcTensor g 0 5 :=
          covGrad (I := I) (M := M) g 0 4 HT
        let A20 : SmoothCcTensor g 4 4 :=
          covGrad (I := I) (M := M) g 4 3
            (covGrad (I := I) (M := M) g 4 2 B)
        let A11L : SmoothCcTensor g 5 4 :=
          slotExtend (I := I) (M := M) g 4 3
            (covGrad (I := I) (M := M) g 4 2 B)
        let A11R : SmoothCcTensor g 5 4 :=
          covGrad (I := I) (M := M) g 5 3
            (slotExtend (I := I) (M := M) g 4 2 B)
        let Q20 : SmoothCcTensor g 0 4 :=
          operatorFieldApply (I := I) (M := M) g 4 4 A20 HT
        let Q11L : SmoothCcTensor g 0 4 :=
          operatorFieldApply (I := I) (M := M) g 5 4 A11L D3T
        let Q11R : SmoothCcTensor g 0 4 :=
          operatorFieldApply (I := I) (M := M) g 5 4 A11R D3T
        ‖(⟨Q20⟩ : SmoothCcTensorH1 g 0 4)‖ +
            ‖(⟨Q11L⟩ : SmoothCcTensorH1 g 0 4)‖ +
            ‖(⟨Q11R⟩ : SmoothCcTensorH1 g 0 4)‖ ≤
          K * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ *
            ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ := by
  classical
  obtain ⟨C20, hC20, happ20⟩ :=
    operatorFieldComposition_h1_uniform_bound (I := I) (M := M) hDim gBase hΛ 0 4 4
  obtain ⟨C11, hC11, happ11⟩ :=
    operatorFieldComposition_h2_uniform_bound (I := I) (M := M) hDim gBase hΛ 0 5 4
  obtain ⟨CJ, hCJ, hjet4⟩ := hsJet_le (I := I) (M := M) g 2 4
  let n : ℝ := Module.finrank ℝ E
  let Kn : ℝ := Real.sqrt n
  let K : ℝ := C20 * CB * CJ + 2 * (C11 * Kn * CB * CJ)
  have hn : 0 ≤ n := by dsimp only [n]; positivity
  have hKn : 0 ≤ Kn := by dsimp only [Kn]; positivity
  have hKnSq : Kn ^ 2 = n := by
    dsimp only [Kn]
    exact Real.sq_sqrt hn
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro T B hBjet
  let HT : SmoothCcTensor g 0 4 :=
    iteratedCovGrad (I := I) g 0 2 2 T
  let D3T : SmoothCcTensor g 0 5 :=
    covGrad (I := I) (M := M) g 0 4 HT
  let A20 : SmoothCcTensor g 4 4 :=
    covGrad (I := I) (M := M) g 4 3
      (covGrad (I := I) (M := M) g 4 2 B)
  let A11L : SmoothCcTensor g 5 4 :=
    slotExtend (I := I) (M := M) g 4 3
      (covGrad (I := I) (M := M) g 4 2 B)
  let A11R : SmoothCcTensor g 5 4 :=
    covGrad (I := I) (M := M) g 5 3
      (slotExtend (I := I) (M := M) g 4 2 B)
  let Q20 : SmoothCcTensor g 0 4 :=
    operatorFieldApply (I := I) (M := M) g 4 4 A20 HT
  let Q11L : SmoothCcTensor g 0 4 :=
    operatorFieldApply (I := I) (M := M) g 5 4 A11L D3T
  let Q11R : SmoothCcTensor g 0 4 :=
    operatorFieldApply (I := I) (M := M) g 5 4 A11R D3T
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let q : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  have hy : 0 ≤ y := norm_nonneg _
  have hq : 0 ≤ q := norm_nonneg _
  have hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ :=
    hjet 1 (by norm_num)
  have hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ :=
    hjet 2 (by norm_num)
  have hTjetSum :
      ∑ j ∈ Finset.range 5,
        ‖iteratedCovGrad (I := I) g 0 2 j T‖ ≤ CJ * q := by
    simpa only [q] using hjet4 T
  have hHTjet :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 4 j HT‖ ^ 2) ≤
          (CJ * q) ^ 2 := by
    have hshift := iter_two_jet_three_le_five_h5
      (I := I) (M := M) g 0 2 T
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range 5,
        ‖iteratedCovGrad (I := I) g 0 2 j T‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    simpa only [HT] using hshift.trans
      (pow_le_pow_left₀ hsum0 hTjetSum 2)
  have hD3jet :
      (∑ j ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g 0 5 j D3T‖ ^ 2) ≤
          (CJ * q) ^ 2 := by
    have hshift := iter_three_jet_two_le_five_h5
      (I := I) (M := M) g 0 2 T
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range 5,
        ‖iteratedCovGrad (I := I) g 0 2 j T‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    simpa only [D3T, HT, iteratedCovGrad_succ, Nat.zero_add] using
      hshift.trans (pow_le_pow_left₀ hsum0 hTjetSum 2)
  have hA20jet :
      (∑ j ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g 4 4 j A20‖ ^ 2) ≤
          (CB * y) ^ 2 := by
    have hshift := iter_two_jet_two_le_four_h5
      (I := I) (M := M) g 4 2 B
    simpa only [A20, y, iteratedCovGrad_succ, iteratedCovGrad_zero,
      Nat.zero_add] using hshift.trans hBjet
  have hA11Ljet :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 5 4 j A11L‖ ^ 2) ≤
          (Kn * CB * y) ^ 2 := by
    have hshift := slot_covgrad_jet_three_le_four_h5
      (I := I) (M := M) g 4 2 B
    calc
      _ ≤ n * ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 4 2 j B‖ ^ 2 := by
        simpa only [A11L, n, Nat.reduceAdd] using hshift
      _ ≤ n * (CB * y) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hn
        simpa only [y] using hBjet
      _ = (Kn * CB * y) ^ 2 := by rw [← hKnSq]; ring
  have hA11Rjet :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 5 4 j A11R‖ ^ 2) ≤
          (Kn * CB * y) ^ 2 := by
    have hshift := covgrad_slot_jet_three_le_four_h5
      (I := I) (M := M) g 4 2 B
    calc
      _ ≤ n * ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 4 2 j B‖ ^ 2 := by
        simpa only [A11R, n, Nat.reduceAdd] using hshift
      _ ≤ n * (CB * y) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hn
        simpa only [y] using hBjet
      _ = (Kn * CB * y) ^ 2 := by rw [← hKnSq]; ring
  have hQ20 :
      ‖(⟨Q20⟩ : SmoothCcTensorH1 g 0 4)‖ ≤
        C20 * (CB * y) * (CJ * q) := by
    simpa only [Q20, operatorFieldComposition_zero_eq_operatorFieldApply] using
      happ20 g hEq hjet1 hjet2 A20 HT (CB * y) (CJ * q)
        (mul_nonneg hCB hy) (mul_nonneg hCJ hq) hA20jet hHTjet
  have hQ11L :
      ‖(⟨Q11L⟩ : SmoothCcTensorH1 g 0 4)‖ ≤
        C11 * (Kn * CB * y) * (CJ * q) := by
    simpa only [Q11L, operatorFieldComposition_zero_eq_operatorFieldApply] using
      happ11 g hEq hjet1 hjet2 A11L D3T (Kn * CB * y) (CJ * q)
        (mul_nonneg (mul_nonneg hKn hCB) hy) (mul_nonneg hCJ hq)
        hA11Ljet hD3jet
  have hQ11R :
      ‖(⟨Q11R⟩ : SmoothCcTensorH1 g 0 4)‖ ≤
        C11 * (Kn * CB * y) * (CJ * q) := by
    simpa only [Q11R, operatorFieldComposition_zero_eq_operatorFieldApply] using
      happ11 g hEq hjet1 hjet2 A11R D3T (Kn * CB * y) (CJ * q)
        (mul_nonneg (mul_nonneg hKn hCB) hy) (mul_nonneg hCJ hq)
        hA11Rjet hD3jet
  dsimp only [Q20, Q11L, Q11R, A20, A11L, A11R, D3T, HT,
    K, y, q] at hQ20 hQ11L hQ11R ⊢
  nlinarith

private theorem trace_three_app_h1_h5
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (g : SmoothRiemannianMetric I M)
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Cj : ℝ), 0 ≤ Cj →
      ∀ (Tr : SmoothCcTensor g 4 2),
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 4 2 j Tr‖ ^ 2) ≤ Cj ^ 2 →
      ∀ Q20 Q11L Q11R : SmoothCcTensor g 0 4,
        let P20 : SmoothCcTensor g 0 2 :=
          operatorFieldApply (I := I) (M := M) g 4 2 Tr Q20
        let P11L : SmoothCcTensor g 0 2 :=
          operatorFieldApply (I := I) (M := M) g 4 2 Tr Q11L
        let P11R : SmoothCcTensor g 0 2 :=
          operatorFieldApply (I := I) (M := M) g 4 2 Tr Q11R
        ‖(⟨P20⟩ : SmoothCcTensorH1 g 0 2)‖ +
            ‖(⟨P11L⟩ : SmoothCcTensorH1 g 0 2)‖ +
            ‖(⟨P11R⟩ : SmoothCcTensorH1 g 0 2)‖ ≤
          C * Cj * (‖(⟨Q20⟩ : SmoothCcTensorH1 g 0 4)‖ +
            ‖(⟨Q11L⟩ : SmoothCcTensorH1 g 0 4)‖ +
            ‖(⟨Q11R⟩ : SmoothCcTensorH1 g 0 4)‖) := by
  classical
  obtain ⟨C, hC, happ⟩ :=
    operatorFieldComposition_h2_uniform_bound (I := I) (M := M) hDim gBase hΛ 0 4 2
  refine ⟨C, hC, ?_⟩
  intro Cj hCj Tr hTrjet Q20 Q11L Q11R
  have outer (Q : SmoothCcTensor g 0 4) :
      ‖(⟨operatorFieldApply (I := I) (M := M) g 4 2 Tr Q⟩ :
          SmoothCcTensorH1 g 0 2)‖ ≤
        C * Cj * ‖(⟨Q⟩ : SmoothCcTensorH1 g 0 4)‖ := by
    have hQjet :
        (∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g 0 4 j Q‖ ^ 2) ≤
            ‖(⟨Q⟩ : SmoothCcTensorH1 g 0 4)‖ ^ 2 := by
      calc
        _ = ‖(⟨Q⟩ : SmoothCcTensorH1 g 0 4)‖ ^ 2 := by
          simpa only [Finset.sum_range_succ, Finset.sum_range_zero,
            zero_add, iteratedCovGrad_zero] using
              (smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M) g 0 4 Q).symm
        _ ≤ _ := le_rfl
    simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using
      happ g hEq hjet1 hjet2 Tr Q Cj
        ‖(⟨Q⟩ : SmoothCcTensorH1 g 0 4)‖ hCj
        (norm_nonneg _) hTrjet hQjet
  have h20 := outer Q20
  have h11L := outer Q11L
  have h11R := outer Q11R
  nlinarith

private theorem three_corner_pair_h5_le
    (g : SmoothRiemannianMetric I M)
    (T P20 P11L P11R : SmoothCcTensor g 0 2) :
    let W := oneMinusConnLapSmooth (I := I) g 0 2 T
    let V := oneMinusConnLapSmooth (I := I) g 0 2
      (oneMinusConnLapSmooth (I := I) g 0 2 W)
    |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P20.toFun| +
        |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11L.toFun| +
        |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11R.toFun| ≤
      ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ *
        (‖(⟨P20⟩ : SmoothCcTensorH1 g 0 2)‖ +
          ‖(⟨P11L⟩ : SmoothCcTensorH1 g 0 2)‖ +
          ‖(⟨P11R⟩ : SmoothCcTensorH1 g 0 2)‖) := by
  let W := oneMinusConnLapSmooth (I := I) g 0 2 T
  let V := oneMinusConnLapSmooth (I := I) g 0 2
    (oneMinusConnLapSmooth (I := I) g 0 2 W)
  let z := ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖
  have hspec (P : SmoothCcTensor g 0 2) :
      ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) P‖ =
        ‖(⟨P⟩ : SmoothCcTensorH1 g 0 2)‖ := by
    have hspectral := cc_h1_jet_sq (I := I) (M := M) g P
    have hintrinsic := smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M) g 0 2 P
    nlinarith [norm_nonneg
      (ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) P),
      norm_nonneg (⟨P⟩ : SmoothCcTensorH1 g 0 2)]
  have hshift :
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W‖ = z := by
    dsimp only [z]
    rw [norm_ccHs_eq_smoothHs, norm_ccHs_eq_smoothHs]
    simpa only [W] using
      (smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap
        (I := I) (M := M) g 3 T).symm
  have h20 := one_minus_connection_laplacian_squared_pairing_h3_h1_bound
    (I := I) (M := M) g W P20
  have h11L := one_minus_connection_laplacian_squared_pairing_h3_h1_bound
    (I := I) (M := M) g W P11L
  have h11R := one_minus_connection_laplacian_squared_pairing_h3_h1_bound
    (I := I) (M := M) g W P11R
  change |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P20.toFun| ≤ _ at h20
  change |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11L.toFun| ≤ _ at h11L
  change |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11R.toFun| ≤ _ at h11R
  rw [hshift, hspec P20] at h20
  rw [hshift, hspec P11L] at h11L
  rw [hshift, hspec P11R] at h11R
  dsimp only [V, W, z]
  nlinarith

set_option backward.isDefEq.respectTransparency false in
theorem mixed_derivative_action_h1_uniform_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ rho : ℝ, 0 < rho ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ b : ℕ, b ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ b g gBase Λ) →
        ∃ G : ℝ, 0 ≤ G ∧
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
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ rho →
            ∀ {a : ℝ}, a ∈ Set.Icc (0 : ℝ) 1 →
            let gm := DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricPerturbationPath
              (I := I) g T 0 hdelta hdeltaZ a
            let B : SmoothCcTensor g 4 2 :=
              lieDecomposition2 (I := I) (M := M) g T hdelta hdeltaZ a +
                (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gBase gm -
                  deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gBase g) +
                (-2 * a : ℝ) •
                  RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T
            let HT : SmoothCcTensor g 0 4 :=
              iteratedCovGrad (I := I) g 0 2 2 T
            let Tr : SmoothCcTensor g 4 2 :=
              DifferentialGeometry.Analysis.Spectral.DeTurck.cometricDoubleTraceField (I := I) g 2
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
            ‖(⟨P20⟩ : SmoothCcTensorH1 g 0 2)‖ +
                ‖(⟨P11L⟩ : SmoothCcTensorH1 g 0 2)‖ +
                ‖(⟨P11R⟩ : SmoothCcTensorH1 g 0 2)‖ ≤
              G * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ *
                ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ := by
  classical
  obtain ⟨rhoB, CB, hrhoB, hCB, hedge⟩ :=
    ricciDeTurckTopOrderCoefficient_h3_uniform_bound (I := I) (M := M) hDim gBase hΛ
  obtain ⟨rhoTr, _, Cj, hrhoTr, _, hCj, hpure⟩ :=
    pureTrace_h3_uniform (I := I) (M := M) hDim gBase hΛ
  refine ⟨min rhoB rhoTr, lt_min hrhoB hrhoTr, ?_⟩
  intro g hEq hjet
  obtain ⟨K, hK, hinner⟩ := edge_corner_inner_h1_of_jets_h5
    (I := I) (M := M) hDim gBase hΛ g hEq hjet CB hCB
  have hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ :=
    hjet 1 (by norm_num)
  have hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ :=
    hjet 2 (by norm_num)
  obtain ⟨C, hC, houter⟩ := trace_three_app_h1_h5
    (I := I) (M := M) hDim gBase hΛ g hEq hjet1 hjet2
  let G : ℝ := C * Cj * K
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  refine ⟨G, hG, ?_⟩
  intro T hTsymm delta hdelta_le hdelta0 hdelta hdeltaZ hT2 a ha
  let gm : SmoothRiemannianMetric I M :=
    DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricPerturbationPath
      (I := I) g T 0 hdelta hdeltaZ a
  let B : SmoothCcTensor g 4 2 :=
    lieDecomposition2 (I := I) (M := M) g T hdelta hdeltaZ a +
      (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gBase gm -
        deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gBase g) +
      (-2 * a : ℝ) • RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient
        (I := I) (M := M) g gm T
  let HT : SmoothCcTensor g 0 4 :=
    iteratedCovGrad (I := I) g 0 2 2 T
  let D3T : SmoothCcTensor g 0 5 :=
    covGrad (I := I) (M := M) g 0 4 HT
  let A20 : SmoothCcTensor g 4 4 :=
    covGrad (I := I) (M := M) g 4 3
      (covGrad (I := I) (M := M) g 4 2 B)
  let A11L : SmoothCcTensor g 5 4 :=
    slotExtend (I := I) (M := M) g 4 3
      (covGrad (I := I) (M := M) g 4 2 B)
  let A11R : SmoothCcTensor g 5 4 :=
    covGrad (I := I) (M := M) g 5 3
      (slotExtend (I := I) (M := M) g 4 2 B)
  let Tr : SmoothCcTensor g 4 2 :=
    DifferentialGeometry.Analysis.Spectral.DeTurck.cometricDoubleTraceField (I := I) g 2
  let Q20 : SmoothCcTensor g 0 4 :=
    operatorFieldApply (I := I) (M := M) g 4 4 A20 HT
  let Q11L : SmoothCcTensor g 0 4 :=
    operatorFieldApply (I := I) (M := M) g 5 4 A11L D3T
  let Q11R : SmoothCcTensor g 0 4 :=
    operatorFieldApply (I := I) (M := M) g 5 4 A11R D3T
  let P20 : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 4 2 Tr Q20
  let P11L : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 4 2 Tr Q11L
  let P11R : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 4 2 Tr Q11R
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let q : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  have hT2B :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ rhoB :=
    hT2.trans (min_le_left _ _)
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
  have hTrjet :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 4 2 j Tr‖ ^ 2) ≤ Cj ^ 2 := by
    have hp := hpure g hEq hjet (0 : SmoothCcTensor g 0 2) g
      hdelta_le hdelta0 hdeltaZ hzero2 hzeroTie
    have hj := hp.2.1
    have hzero3 :
        ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ)
          (0 : SmoothCcTensor g 0 2)‖ = 0 := by
      rw [show (0 : SmoothCcTensor g 0 2) =
          (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
        ccTensorToHs_smul, zero_smul, norm_zero]
    have hj' :
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 4 2 j Tr‖ ^ 2) ≤ Cj ^ 2 := by
      rw [hTrpure]
      simpa only [hzero3, add_zero, mul_one] using hj
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      iteratedCovGrad_zero] at hj' ⊢
    nlinarith [hj', sq_nonneg
      ‖iteratedCovGrad (I := I) g 4 2 3 Tr‖]
  have hIn := hinner T B hBjet
  have hOut := houter Cj hCj Tr hTrjet Q20 Q11L Q11R
  have hscale : 0 ≤ C * Cj := mul_nonneg hC hCj
  calc
    ‖(⟨P20⟩ : SmoothCcTensorH1 g 0 2)‖ +
          ‖(⟨P11L⟩ : SmoothCcTensorH1 g 0 2)‖ +
          ‖(⟨P11R⟩ : SmoothCcTensorH1 g 0 2)‖
        ≤ C * Cj * (‖(⟨Q20⟩ : SmoothCcTensorH1 g 0 4)‖ +
          ‖(⟨Q11L⟩ : SmoothCcTensorH1 g 0 4)‖ +
          ‖(⟨Q11R⟩ : SmoothCcTensorH1 g 0 4)‖) := hOut
    _ ≤ C * Cj * (K * y * q) :=
      mul_le_mul_of_nonneg_left (by simpa only [Q20, Q11L, Q11R,
        A20, A11L, A11R, D3T, HT, y, q] using hIn) hscale
    _ = G * y * q := by dsimp only [G]; ring

set_option backward.isDefEq.respectTransparency false in
theorem mixed_derivative_action_pairing_h5_uniform_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ rho : ℝ, 0 < rho ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ b : ℕ, b ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ b g gBase Λ) →
        ∃ C : ℝ, 0 ≤ C ∧
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
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ rho →
            ∀ {a : ℝ}, a ∈ Set.Icc (0 : ℝ) 1 →
            let gm := DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricPerturbationPath
              (I := I) g T 0 hdelta hdeltaZ a
            let B : SmoothCcTensor g 4 2 :=
              lieDecomposition2 (I := I) (M := M) g T hdelta hdeltaZ a +
                (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gBase gm -
                  deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gBase g) +
                (-2 * a : ℝ) •
                  RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T
            let HT : SmoothCcTensor g 0 4 :=
              iteratedCovGrad (I := I) g 0 2 2 T
            let Tr : SmoothCcTensor g 4 2 :=
              DifferentialGeometry.Analysis.Spectral.DeTurck.cometricDoubleTraceField (I := I) g 2
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
            let V : SmoothCcTensor g 0 2 :=
              oneMinusConnLapSmooth (I := I) g 0 2
                (oneMinusConnLapSmooth (I := I) g 0 2
                  (oneMinusConnLapSmooth (I := I) g 0 2 T))
            2 * (|tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P20.toFun| +
                |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11L.toFun| +
                |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11R.toFun|) ≤
              C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ *
                ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ *
                ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ := by
  classical
  obtain ⟨rho, hrho, hcorner⟩ :=
    mixed_derivative_action_h1_uniform_bound (I := I) (M := M) hDim gBase hΛ
  refine ⟨rho, hrho, ?_⟩
  intro g hEq hjet
  obtain ⟨G, hG, hH1⟩ := hcorner g hEq hjet
  refine ⟨2 * G, mul_nonneg (by norm_num) hG, ?_⟩
  intro T hTsymm delta hdelta_le hdelta0 hdelta hdeltaZ hT2 a ha
  let gm : SmoothRiemannianMetric I M :=
    DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricPerturbationPath
      (I := I) g T 0 hdelta hdeltaZ a
  let B : SmoothCcTensor g 4 2 :=
    lieDecomposition2 (I := I) (M := M) g T hdelta hdeltaZ a +
      (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gBase gm -
        deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gBase g) +
      (-2 * a : ℝ) • RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient
        (I := I) (M := M) g gm T
  let HT : SmoothCcTensor g 0 4 :=
    iteratedCovGrad (I := I) g 0 2 2 T
  let Tr : SmoothCcTensor g 4 2 :=
    DifferentialGeometry.Analysis.Spectral.DeTurck.cometricDoubleTraceField (I := I) g 2
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
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let q : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  let z : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖
  have hz : 0 ≤ z := norm_nonneg _
  have hp := three_corner_pair_h5_le
    (I := I) (M := M) g T P20 P11L P11R
  have hh1 := hH1 T hTsymm hdelta_le hdelta0 hdelta hdeltaZ hT2 ha
  have hscaled :
      z * (‖(⟨P20⟩ : SmoothCcTensorH1 g 0 2)‖ +
          ‖(⟨P11L⟩ : SmoothCcTensorH1 g 0 2)‖ +
          ‖(⟨P11R⟩ : SmoothCcTensorH1 g 0 2)‖) ≤
        z * (G * y * q) := by
    apply mul_le_mul_of_nonneg_left _ hz
    simpa only [P20, P11L, P11R, Tr, HT, B, gm, y, q] using hh1
  dsimp only [P20, P11L, P11R, Tr, HT, B, gm, y, q, z] at hp hscaled ⊢
  nlinarith

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
