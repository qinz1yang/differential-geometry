import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalOperator.CoreIdentification
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H1H2OperatorFieldComposition
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.Inclusion


noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Connection

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private abbrev metricH2 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev rank2H4 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (4 : ℝ)

private abbrev rank2H3 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (3 : ℝ)

private abbrev rank2H2 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev rank2H1 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)

private abbrev rank4H2 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 4 (2 : ℝ)

private abbrev rank4H1 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 4 ((1 : ℕ) : ℝ)

private abbrev rank4End1 (g : SmoothRiemannianMetric I M) :=
  rank4H1 (I := I) (M := M) g →L[ℝ]
    rank4H1 (I := I) (M := M) g

private abbrev rank4End2 (g : SmoothRiemannianMetric I M) :=
  rank4H2 (I := I) (M := M) g →L[ℝ]
    rank4H2 (I := I) (M := M) g

private local instance rank4End1Norm
    (g : SmoothRiemannianMetric I M) :
    NormedAddCommGroup (rank4End1 (I := I) (M := M) g) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance rank4End1Space
    (g : SmoothRiemannianMetric I M) :
    NormedSpace ℝ (rank4End1 (I := I) (M := M) g) :=
  ContinuousLinearMap.toNormedSpace

private local instance rank4End2Norm
    (g : SmoothRiemannianMetric I M) :
    NormedAddCommGroup (rank4End2 (I := I) (M := M) g) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance rank4End2Space
    (g : SmoothRiemannianMetric I M) :
    NormedSpace ℝ (rank4End2 (I := I) (M := M) g) :=
  ContinuousLinearMap.toNormedSpace

private theorem incl_core
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    {τ σ : ℝ} (hτσ : τ ≤ σ) (W : SmoothCcTensor g 0 s) :
    tensorHsInclusion (I := I) (M := M) (g := g)
        (r := 0) (s := s) hτσ
        (ccTensorToHs (I := I) (M := M) g s σ W) =
      ccTensorToHs (I := I) (M := M) g s τ W := by
  apply TensorHs.ext
  funext i
  simp only [tensorHsInclusion_coeff_apply, ccTensorToHs_coeff]

private noncomputable def secondCovariantDerivativeH3ToH1
    (g : SmoothRiemannianMetric I M) :
    rank2H3 (I := I) (M := M) g →L[ℝ]
      rank4H1 (I := I) (M := M) g := by
  let J : rank2H3 (I := I) (M := M) g →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2
        (((1 : ℕ) : ℝ) + (2 : ℝ)) :=
    (TensorHs.castEquiv (I := I) (M := M)
      (by norm_num : (3 : ℝ) =
        ((1 : ℕ) : ℝ) + (2 : ℝ))).toContinuousLinearEquiv.toContinuousLinearMap
  exact (iterCovGradHs (I := I) (M := M) g 2 2 1).comp J

private noncomputable def cometricDoubleTraceH1
    (g : SmoothRiemannianMetric I M) :
    rank4H1 (I := I) (M := M) g →L[ℝ]
      rank2H1 (I := I) (M := M) g :=
  appHs (I := I) (M := M) g 4 2 1
    (cometricDoubleTraceField (I := I) g 2)

private theorem hessianH1_core
    (g : SmoothRiemannianMetric I M) (U : SmoothCcTensor g 0 2) :
    secondCovariantDerivativeH3ToH1 (I := I) (M := M) g
        (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U) =
      ccTensorToHs (I := I) (M := M) g 4 ((1 : ℕ) : ℝ)
        (iteratedCovGrad (I := I) g 0 2 2 U) := by
  unfold secondCovariantDerivativeH3ToH1
  rw [ContinuousLinearMap.comp_apply]
  convert iterCovGradHs_core (I := I) (M := M) g 2 2 1 U using 1
  congr 1

private theorem traceH1_core
    (g : SmoothRiemannianMetric I M) (V : SmoothCcTensor g 0 4) :
    cometricDoubleTraceH1 (I := I) (M := M) g
        (ccTensorToHs (I := I) (M := M) g 4 ((1 : ℕ) : ℝ) V) =
      ccTensorToHs (I := I) (M := M) g 2 ((1 : ℕ) : ℝ)
        (operatorFieldApply (I := I) (M := M) g 4 2
          (cometricDoubleTraceField (I := I) g 2) V) := by
  exact appHs_core (I := I) (M := M) g 4 2 1
    (cometricDoubleTraceField (I := I) g 2) V

omit [NeZero (Module.finrank ℝ E)] in
private theorem perm_iteratedCovGrad_norm
    (g : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 2))
    (T : SmoothCcTensor g 0 2) (k : ℕ) :
    ‖iteratedCovGrad (I := I) g 0 2 k
        (domDomCongrSection (I := I) g σ T)‖ =
      ‖iteratedCovGrad (I := I) g 0 2 k T‖ := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g
  have hbridge : ∀ W : SmoothCcTensor g 0 2,
      ‖iteratedCovGrad (I := I) g 0 2 k W‖ ^ 2 =
        ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (2 + k) x
          ((iteratedCovGrad (I := I) g 0 2 k W).toSection x) ∂μ := by
    intro W
    rw [SmoothCcTensor.norm_def (I := I) (M := M)
      (iteratedCovGrad (I := I) g 0 2 k W)]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq
      (I := I) (M := M) g (2 + k)
        (iteratedCovGrad (I := I) g 0 2 k W)
  have hintegrand : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (2 + k) x
          ((iteratedCovGrad (I := I) g 0 2 k
            (domDomCongrSection (I := I) g σ T)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g 0 (2 + k) x
          ((iteratedCovGrad (I := I) g 0 2 k T).toSection x) :=
    fun x => riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g (s := 2) σ T k x
  have hsq :
      ‖iteratedCovGrad (I := I) g 0 2 k
          (domDomCongrSection (I := I) g σ T)‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g 0 2 k T‖ ^ 2 := by
    rw [hbridge (domDomCongrSection (I := I) g σ T), hbridge T]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall hintegrand)
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

omit [NeZero (Module.finrank ℝ E)] in
private theorem symm_iteratedCovGrad_norm
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) (k : ℕ) :
    ‖iteratedCovGrad (I := I) g 0 2 k
        (ccTensor02Symm (I := I) (M := M) g T)‖ ≤
      ‖iteratedCovGrad (I := I) g 0 2 k T‖ := by
  classical
  let Tsw : SmoothCcTensor g 0 2 :=
    domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T
  have hiter :
      iteratedCovGrad (I := I) g 0 2 k
          (ccTensor02Symm (I := I) (M := M) g T) =
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 k T +
          (1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 k Tsw := by
    dsimp only [Tsw]
    exact iteratedCovGrad_ccTensor02Symm_eq (I := I) (M := M) g T k
  rw [hiter]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul]
  have habs : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by
    rw [Real.norm_eq_abs]
    norm_num
  rw [habs]
  have hperm :
      ‖iteratedCovGrad (I := I) g 0 2 k Tsw‖ =
        ‖iteratedCovGrad (I := I) g 0 2 k T‖ := by
    exact perm_iteratedCovGrad_norm (I := I) (M := M) g
      (Equiv.swap (0 : Fin 2) 1) T k
  rw [hperm]
  linarith [norm_nonneg (iteratedCovGrad (I := I) g 0 2 k T)]

omit [NeZero (Module.finrank ℝ E)] in
private theorem raise_iteratedCovGrad_norm
    (g : SmoothRiemannianMetric I M) (s i : ℕ)
    (W : SmoothCcTensor g 0 (s + 2)) :
    ‖iteratedCovGrad (I := I) g 1 (s + 1) i
        (cometricRaiseSlot0Field (I := I) (M := M) g s W)‖ =
      ‖iteratedCovGrad (I := I) g 0 (s + 2) i W‖ := by
  have hsq :
      ‖iteratedCovGrad (I := I) g 1 (s + 1) i
          (cometricRaiseSlot0Field (I := I) (M := M) g s W)‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g 0 (s + 2) i W‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
    refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => ?_)
    exact riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq
      (I := I) (M := M) g s W i x
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

private theorem insert3_iteratedCovGrad_le
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (i : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    ‖iteratedCovGrad (I := I) g 4 4 i
        (slotInsertEndoCc (I := I) (M := M) g 3 Λ)‖ ≤
      27 * ‖iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ := by
  classical
  set F : M → ℝ := fun x => 27 *
    riemannianFiberNormSq (I := I) (M := M) g 1 (1 + i) x
      ((iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ)).toSection x)
  have hFint : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g 1 (1 + i)
        (iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ))).const_mul _
  have hpt : ∀ x,
      riemannianFiberNormSq (I := I) (M := M) g 4 (4 + i) x
          ((iteratedCovGrad (I := I) g 4 4 i
            (slotInsertEndoCc (I := I) (M := M) g 3 Λ)).toSection x) ≤
        F x := by
    intro x
    have h := riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo
      (I := I) (M := M) g 3 Λ i x
    rw [hDim] at h
    norm_num at h
    simpa only [F, Nat.reduceAdd] using h
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g 4 (4 + i)
      (iteratedCovGrad (I := I) g 4 4 i
        (slotInsertEndoCc (I := I) (M := M) g 3 Λ)) F hFint hpt
  have hint :
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g 1 (1 + i) x
          ((iteratedCovGrad (I := I) g 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g 0 Λ)).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g 1 (1 + i)]
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  refine le_of_sq_le_sq ?_
    (mul_nonneg (by norm_num) (norm_nonneg _))
  calc
    ‖iteratedCovGrad (I := I) g 4 4 i
        (slotInsertEndoCc (I := I) (M := M) g 3 Λ)‖ ^ 2
        ≤ 27 * ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := hsq
    _ ≤ (27 * ‖iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖) ^ 2 := by
      nlinarith [sq_nonneg
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖]

private theorem pcoeff_iteratedCovGrad_le
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g 4 4 i
        (metricPerturbationCoefficientH2 (I := I) (M := M) g T)‖ ≤
      27 * ‖iteratedCovGrad (I := I) g 0 2 i T‖ := by
  let Λ := symmRaiseEndo (I := I) (M := M) g T
  have hslot := insert3_iteratedCovGrad_le (I := I) (M := M) hDim g i Λ
  have hbase :
      ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ≤
        ‖iteratedCovGrad (I := I) g 0 2 i T‖ := by
    rw [show slotInsertEndoCc (I := I) (M := M) g 0 Λ =
        cometricRaiseSlot0Field (I := I) (M := M) g 0
          (domDomCongrSection (I := I) g
            (Equiv.swap (0 : Fin 2) 1)
            (ccTensor02Symm (I := I) (M := M) g T)) from by
      simpa only [Λ] using insert_symmRaise_eq (I := I) (M := M) g T]
    calc
      _ = ‖iteratedCovGrad (I := I) g 0 2 i
          (domDomCongrSection (I := I) g
            (Equiv.swap (0 : Fin 2) 1)
            (ccTensor02Symm (I := I) (M := M) g T))‖ := by
            simpa only [Nat.zero_add, Nat.reduceAdd] using
              raise_iteratedCovGrad_norm (I := I) (M := M) g 0 i
                (domDomCongrSection (I := I) g
                  (Equiv.swap (0 : Fin 2) 1)
                  (ccTensor02Symm (I := I) (M := M) g T))
      _ = ‖iteratedCovGrad (I := I) g 0 2 i
          (ccTensor02Symm (I := I) (M := M) g T)‖ :=
        perm_iteratedCovGrad_norm (I := I) (M := M) g
          (Equiv.swap (0 : Fin 2) 1)
          (ccTensor02Symm (I := I) (M := M) g T) i
      _ ≤ _ := symm_iteratedCovGrad_norm (I := I) (M := M) g T i
  exact hslot.trans
    (mul_le_mul_of_nonneg_left hbase (by norm_num))

private theorem pcoeff1_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : SmoothCcTensor g 0 2,
      ‖appHs (I := I) (M := M) g 4 4 1
          (metricPerturbationCoefficientH2 (I := I) (M := M) g T)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ := by
  classical
  obtain ⟨CinT, hCinT, hinT⟩ := hsJet_le (I := I) (M := M) g 2 2
  obtain ⟨CinW, hCinW, hinW⟩ := hsJet_le (I := I) (M := M) g 4 1
  obtain ⟨Cout, hCout, hout⟩ := hs_le_jet (I := I) (M := M) g 4 1
  obtain ⟨Cmul, hCmul, hmul⟩ :=
    operator_field_composition_h2_h1_to_h1_bound (I := I) (M := M) hDim g 0 4 4
  let C : ℝ := 54 * Cout * Cmul * CinT * CinW
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro T
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 4 ((1 : ℕ) : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 4 (by positivity)
  unfold appHs
  apply LinearMap.opNorm_extendOfNorm_le hdense
    (C := C *
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖)
    (mul_nonneg (by dsimp only [C]; positivity) (norm_nonneg _))
  intro W
  let NT : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  let NW : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 4 ((1 : ℕ) : ℝ) W‖
  let A : ℝ := 27 * CinT * NT
  let B : ℝ := CinW * NW
  let Φ := metricPerturbationCoefficientH2 (I := I) (M := M) g T
  let Y : SmoothCcTensor g 0 4 :=
    operatorFieldApply (I := I) (M := M) g 4 4 Φ W
  have hNT : 0 ≤ NT := norm_nonneg _
  have hNW : 0 ≤ NW := norm_nonneg _
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hTsum :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ≤ CinT * NT := by
    change ∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 2 j T‖ ≤
      CinT * ‖ccTensorToHs (I := I) (M := M) g 2 ((2 : ℕ) : ℝ) T‖
    exact hinT T
  have hΦsum :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 4 4 j Φ‖ ≤ A := by
    calc
      _ ≤ ∑ j ∈ Finset.range 3,
          27 * ‖iteratedCovGrad (I := I) g 0 2 j T‖ :=
        Finset.sum_le_sum fun j _ =>
          pcoeff_iteratedCovGrad_le (I := I) (M := M) hDim g T j
      _ = 27 * ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ := by
        rw [Finset.mul_sum]
      _ ≤ 27 * (CinT * NT) :=
        mul_le_mul_of_nonneg_left hTsum (by norm_num)
      _ = A := by dsimp only [A]; ring
  have hΦsq :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 4 4 j Φ‖ ^ 2) ≤ A ^ 2 := by
    calc
      _ ≤ (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 4 4 j Φ‖) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg
          (fun j _ => norm_nonneg _)
      _ ≤ A ^ 2 := pow_le_pow_left₀
        (Finset.sum_nonneg (fun j _ => norm_nonneg _)) hΦsum 2
  have hWsum :
      ∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g 0 4 j W‖ ≤ B := by
    simpa only [B, NW, Nat.reduceAdd] using hinW W
  have hWsq :
      (∑ j ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g 0 4 j W‖ ^ 2) ≤ B ^ 2 := by
    calc
      _ ≤ (∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g 0 4 j W‖) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg
          (fun j _ => norm_nonneg _)
      _ ≤ B ^ 2 := pow_le_pow_left₀
        (Finset.sum_nonneg (fun j _ => norm_nonneg _)) hWsum 2
  have hprod := hmul Φ W A B hA hB hΦsq hWsq
  have hY0 :
      ‖Y‖ ≤ ‖(⟨Y⟩ : SmoothCcTensorH1 g 0 4)‖ := by
    have hsq :
        ‖(⟨Y⟩ : SmoothCcTensorH1 g 0 4)‖ ^ 2 =
          ‖Y‖ ^ 2 +
            ‖covGrad (I := I) (M := M) g 0 4 Y‖ ^ 2 := by
      rw [SmoothCcTensorH1.norm_sq_eq_inner_self (I := I) (M := M),
        tensorH1Inner_def,
        ← SmoothCcTensor.norm_sq_eq_inner_self (I := I) (M := M) Y,
        ← tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner
          (I := I) (M := M) g 0 4 Y Y,
        ← SmoothCcTensor.norm_sq_eq_inner_self (I := I) (M := M)
          (covGrad (I := I) (M := M) g 0 4 Y)]
    nlinarith [norm_nonneg Y,
      norm_nonneg (⟨Y⟩ : SmoothCcTensorH1 g 0 4),
      sq_nonneg ‖covGrad (I := I) (M := M) g 0 4 Y‖]
  have hY1 :
      ‖covGrad (I := I) (M := M) g 0 4 Y‖ ≤
        ‖(⟨Y⟩ : SmoothCcTensorH1 g 0 4)‖ := by
    have hsq :
        ‖(⟨Y⟩ : SmoothCcTensorH1 g 0 4)‖ ^ 2 =
          ‖Y‖ ^ 2 +
            ‖covGrad (I := I) (M := M) g 0 4 Y‖ ^ 2 := by
      rw [SmoothCcTensorH1.norm_sq_eq_inner_self (I := I) (M := M),
        tensorH1Inner_def,
        ← SmoothCcTensor.norm_sq_eq_inner_self (I := I) (M := M) Y,
        ← tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner
          (I := I) (M := M) g 0 4 Y Y,
        ← SmoothCcTensor.norm_sq_eq_inner_self (I := I) (M := M)
          (covGrad (I := I) (M := M) g 0 4 Y)]
    nlinarith [norm_nonneg (covGrad (I := I) (M := M) g 0 4 Y),
      norm_nonneg (⟨Y⟩ : SmoothCcTensorH1 g 0 4),
      sq_nonneg ‖Y‖]
  have houtY :
      ‖ccTensorToHs (I := I) (M := M) g 4 ((1 : ℕ) : ℝ) Y‖ ≤
        Cout * (‖Y‖ +
          ‖covGrad (I := I) (M := M) g 0 4 Y‖) := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, iteratedCovGrad_zero, iteratedCovGrad_succ,
      Nat.zero_add] using hout Y
  change
    ‖ccTensorToHs (I := I) (M := M) g 4 ((1 : ℕ) : ℝ) Y‖ ≤
      (C * NT) * NW
  calc
    _ ≤ Cout * (‖Y‖ +
        ‖covGrad (I := I) (M := M) g 0 4 Y‖) := houtY
    _ ≤ Cout * (2 * ‖(⟨Y⟩ : SmoothCcTensorH1 g 0 4)‖) := by
      gcongr
      linarith
    _ ≤ Cout * (2 * (Cmul * A * B)) := by
      gcongr
      convert hprod using 1 <;> rfl
    _ = (C * NT) * NW := by
      dsimp only [C, A, B]
      ring

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem pcoeff_add
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2) :
    metricPerturbationCoefficientH2 (I := I) (M := M) g (T + U) =
      metricPerturbationCoefficientH2 (I := I) (M := M) g T +
        metricPerturbationCoefficientH2 (I := I) (M := M) g U := by
  simp only [metricPerturbationCoefficientH2, symmRaiseEndo_add, slotInsertEndoCc_add]

omit [BoundarylessManifold I M] [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem pcoeff_smul
    (g : SmoothRiemannianMetric I M) (a : ℝ) (T : SmoothCcTensor g 0 2) :
    metricPerturbationCoefficientH2 (I := I) (M := M) g (a • T) =
      a • metricPerturbationCoefficientH2 (I := I) (M := M) g T := by
  simp only [metricPerturbationCoefficientH2, symmRaiseEndo_smul, slotInsertEndoCc_smul]

private noncomputable def perturbCcLin1
    (g : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 0 2 →ₗ[ℝ]
      rank4End1 (I := I) (M := M) g where
  toFun := fun T =>
    appHs (I := I) (M := M) g 4 4 1
      (metricPerturbationCoefficientH2 (I := I) (M := M) g T)
  map_add' := fun T U => by
    apply ContinuousLinearMap.ext
    intro V
    rw [pcoeff_add, appHs_add, add_apply]
  map_smul' := fun a T => by
    apply ContinuousLinearMap.ext
    intro V
    simpa only [RingHom.id_apply, smul_apply,
      pcoeff_smul] using
      appHs_smul (I := I) (M := M) g 4 4 1 a
        (metricPerturbationCoefficientH2 (I := I) (M := M) g T) V

private noncomputable def perturbH1
    (g : SmoothRiemannianMetric I M) :
    metricH2 (I := I) (M := M) g →L[ℝ]
      rank4End1 (I := I) (M := M) g :=
  LinearMap.extendOfNorm (σ₁₂ := RingHom.id ℝ)
    (perturbCcLin1 (I := I) (M := M) g)
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ))

private theorem perturbH1_core
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    perturbH1 (I := I) (M := M) g
        (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T) =
      appHs (I := I) (M := M) g 4 4 1
        (metricPerturbationCoefficientH2 (I := I) (M := M) g T) := by
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  change
    ((perturbCcLin1 (I := I) (M := M) g).extendOfNorm
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)))
        ((ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) T) =
      perturbCcLin1 (I := I) (M := M) g T
  apply LinearMap.extendOfNorm_eq hdense
  obtain ⟨C, _, hC⟩ := pcoeff1_bound (I := I) (M := M) hDim g
  exact ⟨C, hC⟩

private theorem perturbH1_norm
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : metricH2 (I := I) (M := M) g,
        ‖perturbH1 (I := I) (M := M) g T‖ ≤ C * ‖T‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    pcoeff1_bound (I := I) (M := M) hDim g
  refine ⟨C, hC, fun T => ?_⟩
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hop : ‖perturbH1 (I := I) (M := M) g‖ ≤ C := by
    unfold perturbH1
    apply LinearMap.opNorm_extendOfNorm_le hdense hC
    exact hbound
  exact (perturbH1 (I := I) (M := M) g).le_opNorm T |>.trans
    (mul_le_mul_of_nonneg_right hop (norm_nonneg _))

private lemma inv_add_sub_one_le
    {R : Type*} [NormedRing R] [CompleteSpace R]
    (B : R) (hnorm1 : ‖(1 : R)‖ ≤ 1)
    (hhalf : ‖B‖ ≤ (1 : ℝ) / 2) :
    ‖Ring.inverse (1 + B) - 1‖ ≤ 2 * ‖B‖ := by
  have hB0 : 0 ≤ ‖B‖ := norm_nonneg _
  have hlt : ‖B‖ < 1 := hhalf.trans_lt (by norm_num)
  have hneg : ‖-B‖ < 1 := by
    simpa only [norm_neg] using hlt
  have hu : IsUnit (1 + B) := by
    have h := isUnit_one_sub_of_norm_lt_one (x := -B) hneg
    simpa only [sub_neg_eq_add] using h
  have hinv :
      ‖Ring.inverse (1 + B)‖ ≤ (1 - ‖B‖)⁻¹ := by
    have hseries := tsum_geometric_le_of_norm_lt_one (-B) hneg
    rw [geom_series_eq_inverse (-B) hneg] at hseries
    have hseries' :
        ‖Ring.inverse (1 + B)‖ ≤
          ‖(1 : R)‖ - 1 + (1 - ‖B‖)⁻¹ := by
      simpa only [sub_neg_eq_add, norm_neg] using hseries
    exact hseries'.trans (by linarith)
  have hden : 0 < 1 - ‖B‖ := by
    linarith
  have hinv2 : (1 - ‖B‖)⁻¹ ≤ 2 := by
    have h : (1 : ℝ) * (1 - ‖B‖)⁻¹ ≤ 2 := by
      rw [mul_inv_le_iff₀ hden]
      linarith
    simpa only [one_mul] using h
  have hcorr :
      Ring.inverse (1 + B) - 1 =
        -(Ring.inverse (1 + B) * B) := by
    calc
      _ = Ring.inverse (1 + B) -
          Ring.inverse (1 + B) * (1 + B) := by
            rw [Ring.inverse_mul_cancel (1 + B) hu]
      _ = _ := by noncomm_ring
  rw [hcorr, norm_neg]
  calc
    ‖Ring.inverse (1 + B) * B‖ ≤
        ‖Ring.inverse (1 + B)‖ * ‖B‖ :=
      norm_mul_le _ _
    _ ≤ (1 - ‖B‖)⁻¹ * ‖B‖ :=
      mul_le_mul_of_nonneg_right hinv hB0
    _ ≤ 2 * ‖B‖ :=
      mul_le_mul_of_nonneg_right hinv2 hB0

private noncomputable def invPerturbH1
    (g : SmoothRiemannianMetric I M)
    (T : metricH2 (I := I) (M := M) g) :
    rank4End1 (I := I) (M := M) g :=
  Ring.inverse (1 + perturbH1 (I := I) (M := M) g T) - 1

private theorem invPerturbH1_norm
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ T : metricH2 (I := I) (M := M) g, ‖T‖ ≤ ρ →
        ‖perturbH1 (I := I) (M := M) g T‖ ≤ (1 : ℝ) / 2 ∧
          ‖invPerturbH1 (I := I) (M := M) g T‖ ≤ C * ‖T‖ := by
  obtain ⟨C₀, hC₀, hpert⟩ :=
    perturbH1_norm (I := I) (M := M) hDim g
  let ρ : ℝ := (2 * (C₀ + 1))⁻¹
  let C : ℝ := 2 * C₀
  have hden : 0 < 2 * (C₀ + 1) := by
    positivity
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    positivity
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T hT
  have hCrho : C₀ * ρ ≤ (1 : ℝ) / 2 := by
    dsimp only [ρ]
    rw [mul_inv_le_iff₀ hden]
    nlinarith
  have hsmall :
      ‖perturbH1 (I := I) (M := M) g T‖ ≤ (1 : ℝ) / 2 := by
    calc
      _ ≤ C₀ * ‖T‖ := hpert T
      _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hT hC₀
      _ ≤ _ := hCrho
  refine ⟨hsmall, ?_⟩
  calc
    ‖invPerturbH1 (I := I) (M := M) g T‖ ≤
        2 * ‖perturbH1 (I := I) (M := M) g T‖ := by
      have hnorm1 :
          ‖(1 : rank4End1 (I := I) (M := M) g)‖ ≤ 1 := by
        change ‖ContinuousLinearMap.id ℝ
          (rank4H1 (I := I) (M := M) g)‖ ≤ 1
        exact ContinuousLinearMap.norm_id_le
      exact inv_add_sub_one_le
        (perturbH1 (I := I) (M := M) g T) hnorm1 hsmall
    _ ≤ 2 * (C₀ * ‖T‖) :=
      mul_le_mul_of_nonneg_left (hpert T) (by norm_num)
    _ = C * ‖T‖ := by
      dsimp only [C]
      ring

noncomputable def lowRegularityPrincipalOperatorH1
    (g : SmoothRiemannianMetric I M)
    (T : metricH2 (I := I) (M := M) g) :
    rank2H3 (I := I) (M := M) g →L[ℝ]
      rank2H1 (I := I) (M := M) g :=
  (cometricDoubleTraceH1 (I := I) (M := M) g).comp
    ((invPerturbH1 (I := I) (M := M) g T).comp
      (secondCovariantDerivativeH3ToH1 (I := I) (M := M) g))

private theorem principalLo_norm
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ T : metricH2 (I := I) (M := M) g, ‖T‖ ≤ ρ →
        ‖lowRegularityPrincipalOperatorH1 (I := I) (M := M) g T‖ ≤ C * ‖T‖ := by
  obtain ⟨ρ, Cinv, hρ, hCinv, hinv⟩ :=
    invPerturbH1_norm (I := I) (M := M) hDim g
  let A := cometricDoubleTraceH1 (I := I) (M := M) g
  let D := secondCovariantDerivativeH3ToH1 (I := I) (M := M) g
  let C : ℝ := ‖A‖ * Cinv * ‖D‖
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T hT
  have hInv := (hinv T hT).2
  calc
    ‖lowRegularityPrincipalOperatorH1 (I := I) (M := M) g T‖ ≤
        ‖A‖ * ‖(invPerturbH1 (I := I) (M := M) g T).comp D‖ := by
      simpa only [lowRegularityPrincipalOperatorH1, A, D] using
        (A.opNorm_comp_le
          ((invPerturbH1 (I := I) (M := M) g T).comp D))
    _ ≤ ‖A‖ * (‖invPerturbH1 (I := I) (M := M) g T‖ * ‖D‖) :=
      mul_le_mul_of_nonneg_left
        ((invPerturbH1 (I := I) (M := M) g T).opNorm_comp_le D)
        (norm_nonneg A)
    _ ≤ ‖A‖ * ((Cinv * ‖T‖) * ‖D‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hInv (norm_nonneg D))
        (norm_nonneg A)
    _ = C * ‖T‖ := by
      dsimp only [C]
      ring

theorem lowRegularityPrincipalOperatorH1_continuousOn
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ContinuousOn (lowRegularityPrincipalOperatorH1 (I := I) (M := M) g)
        {T : TensorHs (I := I) (M := M) g 0 2 (2 : ℝ) | ‖T‖ ≤ ρ} := by
  obtain ⟨ρ, C, hρ, hC, hinv⟩ :=
    invPerturbH1_norm (I := I) (M := M) hDim g
  refine ⟨ρ, hρ, ?_⟩
  have hsand : Continuous fun B : rank4End1 (I := I) (M := M) g =>
      (cometricDoubleTraceH1 (I := I) (M := M) g).comp
        (B.comp (secondCovariantDerivativeH3ToH1 (I := I) (M := M) g)) := by
    have hin : Continuous fun B : rank4End1 (I := I) (M := M) g =>
        B.comp (secondCovariantDerivativeH3ToH1 (I := I) (M := M) g) :=
      (ContinuousLinearMap.compL ℝ
        (rank2H3 (I := I) (M := M) g)
        (rank4H1 (I := I) (M := M) g)
        (rank4H1 (I := I) (M := M) g)).continuous₂.comp
          (continuous_id.prodMk continuous_const)
    exact (ContinuousLinearMap.compL ℝ
      (rank2H3 (I := I) (M := M) g)
      (rank4H1 (I := I) (M := M) g)
      (rank2H1 (I := I) (M := M) g)).continuous₂.comp
        (continuous_const.prodMk hin)
  intro T hT
  have hhalf : ‖perturbH1 (I := I) (M := M) g T‖ ≤ (1 : ℝ) / 2 :=
    (hinv T hT).1
  have hlt : ‖-perturbH1 (I := I) (M := M) g T‖ < 1 := by
    rw [norm_neg]
    linarith
  have hbase : ContinuousAt
      (fun S : metricH2 (I := I) (M := M) g =>
        (1 : rank4End1 (I := I) (M := M) g) +
          perturbH1 (I := I) (M := M) g S) T :=
    (continuous_const.add
      (perturbH1 (I := I) (M := M) g).continuous).continuousAt
  have hring := NormedRing.inverse_continuousAt
    (Units.oneSub (-perturbH1 (I := I) (M := M) g T) hlt)
  rw [Units.val_oneSub, sub_neg_eq_add] at hring
  have hstep : ContinuousAt
      (fun S : metricH2 (I := I) (M := M) g =>
        invPerturbH1 (I := I) (M := M) g S) T := by
    refine ContinuousAt.sub ?_ continuousAt_const
    exact ContinuousAt.comp
      (f := fun S : metricH2 (I := I) (M := M) g =>
        (1 : rank4End1 (I := I) (M := M) g) +
          perturbH1 (I := I) (M := M) g S) hring hbase
  exact (ContinuousAt.comp
    (f := fun S : metricH2 (I := I) (M := M) g =>
      invPerturbH1 (I := I) (M := M) g S)
    hsand.continuousAt hstep).continuousWithinAt

private noncomputable def inc43
    (g : SmoothRiemannianMetric I M) :
    rank2H4 (I := I) (M := M) g →L[ℝ]
      rank2H3 (I := I) (M := M) g :=
  tensorHsInclusion (I := I) (M := M) (g := g)
    (r := 0) (s := 2) (by norm_num : (3 : ℝ) ≤ (4 : ℝ))

private noncomputable def inc21
    (g : SmoothRiemannianMetric I M) :
    rank2H2 (I := I) (M := M) g →L[ℝ]
      rank2H1 (I := I) (M := M) g :=
  tensorHsInclusion (I := I) (M := M) (g := g)
    (r := 0) (s := 2)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ (2 : ℝ))

private noncomputable def inc421
    (g : SmoothRiemannianMetric I M) :
    rank4H2 (I := I) (M := M) g →L[ℝ]
      rank4H1 (I := I) (M := M) g :=
  tensorHsInclusion (I := I) (M := M) (g := g)
    (r := 0) (s := 4)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ (2 : ℝ))

private theorem hessian_comm
    (g : SmoothRiemannianMetric I M) :
    (inc421 (I := I) (M := M) g).comp
        (secondCovariantDerivativeH4ToH2 (I := I) (M := M) g) =
      (secondCovariantDerivativeH3ToH1 (I := I) (M := M) g).comp
        (inc43 (I := I) (M := M) g) := by
  apply ContinuousLinearMap.ext
  intro U
  let ι := ccToHsLin (I := I) (M := M) g 2 (4 : ℝ)
  have hdense : DenseRange ι :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hfun := hdense.equalizer
    ((inc421 (I := I) (M := M) g).comp
      (secondCovariantDerivativeH4ToH2 (I := I) (M := M) g)).continuous
    ((secondCovariantDerivativeH3ToH1 (I := I) (M := M) g).comp
      (inc43 (I := I) (M := M) g)).continuous (by
        funext W
        simp only [Function.comp_apply, ι, ccToHsLin_apply, inc421, inc43,
          ContinuousLinearMap.comp_apply]
        rw [hessianH2_core (I := I) (M := M) g W,
          incl_core (I := I) (M := M) g
            (by norm_num : ((1 : ℕ) : ℝ) ≤ (2 : ℝ)),
          incl_core (I := I) (M := M) g
            (by norm_num : (3 : ℝ) ≤ (4 : ℝ)),
          hessianH1_core (I := I) (M := M) g W])
  exact congrFun hfun U

private theorem trace_comm
    (g : SmoothRiemannianMetric I M) :
    (inc21 (I := I) (M := M) g).comp
        (cometricDoubleTraceH2 (I := I) (M := M) g) =
      (cometricDoubleTraceH1 (I := I) (M := M) g).comp
        (inc421 (I := I) (M := M) g) := by
  apply ContinuousLinearMap.ext
  intro V
  let ι := ccToHsLin (I := I) (M := M) g 4 (2 : ℝ)
  have hdense : DenseRange ι :=
    ccToHsLin_dense (I := I) (M := M) g 4 (by positivity)
  have hfun := hdense.equalizer
    ((inc21 (I := I) (M := M) g).comp
      (cometricDoubleTraceH2 (I := I) (M := M) g)).continuous
    ((cometricDoubleTraceH1 (I := I) (M := M) g).comp
      (inc421 (I := I) (M := M) g)).continuous (by
        funext W
        simp only [Function.comp_apply, ι, ccToHsLin_apply, inc21, inc421,
          ContinuousLinearMap.comp_apply]
        rw [traceH2_core (I := I) (M := M) g W,
          incl_core (I := I) (M := M) g
            (by norm_num : ((1 : ℕ) : ℝ) ≤ (2 : ℝ)),
          incl_core (I := I) (M := M) g
            (by norm_num : ((1 : ℕ) : ℝ) ≤ (2 : ℝ)),
          traceH1_core (I := I) (M := M) g W])
  exact congrFun hfun V

private theorem perturb_comm
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (T : metricH2 (I := I) (M := M) g) :
    (inc421 (I := I) (M := M) g).comp
        (metricPerturbationOperatorH2 (I := I) (M := M) g T) =
      (perturbH1 (I := I) (M := M) g T).comp
        (inc421 (I := I) (M := M) g) := by
  let J := inc421 (I := I) (M := M) g
  let L :
      metricH2 (I := I) (M := M) g →L[ℝ]
        (rank4H2 (I := I) (M := M) g →L[ℝ]
          rank4H1 (I := I) (M := M) g) :=
    ((ContinuousLinearMap.compL ℝ
      (rank4H2 (I := I) (M := M) g)
      (rank4H2 (I := I) (M := M) g)
      (rank4H1 (I := I) (M := M) g)) J).comp
        (metricPerturbationOperatorH2 (I := I) (M := M) g)
  let R :
      metricH2 (I := I) (M := M) g →L[ℝ]
        (rank4H2 (I := I) (M := M) g →L[ℝ]
          rank4H1 (I := I) (M := M) g) :=
    ((ContinuousLinearMap.compL ℝ
      (rank4H2 (I := I) (M := M) g)
      (rank4H1 (I := I) (M := M) g)
      (rank4H1 (I := I) (M := M) g)).flip J).comp
        (perturbH1 (I := I) (M := M) g)
  have hdenseT : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hLR : L = R := by
    apply ContinuousLinearMap.ext
    intro S
    have hfun := hdenseT.equalizer L.continuous R.continuous (by
      funext S₀
      apply ContinuousLinearMap.ext
      intro V
      let ι := ccToHsLin (I := I) (M := M) g 4 (2 : ℝ)
      have hdenseV : DenseRange ι :=
        ccToHsLin_dense (I := I) (M := M) g 4 (by positivity)
      have hV := hdenseV.equalizer
        (L (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S₀)).continuous
        (R (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S₀)).continuous (by
          funext W
          have happ2 :
              appHs (I := I) (M := M) g 4 4 2
                  (metricPerturbationCoefficientH2 (I := I) (M := M) g S₀)
                  (ccTensorToHs (I := I) (M := M) g 4 (2 : ℝ) W) =
                ccTensorToHs (I := I) (M := M) g 4 (2 : ℝ)
                  (operatorFieldApply (I := I) (M := M) g 4 4
                    (metricPerturbationCoefficientH2 (I := I) (M := M) g S₀) W) := by
            simpa only [Nat.cast_ofNat] using
              appHs_core (I := I) (M := M) g 4 4 2
                (metricPerturbationCoefficientH2 (I := I) (M := M) g S₀) W
          simp only [Function.comp_apply, ι, ccToHsLin_apply, L, R, J, inc421,
            ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
            ContinuousLinearMap.flip_apply]
          rw [metricPerturbationOperatorH2_apply_smoothCore (I := I) (M := M) hDim g S₀,
            perturbH1_core (I := I) (M := M) hDim g S₀,
            incl_core (I := I) (M := M) g
              (by norm_num : ((1 : ℕ) : ℝ) ≤ (2 : ℝ)) W]
          calc
            _ = tensorHsInclusion (I := I) (M := M) (g := g)
                (r := 0) (s := 4)
                (by norm_num : ((1 : ℕ) : ℝ) ≤ (2 : ℝ))
                (ccTensorToHs (I := I) (M := M) g 4 (2 : ℝ)
                  (operatorFieldApply (I := I) (M := M) g 4 4
                    (metricPerturbationCoefficientH2 (I := I) (M := M) g S₀) W)) :=
              congrArg
                (tensorHsInclusion (I := I) (M := M) (g := g)
                  (r := 0) (s := 4)
                  (by norm_num : ((1 : ℕ) : ℝ) ≤ (2 : ℝ))) happ2
            _ = ccTensorToHs (I := I) (M := M) g 4 ((1 : ℕ) : ℝ)
                (operatorFieldApply (I := I) (M := M) g 4 4
                  (metricPerturbationCoefficientH2 (I := I) (M := M) g S₀) W) :=
              incl_core (I := I) (M := M) g
                (by norm_num : ((1 : ℕ) : ℝ) ≤ (2 : ℝ)) _
            _ = _ := (appHs_core (I := I) (M := M) g 4 4 1
              (metricPerturbationCoefficientH2 (I := I) (M := M) g S₀) W).symm)
      exact congrFun hV V)
    exact congrFun hfun S
  have hpoint := congrArg (fun Q => Q T) hLR
  simpa only [L, R, J, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply] using hpoint

private theorem inv_intertwine
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (J : X →L[ℝ] Y) (A : X →L[ℝ] X) (B : Y →L[ℝ] Y)
    (hBA : B.comp J = J.comp A)
    (hA : IsUnit A) (hB : IsUnit B) :
    (Ring.inverse B).comp J =
      J.comp (Ring.inverse A) := by
  apply ContinuousLinearMap.ext
  intro x
  have hAinv : A * Ring.inverse A = 1 :=
    Ring.mul_inverse_cancel A hA
  have hBinv : Ring.inverse B * B = 1 :=
    Ring.inverse_mul_cancel B hB
  calc
    Ring.inverse B (J x) =
        Ring.inverse B (J ((A * Ring.inverse A) x)) := by
      rw [hAinv, one_apply_eq_self]
    _ = Ring.inverse B
        (B (J (Ring.inverse A x))) := by
      congr 1
      have hx := congrArg
        (fun Q => Q (Ring.inverse A x)) hBA
      change J (A (Ring.inverse A x)) = B (J (Ring.inverse A x))
      exact hx.symm
    _ = J (Ring.inverse A x) := by
      change (Ring.inverse B * B) (J (Ring.inverse A x)) =
        J (Ring.inverse A x)
      rw [hBinv, one_apply_eq_self]

private theorem inverse_comm
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (T : metricH2 (I := I) (M := M) g)
    (h2 : ‖metricPerturbationOperatorH2 (I := I) (M := M) g T‖ < 1)
    (h1 : ‖perturbH1 (I := I) (M := M) g T‖ < 1) :
    (inc421 (I := I) (M := M) g).comp
        (inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g T) =
      (invPerturbH1 (I := I) (M := M) g T).comp
        (inc421 (I := I) (M := M) g) := by
  let J := inc421 (I := I) (M := M) g
  let A := 1 + metricPerturbationOperatorH2 (I := I) (M := M) g T
  let B := 1 + perturbH1 (I := I) (M := M) g T
  have hA : IsUnit A := by
    have hu := isUnit_one_sub_of_norm_lt_one
      (x := -metricPerturbationOperatorH2 (I := I) (M := M) g T) (by
        simpa only [norm_neg] using h2)
    simpa only [A, sub_neg_eq_add] using hu
  have hB : IsUnit B := by
    have hu := isUnit_one_sub_of_norm_lt_one
      (x := -perturbH1 (I := I) (M := M) g T) (by
        simpa only [norm_neg] using h1)
    simpa only [B, sub_neg_eq_add] using hu
  have hfull : B.comp J = J.comp A := by
    apply ContinuousLinearMap.ext
    intro V
    have hp := congrArg (fun Q => Q V)
      (perturb_comm (I := I) (M := M) hDim g T)
    simp only [A, B, J, ContinuousLinearMap.comp_apply,
      add_apply, one_apply_eq_self,
      map_add]
    congr 1
    simpa only [ContinuousLinearMap.comp_apply] using hp.symm
  have hi := inv_intertwine J A B hfull hA hB
  apply ContinuousLinearMap.ext
  intro V
  have hp := congrArg (fun Q => Q V) hi
  simp only [ContinuousLinearMap.comp_apply, A, B, J] at hp
  simp only [inverseMetricPerturbationCorrectionH2, invPerturbH1,
    ContinuousLinearMap.comp_apply, sub_apply,
    one_apply_eq_self, map_sub]
  rw [hp]

private theorem principal_comm_small
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (T : metricH2 (I := I) (M := M) g)
    (h2 : ‖metricPerturbationOperatorH2 (I := I) (M := M) g T‖ < 1)
    (h1 : ‖perturbH1 (I := I) (M := M) g T‖ < 1) :
    (inc21 (I := I) (M := M) g).comp
        (lowRegularityPrincipalOperatorH2 (I := I) (M := M) g T) =
      (lowRegularityPrincipalOperatorH1 (I := I) (M := M) g T).comp
        (inc43 (I := I) (M := M) g) := by
  apply ContinuousLinearMap.ext
  intro U
  let X := secondCovariantDerivativeH4ToH2 (I := I) (M := M) g U
  have htrace := congrArg (fun Q => Q
      (inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g T X))
    (trace_comm (I := I) (M := M) g)
  have hinv := congrArg (fun Q => Q X)
    (inverse_comm (I := I) (M := M) hDim g T h2 h1)
  have hhess := congrArg (fun Q => Q U)
    (hessian_comm (I := I) (M := M) g)
  simp only [lowRegularityPrincipalOperatorH2, lowRegularityPrincipalOperatorH1,
    ContinuousLinearMap.comp_apply] at htrace hinv hhess ⊢
  calc
    _ = cometricDoubleTraceH1 (I := I) (M := M) g
        (inc421 (I := I) (M := M) g
          (inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g T X)) := htrace
    _ = cometricDoubleTraceH1 (I := I) (M := M) g
        (invPerturbH1 (I := I) (M := M) g T
          (inc421 (I := I) (M := M) g X)) := by rw [hinv]
    _ = cometricDoubleTraceH1 (I := I) (M := M) g
        (invPerturbH1 (I := I) (M := M) g T
          (secondCovariantDerivativeH3ToH1 (I := I) (M := M) g
            (inc43 (I := I) (M := M) g U))) := by rw [hhess]

theorem lowRegularityPrincipalOperators_commute
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ T : metricH2 (I := I) (M := M) g, ‖T‖ ≤ ρ →
        (tensorHsInclusion (I := I) (M := M) (g := g)
          (r := 0) (s := 2)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ (2 : ℝ))).comp
            (lowRegularityPrincipalOperatorH2 (I := I) (M := M) g T) =
          (lowRegularityPrincipalOperatorH1 (I := I) (M := M) g T).comp
            (tensorHsInclusion (I := I) (M := M) (g := g)
              (r := 0) (s := 2)
              (by norm_num : (3 : ℝ) ≤ (4 : ℝ))) := by
  obtain ⟨ρ₂, C₂, hρ₂, _, hhigh⟩ :=
    exists_inverseMetricPerturbationCorrectionH2_norm_bound (I := I) (M := M) hDim g
  obtain ⟨ρ₁, C₁, hρ₁, _, hlow⟩ :=
    invPerturbH1_norm (I := I) (M := M) hDim g
  let ρ := min ρ₂ ρ₁
  have hρ : 0 < ρ := by
    exact lt_min hρ₂ hρ₁
  refine ⟨ρ, hρ, ?_⟩
  intro T hT
  have hT₂ : ‖T‖ ≤ ρ₂ :=
    hT.trans (min_le_left _ _)
  have hT₁ : ‖T‖ ≤ ρ₁ :=
    hT.trans (min_le_right _ _)
  have h2 : ‖metricPerturbationOperatorH2 (I := I) (M := M) g T‖ < 1 :=
    (hhigh T hT₂).1.trans_lt (by norm_num)
  have h1 : ‖perturbH1 (I := I) (M := M) g T‖ < 1 :=
    (hlow T hT₁).1.trans_lt (by norm_num)
  change (inc21 (I := I) (M := M) g).comp
      (lowRegularityPrincipalOperatorH2 (I := I) (M := M) g T) =
    (lowRegularityPrincipalOperatorH1 (I := I) (M := M) g T).comp
      (inc43 (I := I) (M := M) g)
  exact principal_comm_small (I := I) (M := M) hDim g T h2 h1

theorem lowRegularityPrincipalOperators_pairing_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C₄₂ C₃₁ : ℝ,
      0 < ρ ∧ 0 ≤ C₄₂ ∧ 0 ≤ C₃₁ ∧
      ∀ T : metricH2 (I := I) (M := M) g, ‖T‖ ≤ ρ →
        ‖lowRegularityPrincipalOperatorH2 (I := I) (M := M) g T‖ ≤ C₄₂ * ‖T‖ ∧
          ‖lowRegularityPrincipalOperatorH1 (I := I) (M := M) g T‖ ≤ C₃₁ * ‖T‖ := by
  obtain ⟨ρ₂, C₂, hρ₂, hC₂, hhigh⟩ :=
    lowRegularityPrincipalOperatorH2_norm_bound (I := I) (M := M) hDim g
  obtain ⟨ρ₁, C₁, hρ₁, hC₁, hlow⟩ :=
    principalLo_norm (I := I) (M := M) hDim g
  let ρ := min ρ₂ ρ₁
  refine ⟨ρ, C₂, C₁, lt_min hρ₂ hρ₁, hC₂, hC₁, ?_⟩
  intro T hT
  exact ⟨hhigh T (hT.trans (min_le_left _ _)),
    hlow T (hT.trans (min_le_right _ _))⟩

theorem lowRegularityPrincipalOperatorH1_apply_smoothCore
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g₀ 0 2),
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ ≤ ρ →
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w =
            g₀.inner y v w +
              ccTensorBilinSymm (I := I) g₀ T y v w) →
        ∀ U : SmoothCcTensor g₀ 0 2,
          lowRegularityPrincipalOperatorH1 (I := I) (M := M) g₀
              (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T)
              (ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) U) =
            ccTensorToHs (I := I) (M := M) g₀ 2
              ((1 : ℕ) : ℝ)
              (deTurckPrincipalCometricTerm (I := I) (M := M) g₀ g₁ U) := by
  obtain ⟨ρc, hρc, hcomm⟩ :=
    lowRegularityPrincipalOperators_commute (I := I) (M := M) hDim g₀
  obtain ⟨ρh, _, hρh, _, hhigh⟩ :=
    exists_inverseMetricPerturbationCorrectionH2_norm_bound (I := I) (M := M) hDim g₀
  let ρ := min ρc ρh
  refine ⟨ρ, lt_min hρc hρh, ?_⟩
  intro g₁ T hT htie U
  let Ts :=
    ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T
  have hTc : ‖Ts‖ ≤ ρc :=
    hT.trans (min_le_left _ _)
  have hTh : ‖Ts‖ ≤ ρh :=
    hT.trans (min_le_right _ _)
  have hsmall :
      ‖metricPerturbationOperatorH2 (I := I) (M := M) g₀ Ts‖ < 1 :=
    (hhigh Ts hTh).1.trans_lt (by norm_num)
  have hsquare := congrArg
    (fun Q => Q
      (ccTensorToHs (I := I) (M := M) g₀ 2 (4 : ℝ) U))
    (hcomm Ts hTc)
  have hcore := congrArg
    (fun Q => Q
      (ccTensorToHs (I := I) (M := M) g₀ 2 (4 : ℝ) U))
    (lowRegularityPrincipalOperatorH2_apply_smoothCore (I := I) (M := M)
      hDim g₀ g₁ T htie hsmall)
  have hcore' :
      lowRegularityPrincipalOperatorH2 (I := I) (M := M) g₀ Ts
          (ccTensorToHs (I := I) (M := M) g₀ 2 (4 : ℝ) U) =
        principalCometricOperatorH2 (I := I) (M := M) g₀ g₁
          (ccTensorToHs (I := I) (M := M) g₀ 2 (4 : ℝ) U) := by
    simpa only [Ts] using hcore
  have hop :=
    principalCometricOperatorH2_apply_smoothCore (I := I) (M := M) hDim g₀ g₁ U
  simp only [ContinuousLinearMap.comp_apply] at hsquare
  calc
    lowRegularityPrincipalOperatorH1 (I := I) (M := M) g₀ Ts
        (ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) U) =
        lowRegularityPrincipalOperatorH1 (I := I) (M := M) g₀ Ts
          (inc43 (I := I) (M := M) g₀
            (ccTensorToHs (I := I) (M := M) g₀ 2 (4 : ℝ) U)) := by
      rw [inc43, incl_core (I := I) (M := M) g₀
        (by norm_num : (3 : ℝ) ≤ (4 : ℝ))]
    _ = inc21 (I := I) (M := M) g₀
        (lowRegularityPrincipalOperatorH2 (I := I) (M := M) g₀ Ts
          (ccTensorToHs (I := I) (M := M) g₀ 2 (4 : ℝ) U)) := by
      exact hsquare.symm
    _ = inc21 (I := I) (M := M) g₀
        (principalCometricOperatorH2 (I := I) (M := M) g₀ g₁
          (ccTensorToHs (I := I) (M := M) g₀ 2 (4 : ℝ) U)) := by
      rw [hcore']
    _ = inc21 (I := I) (M := M) g₀
        (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ)
          (deTurckPrincipalCometricTerm (I := I) (M := M) g₀ g₁ U)) := by
      rw [hop]
    _ = ccTensorToHs (I := I) (M := M) g₀ 2
        ((1 : ℕ) : ℝ)
        (deTurckPrincipalCometricTerm (I := I) (M := M) g₀ g₁ U) := by
      rw [inc21, incl_core (I := I) (M := M) g₀
        (by norm_num : ((1 : ℕ) : ℝ) ≤ (2 : ℝ))]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
