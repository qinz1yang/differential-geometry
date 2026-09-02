import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.CoefficientDeviationSecondOrderBounds
import DifferentialGeometry.Analysis.Estimates.ProductBounds
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJet.Naturality
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradFibreNormPermutationInvariance
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.InverseCoefficientThirdOrderBounds

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Topology DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis (norm_sq_add_le norm_sq_sub_le)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance instCompleteSpaceE : CompleteSpace E :=
  FiniteDimensional.complete ℝ E


theorem phi_dev_h3_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T T' : SmoothCcTensor g 0 2)
          {δ : ℝ} (_hδ_lt : δ < 1)
          (hδ : gFibreOpBound g (ccTensorBilinSymm (I := I) g T) δ)
          {δ' : ℝ} (_hδ'_lt : δ' < 1)
          (hδ' : gFibreOpBound g (ccTensorBilinSymm (I := I) g T') δ')
          {R : ℝ}, 0 ≤ R → R ≤ ρ →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ R →
          ∀ {s : ℝ}, 0 ≤ s → s ≤ 1 →
            (∀ x : M,
              riemannianFiberNormSq (I := I) (M := M) g 4 2 x
                  ((deTurckMetricPrincipalDefectTotal (I := I) (M := M) g
                      (metricPerturbationPath (I := I) g T T' hδ hδ' s) -
                    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g).toSection x) ≤
                (C * R) ^ 2) ∧
              (∑ i ∈ Finset.range 4,
                ‖iteratedCovGrad (I := I) g 4 2 i
                  (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g
                      (metricPerturbationPath (I := I) g T T' hδ hδ' s) -
                    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g)‖ ^ 2) ≤
                (C *
                  (‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ +
                    ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T'‖)) ^ 2 := by
  classical
  obtain ⟨ρ₂, C₂, hρ₂, hC₂, hphi₂⟩ :=
    phi_dev_h2_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨ρ₃, Cinv, hρ₃, hCinv, hinv⟩ :=
    inv_coeff_h3_uniform (I := I) (M := M) hDim gBase hΛ
  let DTH : ℕ → ℝ := pccJetC (E := E)
  let DR : ℕ → ℝ := ricciJetC (E := E)
  let Kjet : ℝ := 8 * (∑ i ∈ Finset.range 4, DTH i) +
    8 * (∑ i ∈ Finset.range 4, DR i)
  let C₃ : ℝ := Real.sqrt Kjet * Cinv
  let C : ℝ := C₂ + C₃
  have hDTH_nn : ∀ i, 0 ≤ DTH i := by
    intro i
    simpa only [DTH] using pccJetC_nonneg (E := E) i
  have hDR_nn : ∀ i, 0 ≤ DR i := by
    intro i
    simpa only [DR] using ricciJetC_nonneg (E := E) i
  have hKjet : 0 ≤ Kjet := by
    dsimp only [Kjet]
    exact add_nonneg
      (mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => hDTH_nn i))
      (mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => hDR_nn i))
  have hC₃ : 0 ≤ C₃ := by
    dsimp only [C₃]
    positivity
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg hC₂ hC₃
  refine ⟨min ρ₂ ρ₃, C, lt_min hρ₂ hρ₃, hC, ?_⟩
  intro g hEq hjet T T' δ hδ_lt hδ δ' hδ'_lt hδ' R hR hRρ hT hT' s hs0 hs1
  have hRρ₂ : R ≤ ρ₂ := hRρ.trans (min_le_left ρ₂ ρ₃)
  have hRρ₃ : R ≤ ρ₃ := hRρ.trans (min_le_right ρ₂ ρ₃)
  obtain ⟨hphi₂_pt, _⟩ :=
    hphi₂ g hEq hjet T T' hδ_lt hδ hδ'_lt hδ' hR hRρ₂ hT hT' hs0 hs1
  have hC₂_le : C₂ ≤ C := by
    dsimp only [C]
    linarith
  have hpoint : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          ((deTurckMetricPrincipalDefectTotal (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T T' hδ hδ' s) -
            deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g).toSection x) ≤
        (C * R) ^ 2 := by
    intro x
    exact (hphi₂_pt x).trans
      (pow_le_pow_left₀ (mul_nonneg hC₂ hR)
        (mul_le_mul_of_nonneg_right hC₂_le hR) 2)
  have hDTH : ∀ (g₁ : SmoothRiemannianMetric I M) (i : ℕ),
      ‖iteratedCovGrad (I := I) g 4 2 i
          (traceHessianCoeff (I := I) (M := M) g g₁ -
            traceHessianCoeff (I := I) (M := M) g g)‖ ^ 2 ≤
        DTH i * ∑ j ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g 2 2 j
            (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)‖ ^ 2 := by
    intro g₁ i
    simpa only [DTH] using trace_l2_le (I := I) (M := M) g g₁ i
  have hDR : ∀ (g₁ : SmoothRiemannianMetric I M) (i : ℕ),
      ‖iteratedCovGrad (I := I) g 4 2 i
          (ricciDeTurckPrincipalCoefficient (I := I) (M := M) g g₁ -
            ricciDeTurckPrincipalCoefficient (I := I) (M := M) g g)‖ ^ 2 ≤
        DR i * ∑ j ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g 2 2 j
            (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)‖ ^ 2 := by
    intro g₁ i
    simpa only [DR] using ricci_l2_le (I := I) (M := M) g g₁ i
  let P : SmoothCcTensor g 0 2 := convexPerturbation (I := I) g T T' s
  let g₁ : SmoothRiemannianMetric I M := metricPerturbationPath (I := I) g T T' hδ hδ' s
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ +
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T'‖
  have hN : 0 ≤ N := by
    dsimp only [N]
    positivity
  have hP₂ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ R := by
    simpa [P] using convex_hs_bound (I := I) (M := M) g T T' hs0 hs1 hT hT'
  have hP₃ : ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) P‖ ≤ N := by
    have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
    rw [show P = (1 - s) • T' + s • T from rfl,
      ccTensorToHs_add, ccTensorToHs_smul, ccTensorToHs_smul]
    calc
      ‖(1 - s) • ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T' +
          s • ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
          ≤ ‖(1 - s) • ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T'‖ +
            ‖s • ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ :=
        norm_add_le _ _
      _ = (1 - s) *
            ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T'‖ +
          s * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg h1ms, abs_of_nonneg hs0]
      _ ≤ ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T'‖ +
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
        exact add_le_add
          (mul_le_of_le_one_left (norm_nonneg _) (by linarith))
          (mul_le_of_le_one_left (norm_nonneg _) hs1)
      _ = N := by
        dsimp only [N]
        ring
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ') :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt ⟨hs0, hs1⟩
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g.inner y v w +
        ccTensorBilinSymm (I := I) g P y v w := by
    intro y v w
    simpa [g₁, P] using metricPerturbationPath_inner_of_mem
      (I := I) g T T' hδ hδ' hs_mem y v w
  obtain ⟨_, hinv_jet⟩ :=
    hinv g hEq hjet P g₁ (hP₂.trans hRρ₃) htie
  have hinv_scale :
      (Cinv * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) P‖) ^ 2 ≤
        (Cinv * N) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hCinv (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hP₃ hCinv) 2
  have hinv_jet_N : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 2 2 j
        (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)‖ ^ 2) ≤
        (Cinv * N) ^ 2 := hinv_jet.trans hinv_scale
  let DTHs : SmoothCcTensor g 4 2 :=
    traceHessianCoeff (I := I) (M := M) g g₁ -
      traceHessianCoeff (I := I) (M := M) g g
  let DRs : SmoothCcTensor g 4 2 :=
    ricciDeTurckPrincipalCoefficient (I := I) (M := M) g g₁ -
      ricciDeTurckPrincipalCoefficient (I := I) (M := M) g g
  let Dev : SmoothCcTensor g 4 2 :=
    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g₁ -
      deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
  let ρA : Equiv.Perm (Fin 4) :=
    traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA
  let ρAT : Equiv.Perm (Fin 4) :=
    traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT
  have hdev_eq : Dev =
      reindexCoeffGen (I := I) (M := M) g 4 2 DTHs ρA +
        reindexCoeffGen (I := I) (M := M) g 4 2 DTHs ρAT -
          (DRs + DRs) := by
    dsimp [Dev, DTHs, DRs]
    rw [deTurckMetricPrincipalDefectTotal_eq_reindex (I := I) (M := M) g g₁,
      deTurckMetricPrincipalDefectTotal_eq_reindex (I := I) (M := M) g g,
      reindexCoeffGen_sub g _ _ ρA,
      reindexCoeffGen_sub g _ _ ρAT]
    abel
  have hDTHsum : (∑ i ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 2 i DTHs‖ ^ 2) ≤
      (∑ i ∈ Finset.range 4, DTH i) * (Cinv * N) ^ 2 := by
    calc
      (∑ i ∈ Finset.range 4, ‖iteratedCovGrad (I := I) g 4 2 i DTHs‖ ^ 2)
          ≤ ∑ i ∈ Finset.range 4, DTH i * (Cinv * N) ^ 2 := by
            apply Finset.sum_le_sum
            intro i hi
            have hi4 : i < 4 := Finset.mem_range.mp hi
            have hwindow : (∑ j ∈ Finset.range (i + 1),
                ‖iteratedCovGrad (I := I) g 2 2 j
                  (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)‖ ^ 2) ≤
                ∑ j ∈ Finset.range 4,
                  ‖iteratedCovGrad (I := I) g 2 2 j
                    (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)‖ ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.range_mono (by omega)) (fun j _ _ => sq_nonneg _)
            have hcoeff :
                ‖iteratedCovGrad (I := I) g 4 2 i DTHs‖ ^ 2 ≤
                  DTH i * ∑ j ∈ Finset.range (i + 1),
                    ‖iteratedCovGrad (I := I) g 2 2 j
                      (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)‖ ^ 2 := by
              simpa [DTHs] using hDTH g₁ i
            exact hcoeff.trans
              (mul_le_mul_of_nonneg_left (hwindow.trans hinv_jet_N) (hDTH_nn i))
      _ = (∑ i ∈ Finset.range 4, DTH i) * (Cinv * N) ^ 2 := by
            rw [Finset.sum_mul]
  have hDRsum : (∑ i ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 2 i DRs‖ ^ 2) ≤
      (∑ i ∈ Finset.range 4, DR i) * (Cinv * N) ^ 2 := by
    calc
      (∑ i ∈ Finset.range 4, ‖iteratedCovGrad (I := I) g 4 2 i DRs‖ ^ 2)
          ≤ ∑ i ∈ Finset.range 4, DR i * (Cinv * N) ^ 2 := by
            apply Finset.sum_le_sum
            intro i hi
            have hi4 : i < 4 := Finset.mem_range.mp hi
            have hwindow : (∑ j ∈ Finset.range (i + 1),
                ‖iteratedCovGrad (I := I) g 2 2 j
                  (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)‖ ^ 2) ≤
                ∑ j ∈ Finset.range 4,
                  ‖iteratedCovGrad (I := I) g 2 2 j
                    (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)‖ ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.range_mono (by omega)) (fun j _ _ => sq_nonneg _)
            have hcoeff :
                ‖iteratedCovGrad (I := I) g 4 2 i DRs‖ ^ 2 ≤
                  DR i * ∑ j ∈ Finset.range (i + 1),
                    ‖iteratedCovGrad (I := I) g 2 2 j
                      (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)‖ ^ 2 := by
              simpa [DRs] using hDR g₁ i
            exact hcoeff.trans
              (mul_le_mul_of_nonneg_left (hwindow.trans hinv_jet_N) (hDR_nn i))
      _ = (∑ i ∈ Finset.range 4, DR i) * (Cinv * N) ^ 2 := by
            rw [Finset.sum_mul]
  have hdev_sum : (∑ i ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 2 i Dev‖ ^ 2) ≤
      8 * (∑ i ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 4 2 i DTHs‖ ^ 2) +
      8 * (∑ i ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 4 2 i DRs‖ ^ 2) := by
    have hsub : (∑ i ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 4 2 i Dev‖ ^ 2) ≤
        2 * (∑ i ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 4 2 i
            (reindexCoeffGen (I := I) (M := M) g 4 2 DTHs ρA +
              reindexCoeffGen (I := I) (M := M) g 4 2 DTHs ρAT)‖ ^ 2) +
        2 * (∑ i ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 4 2 i (DRs + DRs)‖ ^ 2) := by
      calc
        (∑ i ∈ Finset.range 4, ‖iteratedCovGrad (I := I) g 4 2 i Dev‖ ^ 2)
            ≤ ∑ i ∈ Finset.range 4,
              (2 * ‖iteratedCovGrad (I := I) g 4 2 i
                  (reindexCoeffGen (I := I) (M := M) g 4 2 DTHs ρA +
                    reindexCoeffGen (I := I) (M := M) g 4 2 DTHs ρAT)‖ ^ 2 +
                2 * ‖iteratedCovGrad (I := I) g 4 2 i (DRs + DRs)‖ ^ 2) := by
                  apply Finset.sum_le_sum
                  intro i hi
                  rw [hdev_eq, iteratedCovGrad_sub]
                  exact norm_sq_sub_le _ _
        _ = 2 * (∑ i ∈ Finset.range 4,
              ‖iteratedCovGrad (I := I) g 4 2 i
                (reindexCoeffGen (I := I) (M := M) g 4 2 DTHs ρA +
                  reindexCoeffGen (I := I) (M := M) g 4 2 DTHs ρAT)‖ ^ 2) +
            2 * (∑ i ∈ Finset.range 4,
              ‖iteratedCovGrad (I := I) g 4 2 i (DRs + DRs)‖ ^ 2) := by
                rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    have hAB : (∑ i ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 4 2 i
          (reindexCoeffGen (I := I) (M := M) g 4 2 DTHs ρA +
            reindexCoeffGen (I := I) (M := M) g 4 2 DTHs ρAT)‖ ^ 2) ≤
        4 * (∑ i ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 4 2 i DTHs‖ ^ 2) := by
      calc
        _ ≤ ∑ i ∈ Finset.range 4,
            (2 * ‖iteratedCovGrad (I := I) g 4 2 i
                (reindexCoeffGen (I := I) (M := M) g 4 2 DTHs ρA)‖ ^ 2 +
              2 * ‖iteratedCovGrad (I := I) g 4 2 i
                (reindexCoeffGen (I := I) (M := M) g 4 2 DTHs ρAT)‖ ^ 2) := by
                apply Finset.sum_le_sum
                intro i hi
                rw [iteratedCovGrad_add]
                exact norm_sq_add_le _ _
        _ = 4 * (∑ i ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g 4 2 i DTHs‖ ^ 2) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              simp only [norm_sq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g 4 2]
              ring
    have hCC : (∑ i ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 4 2 i (DRs + DRs)‖ ^ 2) ≤
        4 * (∑ i ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 4 2 i DRs‖ ^ 2) := by
      calc
        _ ≤ ∑ i ∈ Finset.range 4,
            (2 * ‖iteratedCovGrad (I := I) g 4 2 i DRs‖ ^ 2 +
              2 * ‖iteratedCovGrad (I := I) g 4 2 i DRs‖ ^ 2) := by
                apply Finset.sum_le_sum
                intro i hi
                rw [iteratedCovGrad_add]
                exact norm_sq_add_le _ _
        _ = 4 * (∑ i ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g 4 2 i DRs‖ ^ 2) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
    linarith
  have hraw : (∑ i ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 2 i Dev‖ ^ 2) ≤
      Kjet * (Cinv * N) ^ 2 := by
    dsimp only [Kjet]
    nlinarith
  have htarget : (C₃ * N) ^ 2 = Kjet * (Cinv * N) ^ 2 := by
    dsimp only [C₃]
    rw [show (Real.sqrt Kjet * Cinv * N) ^ 2 =
        (Real.sqrt Kjet) ^ 2 * (Cinv * N) ^ 2 by ring,
      Real.sq_sqrt hKjet]
  refine ⟨hpoint, ?_⟩
  have hjet_C₃ : (∑ i ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 2 i Dev‖ ^ 2) ≤
      (C₃ * N) ^ 2 := by
    rw [htarget]
    exact hraw
  have hC₃_le : C₃ ≤ C := by
    dsimp only [C]
    linarith
  simpa only [Dev, g₁, N] using hjet_C₃.trans
    (pow_le_pow_left₀ (mul_nonneg hC₃ hN)
      (mul_le_mul_of_nonneg_right hC₃_le hN) 2)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
