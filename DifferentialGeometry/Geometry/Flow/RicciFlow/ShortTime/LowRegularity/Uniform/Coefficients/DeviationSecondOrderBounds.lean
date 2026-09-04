import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalPath.Decomposition
import DifferentialGeometry.Analysis.Estimates.ProductBounds
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJet.Naturality
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Permutation.FiberNorm
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurck.Coefficient.DimensionBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Coefficients.InverseSecondOrderBounds

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
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
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


theorem phi_dev_h2_uniform
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
              (∑ i ∈ Finset.range 3,
                ‖iteratedCovGrad (I := I) g 4 2 i
                  (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g
                      (metricPerturbationPath (I := I) g T T' hδ hδ' s) -
                    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g)‖ ^ 2) ≤
                (C * R) ^ 2 := by
  classical
  obtain ⟨ρ, Cinv, hρ, hCinv, hinv⟩ :=
    exists_inverseMetricDifferenceSlotCoefficient_secondOrder_bound_uniform (I := I) (M := M) hDim gBase hΛ
  let CTH : ℕ → ℝ := pccJetC (E := E)
  let CR : ℕ → ℝ := ricciJetC (E := E)
  let DTH : ℕ → ℝ := pccJetC (E := E)
  let DR : ℕ → ℝ := ricciJetC (E := E)
  let Kpt : ℝ := 8 * CTH 0 + 8 * CR 0
  let Kjet : ℝ := 8 * (∑ i ∈ Finset.range 3, DTH i) +
    8 * (∑ i ∈ Finset.range 3, DR i)
  let K : ℝ := Kpt + Kjet
  let C : ℝ := Real.sqrt K * Cinv
  have hCTH_nn : ∀ i, 0 ≤ CTH i := by
    intro i
    simpa only [CTH] using pccJetC_nonneg (E := E) i
  have hCR_nn : ∀ i, 0 ≤ CR i := by
    intro i
    simpa only [CR] using ricciJetC_nonneg (E := E) i
  have hDTH_nn : ∀ i, 0 ≤ DTH i := by
    intro i
    simpa only [DTH] using pccJetC_nonneg (E := E) i
  have hDR_nn : ∀ i, 0 ≤ DR i := by
    intro i
    simpa only [DR] using ricciJetC_nonneg (E := E) i
  have hKpt : 0 ≤ Kpt := by
    dsimp only [Kpt]
    exact add_nonneg (mul_nonneg (by norm_num) (hCTH_nn 0))
      (mul_nonneg (by norm_num) (hCR_nn 0))
  have hKjet : 0 ≤ Kjet := by
    dsimp only [Kjet]
    exact add_nonneg
      (mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => hDTH_nn i))
      (mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => hDR_nn i))
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro g hEq hjet T T' δ hδ_lt hδ δ' hδ'_lt hδ' R hR hRρ hT hT' s hs0 hs1
  have hCTH : ∀ (g₁ : SmoothRiemannianMetric I M) (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x
          ((iteratedCovGrad (I := I) g 4 2 i
            (traceHessianCoeff (I := I) (M := M) g g₁ -
              traceHessianCoeff (I := I) (M := M) g g)).toSection x) ≤
        CTH i * ∑ j ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g 2 (2 + j) x
            ((iteratedCovGrad (I := I) g 2 2 j
              (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)).toSection x) := by
    intro g₁ i x
    simpa only [CTH] using trace_riemannianFiberNormSq_le (I := I) (M := M) g g₁ i x
  have hCR : ∀ (g₁ : SmoothRiemannianMetric I M) (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x
          ((iteratedCovGrad (I := I) g 4 2 i
            (ricciDeTurckPrincipalCoefficient (I := I) (M := M) g g₁ -
              ricciDeTurckPrincipalCoefficient (I := I) (M := M) g g)).toSection x) ≤
        CR i * ∑ j ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g 2 (2 + j) x
            ((iteratedCovGrad (I := I) g 2 2 j
              (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)).toSection x) := by
    intro g₁ i x
    simpa only [CR] using ricci_riemannianFiberNormSq_le (I := I) (M := M) g g₁ i x
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
  have hP : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ R := by
    simpa [P] using convex_hs_bound (I := I) (M := M) g T T' hs0 hs1 hT hT'
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ') :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt ⟨hs0, hs1⟩
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g.inner y v w +
        ccTensorBilinSymm (I := I) g P y v w := by
    intro y v w
    simpa [g₁, P] using metricPerturbationPath_inner_of_mem
      (I := I) g T T' hδ hδ' hs_mem y v w
  obtain ⟨hinv_pt, hinv_jet⟩ :=
    hinv g hEq hjet P g₁ (hP.trans hRρ) htie
  have hinv_scale :
      (Cinv * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖) ^ 2 ≤
        (Cinv * R) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hCinv (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hP hCinv) 2
  have hinv_jet_R : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 2 2 j (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)‖ ^ 2) ≤
        (Cinv * R) ^ 2 := hinv_jet.trans hinv_scale
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
    traceHessianSlotPerm⁻¹ * deTurckLieSecondOrderDivSlotPermA
  let ρAT : Equiv.Perm (Fin 4) :=
    traceHessianSlotPerm⁻¹ * deTurckLieSecondOrderDivSlotPermAT
  have hdev_eq : Dev =
      reindexCoefficientInputSlots (I := I) (M := M) g 4 2 DTHs ρA +
        reindexCoefficientInputSlots (I := I) (M := M) g 4 2 DTHs ρAT -
          (DRs + DRs) := by
    dsimp [Dev, DTHs, DRs]
    rw [deTurckMetricPrincipalDefectTotal_eq_reindex (I := I) (M := M) g g₁,
      deTurckMetricPrincipalDefectTotal_eq_reindex (I := I) (M := M) g g,
      reindexCoefficientInputSlots_sub g _ _ ρA,
      reindexCoefficientInputSlots_sub g _ _ ρAT]
    abel
  have htarget : (C * R) ^ 2 = K * (Cinv * R) ^ 2 := by
    dsimp [C]
    rw [show (Real.sqrt K * Cinv * R) ^ 2 =
        (Real.sqrt K) ^ 2 * (Cinv * R) ^ 2 by ring,
      Real.sq_sqrt hK]
  refine ⟨?_, ?_⟩
  · intro x
    let Ks : ℝ := riemannianFiberNormSq (I := I) (M := M) g 2 2 x
      ((inverseMetricDifferenceSlotCoefficient (I := I) g g₁).toSection x)
    have hKs : Ks ≤ (Cinv * R) ^ 2 := (hinv_pt x).trans hinv_scale
    have hKs_nn : 0 ≤ Ks := by
      dsimp [Ks]
      exact riemannianFiberNormSq_nonneg (I := I) (M := M) g 2 2 x _
    have hTH0 : riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        (DTHs.toSection x) ≤ CTH 0 * Ks := by
      simpa [DTHs, Ks] using hCTH g₁ 0 x
    have hR0 : riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        (DRs.toSection x) ≤ CR 0 * Ks := by
      simpa [DRs, Ks] using hCR g₁ 0 x
    have hAr : riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        ((reindexCoefficientInputSlots (I := I) (M := M) g 4 2 DTHs ρA).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g 4 2 x (DTHs.toSection x) := by
      rw [reindexCoefficientInputSlots_toSection]
      exact riemannianFiberNormSq_reindexCoefficientInputSlotsFiber
        (I := I) (M := M) g 4 2 x ρA
          (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from DTHs.toSection x)
    have hATr : riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        ((reindexCoefficientInputSlots (I := I) (M := M) g 4 2 DTHs ρAT).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g 4 2 x (DTHs.toSection x) := by
      rw [reindexCoefficientInputSlots_toSection]
      exact riemannianFiberNormSq_reindexCoefficientInputSlotsFiber
        (I := I) (M := M) g 4 2 x ρAT
          (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from DTHs.toSection x)
    have h0 : riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        (Dev.toSection x) ≤
          4 * riemannianFiberNormSq (I := I) (M := M) g 4 2 x
            ((reindexCoefficientInputSlots (I := I) (M := M) g 4 2 DTHs ρA).toSection x) +
          4 * riemannianFiberNormSq (I := I) (M := M) g 4 2 x
            ((reindexCoefficientInputSlots (I := I) (M := M) g 4 2 DTHs ρAT).toSection x) +
          8 * riemannianFiberNormSq (I := I) (M := M) g 4 2 x
            (DRs.toSection x) := by
      rw [hdev_eq]
      simp only [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
        SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
      have hsub := riemannianFiberNormSq_sub_le (I := I) (M := M) g 4 2 x
        ((reindexCoefficientInputSlots (I := I) (M := M) g 4 2 DTHs ρA).toSection x +
          (reindexCoefficientInputSlots (I := I) (M := M) g 4 2 DTHs ρAT).toSection x)
        (DRs.toSection x + DRs.toSection x)
      have hadd1 := riemannianFiberNormSq_add_le (I := I) (M := M) g 4 2 x
        ((reindexCoefficientInputSlots (I := I) (M := M) g 4 2 DTHs ρA).toSection x)
        ((reindexCoefficientInputSlots (I := I) (M := M) g 4 2 DTHs ρAT).toSection x)
      have hadd2 := riemannianFiberNormSq_add_le (I := I) (M := M) g 4 2 x
        (DRs.toSection x) (DRs.toSection x)
      linarith
    rw [hAr, hATr] at h0
    have hraw : riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        (Dev.toSection x) ≤ Kpt * (Cinv * R) ^ 2 := by
      dsimp [Kpt]
      nlinarith [mul_le_mul_of_nonneg_left hKs hKpt, hCTH_nn 0, hCR_nn 0]
    rw [htarget]
    exact hraw.trans (mul_le_mul_of_nonneg_right
      (by dsimp [K]; linarith [hKjet]) (sq_nonneg _))
  · have hDTHsum : (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 4 2 i DTHs‖ ^ 2) ≤
        (∑ i ∈ Finset.range 3, DTH i) * (Cinv * R) ^ 2 := by
      calc
        (∑ i ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 4 2 i DTHs‖ ^ 2)
            ≤ ∑ i ∈ Finset.range 3, DTH i * (Cinv * R) ^ 2 := by
              apply Finset.sum_le_sum
              intro i hi
              have hi3 : i < 3 := Finset.mem_range.mp hi
              have hwindow : (∑ j ∈ Finset.range (i + 1),
                  ‖iteratedCovGrad (I := I) g 2 2 j
                    (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)‖ ^ 2) ≤
                  ∑ j ∈ Finset.range 3,
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
                (mul_le_mul_of_nonneg_left (hwindow.trans hinv_jet_R) (hDTH_nn i))
        _ = (∑ i ∈ Finset.range 3, DTH i) * (Cinv * R) ^ 2 := by
              rw [Finset.sum_mul]
    have hDRsum : (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 4 2 i DRs‖ ^ 2) ≤
        (∑ i ∈ Finset.range 3, DR i) * (Cinv * R) ^ 2 := by
      calc
        (∑ i ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 4 2 i DRs‖ ^ 2)
            ≤ ∑ i ∈ Finset.range 3, DR i * (Cinv * R) ^ 2 := by
              apply Finset.sum_le_sum
              intro i hi
              have hi3 : i < 3 := Finset.mem_range.mp hi
              have hwindow : (∑ j ∈ Finset.range (i + 1),
                  ‖iteratedCovGrad (I := I) g 2 2 j
                    (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)‖ ^ 2) ≤
                  ∑ j ∈ Finset.range 3,
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
                (mul_le_mul_of_nonneg_left (hwindow.trans hinv_jet_R) (hDR_nn i))
        _ = (∑ i ∈ Finset.range 3, DR i) * (Cinv * R) ^ 2 := by
              rw [Finset.sum_mul]
    have hdev_sum : (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 4 2 i Dev‖ ^ 2) ≤
        8 * (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 4 2 i DTHs‖ ^ 2) +
        8 * (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 4 2 i DRs‖ ^ 2) := by
      have hsub : (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 4 2 i Dev‖ ^ 2) ≤
          2 * (∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 4 2 i
              (reindexCoefficientInputSlots (I := I) (M := M) g 4 2 DTHs ρA +
                reindexCoefficientInputSlots (I := I) (M := M) g 4 2 DTHs ρAT)‖ ^ 2) +
          2 * (∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 4 2 i (DRs + DRs)‖ ^ 2) := by
        calc
          (∑ i ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 4 2 i Dev‖ ^ 2)
              ≤ ∑ i ∈ Finset.range 3,
                (2 * ‖iteratedCovGrad (I := I) g 4 2 i
                    (reindexCoefficientInputSlots (I := I) (M := M) g 4 2 DTHs ρA +
                      reindexCoefficientInputSlots (I := I) (M := M) g 4 2 DTHs ρAT)‖ ^ 2 +
                  2 * ‖iteratedCovGrad (I := I) g 4 2 i (DRs + DRs)‖ ^ 2) := by
                    apply Finset.sum_le_sum
                    intro i hi
                    rw [hdev_eq, iteratedCovGrad_sub]
                    exact norm_sq_sub_le _ _
          _ = 2 * (∑ i ∈ Finset.range 3,
                ‖iteratedCovGrad (I := I) g 4 2 i
                  (reindexCoefficientInputSlots (I := I) (M := M) g 4 2 DTHs ρA +
                    reindexCoefficientInputSlots (I := I) (M := M) g 4 2 DTHs ρAT)‖ ^ 2) +
              2 * (∑ i ∈ Finset.range 3,
                ‖iteratedCovGrad (I := I) g 4 2 i (DRs + DRs)‖ ^ 2) := by
                  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      have hAB : (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 4 2 i
            (reindexCoefficientInputSlots (I := I) (M := M) g 4 2 DTHs ρA +
              reindexCoefficientInputSlots (I := I) (M := M) g 4 2 DTHs ρAT)‖ ^ 2) ≤
          4 * (∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 4 2 i DTHs‖ ^ 2) := by
        calc
          _ ≤ ∑ i ∈ Finset.range 3,
              (2 * ‖iteratedCovGrad (I := I) g 4 2 i
                  (reindexCoefficientInputSlots (I := I) (M := M) g 4 2 DTHs ρA)‖ ^ 2 +
                2 * ‖iteratedCovGrad (I := I) g 4 2 i
                  (reindexCoefficientInputSlots (I := I) (M := M) g 4 2 DTHs ρAT)‖ ^ 2) := by
                  apply Finset.sum_le_sum
                  intro i hi
                  rw [iteratedCovGrad_add]
                  exact norm_sq_add_le _ _
          _ = 4 * (∑ i ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g 4 2 i DTHs‖ ^ 2) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i hi
                simp only [norm_sq_iteratedCovGrad_reindexCoefficientInputSlots_eq (I := I) (M := M) g 4 2]
                ring
      have hCC : (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 4 2 i (DRs + DRs)‖ ^ 2) ≤
          4 * (∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 4 2 i DRs‖ ^ 2) := by
        calc
          _ ≤ ∑ i ∈ Finset.range 3,
              (2 * ‖iteratedCovGrad (I := I) g 4 2 i DRs‖ ^ 2 +
                2 * ‖iteratedCovGrad (I := I) g 4 2 i DRs‖ ^ 2) := by
                  apply Finset.sum_le_sum
                  intro i hi
                  rw [iteratedCovGrad_add]
                  exact norm_sq_add_le _ _
          _ = 4 * (∑ i ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g 4 2 i DRs‖ ^ 2) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i hi
                ring
      linarith
    have hraw : (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 4 2 i Dev‖ ^ 2) ≤
        Kjet * (Cinv * R) ^ 2 := by
      dsimp [Kjet]
      nlinarith
    rw [htarget]
    exact hraw.trans (mul_le_mul_of_nonneg_right
      (by dsimp [K]; linarith [hKpt]) (sq_nonneg _))

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
