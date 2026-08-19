import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.MixedConnectionDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.RicciDerivativeCoefficientBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.VectorBundleDerivativeBounds

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev (covariantJetNormSq
  covariantJetNormSq_nonneg covariantJetNormSq_smul covariantJetNormSq_sum_four_le)
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral (ccTensorToHs ccTensorToHs_smul)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

namespace RicciDeTurckPairing

theorem exists_lowOrderFirstDerivativeCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδT hδZ s -
            affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g U hδU hδZ s) ≤
        (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
  obtain ⟨ρr, Br, hρr, hBr, hric⟩ :=
    exists_ricciConnectionDifferenceDerivativeCoefficient_pairing_secondOrder_bound
      (I := I) (M := M) hDim g
  obtain ⟨ρv, Bv, hρv, hBv, hvb⟩ :=
    exists_lieCorrectionZeroVectorBundleDerivativeCoefficient_pairing_secondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨ρa, Ba, hρa, hBa, hamix⟩ :=
    exists_lieCorrectionZeroMixedConnectionDerivativeCoefficient_pairing_secondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨ρq, Bq, hρq, hBq, hquad⟩ :=
    exists_lieCorrectionQuadraticFirstDerivativeCoefficient_pairing_secondOrder_bound (I := I) (M := M) hDim g
  let ρ : ℝ := min (min ρr ρv) (min ρa ρq)
  let C : ℝ → ℝ := fun R => 2 * Br R + Bv R + Ba R + Bq R
  let B : ℝ → ℝ := fun R => 8 * C R
  have hρ : 0 < ρ := lt_min (lt_min hρr hρv) (lt_min hρa hρq)
  have hC : ∀ R : ℝ, 0 ≤ R → 0 ≤ C R := by
    intro R hR
    exact add_nonneg
      (add_nonneg (add_nonneg (mul_nonneg (by norm_num) (hBr R hR))
        (hBv R hR)) (hBa R hR)) (hBq R hR)
  have hB : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R := by
    intro R hR
    exact mul_nonneg (by norm_num) (hC R hR)
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ hTn hUn
    R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  let gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s
  let gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s
  let P : SmoothCcTensor g 0 2 := s • T
  let Q : SmoothCcTensor g 0 2 := s • U
  let D : ℝ := D3 + D2 + A * D2 + N
  let X : ℝ := C R * (1 + A) * D
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by
    nlinarith [hs.1, hs.2]
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [P, ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hQsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g Q x u v =
        ccTensorBilin (I := I) g Q x v u := by
    intro x u v
    simp only [Q, ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hU x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [gmT, P, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [gmU, Q, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g U 0 hδU hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw := convexPerturbation_gFibreOpBound_abs
      (I := I) g T 0 hδT hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [P, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hδQ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g Q) δ := by
    intro x u v
    have hraw := convexPerturbation_gFibreOpBound_abs
      (I := I) g U 0 hδU hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [Q, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    simp only [P, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hQ2 : covariantJetNormSq (I := I) (M := M) g 2 Q ≤ R ^ 2 := by
    simp only [Q, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g U) hs2).trans hU2
  have hP3 : covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    simp only [P, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g T) hs2).trans hT3
  have hQ3 : covariantJetNormSq (I := I) (M := M) g 3 Q ≤ A ^ 2 := by
    simp only [Q, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g U) hs2).trans hU3
  have hPQ2 : covariantJetNormSq (I := I) (M := M) g 2 (P - Q) ≤ D2 ^ 2 := by
    rw [show P - Q = s • (T - U) by simp only [P, Q, smul_sub], covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g (T - U)) hs2).trans hTU2
  have hPQ3 : covariantJetNormSq (I := I) (M := M) g 3 (P - Q) ≤ D3 ^ 2 := by
    rw [show P - Q = s • (T - U) by simp only [P, Q, smul_sub], covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g (T - U)) hs2).trans hTU3
  have hPn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ := by
    simp only [P, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa only [one_mul] using hTn)
  have hQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρ := by
    simp only [Q, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa only [one_mul] using hUn)
  have hPQn :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    rw [show P - Q = s • (T - U) by simp only [P, Q, smul_sub],
      ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa only [one_mul] using hTUn)
  have hr : covariantJetNormSq (I := I) (M := M) g 2
      (ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gmT P -
        ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gmU Q) ≤
      (Br R * (1 + A) * D) ^ 2 := by
    simpa only [D] using
      hric gmT gmU P Q hPsymm hQsymm hPtie hQtie
        hδ_le hδ0 hδP hδQ hδZ
        (hPn.trans ((min_le_left _ _).trans (min_le_left _ _)))
        (hQn.trans ((min_le_left _ _).trans (min_le_left _ _)))
        R A D2 D3 N hR hA hD2 hD3 hN
        hP2 hQ2 hP3 hQ3 hPQ2 hPQ3 hPQn
  have hv : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gmT P -
        lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gmU Q) ≤
      (Bv R * (1 + A) * D) ^ 2 := by
    simpa only [D] using
      hvb gmT gmU P Q hPsymm hQsymm hPtie hQtie
        hδ_le hδ0 hδP hδQ hδZ
        (hPn.trans ((min_le_left _ _).trans (min_le_right _ _)))
        (hQn.trans ((min_le_left _ _).trans (min_le_right _ _)))
        R A D2 D3 N hR hA hD2 hD3 hN
        hP2 hQ2 hP3 hQ3 hPQ2 hPQ3 hPQn
  have ha : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gmT g P -
        lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gmU g Q) ≤
      (Ba R * (1 + A) * D) ^ 2 := by
    simpa only [D] using
      hamix gmT gmU P Q hPsymm hQsymm hPtie hQtie
        hδ_le hδ0 hδP hδQ hδZ
        (hPn.trans ((min_le_right _ _).trans (min_le_left _ _)))
        (hQn.trans ((min_le_right _ _).trans (min_le_left _ _)))
        R A D2 D3 N hR hA hD2 hD3 hN
        hP2 hQ2 hP3 hQ3 hPQ2 hPQ3 hPQn
  have hq : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gmT P -
        lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gmU Q) ≤
      (Bq R * (1 + A) * D) ^ 2 := by
    simpa only [D] using
      hquad gmT gmU P Q hPsymm hQsymm hPtie hQtie
        hδ_le hδ0 hδP hδQ hδZ
        (hPn.trans ((min_le_right _ _).trans (min_le_right _ _)))
        (hQn.trans ((min_le_right _ _).trans (min_le_right _ _)))
        R A D2 D3 N hR hA hD2 hD3 hN
        hP2 hQ2 hP3 hQ3 hPQ2 hPQ3 hPQn
  have hD : 0 ≤ D :=
    add_nonneg (add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2)) hN
  have honeA : 0 ≤ 1 + A := add_nonneg (by norm_num) hA
  have hfac : 0 ≤ (1 + A) * D := mul_nonneg honeA hD
  have hcr : 2 * Br R ≤ C R := by
    simp only [C]
    linarith [hBv R hR, hBa R hR, hBq R hR]
  have hcv : Bv R ≤ C R := by
    simp only [C]
    linarith [hBr R hR, hBa R hR, hBq R hR]
  have hca : Ba R ≤ C R := by
    simp only [C]
    linarith [hBr R hR, hBv R hR, hBq R hR]
  have hcq : Bq R ≤ C R := by
    simp only [C]
    linarith [hBr R hR, hBv R hR, hBa R hR]
  have hcrX : 2 * Br R * (1 + A) * D ≤ X := by
    have h := mul_le_mul_of_nonneg_right hcr hfac
    simpa only [X, mul_assoc] using h
  have hcvX : Bv R * (1 + A) * D ≤ X := by
    have h := mul_le_mul_of_nonneg_right hcv hfac
    simpa only [X, mul_assoc] using h
  have hcaX : Ba R * (1 + A) * D ≤ X := by
    have h := mul_le_mul_of_nonneg_right hca hfac
    simpa only [X, mul_assoc] using h
  have hcqX : Bq R * (1 + A) * D ≤ X := by
    have h := mul_le_mul_of_nonneg_right hcq hfac
    simpa only [X, mul_assoc] using h
  let XR : SmoothCcTensor g 3 2 := (-2 : ℝ) •
    (ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gmT P -
      ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gmU Q)
  let XV : SmoothCcTensor g 3 2 :=
    lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gmT P -
      lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gmU Q
  let XA : SmoothCcTensor g 3 2 :=
    lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gmT g P -
      lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gmU g Q
  let XQ : SmoothCcTensor g 3 2 :=
    lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gmT P -
      lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gmU Q
  have hXR : covariantJetNormSq (I := I) (M := M) g 2 XR ≤ X ^ 2 := by
    simp only [XR, covariantJetNormSq_smul]
    norm_num
    calc
      4 * covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gmT P -
            ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gmU Q) ≤
        4 * (Br R * (1 + A) * D) ^ 2 :=
          mul_le_mul_of_nonneg_left hr (by norm_num)
      _ = (2 * Br R * (1 + A) * D) ^ 2 := by ring
      _ ≤ X ^ 2 := pow_le_pow_left₀
        (mul_nonneg (mul_nonneg
          (mul_nonneg (by norm_num) (hBr R hR)) honeA) hD) hcrX 2
  have hXV : covariantJetNormSq (I := I) (M := M) g 2 XV ≤ X ^ 2 := by
    exact hv.trans (pow_le_pow_left₀
      (mul_nonneg (mul_nonneg (hBv R hR) honeA) hD) hcvX 2)
  have hXA : covariantJetNormSq (I := I) (M := M) g 2 XA ≤ X ^ 2 := by
    exact ha.trans (pow_le_pow_left₀
      (mul_nonneg (mul_nonneg (hBa R hR) honeA) hD) hcaX 2)
  have hXQ : covariantJetNormSq (I := I) (M := M) g 2 XQ ≤ X ^ 2 := by
    exact hq.trans (pow_le_pow_left₀
      (mul_nonneg (mul_nonneg (hBq R hR) honeA) hD) hcqX 2)
  have hsplit :
      affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδT hδZ s -
          affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g U hδU hδZ s =
        XR + XV + XA + XQ := by
    simp only [affineLowOrderFirstDerivativeCoefficientPath, lowOrderFirstDerivativeCoefficientPath, gmT, gmU, P, Q, XR, XV, XA, XQ,
      ricciConnectionDifferenceDerivativeCoefficient_smul, lieCorrectionZeroVectorBundleDerivativeCoefficient_smul, lieCorrectionZeroMixedConnectionDerivativeCoefficient_smul, lieCorrectionQuadraticFirstDerivativeCoefficient_smul]
    module
  rw [hsplit]
  have hsum := covariantJetNormSq_sum_four_le (I := I) (M := M) g XR XV XA XQ X
    hXR hXV hXA hXQ
  simpa only [B, X, mul_assoc] using hsum

theorem exists_lowOrderFirstDerivativePathIntegral_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      covariantJetNormSq (I := I) (M := M) g 2
          (lowOrderFirstDerivativePathIntegral (I := I) (M := M) g T
              (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ -
            lowOrderFirstDerivativePathIntegral (I := I) (M := M) g U
              (lt_of_le_of_lt hδ_le (by norm_num)) hδU hδZ) ≤
        (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
  obtain ⟨ρ, B, hρ, hB, hpoint⟩ :=
    exists_lowOrderFirstDerivativeCoefficient_pairing_secondOrder_bound
      (I := I) (M := M) hDim g
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ hTn hUn
    R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  let S : Set ℝ := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  let Φ : ℝ → SmoothCcTensor g 3 2 := fun s =>
    affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδT hδZ s -
      affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g U hδU hδZ s
  let D : ℝ := D3 + D2 + A * D2 + N
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ S := by
    dsimp only [S]
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hjoint : JointlySmoothCcTensorFamily (I := I) g 3 2 S Φ := by
    dsimp only [S, Φ]
    exact jointlySmoothCcTensorFamily_sub (I := I) (M := M) g
      (affineLowOrderFirstDerivativeCoefficientPath_jointlySmooth (I := I) (M := M) g T hδT hδZ)
      (affineLowOrderFirstDerivativeCoefficientPath_jointlySmooth (I := I) (M := M) g U hδU hδZ)
  have hD : 0 ≤ D :=
    add_nonneg (add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2)) hN
  have hBtot : 0 ≤ B R * (1 + A) * D :=
    mul_nonneg (mul_nonneg (hB R hR) (add_nonneg (by norm_num) hA)) hD
  have hpath := path_jetL2_le (I := I) (M := M) g 3 2 2
    Φ S metricPerturbationPathDomain_isOpen hSI hjoint hBtot
    (fun s hs => by
      simpa only [Φ, D, covariantJetNormSq, Nat.reduceAdd] using
        hpoint T U hT hU hδ_le hδ0 hδT hδU hδZ hTn hUn
          R A D2 D3 N hR hA hD2 hD3 hN
          hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn hs)
  rw [lowOrderFirstDerivativePathIntegral_sub (I := I) (M := M)
    g T U hδ_lt hδT hδU hδZ]
  simpa only [lowOrderFirstDerivativePathIntegralDifference, Φ, S, D, covariantJetNormSq, Nat.reduceAdd] using hpath

end RicciDeTurckPairing
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
