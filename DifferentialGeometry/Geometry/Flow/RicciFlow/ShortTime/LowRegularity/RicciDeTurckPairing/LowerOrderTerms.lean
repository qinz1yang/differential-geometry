import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.MetricDifference
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.LinearTerms
import DifferentialGeometry.Analysis.Estimates.QuarticInterpolation
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJet.Interpolation
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrection.ZeroOrder.ReindexedPureTraceCovariantJet

noncomputable section

open Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis (quartic_product_sum_le_interpolation_square
  three_term_sq_le_weighted_product)
open DifferentialGeometry.Analysis.Spectral (ccOperatorFieldComp ccTensorToHs ccTensorToHs_smul deTurckLieTopOrderPairingFamily
  lieCorrectionZeroMixedConnection lieCorrectionZeroRiemann lieCorrectionZeroVectorBundle pureTrace slotExtend slotExtendIter slotExtend_sub)
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private theorem exists_lieCorrectionZeroMixedConnectionHalfRF_fourthOrder_tame_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
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
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A A4 D2 D3 D4 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ A4 → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ D4 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 T ≤ A4 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 U ≤ A4 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 (T - U) ≤ D4 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ (σlast : Equiv.Perm (Fin 4)),
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g σlast -
            lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
              (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g σlast) ≤
        (B0 R * (1 + A) * (D4 + D3 + D2 + N) +
          B1 R * A4 * (D3 + N)) ^ 2 := by
  obtain ⟨Ca1, hCa1, happ1⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 4 2
  obtain ⟨Ca2, hCa2, happ2⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 6 4
  obtain ⟨Ca3, hCa3, happ3⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 3 6
  obtain ⟨Ca4, hCa4, happ4⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 5 3
  obtain ⟨ρt2, Ct2, hρt2, hCt2, htp2⟩ :=
    RicciDeTurckLowOrder.trace2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρt3, Ct3, hρt3, hCt3, htp3⟩ :=
    RicciDeTurckLowOrder.trace3_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρt4, Ct4, hρt4, hCt4, htp4⟩ :=
    RicciDeTurckLowOrder.trace4_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb2, Bt2, hρb2, hBt2, htb2⟩ :=
    RicciDeTurckLowOrder.trace_two_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρb3, Bt3, hρb3, hBt3, htb3⟩ :=
    RicciDeTurckLowOrder.trace_three_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρb4, Bt4, hρb4, hBt4, htb4⟩ :=
    RicciDeTurckLowOrder.trace_four_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨B0m, B1m, hB0m, hB1m, hmcdp⟩ :=
    RicciDeTurckLowOrder.mcd_pair_h2 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bm, hBm, hmcdb⟩ :=
    RicciDeTurckLowOrder.metric_connection_difference_coefficient_sobolev_two_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Cip, hCip, hinterp⟩ := covariantJetNormSq_three_interpolation (I := I) (M := M) g 2
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hfr2 : (0 : ℝ) ≤ fr ^ 2 := sq_nonneg _
  have hfr3 : (0 : ℝ) ≤ fr ^ 3 := pow_nonneg hfr 3
  set ρ : ℝ := min (min ρt2 (min ρt3 ρt4)) (min ρb2 (min ρb3 ρb4))
    with hρdef
  have hρ0 : 0 < ρ :=
    lt_min (lt_min hρt2 (lt_min hρt3 hρt4))
      (lt_min hρb2 (lt_min hρb3 hρb4))
  let S5b : ℝ → ℝ := fun R => fr ^ 2 * (Bm R) ^ 2
  let E3b : ℝ → ℝ := fun R => fr ^ 3 * (Bm R) ^ 2
  let S4b : ℝ → ℝ := fun R => Ca4 * Bt3 ^ 2 * S5b R
  let S3b : ℝ → ℝ := fun R => Ca3 * E3b R * S4b R
  let S2b : ℝ → ℝ := fun R => Ca2 * Bt4 ^ 2 * S3b R
  let M5 : ℝ → ℝ := fun R => 2 * (B0m R + B1m R) ^ 2 + 2 * (B1m R) ^ 2
  let D5c : ℝ → ℝ := fun R => fr ^ 2 * M5 R
  let E3d : ℝ → ℝ := fun R => fr ^ 3 * M5 R
  let K4 : ℝ → ℝ := fun R => Ca4 * Ct3 ^ 2 * S5b R
  let K5 : ℝ → ℝ := fun R => Ca4 * Bt3 ^ 2 * D5c R
  let K3 : ℝ → ℝ := fun R => Ca3 * E3d R * S4b R
  let K34 : ℝ → ℝ := fun R => Ca3 * E3b R * (2 * (K4 R + K5 R))
  let K2 : ℝ → ℝ := fun R => Ca2 * Ct4 ^ 2 * S3b R
  let K23 : ℝ → ℝ := fun R => Ca2 * Bt4 ^ 2 * (2 * (K3 R + K34 R))
  let K1 : ℝ → ℝ := fun R => Ca1 * Ct2 ^ 2 * S2b R
  let K12 : ℝ → ℝ := fun R => Ca1 * Bt2 ^ 2 * (2 * (K2 R + K23 R))
  let Bh : ℝ → ℝ := fun R => 2 * (K1 R + K12 R)
  let B0 : ℝ → ℝ := fun R => Real.sqrt (8 * Bh R)
  let B1 : ℝ → ℝ := fun R => Real.sqrt (8 * Bh R) * Cip * R
  have hS5b : ∀ R : ℝ, 0 ≤ R → 0 ≤ S5b R := fun R hR =>
    mul_nonneg hfr2 (sq_nonneg _)
  have hE3b : ∀ R : ℝ, 0 ≤ R → 0 ≤ E3b R := fun R hR =>
    mul_nonneg hfr3 (sq_nonneg _)
  have hS4b : ∀ R : ℝ, 0 ≤ R → 0 ≤ S4b R := fun R hR =>
    mul_nonneg (mul_nonneg hCa4 (sq_nonneg _)) (hS5b R hR)
  have hS3b : ∀ R : ℝ, 0 ≤ R → 0 ≤ S3b R := fun R hR =>
    mul_nonneg (mul_nonneg hCa3 (hE3b R hR)) (hS4b R hR)
  have hS2b : ∀ R : ℝ, 0 ≤ R → 0 ≤ S2b R := fun R hR =>
    mul_nonneg (mul_nonneg hCa2 (sq_nonneg _)) (hS3b R hR)
  have hM5 : ∀ R : ℝ, 0 ≤ R → 0 ≤ M5 R := fun R hR => by
    have h1 : (0 : ℝ) ≤ 2 * (B0m R + B1m R) ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ 2 * (B1m R) ^ 2 := by positivity
    simp only [M5]
    exact add_nonneg h1 h2
  have hD5c : ∀ R : ℝ, 0 ≤ R → 0 ≤ D5c R := fun R hR =>
    mul_nonneg hfr2 (hM5 R hR)
  have hE3d : ∀ R : ℝ, 0 ≤ R → 0 ≤ E3d R := fun R hR =>
    mul_nonneg hfr3 (hM5 R hR)
  have hK4 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K4 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa4 (sq_nonneg _)) (hS5b R hR)
  have hK5 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K5 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa4 (sq_nonneg _)) (hD5c R hR)
  have hK3 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K3 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa3 (hE3d R hR)) (hS4b R hR)
  have hK34 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K34 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa3 (hE3b R hR))
      (mul_nonneg (by norm_num) (add_nonneg (hK4 R hR) (hK5 R hR)))
  have hK2 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K2 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa2 (sq_nonneg _)) (hS3b R hR)
  have hK23 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K23 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa2 (sq_nonneg _))
      (mul_nonneg (by norm_num) (add_nonneg (hK3 R hR) (hK34 R hR)))
  have hK1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K1 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa1 (sq_nonneg _)) (hS2b R hR)
  have hK12 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K12 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa1 (sq_nonneg _))
      (mul_nonneg (by norm_num) (add_nonneg (hK2 R hR) (hK23 R hR)))
  have hBhnn : ∀ R : ℝ, 0 ≤ R → 0 ≤ Bh R := fun R hR => by
    simp only [Bh]
    exact mul_nonneg (by norm_num) (add_nonneg (hK1 R hR) (hK12 R hR))
  refine ⟨ρ, B0, B1, hρ0,
    fun R hR => by
      simp only [B0]
      exact Real.sqrt_nonneg _,
    fun R hR => by
      simp only [B1]
      exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCip) hR, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN
    hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4 hTn hUn hTUn s hs σlast
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by
    simpa only [one_pow] using pow_le_pow_left₀ hs.1 hs.2 2
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [hcP, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hQsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g Q x u v =
        ccTensorBilin (I := I) g Q x v u := by
    intro x u v
    simp only [hcQ, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hU x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem
        (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem
        (I := I) g U 0 hδU hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g T 0 hδT hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.2),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcP, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hδQ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g Q) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g U 0 hδU hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.2),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcQ, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hQ2 : covariantJetNormSq (I := I) (M := M) g 2 Q ≤ R ^ 2 := by
    rw [hcQ, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g U) hs2).trans hU2
  have hP4 : covariantJetNormSq (I := I) (M := M) g 4 P ≤ A4 ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 4) g T) hs2).trans hT4
  have hQ4 : covariantJetNormSq (I := I) (M := M) g 4 Q ≤ A4 ^ 2 := by
    rw [hcQ, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 4) g U) hs2).trans hU4
  have hPQ3 : covariantJetNormSq (I := I) (M := M) g 3 (P - Q) ≤ D3 ^ 2 := by
    have hPQ : P - Q = s • (T - U) := by
      rw [hcP, hcQ, smul_sub]
    rw [hPQ, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g (T - U)) hs2).trans hTU3
  have hPQ2 : covariantJetNormSq (I := I) (M := M) g 2 (P - Q) ≤ D3 ^ 2 :=
    (covariantJetNormSq_mono (I := I) (M := M) g (by norm_num : (2 : ℕ) ≤ 3) (P - Q)).trans hPQ3
  have hball : ∀ ρ' : ℝ, ρ ≤ ρ' →
      (‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ' ∧
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρ') := by
    intro ρ' hρ'
    constructor
    · rw [hcP, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using (hTn.trans hρ'))
    · rw [hcQ, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using (hUn.trans hρ'))
  have hPQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    have hPQ : P - Q = s • (T - U) := by
      rw [hcP, hcQ, smul_sub]
    rw [hPQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTUn)
  set a : ℝ := Real.sqrt (Cip * (R * A4)) with hadef
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hasq : a ^ 2 = Cip * (R * A4) :=
    Real.sq_sqrt (mul_nonneg hCip (mul_nonneg hR hA4))
  have hP3i : covariantJetNormSq (I := I) (M := M) g 3 P ≤ a ^ 2 := by
    rw [hasq]
    exact hinterp P R A4 hR hA4 hP2 hP4
  have hQ3i : covariantJetNormSq (I := I) (M := M) g 3 Q ≤ a ^ 2 := by
    rw [hasq]
    exact hinterp Q R A4 hR hA4 hQ2 hQ4
  set pl2 : ℝ := (1 + a) ^ 2 with hpl2
  have hpl21 : (1 : ℝ) ≤ pl2 := by
    rw [hpl2]
    simpa only [one_pow] using
      pow_le_pow_left₀ zero_le_one (le_add_of_nonneg_right ha0) 2
  have hpl20 : 0 ≤ pl2 := le_trans zero_le_one hpl21
  have hplA2 : a ^ 2 ≤ pl2 := by
    rw [hpl2]
    exact pow_le_pow_left₀ ha0 (le_add_of_nonneg_left zero_le_one) 2
  set u : ℝ := D3 ^ 2 + N ^ 2 with hu
  have hu0 : 0 ≤ u := by
    rw [hu]
    positivity
  have hD3le : D3 ^ 2 ≤ u := by
    rw [hu]
    exact le_add_of_nonneg_right (sq_nonneg N)
  have hD3u : D3 ^ 2 ≤ pl2 * u := by
    calc D3 ^ 2 ≤ u := hD3le
      _ = 1 * u := (one_mul u).symm
      _ ≤ pl2 * u := mul_le_mul_of_nonneg_right hpl21 hu0
  have hNu : N ^ 2 ≤ u := by
    rw [hu]
    exact le_add_of_nonneg_left (sq_nonneg D3)
  set mcdT : SmoothCcTensor g 0 3 :=
    metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gmT g with hmT
  set mcdU : SmoothCcTensor g 0 3 :=
    metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gmU g with hmU
  have hmbT : covariantJetNormSq (I := I) (M := M) g 2 mcdT ≤ (Bm R) ^ 2 * pl2 := by
    have h := hmcdb gmT P hPsymm hPtie hδ_le hδ0 hδP R a hR ha0 hP2 hP3i
    rw [hmT]
    refine h.trans (le_of_eq ?_)
    rw [hpl2]
    ring
  have hmbU : covariantJetNormSq (I := I) (M := M) g 2 mcdU ≤ (Bm R) ^ 2 * pl2 := by
    have h := hmcdb gmU Q hQsymm hQtie hδ_le hδ0 hδQ R a hR ha0 hQ2 hQ3i
    rw [hmU]
    refine h.trans (le_of_eq ?_)
    rw [hpl2]
    ring
  have hmpd : covariantJetNormSq (I := I) (M := M) g 2 (mcdT - mcdU) ≤
      M5 R * (pl2 * u) := by
    have h := hmcdp gmT gmU P Q hPsymm hQsymm hPtie hQtie
      hδ_le hδ0 hδP hδ_le hδ0 hδQ R a D3 D3 hR ha0 hD3 hD3 hQ2 hP3i hPQ2 hPQ3
    rw [hmT, hmU]
    refine h.trans ?_
    have hstep : (B0m R * D3 + B1m R * D3 + B1m R * a * D3) ^ 2 ≤
        2 * (B0m R + B1m R) ^ 2 * D3 ^ 2 +
          2 * (B1m R) ^ 2 * (a ^ 2 * D3 ^ 2) := by
      have hre : B0m R * D3 + B1m R * D3 + B1m R * a * D3 =
          (B0m R + B1m R) * D3 + B1m R * a * D3 := by ring
      rw [hre]
      have hsq : ((B0m R + B1m R) * D3 + B1m R * a * D3) ^ 2 ≤
          2 * (((B0m R + B1m R) * D3) ^ 2 + (B1m R * a * D3) ^ 2) :=
        add_sq_le
      rw [mul_add] at hsq
      refine hsq.trans (le_of_eq ?_)
      ring
    refine hstep.trans ?_
    have hA2D : a ^ 2 * D3 ^ 2 ≤ pl2 * u := by
      have h1 : a ^ 2 * D3 ^ 2 ≤ pl2 * D3 ^ 2 :=
        mul_le_mul_of_nonneg_right hplA2 (sq_nonneg _)
      have h2 : pl2 * D3 ^ 2 ≤ pl2 * u :=
        mul_le_mul_of_nonneg_left hD3le hpl20
      exact h1.trans h2
    have e1 : 2 * (B0m R + B1m R) ^ 2 * D3 ^ 2 ≤
        2 * (B0m R + B1m R) ^ 2 * (pl2 * u) :=
      mul_le_mul_of_nonneg_left hD3u (by positivity)
    have e2 : 2 * (B1m R) ^ 2 * (a ^ 2 * D3 ^ 2) ≤
        2 * (B1m R) ^ 2 * (pl2 * u) :=
      mul_le_mul_of_nonneg_left hA2D (by positivity)
    have hM5eq : M5 R * (pl2 * u) =
        2 * (B0m R + B1m R) ^ 2 * (pl2 * u) +
          2 * (B1m R) ^ 2 * (pl2 * u) := by
      simp only [M5]
      ring
    rw [hM5eq]
    exact add_le_add e1 e2
  have hρc : ρ ≤ ρt2 ∧ ρ ≤ ρt3 ∧ ρ ≤ ρt4 ∧ ρ ≤ ρb2 ∧ ρ ≤ ρb3 ∧
      ρ ≤ ρb4 := by
    rw [hρdef]
    exact ⟨
      le_trans (min_le_left _ _) (min_le_left _ _),
      le_trans (min_le_left _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)),
      le_trans (min_le_left _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _)),
      le_trans (min_le_right _ _) (min_le_left _ _),
      le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)),
      le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _))⟩
  have htrp : ∀ (p : ℕ) (Cp : ℝ) (ρp' : ℝ),
      (∀ (T' U' : SmoothCcTensor g 0 2)
        (gT' gU' : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT'.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T' y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU'.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g U' y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ ρp' →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U'‖ ≤ ρp' →
        covariantJetNormSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT' p -
              pureTrace (I := I) (M := M) g gU' p) ≤
          (Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T' - U')‖) ^ 2) →
      0 ≤ Cp → ρ ≤ ρp' →
      covariantJetNormSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gmT p -
            pureTrace (I := I) (M := M) g gmU p) ≤
        Cp ^ 2 * u := by
    intro p Cp ρp' hpair hCp hρp'
    obtain ⟨hPn, hQn⟩ := hball ρp' hρp'
    have h := hpair P Q gmT gmU hPtie hQtie hPn hQn
    refine h.trans ?_
    have h1 : Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (P - Q)‖ ≤ Cp * N :=
      mul_le_mul_of_nonneg_left hPQn hCp
    have h2 : (Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (P - Q)‖) ^ 2 ≤ (Cp * N) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hCp (norm_nonneg _)) h1 2
    refine h2.trans ?_
    have he : (Cp * N) ^ 2 = Cp ^ 2 * N ^ 2 := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hNu (sq_nonneg Cp)
  have htrb : ∀ (p : ℕ) (Bp : ℝ) (ρp' : ℝ),
      (∀ (T' : SmoothCcTensor g 0 2)
        (gT' : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT'.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T' y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ ρp' →
        covariantJetNormSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT' p) ≤ Bp ^ 2) →
      ρ ≤ ρp' →
      (covariantJetNormSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gmT p) ≤ Bp ^ 2 ∧
        covariantJetNormSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gmU p) ≤ Bp ^ 2) := by
    intro p Bp ρp' hbdd hρp'
    obtain ⟨hPn, hQn⟩ := hball ρp' hρp'
    exact ⟨hbdd P gmT hPtie hPn, hbdd Q gmU hQtie hQn⟩
  have htp2' := htrp 2 Ct2 ρt2 htp2 hCt2 hρc.1
  have htp3' := htrp 3 Ct3 ρt3 htp3 hCt3 hρc.2.1
  have htp4' := htrp 4 Ct4 ρt4 htp4 hCt4 hρc.2.2.1
  have htb2' := htrb 2 Bt2 ρb2 htb2 hρc.2.2.2.1
  have htb3' := htrb 3 Bt3 ρb3 htb3 hρc.2.2.2.2.1
  have htb4' := htrb 4 Bt4 ρb4 htb4 hρc.2.2.2.2.2
  set S5T : SmoothCcTensor g 2 5 :=
    slotExtendIter (I := I) (M := M) g 0 3 2 mcdT with hS5Tdef
  set S5U : SmoothCcTensor g 2 5 :=
    slotExtendIter (I := I) (M := M) g 0 3 2 mcdU with hS5Udef
  set S4T : SmoothCcTensor g 2 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 5 3
      (reindexedPureTrace (I := I) (M := M) g gmT 3 DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour) S5T
    with hS4Tdef
  set S4U : SmoothCcTensor g 2 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 5 3
      (reindexedPureTrace (I := I) (M := M) g gmU 3 DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour) S5U
    with hS4Udef
  set E3T : SmoothCcTensor g 3 6 :=
    slotExtendIter (I := I) (M := M) g 0 3 3 mcdT with hE3Tdef
  set E3U : SmoothCcTensor g 3 6 :=
    slotExtendIter (I := I) (M := M) g 0 3 3 mcdU with hE3Udef
  set S3T : SmoothCcTensor g 2 6 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 3 6 E3T S4T with hS3Tdef
  set S3U : SmoothCcTensor g 2 6 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 3 6 E3U S4U with hS3Udef
  set S2T : SmoothCcTensor g 2 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 6 4
      (reindexedPureTrace (I := I) (M := M) g gmT 4 DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne) S3T
    with hS2Tdef
  set S2U : SmoothCcTensor g 2 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 6 4
      (reindexedPureTrace (I := I) (M := M) g gmU 4 DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne) S3U
    with hS2Udef
  have hHalfT : lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g gmT g σlast =
      ccOperatorFieldComp (I := I) (M := M) g 2 4 2
        (reindexedPureTrace (I := I) (M := M) g gmT 2 σlast) S2T := rfl
  have hHalfU : lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g gmU g σlast =
      ccOperatorFieldComp (I := I) (M := M) g 2 4 2
        (reindexedPureTrace (I := I) (M := M) g gmU 2 σlast) S2U := rfl
  have hS5T2 : covariantJetNormSq (I := I) (M := M) g 2 S5T ≤ S5b R * pl2 := by
    rw [hS5Tdef]
    have h0 : slotExtendIter (I := I) (M := M) g 0 3 2 mcdT =
        slotExtend (I := I) (M := M) g 1 4
          (slotExtend (I := I) (M := M) g 0 3 mcdT) := rfl
    rw [h0]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdT)) ≤
        fr * covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 3 mcdT) :=
        covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 4 _
      _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 mcdT) :=
        mul_le_mul_of_nonneg_left
          (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 3 _) hfr
      _ ≤ fr * (fr * ((Bm R) ^ 2 * pl2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmbT hfr) hfr
      _ = S5b R * pl2 := by
        simp only [S5b]
        ring
  have hE3T2 : covariantJetNormSq (I := I) (M := M) g 2 E3T ≤ E3b R * pl2 := by
    rw [hE3Tdef]
    have h0 : slotExtendIter (I := I) (M := M) g 0 3 3 mcdT =
        slotExtend (I := I) (M := M) g 2 5
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdT)) := rfl
    rw [h0]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 2 5
            (slotExtend (I := I) (M := M) g 1 4
              (slotExtend (I := I) (M := M) g 0 3 mcdT))) ≤
        fr * covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdT)) :=
        covariantJetNormSq_slotExtend_le (I := I) (M := M) g 2 5 _
      _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 3 mcdT)) :=
        mul_le_mul_of_nonneg_left
          (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 4 _) hfr
      _ ≤ fr * (fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 mcdT)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 3 _) hfr) hfr
      _ ≤ fr * (fr * (fr * ((Bm R) ^ 2 * pl2))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmbT hfr) hfr) hfr
      _ = E3b R * pl2 := by
        simp only [E3b]
        ring
  have hE3U2 : covariantJetNormSq (I := I) (M := M) g 2 E3U ≤ E3b R * pl2 := by
    rw [hE3Udef]
    have h0 : slotExtendIter (I := I) (M := M) g 0 3 3 mcdU =
        slotExtend (I := I) (M := M) g 2 5
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdU)) := rfl
    rw [h0]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 2 5
            (slotExtend (I := I) (M := M) g 1 4
              (slotExtend (I := I) (M := M) g 0 3 mcdU))) ≤
        fr * covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdU)) :=
        covariantJetNormSq_slotExtend_le (I := I) (M := M) g 2 5 _
      _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 3 mcdU)) :=
        mul_le_mul_of_nonneg_left
          (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 4 _) hfr
      _ ≤ fr * (fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 mcdU)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 3 _) hfr) hfr
      _ ≤ fr * (fr * (fr * ((Bm R) ^ 2 * pl2))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmbU hfr) hfr) hfr
      _ = E3b R * pl2 := by
        simp only [E3b]
        ring
  have hpl2u : 0 ≤ pl2 * u := mul_nonneg hpl20 hu0
  have hS4T2 : covariantJetNormSq (I := I) (M := M) g 2 S4T ≤ S4b R * pl2 := by
    rw [hS4Tdef]
    refine (happ4 _ S5T).trans ?_
    have htr := (covariantJetNormSq_reindexedPureTrace (I := I) (M := M) g gmT 3 2
      DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour).le.trans htb3'.1
    calc
      Ca4 * covariantJetNormSq (I := I) (M := M) g 2
          (reindexedPureTrace (I := I) (M := M) g gmT 3 DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour) *
        covariantJetNormSq (I := I) (M := M) g 2 S5T ≤
        Ca4 * Bt3 ^ 2 * (S5b R * pl2) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left htr hCa4) hS5T2
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hCa4 (sq_nonneg _))
      _ = S4b R * pl2 := by
        simp only [S4b]
        ring
  have hS3T2 : covariantJetNormSq (I := I) (M := M) g 2 S3T ≤
      S3b R * (pl2 * pl2) := by
    rw [hS3Tdef]
    refine (happ3 E3T S4T).trans ?_
    calc
      Ca3 * covariantJetNormSq (I := I) (M := M) g 2 E3T *
        covariantJetNormSq (I := I) (M := M) g 2 S4T ≤
        Ca3 * (E3b R * pl2) * (S4b R * pl2) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hE3T2 hCa3) hS4T2
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hCa3 (mul_nonneg (hE3b R hR) hpl20))
      _ = S3b R * (pl2 * pl2) := by
        simp only [S3b]
        ring
  have hS2T2 : covariantJetNormSq (I := I) (M := M) g 2 S2T ≤
      S2b R * (pl2 * pl2) := by
    rw [hS2Tdef]
    refine (happ2 _ S3T).trans ?_
    have htr := (covariantJetNormSq_reindexedPureTrace (I := I) (M := M) g gmT 4 2
      DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne).le.trans htb4'.1
    calc
      Ca2 * covariantJetNormSq (I := I) (M := M) g 2
          (reindexedPureTrace (I := I) (M := M) g gmT 4 DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne) *
        covariantJetNormSq (I := I) (M := M) g 2 S3T ≤
        Ca2 * Bt4 ^ 2 * (S3b R * (pl2 * pl2)) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left htr hCa2) hS3T2
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hCa2 (sq_nonneg _))
      _ = S2b R * (pl2 * pl2) := by
        simp only [S2b]
        ring
  have hdel5 : S5T - S5U =
      slotExtend (I := I) (M := M) g 1 4
        (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU)) := by
    rw [hS5Tdef, hS5Udef,
      show slotExtendIter (I := I) (M := M) g 0 3 2 mcdT =
        slotExtend (I := I) (M := M) g 1 4
          (slotExtend (I := I) (M := M) g 0 3 mcdT) from rfl,
      show slotExtendIter (I := I) (M := M) g 0 3 2 mcdU =
        slotExtend (I := I) (M := M) g 1 4
          (slotExtend (I := I) (M := M) g 0 3 mcdU) from rfl,
      slotExtend_sub, slotExtend_sub]
  have hd5 : covariantJetNormSq (I := I) (M := M) g 2 (S5T - S5U) ≤
      D5c R * (pl2 * u) := by
    rw [hdel5]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU))) ≤
        fr * covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU)) :=
        covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 4 _
      _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 (mcdT - mcdU)) :=
        mul_le_mul_of_nonneg_left
          (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 3 _) hfr
      _ ≤ fr * (fr * (M5 R * (pl2 * u))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmpd hfr) hfr
      _ = D5c R * (pl2 * u) := by
        simp only [D5c]
        ring
  have htrd3 : covariantJetNormSq (I := I) (M := M) g 2
      (reindexedPureTrace (I := I) (M := M) g gmT 3 DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour -
        reindexedPureTrace (I := I) (M := M) g gmU 3 DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour) ≤
      Ct3 ^ 2 * u := by
    rw [reindexedPureTrace_sub, covariantJetNormSq_reindexCoeffGen]
    exact htp3'
  have hd4 : covariantJetNormSq (I := I) (M := M) g 2 (S4T - S4U) ≤
      2 * (K4 R * (pl2 * u) + K5 R * (pl2 * u)) := by
    rw [hS4Tdef, hS4Udef]
    have htr := (covariantJetNormSq_reindexedPureTrace (I := I) (M := M) g gmU 3 2
      DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour).le.trans htb3'.2
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (_ - _) ≤
          2 * (Ca4 * (Ct3 ^ 2 * u) * (S5b R * pl2) +
            Ca4 * Bt3 ^ 2 * (D5c R * (pl2 * u))) :=
        covariantJetNormSq_operatorFieldComposition_sub_le (I := I) (M := M) g 2 2 5 3
          Ca4 (Ct3 ^ 2 * u) (S5b R * pl2) (Bt3 ^ 2)
          (D5c R * (pl2 * u)) hCa4 _ _ _ _ happ4 htrd3 hS5T2 htr hd5
      _ = 2 * (K4 R * (pl2 * u) + K5 R * (pl2 * u)) := by
        simp only [K4, K5]
        ring
  have hdelE3 : E3T - E3U =
      slotExtend (I := I) (M := M) g 2 5
        (slotExtend (I := I) (M := M) g 1 4
          (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU))) := by
    rw [hE3Tdef, hE3Udef,
      show slotExtendIter (I := I) (M := M) g 0 3 3 mcdT =
        slotExtend (I := I) (M := M) g 2 5
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdT)) from rfl,
      show slotExtendIter (I := I) (M := M) g 0 3 3 mcdU =
        slotExtend (I := I) (M := M) g 2 5
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdU)) from rfl,
      slotExtend_sub, slotExtend_sub, slotExtend_sub]
  have hdE32 : covariantJetNormSq (I := I) (M := M) g 2 (E3T - E3U) ≤
      E3d R * (pl2 * u) := by
    rw [hdelE3]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 2 5
            (slotExtend (I := I) (M := M) g 1 4
              (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU)))) ≤
        fr * covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU))) :=
        covariantJetNormSq_slotExtend_le (I := I) (M := M) g 2 5 _
      _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU))) :=
        mul_le_mul_of_nonneg_left
          (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 4 _) hfr
      _ ≤ fr * (fr * (fr *
          covariantJetNormSq (I := I) (M := M) g 2 (mcdT - mcdU))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 3 _) hfr) hfr
      _ ≤ fr * (fr * (fr * (M5 R * (pl2 * u)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmpd hfr) hfr) hfr
      _ = E3d R * (pl2 * u) := by
        simp only [E3d]
        ring
  have hd3 : covariantJetNormSq (I := I) (M := M) g 2 (S3T - S3U) ≤
      2 * (K3 R * ((pl2 * pl2) * u) + K34 R * ((pl2 * pl2) * u)) := by
    rw [hS3Tdef, hS3Udef]
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (_ - _) ≤
          2 * (Ca3 * (E3d R * (pl2 * u)) * (S4b R * pl2) +
            Ca3 * (E3b R * pl2) *
              (2 * (K4 R * (pl2 * u) + K5 R * (pl2 * u)))) :=
        covariantJetNormSq_operatorFieldComposition_sub_le (I := I) (M := M) g 2 2 3 6
          Ca3 (E3d R * (pl2 * u)) (S4b R * pl2) (E3b R * pl2)
          (2 * (K4 R * (pl2 * u) + K5 R * (pl2 * u)))
          hCa3 _ _ _ _ happ3 hdE32 hS4T2 hE3U2 hd4
      _ = 2 * (K3 R * ((pl2 * pl2) * u) +
          K34 R * ((pl2 * pl2) * u)) := by
        simp only [K3, K34]
        ring
  have htrd4 : covariantJetNormSq (I := I) (M := M) g 2
      (reindexedPureTrace (I := I) (M := M) g gmT 4 DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne -
        reindexedPureTrace (I := I) (M := M) g gmU 4 DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne) ≤
      Ct4 ^ 2 * u := by
    rw [reindexedPureTrace_sub, covariantJetNormSq_reindexCoeffGen]
    exact htp4'
  have hd2 : covariantJetNormSq (I := I) (M := M) g 2 (S2T - S2U) ≤
      2 * (K2 R * ((pl2 * pl2) * u) + K23 R * ((pl2 * pl2) * u)) := by
    rw [hS2Tdef, hS2Udef]
    have htr := (covariantJetNormSq_reindexedPureTrace (I := I) (M := M) g gmU 4 2
      DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne).le.trans htb4'.2
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (_ - _) ≤
          2 * (Ca2 * (Ct4 ^ 2 * u) * (S3b R * (pl2 * pl2)) +
            Ca2 * Bt4 ^ 2 * (2 * (K3 R * ((pl2 * pl2) * u) +
              K34 R * ((pl2 * pl2) * u)))) :=
        covariantJetNormSq_operatorFieldComposition_sub_le (I := I) (M := M) g 2 2 6 4
          Ca2 (Ct4 ^ 2 * u) (S3b R * (pl2 * pl2)) (Bt4 ^ 2)
          (2 * (K3 R * ((pl2 * pl2) * u) + K34 R * ((pl2 * pl2) * u)))
          hCa2 _ _ _ _ happ2 htrd4 hS3T2 htr hd3
      _ = 2 * (K2 R * ((pl2 * pl2) * u) +
          K23 R * ((pl2 * pl2) * u)) := by
        simp only [K2, K23]
        ring
  have htrd2 : covariantJetNormSq (I := I) (M := M) g 2
      (reindexedPureTrace (I := I) (M := M) g gmT 2 σlast -
        reindexedPureTrace (I := I) (M := M) g gmU 2 σlast) ≤
      Ct2 ^ 2 * u := by
    rw [reindexedPureTrace_sub, covariantJetNormSq_reindexCoeffGen]
    exact htp2'
  have hhalf : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g gmT g σlast -
        lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g gmU g σlast) ≤
      Bh R * ((pl2 * pl2) * u) := by
    rw [hHalfT, hHalfU]
    have htr := (covariantJetNormSq_reindexedPureTrace (I := I) (M := M) g gmU 2 2
      σlast).le.trans htb2'.2
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (_ - _) ≤
          2 * (Ca1 * (Ct2 ^ 2 * u) * (S2b R * (pl2 * pl2)) +
            Ca1 * Bt2 ^ 2 * (2 * (K2 R * ((pl2 * pl2) * u) +
              K23 R * ((pl2 * pl2) * u)))) :=
        covariantJetNormSq_operatorFieldComposition_sub_le (I := I) (M := M) g 2 2 4 2
          Ca1 (Ct2 ^ 2 * u) (S2b R * (pl2 * pl2)) (Bt2 ^ 2)
          (2 * (K2 R * ((pl2 * pl2) * u) + K23 R * ((pl2 * pl2) * u)))
          hCa1 _ _ _ _ happ1 htrd2 hS2T2 htr hd2
      _ = Bh R * ((pl2 * pl2) * u) := by
        simp only [Bh, K1, K12]
        ring
  refine hhalf.trans ?_
  rw [hpl2, hu]
  simp only [B0, B1]
  exact quartic_product_sum_le_interpolation_square (hBhnn R hR) hCip hR hA hA4 hD2 hD3 hD4 hN hasq

theorem RicciDeTurckLowOrder.exists_lieCorrectionZeroMixedConnection_covariantJetNormSq_tame_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
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
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A A4 D2 D3 D4 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ A4 → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ D4 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 T ≤ A4 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 U ≤ A4 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 (T - U) ≤ D4 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroMixedConnection (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g -
            lieCorrectionZeroMixedConnection (I := I) (M := M) g
              (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g) ≤
        (B0 R * (1 + A) * (D4 + D3 + D2 + N) +
          B1 R * A4 * (D3 + N)) ^ 2 :=
 by
  obtain ⟨ρ, Bp0, Bp1, hρ, hBp0, hBp1, hhalf⟩ :=
    exists_lieCorrectionZeroMixedConnectionHalfRF_fourthOrder_tame_difference_bound (I := I) (M := M) hDim g
  refine ⟨ρ, fun R => 4 * Bp0 R, fun R => 4 * Bp1 R, hρ,
    fun R hR => by
      have := hBp0 R hR
      linarith,
    fun R hR => by
      have := hBp1 R hR
      linarith, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN
    hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4 hTn hUn hTUn s hs
  have hh1 := hhalf T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN
    hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4 hTn hUn hTUn hs
    DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne
  have hh2 := hhalf T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN
    hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4 hTn hUn hTUn hs
    (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)
  rw [lieCorrectionZeroMixedConnection_eq_expansion (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g,
    lieCorrectionZeroMixedConnection_eq_expansion (I := I) (M := M) g
      (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g]
  have hform :
      lieCorrectionZeroMixedConnectionExpansion (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g -
        lieCorrectionZeroMixedConnectionExpansion (I := I) (M := M) g
          (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g =
      (2 : ℝ) •
        ((lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g
              DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne -
          lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
            (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g
              DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne) +
        (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g
              (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne) -
          lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
            (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g
              (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne))) := by
    simp only [lieCorrectionZeroMixedConnectionExpansion]
    module
  rw [hform, covariantJetNormSq_smul]
  have hadd := covariantJetNormSq_add_le (I := I) (M := M) g 2
    (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g
          DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne -
      lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
        (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g
          DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)
    (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g
          (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne) -
      lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
        (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g
          (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne))
  calc
    (2 : ℝ) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 (_ + _) ≤
      (2 : ℝ) ^ 2 * (2 * (covariantJetNormSq (I := I) (M := M) g 2 _ +
        covariantJetNormSq (I := I) (M := M) g 2 _)) :=
      mul_le_mul_of_nonneg_left hadd (by positivity)
    _ ≤ (2 : ℝ) ^ 2 * (2 *
        ((Bp0 R * (1 + A) * (D4 + D3 + D2 + N) +
            Bp1 R * A4 * (D3 + N)) ^ 2 +
          (Bp0 R * (1 + A) * (D4 + D3 + D2 + N) +
            Bp1 R * A4 * (D3 + N)) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (add_le_add hh1 hh2) (by norm_num)) (by norm_num)
    _ = (4 * Bp0 R * (1 + A) * (D4 + D3 + D2 + N) +
        4 * Bp1 R * A4 * (D3 + N)) ^ 2 := by
      ring

theorem RicciDeTurckLowOrder.exists_lieCorrectionZeroRiemann_covariantJetNormSq_tame_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
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
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A A4 D2 D3 D4 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ A4 → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ D4 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 T ≤ A4 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 U ≤ A4 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 (T - U) ≤ D4 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroRiemann (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδT hδZ s) -
            lieCorrectionZeroRiemann (I := I) (M := M) g
              (metricPerturbationPath (I := I) g U 0 hδU hδZ s)) ≤
        (B0 R * (1 + A) * (D4 + D3 + D2 + N) +
          B1 R * A4 * (D3 + N)) ^ 2 :=
 by
  obtain ⟨ρ, C, hρ, hC, hriem⟩ :=
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_lieCorrectionZeroRiemann_covariantJetNormSq_difference_bound
      (I := I) (M := M) hDim g
  refine ⟨ρ, fun _ => C, fun _ => 0, hρ,
    fun _ _ => hC, fun _ _ => le_refl 0, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4
    hTn hUn hTUn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g U 0 hδU hδZ hs_mem x u v
  have hPn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ := by
    rw [hcP, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTn)
  have hQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρ := by
    rw [hcQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hUn)
  have hPQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    have hPQ : P - Q = s • (T - U) := by rw [hcP, hcQ, smul_sub]
    rw [hPQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTUn)
  refine (hriem P Q gmT gmU hPtie hQtie hPn hQn).trans ?_
  have hstep : C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤
      C * N := mul_le_mul_of_nonneg_left hPQn hC
  refine (pow_le_pow_left₀ (mul_nonneg hC (norm_nonneg _)) hstep 2).trans ?_
  have hbig : C * N ≤ C * (1 + A) * (D4 + D3 + D2 + N) + 0 * A4 * (D3 + N) := by
    have hin : N ≤ (1 + A) * (D4 + D3 + D2 + N) := by
      have hbase : 0 ≤ D4 + D3 + D2 + N :=
        add_nonneg (add_nonneg (add_nonneg hD4 hD3) hD2) hN
      have hone : 1 ≤ 1 + A := by linarith only [hA]
      calc
        N ≤ D4 + D3 + D2 + N := by linarith only [hD2, hD3, hD4]
        _ = 1 * (D4 + D3 + D2 + N) := by ring
        _ ≤ (1 + A) * (D4 + D3 + D2 + N) :=
          mul_le_mul_of_nonneg_right hone hbase
    simpa only [zero_mul, add_zero, mul_assoc] using mul_le_mul_of_nonneg_left hin hC
  exact pow_le_pow_left₀ (mul_nonneg hC hN) hbig 2

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem pair_sum_sq_le
    {b A D N : ℝ} (hb : 0 ≤ b) (hD : 0 ≤ D) (hN : 0 ≤ N) :
    b * (((1 + A) ^ 2 * (1 + A) ^ 2) * (D ^ 2 + N ^ 2)) ≤
      (Real.sqrt (2 * b) * (1 + A) ^ 2 * (D + N)) ^ 2 := by
  have hfac : 0 ≤ (1 + A) ^ 2 * (1 + A) ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hsum : D ^ 2 + N ^ 2 ≤ (D + N) ^ 2 := by
    nlinarith only [mul_nonneg hD hN]
  have hcore :
      b * (((1 + A) ^ 2 * (1 + A) ^ 2) * (D ^ 2 + N ^ 2)) ≤
        b * (((1 + A) ^ 2 * (1 + A) ^ 2) * (D + N) ^ 2) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hsum hfac) hb
  refine hcore.trans ?_
  have hnonneg :
      0 ≤ b * (((1 + A) ^ 2 * (1 + A) ^ 2) * (D + N) ^ 2) :=
    mul_nonneg hb (mul_nonneg hfac (sq_nonneg _))
  have hsqrt : Real.sqrt (2 * b) ^ 2 = 2 * b :=
    Real.sq_sqrt (mul_nonneg (by norm_num) hb)
  calc
    b * (((1 + A) ^ 2 * (1 + A) ^ 2) * (D + N) ^ 2) ≤
        2 * (b * (((1 + A) ^ 2 * (1 + A) ^ 2) * (D + N) ^ 2)) := by
      linarith
    _ = (Real.sqrt (2 * b) * (1 + A) ^ 2 * (D + N)) ^ 2 := by
      rw [mul_pow, mul_pow, hsqrt]
      ring

theorem RicciDeTurckLowOrder.exists_deTurckLieCovariantDerivative_covariantJetNormSq_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
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
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          ((deTurckLieCovariantDerivativeTermField (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g -
            deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδT hδZ
              lieDecompositionQ lieDecompositionEps s) -
          (deTurckLieCovariantDerivativeTermField (I := I) (M := M) g
              (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g -
            deTurckLieTopOrderPairingFamily (I := I) (M := M) g U hδU hδZ
              lieDecompositionQ lieDecompositionEps s)) ≤
        (B R * (1 + A) ^ 2 * (D3 + N)) ^ 2 := by
  obtain ⟨Ca, hCa, happ⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 6 2
  obtain ⟨ρp, Cp, hρp, hCp, hlcvp⟩ :=
    RicciDeTurckLowOrder.pairTrace_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb, Bp, hρb, hBp, hlcvb⟩ :=
    RicciDeTurckLowOrder.pair_trace_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨Dx, hDx, hcovb⟩ := exists_deTurckLieCovariantDerivativeRemainderPairTrace_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨Cx, hCx, hcovp⟩ := exists_deTurckLieCovariantDerivativeRemainderPairTrace_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
  let Bh : ℝ → ℝ := fun R =>
    2 * (Ca * Cp ^ 2 * Dx R + Ca * Bp ^ 2 * Cx R)
  let B : ℝ → ℝ := fun R => Real.sqrt (2 * Bh R)
  have hBhnn : ∀ R : ℝ, 0 ≤ R → 0 ≤ Bh R := by
    intro R hR
    have h1 : (0 : ℝ) ≤ Ca * Cp ^ 2 * Dx R :=
      mul_nonneg (mul_nonneg hCa (sq_nonneg _)) (hDx R hR)
    have h2 : (0 : ℝ) ≤ Ca * Bp ^ 2 * Cx R :=
      mul_nonneg (mul_nonneg hCa (sq_nonneg _)) (hCx R hR)
    simp only [Bh]
    linarith
  refine ⟨min ρp ρb, B, lt_min hρp hρb,
    fun R hR => by
      simp only [B]
      exact Real.sqrt_nonneg _, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D3 N hR hA hD3 hN hT2 hU2 hT3 hU3 hTU3
    hTn hUn hTUn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g U 0 hδU hδZ hs_mem x u v
  have hPn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρp := by
    rw [hcP, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTn.trans (min_le_left _ _))
  have hQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρp := by
    rw [hcQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hUn.trans (min_le_left _ _))
  have hQnb : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρb := by
    rw [hcQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hUn.trans (min_le_right _ _))
  have hPQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    have hPQ : P - Q = s • (T - U) := by rw [hcP, hcQ, smul_sub]
    rw [hPQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTUn)
  let pl2 : ℝ := (1 + A) ^ 2
  have hpl20 : 0 ≤ pl2 := by simp only [pl2]; positivity
  have hpl4 : 0 ≤ pl2 * pl2 := mul_nonneg hpl20 hpl20
  let u : ℝ := D3 ^ 2 + N ^ 2
  have hu0 : 0 ≤ u := by simp only [u]; positivity
  have hD3le : D3 ^ 2 ≤ u := by simp only [u]; linarith [sq_nonneg N]
  have hNu : N ^ 2 ≤ u := by simp only [u]; linarith [sq_nonneg D3]
  have hUT :
      deTurckLieCovariantDerivativeTermField (I := I) (M := M) g gmT g -
        deTurckLieCovariantDerivativeDecompositionPairTraceFamily (I := I) (M := M)
          g T hδT hδZ
            ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
              Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                Equiv.swap (0 : Fin 4) 1,
              Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
            ![(-1 : ℝ), -1, 1] s =
      (-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g 2 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) := by
    rw [hgmT]
    exact lieCov_residual (I := I) (M := M) g T hδ_lt hδT hδZ hT hs
  have hUU :
      deTurckLieCovariantDerivativeTermField (I := I) (M := M) g gmU g -
        deTurckLieCovariantDerivativeDecompositionPairTraceFamily (I := I) (M := M)
          g U hδU hδZ
            ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
              Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                Equiv.swap (0 : Fin 4) 1,
              Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
            ![(-1 : ℝ), -1, 1] s =
      (-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g 2 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s))) := by
    rw [hgmU]
    exact lieCov_residual (I := I) (M := M) g U hδ_lt hδU hδZ hU hs
  rw [deTurckLieEdgePairingFamily_eq_deTurckLieCovariantDerivativeExpansionPairTraceFamily (I := I) (M := M) g T hδT hδZ s,
    deTurckLieEdgePairingFamily_eq_deTurckLieCovariantDerivativeExpansionPairTraceFamily (I := I) (M := M) g U hδU hδZ s, hUT, hUU]
  have htel :
      (-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g 2 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) -
        (-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g 2 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s))) =
      (-1 : ℝ) • (ccOperatorFieldComp (I := I) (M := M) g 2 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT -
            cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) +
        ccOperatorFieldComp (I := I) (M := M) g 2 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) -
            rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s)))) := by
    simpa only [smul_sub] using
      congrArg (fun Z => (-1 : ℝ) • Z)
        (operatorFieldComposition_sub (I := I) (M := M) g 2 6 2 _ _ _ _)
  rw [htel, covariantJetNormSq_smul, neg_one_sq, one_mul]
  have hPairD : covariantJetNormSq (I := I) (M := M) g 2
      (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT -
        cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU) ≤ (Cp * N) ^ 2 := by
    refine (hlcvp P Q gmT gmU hPtie hQtie hPn hQn).trans ?_
    exact pow_le_pow_left₀ (mul_nonneg hCp (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hPQn hCp) 2
  have hPairU : covariantJetNormSq (I := I) (M := M) g 2
      (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU) ≤ Bp ^ 2 :=
    hlcvb Q gmU hQtie hQnb
  have hXT : covariantJetNormSq (I := I) (M := M) g 2
      (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
        (slotExtendIter (I := I) (M := M) g 0 4 2
          (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) ≤
      Dx R * (pl2 * pl2) := by
    refine (hcovb T hT hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 hs).trans
      (le_of_eq ?_)
    simp only [pl2]
    ring
  have hXD : covariantJetNormSq (I := I) (M := M) g 2
      (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) -
        rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s))) ≤
      Cx R * ((pl2 * pl2) * D3 ^ 2) := by
    refine (hcovp T U hT hU hδ_le hδ0 hδT hδU hδZ R A D3 hR hA hD3
      hT2 hU2 hT3 hU3 hTU3 hs).trans (le_of_eq ?_)
    simp only [pl2]
    ring
  have hc1 : (0 : ℝ) ≤ Ca * Cp ^ 2 * Dx R :=
    mul_nonneg (mul_nonneg hCa (sq_nonneg _)) (hDx R hR)
  have hc2 : (0 : ℝ) ≤ Ca * Bp ^ 2 * Cx R :=
    mul_nonneg (mul_nonneg hCa (sq_nonneg _)) (hCx R hR)
  have hT1 : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 2 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT -
          cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)))) ≤
      Ca * Cp ^ 2 * Dx R * ((pl2 * pl2) * u) := by
    refine (happ _ _).trans ?_
    have hstep := mul_le_mul (mul_le_mul_of_nonneg_left hPairD hCa) hXT
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
      (mul_nonneg hCa (sq_nonneg _))
    refine hstep.trans ?_
    calc
      Ca * (Cp * N) ^ 2 * (Dx R * (pl2 * pl2)) =
          Ca * Cp ^ 2 * Dx R * ((pl2 * pl2) * N ^ 2) := by ring
      _ ≤ Ca * Cp ^ 2 * Dx R * ((pl2 * pl2) * u) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hNu hpl4) hc1
  have hT2b : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 2 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) -
          rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s)))) ≤
      Ca * Bp ^ 2 * Cx R * ((pl2 * pl2) * u) := by
    refine (happ _ _).trans ?_
    have hstep := mul_le_mul (mul_le_mul_of_nonneg_left hPairU hCa) hXD
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
      (mul_nonneg hCa (sq_nonneg _))
    refine hstep.trans ?_
    calc
      Ca * Bp ^ 2 * (Cx R * ((pl2 * pl2) * D3 ^ 2)) =
          Ca * Bp ^ 2 * Cx R * ((pl2 * pl2) * D3 ^ 2) := by ring
      _ ≤ Ca * Bp ^ 2 * Cx R * ((pl2 * pl2) * u) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hD3le hpl4) hc2
  have hwhole : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 2 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT -
            cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) +
        ccOperatorFieldComp (I := I) (M := M) g 2 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) -
            rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s)))) ≤
      Bh R * ((pl2 * pl2) * u) := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (_ + _) ≤
          2 * (covariantJetNormSq (I := I) (M := M) g 2 _ +
            covariantJetNormSq (I := I) (M := M) g 2 _) :=
        covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _
      _ ≤ 2 * (Ca * Cp ^ 2 * Dx R * ((pl2 * pl2) * u) +
          Ca * Bp ^ 2 * Cx R * ((pl2 * pl2) * u)) := by
        linarith [hT1, hT2b]
      _ = Bh R * ((pl2 * pl2) * u) := by
        simp only [Bh]
        ring
  refine hwhole.trans ?_
  simp only [pl2, u, B]
  exact pair_sum_sq_le (hBhnn R hR) hD3 hN

theorem RicciDeTurckLowOrder.exists_lieCorrectionZeroRiemann_covariantJetNormSq_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
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
            (0 : SmoothCcTensor g 0 2)) δ)
        (D2 D3 N : ℝ),
        0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroRiemann (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδT hδZ s) -
            lieCorrectionZeroRiemann (I := I) (M := M) g
              (metricPerturbationPath (I := I) g U 0 hδU hδZ s)) ≤
        (C * (D3 + D2 + N)) ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, hriem⟩ :=
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_lieCorrectionZeroRiemann_covariantJetNormSq_difference_bound
      (I := I) (M := M) hDim g
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    D2 D3 N hD2 hD3 hN hTn hUn hTUn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  let gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s
  let gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s
  let P : SmoothCcTensor g 0 2 := s • T
  let Q : SmoothCcTensor g 0 2 := s • U
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
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
  have hPn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ := by
    rw [show P = s • T by rfl, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTn)
  have hQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρ := by
    rw [show Q = s • U by rfl, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hUn)
  have hPQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    have hPQ : P - Q = s • (T - U) := by
      simp only [P, Q, smul_sub]
    rw [hPQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTUn)
  refine (hriem P Q gmT gmU hPtie hQtie hPn hQn).trans ?_
  have hstep : C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤
      C * N := mul_le_mul_of_nonneg_left hPQn hC
  refine (pow_le_pow_left₀ (mul_nonneg hC (norm_nonneg _)) hstep 2).trans ?_
  have hNle : N ≤ D3 + D2 + N := by linarith
  exact pow_le_pow_left₀ (mul_nonneg hC hN)
    (mul_le_mul_of_nonneg_left hNle hC) 2

theorem RicciDeTurckLowOrder.exists_lieCorrectionZeroVectorBundle_covariantJetNormSq_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
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
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroVectorBundle (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδT hδZ s) -
            lieCorrectionZeroVectorBundle (I := I) (M := M) g
              (metricPerturbationPath (I := I) g U 0 hδU hδZ s)) ≤
        (B R * (1 + A) ^ 2 * (D3 + N)) ^ 2 := by
  obtain ⟨Cout, hCout, happOut⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 4 2
  obtain ⟨Cin, hCin, happIn⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 1 4
  obtain ⟨Cipp, hCipp, happIp⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 3 1
  obtain ⟨Cw, hCw, happW⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 0 3 1
  obtain ⟨ρt1, Ct1, hρt1, hCt1, htp1⟩ :=
    RicciDeTurckLowOrder.trace1_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb1, Bt1, hρb1, hBt1, htb1⟩ :=
    RicciDeTurckLowOrder.trace_one_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρt2, Ct2, hρt2, hCt2, htp2⟩ :=
    RicciDeTurckLowOrder.trace2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb2, Bt2, hρb2, hBt2, htb2⟩ :=
    RicciDeTurckLowOrder.trace_two_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨B0m, B1m, hB0m, hB1m, hmcdp⟩ :=
    RicciDeTurckLowOrder.mcd_pair_h2 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bm, hBm, hmcdb⟩ :=
    RicciDeTurckLowOrder.metric_connection_difference_coefficient_sobolev_two_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨W0, W1, hW0, hW1, hwxip⟩ :=
    exists_metricLoweredConnectionDifference_covariantJetNormSq_two_sub_tame_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bs, hBs, hwxib⟩ := exists_metricLoweredConnectionDifference_covariantJetNormSq_bound (I := I) (M := M) hDim g
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hfr2 : (0 : ℝ) ≤ fr ^ 2 := sq_nonneg _
  set Jp : ℝ := covariantJetNormSq (I := I) (M := M) g 2 (ipLowCoeff (I := I) (M := M) g)
    with hJpdef
  have hJp : 0 ≤ Jp := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  set ρ : ℝ := min (min ρt1 ρb1) (min ρt2 ρb2) with hρdef
  have hρ0 : 0 < ρ :=
    lt_min (lt_min hρt1 hρb1) (lt_min hρt2 hρb2)
  let Cs : ℝ → ℝ := fun R => (Bs R) ^ 2
  let M5 : ℝ → ℝ := fun R => 2 * (B0m R + B1m R) ^ 2 + 2 * (B1m R) ^ 2
  let M5w : ℝ → ℝ := fun R => 2 * (W0 R + W1 R) ^ 2 + 2 * (W1 R) ^ 2
  let Wb : ℝ → ℝ := fun R => Cw * Bt1 ^ 2 * Cs R
  let Wm : ℝ → ℝ := fun R =>
    2 * (Cw * Ct1 ^ 2 * Cs R + Cw * Bt1 ^ 2 * M5w R)
  let Ib : ℝ → ℝ := fun R => Cipp * Jp * fr ^ 2 * Wb R
  let Im : ℝ → ℝ := fun R => Cipp * Jp * fr ^ 2 * Wm R
  let Vb : ℝ → ℝ := fun R => fr * (Bm R) ^ 2
  let Vd : ℝ → ℝ := fun R => fr * M5 R
  let Sin : ℝ → ℝ := fun R => Cin * Vb R * Ib R
  let Kv : ℝ → ℝ := fun R => Cin * Vd R * Ib R
  let Ki : ℝ → ℝ := fun R => Cin * Vb R * Im R
  let K1 : ℝ → ℝ := fun R => Cout * Ct2 ^ 2 * Sin R
  let K2 : ℝ → ℝ := fun R => Cout * Bt2 ^ 2 * (2 * (Kv R + Ki R))
  let Bh : ℝ → ℝ := fun R => 4 * (2 * (K1 R + K2 R))
  let B : ℝ → ℝ := fun R => Real.sqrt (2 * Bh R)
  have hCs : ∀ R : ℝ, 0 ≤ R → 0 ≤ Cs R := fun R hR => sq_nonneg _
  have hM5 : ∀ R : ℝ, 0 ≤ R → 0 ≤ M5 R := fun R hR => by
    have h1 : (0 : ℝ) ≤ 2 * (B0m R + B1m R) ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ 2 * (B1m R) ^ 2 := by positivity
    simp only [M5]
    exact add_nonneg h1 h2
  have hM5w : ∀ R : ℝ, 0 ≤ R → 0 ≤ M5w R := fun R hR => by
    have h1 : (0 : ℝ) ≤ 2 * (W0 R + W1 R) ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ 2 * (W1 R) ^ 2 := by positivity
    simp only [M5w]
    exact add_nonneg h1 h2
  have hWb : ∀ R : ℝ, 0 ≤ R → 0 ≤ Wb R := fun R hR =>
    mul_nonneg (mul_nonneg hCw (sq_nonneg _)) (hCs R hR)
  have hWm : ∀ R : ℝ, 0 ≤ R → 0 ≤ Wm R := fun R hR => by
    have h1 : (0 : ℝ) ≤ Cw * Ct1 ^ 2 * Cs R :=
      mul_nonneg (mul_nonneg hCw (sq_nonneg _)) (hCs R hR)
    have h2 : (0 : ℝ) ≤ Cw * Bt1 ^ 2 * M5w R :=
      mul_nonneg (mul_nonneg hCw (sq_nonneg _)) (hM5w R hR)
    simp only [Wm]
    exact mul_nonneg (by norm_num) (add_nonneg h1 h2)
  have hIb : ∀ R : ℝ, 0 ≤ R → 0 ≤ Ib R := fun R hR =>
    mul_nonneg (mul_nonneg (mul_nonneg hCipp hJp) hfr2) (hWb R hR)
  have hIm : ∀ R : ℝ, 0 ≤ R → 0 ≤ Im R := fun R hR =>
    mul_nonneg (mul_nonneg (mul_nonneg hCipp hJp) hfr2) (hWm R hR)
  have hVb : ∀ R : ℝ, 0 ≤ R → 0 ≤ Vb R := fun R hR =>
    mul_nonneg hfr (sq_nonneg _)
  have hVd : ∀ R : ℝ, 0 ≤ R → 0 ≤ Vd R := fun R hR =>
    mul_nonneg hfr (hM5 R hR)
  have hSin : ∀ R : ℝ, 0 ≤ R → 0 ≤ Sin R := fun R hR =>
    mul_nonneg (mul_nonneg hCin (hVb R hR)) (hIb R hR)
  have hKv : ∀ R : ℝ, 0 ≤ R → 0 ≤ Kv R := fun R hR =>
    mul_nonneg (mul_nonneg hCin (hVd R hR)) (hIb R hR)
  have hKi : ∀ R : ℝ, 0 ≤ R → 0 ≤ Ki R := fun R hR =>
    mul_nonneg (mul_nonneg hCin (hVb R hR)) (hIm R hR)
  have hK1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K1 R := fun R hR =>
    mul_nonneg (mul_nonneg hCout (sq_nonneg _)) (hSin R hR)
  have hK2 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K2 R := fun R hR =>
    mul_nonneg (mul_nonneg hCout (sq_nonneg _))
      (mul_nonneg (by norm_num) (add_nonneg (hKv R hR) (hKi R hR)))
  have hBhnn : ∀ R : ℝ, 0 ≤ R → 0 ≤ Bh R := fun R hR => by
    simp only [Bh]
    exact mul_nonneg (by norm_num)
      (mul_nonneg (by norm_num) (add_nonneg (hK1 R hR) (hK2 R hR)))
  refine ⟨ρ, B, hρ0,
    fun R hR => by
      simp only [B]
      exact Real.sqrt_nonneg _, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D3 N hR hA hD3 hN hT2 hU2 hT3 hU3 hTU3
    hTn hUn hTUn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by
    simpa only [one_pow] using pow_le_pow_left₀ hs.1 hs.2 2
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [hcP, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hQsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g Q x u v =
        ccTensorBilin (I := I) g Q x v u := by
    intro x u v
    simp only [hcQ, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hU x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem
        (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem
        (I := I) g U 0 hδU hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g T 0 hδT hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.2),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcP, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hδQ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g Q) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g U 0 hδU hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.2),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcQ, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hQ2 : covariantJetNormSq (I := I) (M := M) g 2 Q ≤ R ^ 2 := by
    rw [hcQ, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g U) hs2).trans hU2
  have hP3 : covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g T) hs2).trans hT3
  have hQ3 : covariantJetNormSq (I := I) (M := M) g 3 Q ≤ A ^ 2 := by
    rw [hcQ, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g U) hs2).trans hU3
  have hPQ3 : covariantJetNormSq (I := I) (M := M) g 3 (P - Q) ≤ D3 ^ 2 := by
    have hPQ : P - Q = s • (T - U) := by
      rw [hcP, hcQ, smul_sub]
    rw [hPQ, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g (T - U)) hs2).trans hTU3
  have hPQ2 : covariantJetNormSq (I := I) (M := M) g 2 (P - Q) ≤ D3 ^ 2 :=
    (covariantJetNormSq_mono (I := I) (M := M) g (by norm_num : (2 : ℕ) ≤ 3) (P - Q)).trans hPQ3
  have hball : ∀ ρ' : ℝ, ρ ≤ ρ' →
      (‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ' ∧
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρ') := by
    intro ρ' hρ'
    constructor
    · rw [hcP, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using (hTn.trans hρ'))
    · rw [hcQ, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using (hUn.trans hρ'))
  have hPQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    have hPQ : P - Q = s • (T - U) := by
      rw [hcP, hcQ, smul_sub]
    rw [hPQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTUn)
  set a : ℝ := A with hadef
  have ha0 : 0 ≤ a := by rw [hadef]; exact hA
  have hP3i : covariantJetNormSq (I := I) (M := M) g 3 P ≤ a ^ 2 := by
    rw [hadef]
    exact hP3
  have hQ3i : covariantJetNormSq (I := I) (M := M) g 3 Q ≤ a ^ 2 := by
    rw [hadef]
    exact hQ3
  set pl2 : ℝ := (1 + a) ^ 2 with hpl2
  have hpl21 : (1 : ℝ) ≤ pl2 := by
    rw [hpl2]
    simpa only [one_pow] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
        (le_add_of_nonneg_right ha0) 2
  have hpl20 : 0 ≤ pl2 := le_trans zero_le_one hpl21
  have hplA2 : a ^ 2 ≤ pl2 := by
    rw [hpl2]
    exact pow_le_pow_left₀ ha0 (le_add_of_nonneg_left (by norm_num)) 2
  set u : ℝ := D3 ^ 2 + N ^ 2 with hu
  have hu0 : 0 ≤ u := by
    rw [hu]
    positivity
  have hD3le : D3 ^ 2 ≤ u := by
    rw [hu]
    exact le_add_of_nonneg_right (sq_nonneg N)
  have hD3u : D3 ^ 2 ≤ pl2 * u := by
    calc D3 ^ 2 ≤ u := hD3le
      _ = 1 * u := (one_mul u).symm
      _ ≤ pl2 * u := mul_le_mul_of_nonneg_right hpl21 hu0
  have hNu : N ^ 2 ≤ u := by
    rw [hu]
    exact le_add_of_nonneg_left (sq_nonneg D3)
  have hpl2u : 0 ≤ pl2 * u := mul_nonneg hpl20 hu0
  set mcdT : SmoothCcTensor g 0 3 :=
    metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gmT g with hmT
  set mcdU : SmoothCcTensor g 0 3 :=
    metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gmU g with hmU
  set cdT : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifferenceCoefficient (I := I) g gmT with hcdT
  set cdU : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifferenceCoefficient (I := I) g gmU with hcdU
  set Tr1T : SmoothCcTensor g 3 1 :=
    reindexedPureTrace (I := I) (M := M) g gmT 1 (Equiv.refl (Fin 3)) with hTr1T
  set Tr1U : SmoothCcTensor g 3 1 :=
    reindexedPureTrace (I := I) (M := M) g gmU 1 (Equiv.refl (Fin 3)) with hTr1U
  set WT : SmoothCcTensor g 0 1 :=
    deTurckVectorFieldCovector (I := I) (M := M) g gmT g with hWTdef
  set WU : SmoothCcTensor g 0 1 :=
    deTurckVectorFieldCovector (I := I) (M := M) g gmU g with hWUdef
  set IpT : SmoothCcTensor g 2 1 := ipLowCc (I := I) (M := M) g WT with hIpT
  set IpU : SmoothCcTensor g 2 1 := ipLowCc (I := I) (M := M) g WU with hIpU
  set VmT : SmoothCcTensor g 1 4 := lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gmT with hVmT
  set VmU : SmoothCcTensor g 1 4 := lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gmU with hVmU
  set LvT : SmoothCcTensor g 4 2 :=
    reindexedCometricDoubleTrace (I := I) (M := M) g gmT with hLvT
  set LvU : SmoothCcTensor g 4 2 :=
    reindexedCometricDoubleTrace (I := I) (M := M) g gmU with hLvU
  set InT : SmoothCcTensor g 2 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 1 4 VmT IpT with hInT
  set InU : SmoothCcTensor g 2 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 1 4 VmU IpU with hInU
  have hρc : ρ ≤ ρt1 ∧ ρ ≤ ρb1 ∧ ρ ≤ ρt2 ∧ ρ ≤ ρb2 := by
    rw [hρdef]
    exact ⟨
      le_trans (min_le_left _ _) (min_le_left _ _),
      le_trans (min_le_left _ _) (min_le_right _ _),
      le_trans (min_le_right _ _) (min_le_left _ _),
      le_trans (min_le_right _ _) (min_le_right _ _)⟩
  have htrp : ∀ (p : ℕ) (Cp : ℝ) (ρp' : ℝ),
      (∀ (T' U' : SmoothCcTensor g 0 2)
        (gT' gU' : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT'.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T' y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU'.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g U' y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ ρp' →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U'‖ ≤ ρp' →
        covariantJetNormSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT' p -
              pureTrace (I := I) (M := M) g gU' p) ≤
          (Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T' - U')‖) ^ 2) →
      0 ≤ Cp → ρ ≤ ρp' →
      covariantJetNormSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gmT p -
            pureTrace (I := I) (M := M) g gmU p) ≤
        Cp ^ 2 * u := by
    intro p Cp ρp' hpair hCp hρp'
    obtain ⟨hPn, hQn⟩ := hball ρp' hρp'
    have h := hpair P Q gmT gmU hPtie hQtie hPn hQn
    refine h.trans ?_
    have h1 : Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (P - Q)‖ ≤ Cp * N :=
      mul_le_mul_of_nonneg_left hPQn hCp
    have h2 : (Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (P - Q)‖) ^ 2 ≤ (Cp * N) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hCp (norm_nonneg _)) h1 2
    refine h2.trans ?_
    have he : (Cp * N) ^ 2 = Cp ^ 2 * N ^ 2 := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hNu (sq_nonneg Cp)
  have htrb : ∀ (p : ℕ) (Bp : ℝ) (ρp' : ℝ),
      (∀ (T' : SmoothCcTensor g 0 2)
        (gT' : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT'.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T' y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ ρp' →
        covariantJetNormSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT' p) ≤ Bp ^ 2) →
      ρ ≤ ρp' →
      (covariantJetNormSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gmT p) ≤ Bp ^ 2 ∧
        covariantJetNormSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gmU p) ≤ Bp ^ 2) := by
    intro p Bp ρp' hbdd hρp'
    obtain ⟨hPn, hQn⟩ := hball ρp' hρp'
    exact ⟨hbdd P gmT hPtie hPn, hbdd Q gmU hQtie hQn⟩
  have htp1' := htrp 1 Ct1 ρt1 htp1 hCt1 hρc.1
  have htb1' := htrb 1 Bt1 ρb1 htb1 hρc.2.1
  have htp2' := htrp 2 Ct2 ρt2 htp2 hCt2 hρc.2.2.1
  have htb2' := htrb 2 Bt2 ρb2 htb2 hρc.2.2.2
  have hmbT : covariantJetNormSq (I := I) (M := M) g 2 mcdT ≤ (Bm R) ^ 2 * pl2 := by
    have h := hmcdb gmT P hPsymm hPtie hδ_le hδ0 hδP R a hR ha0 hP2 hP3i
    rw [hmT]
    refine h.trans (le_of_eq ?_)
    rw [hpl2]
    ring
  have hmbU : covariantJetNormSq (I := I) (M := M) g 2 mcdU ≤ (Bm R) ^ 2 * pl2 := by
    have h := hmcdb gmU Q hQsymm hQtie hδ_le hδ0 hδQ R a hR ha0 hQ2 hQ3i
    rw [hmU]
    refine h.trans (le_of_eq ?_)
    rw [hpl2]
    ring
  have hmpd : covariantJetNormSq (I := I) (M := M) g 2 (mcdT - mcdU) ≤
      M5 R * (pl2 * u) := by
    have h := hmcdp gmT gmU P Q hPsymm hQsymm hPtie hQtie
      hδ_le hδ0 hδP hδ_le hδ0 hδQ R a D3 D3 hR ha0 hD3 hD3 hQ2 hP3i hPQ2 hPQ3
    rw [hmT, hmU]
    refine h.trans ?_
    refine (three_term_sq_le_weighted_product (b0 := B0m R) (b1 := B1m R) (a := a)
      (p := pl2) (u := u) (d := D3) hpl21 hplA2 hu0 hD3le).trans (le_of_eq ?_)
    simp only [M5]
  have hcdT2 : covariantJetNormSq (I := I) (M := M) g 2 cdT ≤ Cs R * pl2 := by
    rw [hcdT, ← metricLoweredConnectionDifference_eq_connectionDifferenceLoweredCc (I := I) (M := M) g gmT]
    refine (hwxib gmT P hPsymm hPtie hδ_le hδ0 hδP hδZ R a hR ha0
      hP2 hP3i).trans ?_
    have he : (Bs R * a) ^ 2 = (Bs R) ^ 2 * a ^ 2 := by ring
    rw [he]
    refine (mul_le_mul_of_nonneg_left hplA2 (sq_nonneg (Bs R))).trans
      (le_of_eq ?_)
    simp only [Cs]
  have hcdd2 : covariantJetNormSq (I := I) (M := M) g 2 (cdT - cdU) ≤
      M5w R * (pl2 * u) := by
    rw [hcdT, hcdU, ← metricLoweredConnectionDifference_eq_connectionDifferenceLoweredCc (I := I) (M := M) g gmT,
      ← metricLoweredConnectionDifference_eq_connectionDifferenceLoweredCc (I := I) (M := M) g gmU]
    refine (hwxip gmT gmU g P Q hPsymm hQsymm hPtie hQtie
      hδ_le hδ0 hδP hδ_le hδ0 hδQ R a D3 D3 hR ha0 hD3 hD3
      hQ2 hP3i hPQ2 hPQ3).trans ?_
    refine (three_term_sq_le_weighted_product (b0 := W0 R) (b1 := W1 R) (a := a)
      (p := pl2) (u := u) (d := D3) hpl21 hplA2 hu0 hD3le).trans (le_of_eq ?_)
    simp only [M5w]
  have hTr1T2 : covariantJetNormSq (I := I) (M := M) g 2 Tr1T ≤ Bt1 ^ 2 := by
    rw [hTr1T, covariantJetNormSq_reindexedPureTrace]
    exact htb1'.1
  have hTr1U2 : covariantJetNormSq (I := I) (M := M) g 2 Tr1U ≤ Bt1 ^ 2 := by
    rw [hTr1U, covariantJetNormSq_reindexedPureTrace]
    exact htb1'.2
  have hTr1d2 : covariantJetNormSq (I := I) (M := M) g 2 (Tr1T - Tr1U) ≤
      Ct1 ^ 2 * u := by
    rw [hTr1T, hTr1U, reindexedPureTrace_sub, covariantJetNormSq_reindexCoeffGen]
    exact htp1'
  have hWTform : WT = ccOperatorFieldComp (I := I) (M := M) g 0 3 1 Tr1T cdT := by
    rw [hWTdef, hTr1T, hcdT, deTurckVectorFieldCovector_eq_reindexedPureTrace_ccOperatorFieldComp]
  have hWUform : WU = ccOperatorFieldComp (I := I) (M := M) g 0 3 1 Tr1U cdU := by
    rw [hWUdef, hTr1U, hcdU, deTurckVectorFieldCovector_eq_reindexedPureTrace_ccOperatorFieldComp]
  have hWT2 : covariantJetNormSq (I := I) (M := M) g 2 WT ≤ Wb R * pl2 := by
    rw [hWTform]
    refine (happW Tr1T cdT).trans ?_
    calc
      Cw * covariantJetNormSq (I := I) (M := M) g 2 Tr1T *
          covariantJetNormSq (I := I) (M := M) g 2 cdT ≤
          Cw * Bt1 ^ 2 * (Cs R * pl2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hTr1T2 hCw) hcdT2
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g cdT)
          (mul_nonneg hCw (sq_nonneg _))
      _ = Wb R * pl2 := by
        simp only [Wb]
        ring
  have hWd2 : covariantJetNormSq (I := I) (M := M) g 2 (WT - WU) ≤ Wm R * (pl2 * u) := by
    rw [hWTform, hWUform]
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (_ - _) ≤
          2 * (Cw * (Ct1 ^ 2 * u) * (Cs R * pl2) +
            Cw * Bt1 ^ 2 * (M5w R * (pl2 * u))) :=
        covariantJetNormSq_operatorFieldComposition_sub_le (I := I) (M := M) g 2 0 3 1
          Cw (Ct1 ^ 2 * u) (Cs R * pl2) (Bt1 ^ 2)
          (M5w R * (pl2 * u)) hCw _ _ _ _ happW
          hTr1d2 hcdT2 hTr1U2 hcdd2
      _ = Wm R * (pl2 * u) := by
        simp only [Wm]
        ring
  have hIpT2 : covariantJetNormSq (I := I) (M := M) g 2 IpT ≤ Ib R * pl2 := by
    rw [hIpT, ipLowCc_eq_ccOperatorFieldComp]
    refine (happIp (ipLowCoeff (I := I) (M := M) g) _).trans ?_
    have hslot : covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 1 2
          (slotExtend (I := I) (M := M) g 0 1 WT)) ≤
        fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 WT) :=
      le_trans (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 2 _)
        (mul_le_mul_of_nonneg_left (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 1 _) hfr)
    calc
      Cipp * covariantJetNormSq (I := I) (M := M) g 2 (ipLowCoeff (I := I) (M := M) g) *
          covariantJetNormSq (I := I) (M := M) g 2
            (slotExtend (I := I) (M := M) g 1 2
              (slotExtend (I := I) (M := M) g 0 1 WT)) ≤
          Cipp * Jp * (fr * (fr * (Wb R * pl2))) := by
        refine mul_le_mul (le_of_eq (by rw [hJpdef]))
          (le_trans hslot
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hWT2 hfr) hfr))
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hCipp hJp)
      _ = Ib R * pl2 := by
        simp only [Ib]
        ring
  have hIpd2 : covariantJetNormSq (I := I) (M := M) g 2 (IpT - IpU) ≤
      Im R * (pl2 * u) := by
    rw [hIpT, hIpU, ← ipLowCc_sub, ipLowCc_eq_ccOperatorFieldComp]
    refine (happIp (ipLowCoeff (I := I) (M := M) g) _).trans ?_
    have hslot : covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 1 2
          (slotExtend (I := I) (M := M) g 0 1 (WT - WU))) ≤
        fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 (WT - WU)) :=
      le_trans (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 2 _)
        (mul_le_mul_of_nonneg_left (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 1 _) hfr)
    calc
      Cipp * covariantJetNormSq (I := I) (M := M) g 2 (ipLowCoeff (I := I) (M := M) g) *
          covariantJetNormSq (I := I) (M := M) g 2
            (slotExtend (I := I) (M := M) g 1 2
              (slotExtend (I := I) (M := M) g 0 1 (WT - WU))) ≤
          Cipp * Jp * (fr * (fr * (Wm R * (pl2 * u)))) := by
        refine mul_le_mul (le_of_eq (by rw [hJpdef]))
          (le_trans hslot
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hWd2 hfr) hfr))
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hCipp hJp)
      _ = Im R * (pl2 * u) := by
        simp only [Im]
        ring
  have hVmT2 : covariantJetNormSq (I := I) (M := M) g 2 VmT ≤ Vb R * pl2 := by
    rw [hVmT]
    refine (covariantJetNormSq_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_le (I := I) (M := M) g gmT).trans ?_
    calc
      fr * covariantJetNormSq (I := I) (M := M) g 2
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gmT g) ≤
          fr * ((Bm R) ^ 2 * pl2) := by
        have h := hmbT
        rw [hmT] at h
        exact mul_le_mul_of_nonneg_left h hfr
      _ = Vb R * pl2 := by
        simp only [Vb]
        ring
  have hVmU2 : covariantJetNormSq (I := I) (M := M) g 2 VmU ≤ Vb R * pl2 := by
    rw [hVmU]
    refine (covariantJetNormSq_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_le (I := I) (M := M) g gmU).trans ?_
    calc
      fr * covariantJetNormSq (I := I) (M := M) g 2
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gmU g) ≤
          fr * ((Bm R) ^ 2 * pl2) := by
        have h := hmbU
        rw [hmU] at h
        exact mul_le_mul_of_nonneg_left h hfr
      _ = Vb R * pl2 := by
        simp only [Vb]
        ring
  have hVmd2 : covariantJetNormSq (I := I) (M := M) g 2 (VmT - VmU) ≤
      Vd R * (pl2 * u) := by
    rw [hVmT, hVmU]
    refine (covariantJetNormSq_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_sub_le (I := I) (M := M) g gmT gmU).trans ?_
    calc
      fr * covariantJetNormSq (I := I) (M := M) g 2
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gmT g -
            metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gmU g) ≤
          fr * (M5 R * (pl2 * u)) := by
        have h := hmpd
        rw [hmT, hmU] at h
        exact mul_le_mul_of_nonneg_left h hfr
      _ = Vd R * (pl2 * u) := by
        simp only [Vd]
        ring
  have hInT2 : covariantJetNormSq (I := I) (M := M) g 2 InT ≤ Sin R * (pl2 * pl2) := by
    rw [hInT]
    refine (happIn VmT IpT).trans ?_
    calc
      Cin * covariantJetNormSq (I := I) (M := M) g 2 VmT *
          covariantJetNormSq (I := I) (M := M) g 2 IpT ≤
          Cin * (Vb R * pl2) * (Ib R * pl2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hVmT2 hCin) hIpT2
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g IpT)
          (mul_nonneg hCin (mul_nonneg (hVb R hR) hpl20))
      _ = Sin R * (pl2 * pl2) := by
        simp only [Sin]
        ring
  have hInd2 : covariantJetNormSq (I := I) (M := M) g 2 (InT - InU) ≤
      2 * (Kv R * ((pl2 * pl2) * u) + Ki R * ((pl2 * pl2) * u)) := by
    rw [hInT, hInU]
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (_ - _) ≤
          2 * (Cin * (Vd R * (pl2 * u)) * (Ib R * pl2) +
            Cin * (Vb R * pl2) * (Im R * (pl2 * u))) :=
        covariantJetNormSq_operatorFieldComposition_sub_le (I := I) (M := M) g 2 2 1 4
          Cin (Vd R * (pl2 * u)) (Ib R * pl2) (Vb R * pl2)
          (Im R * (pl2 * u)) hCin _ _ _ _ happIn
          hVmd2 hIpT2 hVmU2 hIpd2
      _ = 2 * (Kv R * ((pl2 * pl2) * u) +
          Ki R * ((pl2 * pl2) * u)) := by
        simp only [Kv, Ki]
        ring
  have hLvd2 : covariantJetNormSq (I := I) (M := M) g 2 (LvT - LvU) ≤ Ct2 ^ 2 * u := by
    rw [hLvT, hLvU, reindexedCometricDoubleTrace_eq_pureTrace, reindexedCometricDoubleTrace_eq_pureTrace]
    exact htp2'
  have hLvU2 : covariantJetNormSq (I := I) (M := M) g 2 LvU ≤ Bt2 ^ 2 := by
    rw [hLvU, reindexedCometricDoubleTrace_eq_pureTrace]
    exact htb2'.2
  have hFormT : lieCorrectionZeroVectorBundle (I := I) (M := M) g gmT =
      (2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g 2 4 2 LvT InT := by
    rw [hLvT, hInT, hVmT, hIpT, hWTdef, lieCorrectionZeroVectorBundle_eq_expansion, lieCorrectionZeroVectorBundleExpansion]
  have hFormU : lieCorrectionZeroVectorBundle (I := I) (M := M) g gmU =
      (2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g 2 4 2 LvU InU := by
    rw [hLvU, hInU, hVmU, hIpU, hWUdef, lieCorrectionZeroVectorBundle_eq_expansion, lieCorrectionZeroVectorBundleExpansion]
  have hwhole : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroVectorBundle (I := I) (M := M) g gmT - lieCorrectionZeroVectorBundle (I := I) (M := M) g gmU) ≤
      Bh R * ((pl2 * pl2) * u) := by
    rw [hFormT, hFormU, ← smul_sub, covariantJetNormSq_smul]
    have h4 : ((2 : ℝ)) ^ 2 = 4 := by norm_num
    rw [h4]
    calc
      (4 : ℝ) * covariantJetNormSq (I := I) (M := M) g 2 (_ - _) ≤
          4 * (2 * (Cout * (Ct2 ^ 2 * u) * (Sin R * (pl2 * pl2)) +
            Cout * Bt2 ^ 2 * (2 * (Kv R * ((pl2 * pl2) * u) +
              Ki R * ((pl2 * pl2) * u))))) :=
        mul_le_mul_of_nonneg_left
          (covariantJetNormSq_operatorFieldComposition_sub_le (I := I) (M := M) g 2 2 4 2
            Cout (Ct2 ^ 2 * u) (Sin R * (pl2 * pl2)) (Bt2 ^ 2)
            (2 * (Kv R * ((pl2 * pl2) * u) + Ki R * ((pl2 * pl2) * u)))
            hCout _ _ _ _ happOut hLvd2 hInT2 hLvU2 hInd2)
          (by norm_num)
      _ = Bh R * ((pl2 * pl2) * u) := by
        simp only [Bh, K1, K2]
        ring
  refine hwhole.trans ?_
  rw [hpl2, hu, hadef]
  simp only [B]
  exact pair_sum_sq_le (hBhnn R hR) hD3 hN

private theorem exists_lieCorrectionZeroMixedConnectionHalfRF_thirdOrder_tame_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
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
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ (σlast : Equiv.Perm (Fin 4)),
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g σlast -
            lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
              (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g σlast) ≤
        (B R * (1 + A) ^ 2 * (D3 + N)) ^ 2 := by
  obtain ⟨Ca1, hCa1, happ1⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 4 2
  obtain ⟨Ca2, hCa2, happ2⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 6 4
  obtain ⟨Ca3, hCa3, happ3⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 3 6
  obtain ⟨Ca4, hCa4, happ4⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 5 3
  obtain ⟨ρt2, Ct2, hρt2, hCt2, htp2⟩ :=
    RicciDeTurckLowOrder.trace2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρt3, Ct3, hρt3, hCt3, htp3⟩ :=
    RicciDeTurckLowOrder.trace3_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρt4, Ct4, hρt4, hCt4, htp4⟩ :=
    RicciDeTurckLowOrder.trace4_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb2, Bt2, hρb2, hBt2, htb2⟩ :=
    RicciDeTurckLowOrder.trace_two_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρb3, Bt3, hρb3, hBt3, htb3⟩ :=
    RicciDeTurckLowOrder.trace_three_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρb4, Bt4, hρb4, hBt4, htb4⟩ :=
    RicciDeTurckLowOrder.trace_four_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨B0m, B1m, hB0m, hB1m, hmcdp⟩ :=
    RicciDeTurckLowOrder.mcd_pair_h2 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bm, hBm, hmcdb⟩ :=
    RicciDeTurckLowOrder.metric_connection_difference_coefficient_sobolev_two_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hfr2 : (0 : ℝ) ≤ fr ^ 2 := sq_nonneg _
  have hfr3 : (0 : ℝ) ≤ fr ^ 3 := pow_nonneg hfr 3
  set ρ : ℝ := min (min ρt2 (min ρt3 ρt4)) (min ρb2 (min ρb3 ρb4))
    with hρdef
  have hρ0 : 0 < ρ :=
    lt_min (lt_min hρt2 (lt_min hρt3 hρt4))
      (lt_min hρb2 (lt_min hρb3 hρb4))
  let S5b : ℝ → ℝ := fun R => fr ^ 2 * (Bm R) ^ 2
  let E3b : ℝ → ℝ := fun R => fr ^ 3 * (Bm R) ^ 2
  let S4b : ℝ → ℝ := fun R => Ca4 * Bt3 ^ 2 * S5b R
  let S3b : ℝ → ℝ := fun R => Ca3 * E3b R * S4b R
  let S2b : ℝ → ℝ := fun R => Ca2 * Bt4 ^ 2 * S3b R
  let M5 : ℝ → ℝ := fun R => 2 * (B0m R + B1m R) ^ 2 + 2 * (B1m R) ^ 2
  let D5c : ℝ → ℝ := fun R => fr ^ 2 * M5 R
  let E3d : ℝ → ℝ := fun R => fr ^ 3 * M5 R
  let K4 : ℝ → ℝ := fun R => Ca4 * Ct3 ^ 2 * S5b R
  let K5 : ℝ → ℝ := fun R => Ca4 * Bt3 ^ 2 * D5c R
  let K3 : ℝ → ℝ := fun R => Ca3 * E3d R * S4b R
  let K34 : ℝ → ℝ := fun R => Ca3 * E3b R * (2 * (K4 R + K5 R))
  let K2 : ℝ → ℝ := fun R => Ca2 * Ct4 ^ 2 * S3b R
  let K23 : ℝ → ℝ := fun R => Ca2 * Bt4 ^ 2 * (2 * (K3 R + K34 R))
  let K1 : ℝ → ℝ := fun R => Ca1 * Ct2 ^ 2 * S2b R
  let K12 : ℝ → ℝ := fun R => Ca1 * Bt2 ^ 2 * (2 * (K2 R + K23 R))
  let Bh : ℝ → ℝ := fun R => 2 * (K1 R + K12 R)
  let B : ℝ → ℝ := fun R => Real.sqrt (2 * Bh R)
  have hS5b : ∀ R : ℝ, 0 ≤ R → 0 ≤ S5b R := fun R hR =>
    mul_nonneg hfr2 (sq_nonneg _)
  have hE3b : ∀ R : ℝ, 0 ≤ R → 0 ≤ E3b R := fun R hR =>
    mul_nonneg hfr3 (sq_nonneg _)
  have hS4b : ∀ R : ℝ, 0 ≤ R → 0 ≤ S4b R := fun R hR =>
    mul_nonneg (mul_nonneg hCa4 (sq_nonneg _)) (hS5b R hR)
  have hS3b : ∀ R : ℝ, 0 ≤ R → 0 ≤ S3b R := fun R hR =>
    mul_nonneg (mul_nonneg hCa3 (hE3b R hR)) (hS4b R hR)
  have hS2b : ∀ R : ℝ, 0 ≤ R → 0 ≤ S2b R := fun R hR =>
    mul_nonneg (mul_nonneg hCa2 (sq_nonneg _)) (hS3b R hR)
  have hM5 : ∀ R : ℝ, 0 ≤ R → 0 ≤ M5 R := fun R hR => by
    have h1 : (0 : ℝ) ≤ 2 * (B0m R + B1m R) ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ 2 * (B1m R) ^ 2 := by positivity
    simp only [M5]
    exact add_nonneg h1 h2
  have hD5c : ∀ R : ℝ, 0 ≤ R → 0 ≤ D5c R := fun R hR =>
    mul_nonneg hfr2 (hM5 R hR)
  have hE3d : ∀ R : ℝ, 0 ≤ R → 0 ≤ E3d R := fun R hR =>
    mul_nonneg hfr3 (hM5 R hR)
  have hK4 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K4 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa4 (sq_nonneg _)) (hS5b R hR)
  have hK5 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K5 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa4 (sq_nonneg _)) (hD5c R hR)
  have hK3 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K3 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa3 (hE3d R hR)) (hS4b R hR)
  have hK34 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K34 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa3 (hE3b R hR))
      (mul_nonneg (by norm_num) (add_nonneg (hK4 R hR) (hK5 R hR)))
  have hK2 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K2 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa2 (sq_nonneg _)) (hS3b R hR)
  have hK23 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K23 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa2 (sq_nonneg _))
      (mul_nonneg (by norm_num) (add_nonneg (hK3 R hR) (hK34 R hR)))
  have hK1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K1 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa1 (sq_nonneg _)) (hS2b R hR)
  have hK12 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K12 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa1 (sq_nonneg _))
      (mul_nonneg (by norm_num) (add_nonneg (hK2 R hR) (hK23 R hR)))
  have hBhnn : ∀ R : ℝ, 0 ≤ R → 0 ≤ Bh R := fun R hR => by
    simp only [Bh]
    exact mul_nonneg (by norm_num) (add_nonneg (hK1 R hR) (hK12 R hR))
  refine ⟨ρ, B, hρ0,
    fun R hR => by
      simp only [B]
      exact Real.sqrt_nonneg _, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D3 N hR hA hD3 hN hT2 hU2 hT3 hU3 hTU3
    hTn hUn hTUn s hs σlast
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by
    simpa only [one_pow] using pow_le_pow_left₀ hs.1 hs.2 2
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [hcP, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hQsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g Q x u v =
        ccTensorBilin (I := I) g Q x v u := by
    intro x u v
    simp only [hcQ, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hU x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem
        (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem
        (I := I) g U 0 hδU hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g T 0 hδT hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.2),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcP, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hδQ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g Q) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g U 0 hδU hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.2),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcQ, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hQ2 : covariantJetNormSq (I := I) (M := M) g 2 Q ≤ R ^ 2 := by
    rw [hcQ, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g U) hs2).trans hU2
  have hP3 : covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g T) hs2).trans hT3
  have hQ3 : covariantJetNormSq (I := I) (M := M) g 3 Q ≤ A ^ 2 := by
    rw [hcQ, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g U) hs2).trans hU3
  have hPQ3 : covariantJetNormSq (I := I) (M := M) g 3 (P - Q) ≤ D3 ^ 2 := by
    have hPQ : P - Q = s • (T - U) := by
      rw [hcP, hcQ, smul_sub]
    rw [hPQ, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g (T - U)) hs2).trans hTU3
  have hPQ2 : covariantJetNormSq (I := I) (M := M) g 2 (P - Q) ≤ D3 ^ 2 :=
    (covariantJetNormSq_mono (I := I) (M := M) g (by norm_num : (2 : ℕ) ≤ 3) (P - Q)).trans hPQ3
  have hball : ∀ ρ' : ℝ, ρ ≤ ρ' →
      (‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ' ∧
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρ') := by
    intro ρ' hρ'
    constructor
    · rw [hcP, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using (hTn.trans hρ'))
    · rw [hcQ, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using (hUn.trans hρ'))
  have hPQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    have hPQ : P - Q = s • (T - U) := by
      rw [hcP, hcQ, smul_sub]
    rw [hPQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTUn)
  set a : ℝ := A with hadef
  have ha0 : 0 ≤ a := by rw [hadef]; exact hA
  have hP3i : covariantJetNormSq (I := I) (M := M) g 3 P ≤ a ^ 2 := by
    rw [hadef]
    exact hP3
  have hQ3i : covariantJetNormSq (I := I) (M := M) g 3 Q ≤ a ^ 2 := by
    rw [hadef]
    exact hQ3
  set pl2 : ℝ := (1 + a) ^ 2 with hpl2
  have hpl21 : (1 : ℝ) ≤ pl2 := by
    rw [hpl2]
    simpa only [one_pow] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
        (le_add_of_nonneg_right ha0) 2
  have hpl20 : 0 ≤ pl2 := le_trans zero_le_one hpl21
  have hplA2 : a ^ 2 ≤ pl2 := by
    rw [hpl2]
    exact pow_le_pow_left₀ ha0 (le_add_of_nonneg_left (by norm_num)) 2
  set u : ℝ := D3 ^ 2 + N ^ 2 with hu
  have hu0 : 0 ≤ u := by
    rw [hu]
    positivity
  have hD3le : D3 ^ 2 ≤ u := by
    rw [hu]
    exact le_add_of_nonneg_right (sq_nonneg N)
  have hD3u : D3 ^ 2 ≤ pl2 * u := by
    calc D3 ^ 2 ≤ u := hD3le
      _ = 1 * u := (one_mul u).symm
      _ ≤ pl2 * u := mul_le_mul_of_nonneg_right hpl21 hu0
  have hNu : N ^ 2 ≤ u := by
    rw [hu]
    exact le_add_of_nonneg_left (sq_nonneg D3)
  set mcdT : SmoothCcTensor g 0 3 :=
    metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gmT g with hmT
  set mcdU : SmoothCcTensor g 0 3 :=
    metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gmU g with hmU
  have hmbT : covariantJetNormSq (I := I) (M := M) g 2 mcdT ≤ (Bm R) ^ 2 * pl2 := by
    have h := hmcdb gmT P hPsymm hPtie hδ_le hδ0 hδP R a hR ha0 hP2 hP3i
    rw [hmT]
    refine h.trans (le_of_eq ?_)
    rw [hpl2]
    ring
  have hmbU : covariantJetNormSq (I := I) (M := M) g 2 mcdU ≤ (Bm R) ^ 2 * pl2 := by
    have h := hmcdb gmU Q hQsymm hQtie hδ_le hδ0 hδQ R a hR ha0 hQ2 hQ3i
    rw [hmU]
    refine h.trans (le_of_eq ?_)
    rw [hpl2]
    ring
  have hmpd : covariantJetNormSq (I := I) (M := M) g 2 (mcdT - mcdU) ≤
      M5 R * (pl2 * u) := by
    have h := hmcdp gmT gmU P Q hPsymm hQsymm hPtie hQtie
      hδ_le hδ0 hδP hδ_le hδ0 hδQ R a D3 D3 hR ha0 hD3 hD3 hQ2 hP3i hPQ2 hPQ3
    rw [hmT, hmU]
    refine h.trans ?_
    have hstep : (B0m R * D3 + B1m R * D3 + B1m R * a * D3) ^ 2 ≤
        2 * (B0m R + B1m R) ^ 2 * D3 ^ 2 +
          2 * (B1m R) ^ 2 * (a ^ 2 * D3 ^ 2) := by
      have hre : B0m R * D3 + B1m R * D3 + B1m R * a * D3 =
          (B0m R + B1m R) * D3 + B1m R * a * D3 := by ring
      rw [hre]
      have hsq : ((B0m R + B1m R) * D3 + B1m R * a * D3) ^ 2 ≤
          2 * (((B0m R + B1m R) * D3) ^ 2 + (B1m R * a * D3) ^ 2) :=
        add_sq_le
      rw [mul_add] at hsq
      refine hsq.trans (le_of_eq ?_)
      ring
    refine hstep.trans ?_
    have hA2D : a ^ 2 * D3 ^ 2 ≤ pl2 * u := by
      have h1 : a ^ 2 * D3 ^ 2 ≤ pl2 * D3 ^ 2 :=
        mul_le_mul_of_nonneg_right hplA2 (sq_nonneg _)
      have h2 : pl2 * D3 ^ 2 ≤ pl2 * u :=
        mul_le_mul_of_nonneg_left hD3le hpl20
      exact h1.trans h2
    have e1 : 2 * (B0m R + B1m R) ^ 2 * D3 ^ 2 ≤
        2 * (B0m R + B1m R) ^ 2 * (pl2 * u) :=
      mul_le_mul_of_nonneg_left hD3u (by positivity)
    have e2 : 2 * (B1m R) ^ 2 * (a ^ 2 * D3 ^ 2) ≤
        2 * (B1m R) ^ 2 * (pl2 * u) :=
      mul_le_mul_of_nonneg_left hA2D (by positivity)
    have hM5eq : M5 R * (pl2 * u) =
        2 * (B0m R + B1m R) ^ 2 * (pl2 * u) +
          2 * (B1m R) ^ 2 * (pl2 * u) := by
      simp only [M5]
      ring
    rw [hM5eq]
    exact add_le_add e1 e2
  have hρc : ρ ≤ ρt2 ∧ ρ ≤ ρt3 ∧ ρ ≤ ρt4 ∧ ρ ≤ ρb2 ∧ ρ ≤ ρb3 ∧
      ρ ≤ ρb4 := by
    rw [hρdef]
    exact ⟨
      le_trans (min_le_left _ _) (min_le_left _ _),
      le_trans (min_le_left _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)),
      le_trans (min_le_left _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _)),
      le_trans (min_le_right _ _) (min_le_left _ _),
      le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)),
      le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _))⟩
  have htrp : ∀ (p : ℕ) (Cp : ℝ) (ρp' : ℝ),
      (∀ (T' U' : SmoothCcTensor g 0 2)
        (gT' gU' : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT'.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T' y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU'.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g U' y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ ρp' →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U'‖ ≤ ρp' →
        covariantJetNormSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT' p -
              pureTrace (I := I) (M := M) g gU' p) ≤
          (Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T' - U')‖) ^ 2) →
      0 ≤ Cp → ρ ≤ ρp' →
      covariantJetNormSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gmT p -
            pureTrace (I := I) (M := M) g gmU p) ≤
        Cp ^ 2 * u := by
    intro p Cp ρp' hpair hCp hρp'
    obtain ⟨hPn, hQn⟩ := hball ρp' hρp'
    have h := hpair P Q gmT gmU hPtie hQtie hPn hQn
    refine h.trans ?_
    have h1 : Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (P - Q)‖ ≤ Cp * N :=
      mul_le_mul_of_nonneg_left hPQn hCp
    have h2 : (Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (P - Q)‖) ^ 2 ≤ (Cp * N) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hCp (norm_nonneg _)) h1 2
    refine h2.trans ?_
    have he : (Cp * N) ^ 2 = Cp ^ 2 * N ^ 2 := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hNu (sq_nonneg Cp)
  have htrb : ∀ (p : ℕ) (Bp : ℝ) (ρp' : ℝ),
      (∀ (T' : SmoothCcTensor g 0 2)
        (gT' : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT'.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T' y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ ρp' →
        covariantJetNormSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT' p) ≤ Bp ^ 2) →
      ρ ≤ ρp' →
      (covariantJetNormSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gmT p) ≤ Bp ^ 2 ∧
        covariantJetNormSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gmU p) ≤ Bp ^ 2) := by
    intro p Bp ρp' hbdd hρp'
    obtain ⟨hPn, hQn⟩ := hball ρp' hρp'
    exact ⟨hbdd P gmT hPtie hPn, hbdd Q gmU hQtie hQn⟩
  have htp2' := htrp 2 Ct2 ρt2 htp2 hCt2 hρc.1
  have htp3' := htrp 3 Ct3 ρt3 htp3 hCt3 hρc.2.1
  have htp4' := htrp 4 Ct4 ρt4 htp4 hCt4 hρc.2.2.1
  have htb2' := htrb 2 Bt2 ρb2 htb2 hρc.2.2.2.1
  have htb3' := htrb 3 Bt3 ρb3 htb3 hρc.2.2.2.2.1
  have htb4' := htrb 4 Bt4 ρb4 htb4 hρc.2.2.2.2.2
  set S5T : SmoothCcTensor g 2 5 :=
    slotExtendIter (I := I) (M := M) g 0 3 2 mcdT with hS5Tdef
  set S5U : SmoothCcTensor g 2 5 :=
    slotExtendIter (I := I) (M := M) g 0 3 2 mcdU with hS5Udef
  set S4T : SmoothCcTensor g 2 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 5 3
      (reindexedPureTrace (I := I) (M := M) g gmT 3 DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour) S5T
    with hS4Tdef
  set S4U : SmoothCcTensor g 2 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 5 3
      (reindexedPureTrace (I := I) (M := M) g gmU 3 DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour) S5U
    with hS4Udef
  set E3T : SmoothCcTensor g 3 6 :=
    slotExtendIter (I := I) (M := M) g 0 3 3 mcdT with hE3Tdef
  set E3U : SmoothCcTensor g 3 6 :=
    slotExtendIter (I := I) (M := M) g 0 3 3 mcdU with hE3Udef
  set S3T : SmoothCcTensor g 2 6 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 3 6 E3T S4T with hS3Tdef
  set S3U : SmoothCcTensor g 2 6 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 3 6 E3U S4U with hS3Udef
  set S2T : SmoothCcTensor g 2 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 6 4
      (reindexedPureTrace (I := I) (M := M) g gmT 4 DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne) S3T
    with hS2Tdef
  set S2U : SmoothCcTensor g 2 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 6 4
      (reindexedPureTrace (I := I) (M := M) g gmU 4 DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne) S3U
    with hS2Udef
  have hHalfT : lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g gmT g σlast =
      ccOperatorFieldComp (I := I) (M := M) g 2 4 2
        (reindexedPureTrace (I := I) (M := M) g gmT 2 σlast) S2T := rfl
  have hHalfU : lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g gmU g σlast =
      ccOperatorFieldComp (I := I) (M := M) g 2 4 2
        (reindexedPureTrace (I := I) (M := M) g gmU 2 σlast) S2U := rfl
  have hS5T2 : covariantJetNormSq (I := I) (M := M) g 2 S5T ≤ S5b R * pl2 := by
    rw [hS5Tdef]
    have h0 : slotExtendIter (I := I) (M := M) g 0 3 2 mcdT =
        slotExtend (I := I) (M := M) g 1 4
          (slotExtend (I := I) (M := M) g 0 3 mcdT) := rfl
    rw [h0]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdT)) ≤
        fr * covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 3 mcdT) :=
        covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 4 _
      _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 mcdT) :=
        mul_le_mul_of_nonneg_left
          (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 3 _) hfr
      _ ≤ fr * (fr * ((Bm R) ^ 2 * pl2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmbT hfr) hfr
      _ = S5b R * pl2 := by
        simp only [S5b]
        ring
  have hE3T2 : covariantJetNormSq (I := I) (M := M) g 2 E3T ≤ E3b R * pl2 := by
    rw [hE3Tdef]
    have h0 : slotExtendIter (I := I) (M := M) g 0 3 3 mcdT =
        slotExtend (I := I) (M := M) g 2 5
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdT)) := rfl
    rw [h0]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 2 5
            (slotExtend (I := I) (M := M) g 1 4
              (slotExtend (I := I) (M := M) g 0 3 mcdT))) ≤
        fr * covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdT)) :=
        covariantJetNormSq_slotExtend_le (I := I) (M := M) g 2 5 _
      _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 3 mcdT)) :=
        mul_le_mul_of_nonneg_left
          (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 4 _) hfr
      _ ≤ fr * (fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 mcdT)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 3 _) hfr) hfr
      _ ≤ fr * (fr * (fr * ((Bm R) ^ 2 * pl2))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmbT hfr) hfr) hfr
      _ = E3b R * pl2 := by
        simp only [E3b]
        ring
  have hE3U2 : covariantJetNormSq (I := I) (M := M) g 2 E3U ≤ E3b R * pl2 := by
    rw [hE3Udef]
    have h0 : slotExtendIter (I := I) (M := M) g 0 3 3 mcdU =
        slotExtend (I := I) (M := M) g 2 5
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdU)) := rfl
    rw [h0]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 2 5
            (slotExtend (I := I) (M := M) g 1 4
              (slotExtend (I := I) (M := M) g 0 3 mcdU))) ≤
        fr * covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdU)) :=
        covariantJetNormSq_slotExtend_le (I := I) (M := M) g 2 5 _
      _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 3 mcdU)) :=
        mul_le_mul_of_nonneg_left
          (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 4 _) hfr
      _ ≤ fr * (fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 mcdU)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 3 _) hfr) hfr
      _ ≤ fr * (fr * (fr * ((Bm R) ^ 2 * pl2))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmbU hfr) hfr) hfr
      _ = E3b R * pl2 := by
        simp only [E3b]
        ring
  have hpl2u : 0 ≤ pl2 * u := mul_nonneg hpl20 hu0
  have hS4T2 : covariantJetNormSq (I := I) (M := M) g 2 S4T ≤ S4b R * pl2 := by
    rw [hS4Tdef]
    refine (happ4 _ S5T).trans ?_
    have htr := (covariantJetNormSq_reindexedPureTrace (I := I) (M := M) g gmT 3 2
      DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour).le.trans htb3'.1
    calc
      Ca4 * covariantJetNormSq (I := I) (M := M) g 2
          (reindexedPureTrace (I := I) (M := M) g gmT 3 DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour) *
        covariantJetNormSq (I := I) (M := M) g 2 S5T ≤
        Ca4 * Bt3 ^ 2 * (S5b R * pl2) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left htr hCa4) hS5T2
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hCa4 (sq_nonneg _))
      _ = S4b R * pl2 := by
        simp only [S4b]
        ring
  have hS3T2 : covariantJetNormSq (I := I) (M := M) g 2 S3T ≤
      S3b R * (pl2 * pl2) := by
    rw [hS3Tdef]
    refine (happ3 E3T S4T).trans ?_
    calc
      Ca3 * covariantJetNormSq (I := I) (M := M) g 2 E3T *
        covariantJetNormSq (I := I) (M := M) g 2 S4T ≤
        Ca3 * (E3b R * pl2) * (S4b R * pl2) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hE3T2 hCa3) hS4T2
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hCa3 (mul_nonneg (hE3b R hR) hpl20))
      _ = S3b R * (pl2 * pl2) := by
        simp only [S3b]
        ring
  have hS2T2 : covariantJetNormSq (I := I) (M := M) g 2 S2T ≤
      S2b R * (pl2 * pl2) := by
    rw [hS2Tdef]
    refine (happ2 _ S3T).trans ?_
    have htr := (covariantJetNormSq_reindexedPureTrace (I := I) (M := M) g gmT 4 2
      DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne).le.trans htb4'.1
    calc
      Ca2 * covariantJetNormSq (I := I) (M := M) g 2
          (reindexedPureTrace (I := I) (M := M) g gmT 4 DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne) *
        covariantJetNormSq (I := I) (M := M) g 2 S3T ≤
        Ca2 * Bt4 ^ 2 * (S3b R * (pl2 * pl2)) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left htr hCa2) hS3T2
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hCa2 (sq_nonneg _))
      _ = S2b R * (pl2 * pl2) := by
        simp only [S2b]
        ring
  have hdel5 : S5T - S5U =
      slotExtend (I := I) (M := M) g 1 4
        (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU)) := by
    rw [hS5Tdef, hS5Udef,
      show slotExtendIter (I := I) (M := M) g 0 3 2 mcdT =
        slotExtend (I := I) (M := M) g 1 4
          (slotExtend (I := I) (M := M) g 0 3 mcdT) from rfl,
      show slotExtendIter (I := I) (M := M) g 0 3 2 mcdU =
        slotExtend (I := I) (M := M) g 1 4
          (slotExtend (I := I) (M := M) g 0 3 mcdU) from rfl,
      slotExtend_sub, slotExtend_sub]
  have hd5 : covariantJetNormSq (I := I) (M := M) g 2 (S5T - S5U) ≤
      D5c R * (pl2 * u) := by
    rw [hdel5]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU))) ≤
        fr * covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU)) :=
        covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 4 _
      _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 (mcdT - mcdU)) :=
        mul_le_mul_of_nonneg_left
          (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 3 _) hfr
      _ ≤ fr * (fr * (M5 R * (pl2 * u))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmpd hfr) hfr
      _ = D5c R * (pl2 * u) := by
        simp only [D5c]
        ring
  have htrd3 : covariantJetNormSq (I := I) (M := M) g 2
      (reindexedPureTrace (I := I) (M := M) g gmT 3 DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour -
        reindexedPureTrace (I := I) (M := M) g gmU 3 DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour) ≤
      Ct3 ^ 2 * u := by
    rw [reindexedPureTrace_sub, covariantJetNormSq_reindexCoeffGen]
    exact htp3'
  have hd4 : covariantJetNormSq (I := I) (M := M) g 2 (S4T - S4U) ≤
      2 * (K4 R * (pl2 * u) + K5 R * (pl2 * u)) := by
    rw [hS4Tdef, hS4Udef]
    have htr := (covariantJetNormSq_reindexedPureTrace (I := I) (M := M) g gmU 3 2
      DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour).le.trans htb3'.2
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (_ - _) ≤
          2 * (Ca4 * (Ct3 ^ 2 * u) * (S5b R * pl2) +
            Ca4 * Bt3 ^ 2 * (D5c R * (pl2 * u))) :=
        covariantJetNormSq_operatorFieldComposition_sub_le (I := I) (M := M) g 2 2 5 3
          Ca4 (Ct3 ^ 2 * u) (S5b R * pl2) (Bt3 ^ 2)
          (D5c R * (pl2 * u)) hCa4 _ _ _ _ happ4 htrd3 hS5T2 htr hd5
      _ = 2 * (K4 R * (pl2 * u) + K5 R * (pl2 * u)) := by
        simp only [K4, K5]
        ring
  have hdelE3 : E3T - E3U =
      slotExtend (I := I) (M := M) g 2 5
        (slotExtend (I := I) (M := M) g 1 4
          (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU))) := by
    rw [hE3Tdef, hE3Udef,
      show slotExtendIter (I := I) (M := M) g 0 3 3 mcdT =
        slotExtend (I := I) (M := M) g 2 5
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdT)) from rfl,
      show slotExtendIter (I := I) (M := M) g 0 3 3 mcdU =
        slotExtend (I := I) (M := M) g 2 5
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdU)) from rfl,
      slotExtend_sub, slotExtend_sub, slotExtend_sub]
  have hdE32 : covariantJetNormSq (I := I) (M := M) g 2 (E3T - E3U) ≤
      E3d R * (pl2 * u) := by
    rw [hdelE3]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 2 5
            (slotExtend (I := I) (M := M) g 1 4
              (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU)))) ≤
        fr * covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU))) :=
        covariantJetNormSq_slotExtend_le (I := I) (M := M) g 2 5 _
      _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU))) :=
        mul_le_mul_of_nonneg_left
          (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 4 _) hfr
      _ ≤ fr * (fr * (fr *
          covariantJetNormSq (I := I) (M := M) g 2 (mcdT - mcdU))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 3 _) hfr) hfr
      _ ≤ fr * (fr * (fr * (M5 R * (pl2 * u)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmpd hfr) hfr) hfr
      _ = E3d R * (pl2 * u) := by
        simp only [E3d]
        ring
  have hd3 : covariantJetNormSq (I := I) (M := M) g 2 (S3T - S3U) ≤
      2 * (K3 R * ((pl2 * pl2) * u) + K34 R * ((pl2 * pl2) * u)) := by
    rw [hS3Tdef, hS3Udef]
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (_ - _) ≤
          2 * (Ca3 * (E3d R * (pl2 * u)) * (S4b R * pl2) +
            Ca3 * (E3b R * pl2) *
              (2 * (K4 R * (pl2 * u) + K5 R * (pl2 * u)))) :=
        covariantJetNormSq_operatorFieldComposition_sub_le (I := I) (M := M) g 2 2 3 6
          Ca3 (E3d R * (pl2 * u)) (S4b R * pl2) (E3b R * pl2)
          (2 * (K4 R * (pl2 * u) + K5 R * (pl2 * u)))
          hCa3 _ _ _ _ happ3 hdE32 hS4T2 hE3U2 hd4
      _ = 2 * (K3 R * ((pl2 * pl2) * u) +
          K34 R * ((pl2 * pl2) * u)) := by
        simp only [K3, K34]
        ring
  have htrd4 : covariantJetNormSq (I := I) (M := M) g 2
      (reindexedPureTrace (I := I) (M := M) g gmT 4 DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne -
        reindexedPureTrace (I := I) (M := M) g gmU 4 DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne) ≤
      Ct4 ^ 2 * u := by
    rw [reindexedPureTrace_sub, covariantJetNormSq_reindexCoeffGen]
    exact htp4'
  have hd2 : covariantJetNormSq (I := I) (M := M) g 2 (S2T - S2U) ≤
      2 * (K2 R * ((pl2 * pl2) * u) + K23 R * ((pl2 * pl2) * u)) := by
    rw [hS2Tdef, hS2Udef]
    have htr := (covariantJetNormSq_reindexedPureTrace (I := I) (M := M) g gmU 4 2
      DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne).le.trans htb4'.2
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (_ - _) ≤
          2 * (Ca2 * (Ct4 ^ 2 * u) * (S3b R * (pl2 * pl2)) +
            Ca2 * Bt4 ^ 2 * (2 * (K3 R * ((pl2 * pl2) * u) +
              K34 R * ((pl2 * pl2) * u)))) :=
        covariantJetNormSq_operatorFieldComposition_sub_le (I := I) (M := M) g 2 2 6 4
          Ca2 (Ct4 ^ 2 * u) (S3b R * (pl2 * pl2)) (Bt4 ^ 2)
          (2 * (K3 R * ((pl2 * pl2) * u) + K34 R * ((pl2 * pl2) * u)))
          hCa2 _ _ _ _ happ2 htrd4 hS3T2 htr hd3
      _ = 2 * (K2 R * ((pl2 * pl2) * u) +
          K23 R * ((pl2 * pl2) * u)) := by
        simp only [K2, K23]
        ring
  have htrd2 : covariantJetNormSq (I := I) (M := M) g 2
      (reindexedPureTrace (I := I) (M := M) g gmT 2 σlast -
        reindexedPureTrace (I := I) (M := M) g gmU 2 σlast) ≤
      Ct2 ^ 2 * u := by
    rw [reindexedPureTrace_sub, covariantJetNormSq_reindexCoeffGen]
    exact htp2'
  have hhalf : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g gmT g σlast -
        lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g gmU g σlast) ≤
      Bh R * ((pl2 * pl2) * u) := by
    rw [hHalfT, hHalfU]
    have htr := (covariantJetNormSq_reindexedPureTrace (I := I) (M := M) g gmU 2 2
      σlast).le.trans htb2'.2
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (_ - _) ≤
          2 * (Ca1 * (Ct2 ^ 2 * u) * (S2b R * (pl2 * pl2)) +
            Ca1 * Bt2 ^ 2 * (2 * (K2 R * ((pl2 * pl2) * u) +
              K23 R * ((pl2 * pl2) * u)))) :=
        covariantJetNormSq_operatorFieldComposition_sub_le (I := I) (M := M) g 2 2 4 2
          Ca1 (Ct2 ^ 2 * u) (S2b R * (pl2 * pl2)) (Bt2 ^ 2)
          (2 * (K2 R * ((pl2 * pl2) * u) + K23 R * ((pl2 * pl2) * u)))
          hCa1 _ _ _ _ happ1 htrd2 hS2T2 htr hd2
      _ = Bh R * ((pl2 * pl2) * u) := by
        simp only [Bh, K1, K12]
        ring
  refine hhalf.trans ?_
  rw [hpl2, hu, hadef]
  simp only [B]
  exact pair_sum_sq_le (hBhnn R hR) hD3 hN

theorem RicciDeTurckLowOrder.exists_lieCorrectionZeroMixedConnection_covariantJetNormSq_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
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
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroMixedConnection (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g -
            lieCorrectionZeroMixedConnection (I := I) (M := M) g
              (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g) ≤
        (B R * (1 + A) ^ 2 * (D3 + N)) ^ 2 := by
  obtain ⟨ρ, Bp, hρ, hBp, hhalf⟩ :=
    exists_lieCorrectionZeroMixedConnectionHalfRF_thirdOrder_tame_difference_bound (I := I) (M := M) hDim g
  refine ⟨ρ, fun R => 4 * Bp R, hρ,
    fun R hR => by
      have := hBp R hR
      linarith, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D3 N hR hA hD3 hN hT2 hU2 hT3 hU3 hTU3
    hTn hUn hTUn s hs
  have hh1 := hhalf T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A D3 N hR hA hD3 hN hT2 hU2 hT3 hU3 hTU3
    hTn hUn hTUn hs DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne
  have hh2 := hhalf T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A D3 N hR hA hD3 hN hT2 hU2 hT3 hU3 hTU3
    hTn hUn hTUn hs
    (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)
  rw [lieCorrectionZeroMixedConnection_eq_expansion (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g,
    lieCorrectionZeroMixedConnection_eq_expansion (I := I) (M := M) g
      (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g]
  have hform :
      lieCorrectionZeroMixedConnectionExpansion (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g -
        lieCorrectionZeroMixedConnectionExpansion (I := I) (M := M) g
          (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g =
      (2 : ℝ) •
        ((lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g
              DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne -
          lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
            (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g
              DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne) +
        (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g
              (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne) -
          lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
            (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g
              (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne))) := by
    simp only [lieCorrectionZeroMixedConnectionExpansion]
    module
  rw [hform, covariantJetNormSq_smul]
  have hadd := covariantJetNormSq_add_le (I := I) (M := M) g 2
    (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g
          DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne -
      lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
        (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g
          DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)
    (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g
          (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne) -
      lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
        (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g
          (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne))
  calc
    (2 : ℝ) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 (_ + _) ≤
      (2 : ℝ) ^ 2 * (2 * (covariantJetNormSq (I := I) (M := M) g 2 _ +
        covariantJetNormSq (I := I) (M := M) g 2 _)) :=
      mul_le_mul_of_nonneg_left hadd (by positivity)
    _ ≤ (2 : ℝ) ^ 2 * (2 *
        ((Bp R * (1 + A) ^ 2 * (D3 + N)) ^ 2 +
          (Bp R * (1 + A) ^ 2 * (D3 + N)) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (add_le_add hh1 hh2) (by norm_num)) (by norm_num)
    _ = (4 * Bp R * (1 + A) ^ 2 * (D3 + N)) ^ 2 := by
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
