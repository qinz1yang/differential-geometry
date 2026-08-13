import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNormConnLapIterateJetLadderGridCore
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

section BalLadder

variable (g₀ : SmoothRiemannianMetric I M)


lemma bal_fT_index_congr (g₀ : SmoothRiemannianMetric I M)
    (T₀ : SmoothCcTensor g₀ 0 2) {k k' : ℕ} (h : k = k') :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) T₀‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k' : ℕ) : ℝ) T₀‖ := by
  subst h; rfl

lemma bal_block1 (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (εa : ℝ) (hεa_nn : 0 ≤ εa) :
    ∃ CB : ℕ → ℕ → ℝ, (∀ q j, 0 ≤ CB q j) ∧
      ∀ (C₀ : SmoothCcTensor g₀ 2 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ (q j : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j
              (operatorFieldApply (I := I) (M := M) g₀ 2 2
                (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))‖ ≤
            CB q j * ‖smoothCcToTensorHs (I := I) (M := M) g₀
              ((j + 2 * q + 3 : ℕ) : ℝ) T₀‖ := by
  classical
  obtain ⟨CC, hCC_nn, hCC⟩ := exists_iteratedCovGrad_oneMinusConnLapSmoothIter_le_mul_tensorHs
    (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn
  obtain ⟨CCS, hCCS_nn, hCCS⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_oneMinusConnLapSmoothIter_le_sq_tensorHs (I := I) (M := M)
    g₀ Kc hKc_nn εa hεa_nn
  obtain ⟨CDL, hCDL_nn, hCDL⟩ := exists_iteratedCovGrad_rawTensorConnLapSmooth_le_mul_tensorHs
    (I := I) (M := M) g₀
  obtain ⟨CDS, hCDS_nn, hCDS⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_rawTensorConnLapSmooth_le_sq_tensorHs (I := I) (M := M) g₀
  refine ⟨fun q j => Real.sqrt (diagonalGridGrowthFactor (E := E) j *
      ((∑ i ∈ Finset.range (j + 1), (CCS i q * (1 + R₀)) ^ 2) *
        (∑ l ∈ Finset.range (j + 1), (CDL l) ^ 2) +
        (∑ i ∈ Finset.range (j + 1), (CC i q) ^ 2) *
          ((∑ l ∈ Finset.range (j + 1), (CDS l) ^ 2) * (1 + R₀) ^ 2))),
    fun q j => Real.sqrt_nonneg _, ?_⟩
  intro C₀ T₀ hball henv q j
  refine bal_gridcore (I := I) (M := M) g₀ a ha_super hR₀ T₀ hball q j 0 2
    (Module.finrank ℝ E / 2 + 3) (by omega) (by omega) (by omega) (by omega)
    (iteratedCovGrad (I := I) g₀ 0 2 j
      (operatorFieldApply (I := I) (M := M) g₀ 2 2
        (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)))
    (fun i => 2 + i)
    (fun i => iteratedCovGrad (I := I) g₀ 2 2 i
      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀))
    (fun i => CC i q) (fun i => CCS i q) (fun i => hCC_nn i q) (fun i => hCCS_nn i q)
    (fun i => ?_) (fun i x => ?_)
    (fun l => 2 + l)
    (fun l => iteratedCovGrad (I := I) g₀ 0 2 l
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))
    CDL CDS hCDL_nn hCDS_nn
    (fun l => ?_) (fun l x => ?_)
    (diagonalGridGrowthFactor (E := E) j) (appCcGdiag_nonneg (E := E) j)
    (fun x => ?_)
  · rw [bal_fT_index_congr (I := I) (M := M) g₀ T₀ (show 0 + i + 2 * q + 2 = i + 2 * q + 2
      from by omega)]
    exact hCC C₀ T₀ henv i q
  · have h := hCCS C₀ T₀ henv i q x
    rw [bal_fT_index_congr (I := I) (M := M) g₀ T₀
      (show 0 + i + (Module.finrank ℝ E / 2 + 2) + 2 * q + 1 =
        i + (Module.finrank ℝ E / 2 + 2) + 2 * q + 1 from by omega)]
    exact h
  · exact hCDL T₀ l
  · have h := hCDS T₀ l x
    rw [bal_fT_index_congr (I := I) (M := M) g₀ T₀
      (show l + (Module.finrank ℝ E / 2 + 3) = l + (Module.finrank ℝ E / 2 + 2) + 1
        from by omega)]
    exact h
  · exact riemannianFiberNormSq_iteratedCovGrad_comp_diagonalProductGrid_le (I := I) (M := M) g₀ 2 2
      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀) j x

lemma bal_DTwrap (g₀ : SmoothRiemannianMetric I M) :
    ∃ CDT : ℝ, 0 ≤ CDT ∧ ∀ (Y : SmoothCcTensor g₀ 0 (2 + 2)) (j : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j
            (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
              (DeTurck.cometricDoubleTraceField (I := I) g₀ 2) Y)).toSection x) ≤
        diagonalGridGrowthFactor (E := E) j * CDT * ∑ l' ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + l') x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) l' Y).toSection x) := by
  classical
  have hfam := fun i' : ℕ =>
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g₀ (2 + 2) (2 + i')
  choose Csh hCsh_nn hCsh using hfam
  set DT₂ : SmoothCcTensor g₀ (2 + 2) 2 := DeTurck.cometricDoubleTraceField (I := I) g₀ 2
    with hDT_def
  set w : ℕ := Module.finrank ℝ E / 2 + 2 with hw_def
  have hvanish : ∀ k : ℕ, 1 ≤ k → ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 k DT₂‖ = 0 := by
    intro k hk
    obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [show 1 + k' = k' + 1 from by omega]
    rw [iteratedCovGrad_eq_zero_of_covGrad_eq_zero (I := I) (M := M) g₀ (2 + 2) 2 DT₂
      (DeTurck.cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ 2) k']
    exact norm_zero
  set CDT : ℝ := Csh 0 ^ 2 * ∑ t ∈ Finset.range w,
    ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 t DT₂‖ ^ 2 with hCDT_def
  have hCDT_nn : 0 ≤ CDT :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun t _ => sq_nonneg _))
  refine ⟨CDT, hCDT_nn, fun Y j x => ?_⟩
  have hgrid := riemannianFiberNormSq_iteratedCovGrad_comp_diagonalProductGrid_le (I := I) (M := M)
    g₀ (2 + 2) 2
    DT₂ Y j x
  refine le_trans hgrid ?_
  have hDTsup : ∀ i' : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) (2 + i') x
          ((iteratedCovGrad (I := I) g₀ (2 + 2) 2 i' DT₂).toSection x) ≤
        (if i' = 0 then CDT else 0) := by
    intro i'
    match i' with
    | 0 =>
      rw [if_pos rfl]
      have h := hCsh 0 (iteratedCovGrad (I := I) g₀ (2 + 2) 2 0 DT₂) x
      refine le_trans h ?_
      rw [hCDT_def]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      refine le_of_eq (Finset.sum_congr rfl (fun t _ => ?_))
      have hcomp : ‖iteratedCovGrad (I := I) g₀ (2 + 2) (2 + 0) t
          (iteratedCovGrad (I := I) g₀ (2 + 2) 2 0 DT₂)‖ =
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 (0 + t) DT₂‖ :=
        norm_iteratedCovGrad_iteratedCovGrad_eq (I := I) (M := M) g₀ (2 + 2) 2 0 t DT₂
      rw [hcomp, show (0 + t : ℕ) = t from by omega]
    | (k + 1) =>
      rw [if_neg (Nat.succ_ne_zero k)]
      have h := hCsh (k + 1) (iteratedCovGrad (I := I) g₀ (2 + 2) 2 (k + 1) DT₂) x
      refine le_trans h ?_
      have hz : ∑ t ∈ Finset.range w,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) (2 + (k + 1)) t
            (iteratedCovGrad (I := I) g₀ (2 + 2) 2 (k + 1) DT₂)‖ ^ 2 = 0 := by
        refine Finset.sum_eq_zero (fun t _ => ?_)
        have hcomp : ‖iteratedCovGrad (I := I) g₀ (2 + 2) (2 + (k + 1)) t
            (iteratedCovGrad (I := I) g₀ (2 + 2) 2 (k + 1) DT₂)‖ =
            ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 ((k + 1) + t) DT₂‖ :=
          norm_iteratedCovGrad_iteratedCovGrad_eq (I := I) (M := M) g₀ (2 + 2) 2 (k + 1) t DT₂
        rw [hcomp, hvanish ((k + 1) + t) (by omega)]
        norm_num
      rw [hz, mul_zero]
  have hterm : ∀ i' ∈ Finset.range (j + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) (2 + i') x
          ((iteratedCovGrad (I := I) g₀ (2 + 2) 2 i' DT₂).toSection x) *
        ∑ l' ∈ Finset.range (j + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + l') x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) l' Y).toSection x) ≤
      (if i' = 0 then CDT * ∑ l' ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + l') x
          ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) l' Y).toSection x) else 0) := by
    intro i' hi'
    have hY_nn : 0 ≤ ∑ l' ∈ Finset.range (j + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + l') x
          ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) l' Y).toSection x) :=
      Finset.sum_nonneg (fun l' _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 _ x _)
    split_ifs with h0
    · subst h0
      refine mul_le_mul (le_trans (hDTsup 0) (by rw [if_pos rfl])) ?_ hY_nn hCDT_nn
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun l' _ _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 _ x _)
      exact fun y hy => Finset.mem_range.mpr (by have := Finset.mem_range.mp hy; omega)
    · have hle := hDTsup i'
      rw [if_neg h0] at hle
      have hrf_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) (2 + i') x
          ((iteratedCovGrad (I := I) g₀ (2 + 2) 2 i' DT₂).toSection x) :=
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ (2 + 2) _ x _
      have hzero : riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) (2 + i') x
          ((iteratedCovGrad (I := I) g₀ (2 + 2) 2 i' DT₂).toSection x) = 0 :=
        le_antisymm hle hrf_nn
      rw [hzero, zero_mul]
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
    (appCcGdiag_nonneg (E := E) j)) ?_
  rw [Finset.sum_ite_eq' (Finset.range (j + 1)) 0]
  rw [if_pos (Finset.mem_range.mpr (by omega))]
  rw [← mul_assoc]

end BalLadder

end Spectral
end Analysis
end DifferentialGeometry

end
