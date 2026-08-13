import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNormConnLapIterateJetLadderPrincipalBlock
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


private lemma bal_grid_mono {A B : ℕ → ℝ} (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    {l' j : ℕ} (hl' : l' ≤ j) :
    ∑ α ∈ Finset.range (l' + 1), A α * ∑ β ∈ Finset.range (l' + 1 - α), B β ≤
      ∑ α ∈ Finset.range (j + 1), A α * ∑ β ∈ Finset.range (j + 1 - α), B β := by
  refine le_trans (Finset.sum_le_sum (fun α _ => ?_))
    (Finset.sum_le_sum_of_subset_of_nonneg
      (fun y hy => Finset.mem_range.mpr (by have := Finset.mem_range.mp hy; omega))
      (fun α _ _ => mul_nonneg (hA α) (Finset.sum_nonneg (fun β _ => hB β))))
  refine mul_le_mul_of_nonneg_left ?_ (hA α)
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun y hy => Finset.mem_range.mpr (by have := Finset.mem_range.mp hy; omega))
    (fun β _ _ => hB β)

lemma bal_block23 (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
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
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
                (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                    (covGrad (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀)))‖ ≤
            CB q j * ‖smoothCcToTensorHs (I := I) (M := M) g₀
              ((j + 2 * q + 3 : ℕ) : ℝ) T₀‖ ∧
          ‖iteratedCovGrad (I := I) g₀ 0 2 j
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
                (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                    (slotExtend (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀)))‖ ≤
            CB q j * ‖smoothCcToTensorHs (I := I) (M := M) g₀
              ((j + 2 * q + 3 : ℕ) : ℝ) T₀‖ := by
  classical
  obtain ⟨CC, hCC_nn, hCC⟩ := exists_iteratedCovGrad_oneMinusConnLapSmoothIter_le_mul_tensorHs
    (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn
  obtain ⟨CCS, hCCS_nn, hCCS⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_oneMinusConnLapSmoothIter_le_sq_tensorHs (I := I) (M := M)
    g₀ Kc hKc_nn εa hεa_nn
  obtain ⟨CJ, hCJ_nn, hCJ⟩ := exists_iteratedCovGrad_le_const_mul_tensorHs (I := I) (M := M) g₀
  obtain ⟨CDS0, hCDS0_nn, hCDS0⟩ := riemannianFiberNormSq_iteratedCovGrad_le_sq_tensorHs (I := I)
    (M := M) g₀
  obtain ⟨CDT, hCDT_nn, hCDT⟩ := bal_DTwrap (I := I) (M := M) g₀
  set n : ℕ := Module.finrank ℝ E with hn_def
  set G : ℕ → ℝ := fun j => diagonalGridGrowthFactor (E := E) j * CDT *
    ((j + 1 : ℕ) * (diagonalGridGrowthFactor (E := E) j * n)) with hG_def
  have hG_nn : ∀ j, 0 ≤ G j := fun j => by
    have h1 := appCcGdiag_nonneg (E := E) j
    have h2 : (0:ℝ) ≤ (j + 1 : ℕ) := Nat.cast_nonneg _
    have h3 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    positivity
  refine ⟨fun q j => Real.sqrt (G j *
      ((∑ i ∈ Finset.range (j + 1), (CCS (1 + i) q * (1 + R₀)) ^ 2) *
        (∑ l ∈ Finset.range (j + 1), (CJ (1 + l)) ^ 2) +
        (∑ i ∈ Finset.range (j + 1), (CC (1 + i) q) ^ 2) *
          ((∑ l ∈ Finset.range (j + 1), (CDS0 (1 + l)) ^ 2) * (1 + R₀) ^ 2))),
    fun q j => Real.sqrt_nonneg _, ?_⟩
  intro C₀ T₀ hball henv q j
  set Ĉq : SmoothCcTensor g₀ 2 2 := oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀
    with hĈq_def
  have hcore : ∀ {sz : ℕ} (Z : SmoothCcTensor g₀ 0 sz),
      (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 sz x (Z.toSection x) ≤
        G j * ∑ i ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (1 + i)) x
            ((iteratedCovGrad (I := I) g₀ 2 2 (1 + i) Ĉq).toSection x) *
            ∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + l)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (1 + l) T₀).toSection x)) →
      ‖Z‖ ≤ Real.sqrt (G j *
        ((∑ i ∈ Finset.range (j + 1), (CCS (1 + i) q * (1 + R₀)) ^ 2) *
          (∑ l ∈ Finset.range (j + 1), (CJ (1 + l)) ^ 2) +
          (∑ i ∈ Finset.range (j + 1), (CC (1 + i) q) ^ 2) *
            ((∑ l ∈ Finset.range (j + 1), (CDS0 (1 + l)) ^ 2) * (1 + R₀) ^ 2))) *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 2 * q + 3 : ℕ) : ℝ) T₀‖ := by
    intro sz Z hpt
    refine bal_gridcore (I := I) (M := M) g₀ a ha_super hR₀ T₀ hball q j 1 1
      (Module.finrank ℝ E / 2 + 2) (by omega) (by omega) (by omega) (by omega)
      Z (fun i => 2 + (1 + i))
      (fun i => iteratedCovGrad (I := I) g₀ 2 2 (1 + i) Ĉq)
      (fun i => CC (1 + i) q) (fun i => CCS (1 + i) q)
      (fun i => hCC_nn (1 + i) q) (fun i => hCCS_nn (1 + i) q)
      (fun i => ?_) (fun i x => ?_)
      (fun l => 2 + (1 + l))
      (fun l => iteratedCovGrad (I := I) g₀ 0 2 (1 + l) T₀)
      (fun l => CJ (1 + l)) (fun l => CDS0 (1 + l))
      (fun l => hCJ_nn (1 + l)) (fun l => hCDS0_nn (1 + l))
      (fun l => ?_) (fun l x => ?_)
      (G j) (hG_nn j) hpt
    · rw [bal_fT_index_congr (I := I) (M := M) g₀ T₀
        (show 1 + i + 2 * q + 2 = (1 + i) + 2 * q + 2 from by omega)]
      exact hCC C₀ T₀ henv (1 + i) q
    · rw [bal_fT_index_congr (I := I) (M := M) g₀ T₀
        (show 1 + i + (Module.finrank ℝ E / 2 + 2) + 2 * q + 1 =
          (1 + i) + (Module.finrank ℝ E / 2 + 2) + 2 * q + 1 from by omega)]
      exact hCCS C₀ T₀ henv (1 + i) q x
    · rw [bal_fT_index_congr (I := I) (M := M) g₀ T₀
        (show (l + 1 : ℕ) = 1 + l from by omega)]
      exact hCJ (1 + l) T₀
    · rw [bal_fT_index_congr (I := I) (M := M) g₀ T₀
        (show l + (Module.finrank ℝ E / 2 + 2) =
          (1 + l) + (Module.finrank ℝ E / 2 + 1) from by omega)]
      exact hCDS0 T₀ (1 + l) x
  have hGd_mono : ∀ {l' : ℕ}, l' ≤ j → diagonalGridGrowthFactor (E := E) l' ≤
    diagonalGridGrowthFactor (E := E) j := by
    intro l' hl'
    have hbase : (1 : ℝ) ≤ 2 * ((Module.finrank ℝ E : ℝ) + 1) := by
      have : (0:ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
      linarith
    exact pow_le_pow_right₀ hbase hl'
  have hYgrid : ∀ (Cf' : SmoothCcTensor g₀ (2 + 1) (2 + 2)),
      (∀ (α : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 1) ((2 + 2) + α) x
            ((iteratedCovGrad (I := I) g₀ (2 + 1) (2 + 2) α Cf').toSection x) ≤
          (n : ℝ) * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (1 + α)) x
            ((iteratedCovGrad (I := I) g₀ 2 2 (1 + α) Ĉq).toSection x)) →
      ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 0 2 j
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
                (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2) Cf'
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀)))).toSection x) ≤
          G j * ∑ i ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (1 + i)) x
              ((iteratedCovGrad (I := I) g₀ 2 2 (1 + i) Ĉq).toSection x) *
              ∑ l ∈ Finset.range (j + 1 - i),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + l)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (1 + l) T₀).toSection x) := by
    intro Cf' hCf' x
    have hβconv : ∀ (β : ℕ),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 1) + β) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 1) β
              (covGrad (I := I) (M := M) g₀ 0 2 T₀)).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + β)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (1 + β) T₀).toSection x) := by
      intro β
      rw [covGrad_eq_iteratedCovGrad_one (I := I) (M := M) g₀ 0 2 T₀]
      exact riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 1 β T₀ x
    set gridj : ℝ := ∑ i ∈ Finset.range (j + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (1 + i)) x
        ((iteratedCovGrad (I := I) g₀ 2 2 (1 + i) Ĉq).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + l)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (1 + l) T₀).toSection x) with hgridj_def
    have hgridj_nn : 0 ≤ gridj :=
      Finset.sum_nonneg (fun i _ => mul_nonneg
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 _ x _)
        (Finset.sum_nonneg (fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 _ x _)))
    have hY : ∀ l' : ℕ, l' ≤ j →
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + l') x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) l'
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2) Cf'
                (covGrad (I := I) (M := M) g₀ 0 2 T₀))).toSection x) ≤
          diagonalGridGrowthFactor (E := E) j * (n : ℝ) * gridj := by
      intro l' hl'
      have hgrid := riemannianFiberNormSq_iteratedCovGrad_comp_diagonalProductGrid_le (I := I)
        (M := M) g₀
        (2 + 1) (2 + 2) Cf' (covGrad (I := I) (M := M) g₀ 0 2 T₀) l' x
      refine le_trans hgrid ?_
      have hterm : ∀ α ∈ Finset.range (l' + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 1) ((2 + 2) + α) x
              ((iteratedCovGrad (I := I) g₀ (2 + 1) (2 + 2) α Cf').toSection x) *
            ∑ β ∈ Finset.range (l' + 1 - α),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 1) + β) x
                ((iteratedCovGrad (I := I) g₀ 0 (2 + 1) β
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀)).toSection x) ≤
          (n : ℝ) * (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (1 + α)) x
              ((iteratedCovGrad (I := I) g₀ 2 2 (1 + α) Ĉq).toSection x) *
            ∑ β ∈ Finset.range (l' + 1 - α),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + β)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (1 + β) T₀).toSection x)) := by
        intro α _
        have hsum_eq : ∑ β ∈ Finset.range (l' + 1 - α),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 1) + β) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + 1) β
                (covGrad (I := I) (M := M) g₀ 0 2 T₀)).toSection x) =
            ∑ β ∈ Finset.range (l' + 1 - α),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + β)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (1 + β) T₀).toSection x) :=
          Finset.sum_congr rfl (fun β _ => hβconv β)
        rw [hsum_eq]
        have hs_nn : 0 ≤ ∑ β ∈ Finset.range (l' + 1 - α),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + β)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (1 + β) T₀).toSection x) :=
          Finset.sum_nonneg (fun β _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 _ x _)
        have h := mul_le_mul_of_nonneg_right (hCf' α x) hs_nn
        refine le_trans h (le_of_eq ?_)
        ring
      refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
        (appCcGdiag_nonneg (E := E) l')) ?_
      have hpull : ∑ α ∈ Finset.range (l' + 1),
          (n : ℝ) * (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (1 + α)) x
              ((iteratedCovGrad (I := I) g₀ 2 2 (1 + α) Ĉq).toSection x) *
            ∑ β ∈ Finset.range (l' + 1 - α),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + β)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (1 + β) T₀).toSection x)) =
          (n : ℝ) * ∑ α ∈ Finset.range (l' + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (1 + α)) x
              ((iteratedCovGrad (I := I) g₀ 2 2 (1 + α) Ĉq).toSection x) *
              ∑ β ∈ Finset.range (l' + 1 - α),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + β)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (1 + β) T₀).toSection x) := by
        rw [Finset.mul_sum]
      rw [hpull]
      have hmono := bal_grid_mono
        (A := fun α => riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (1 + α)) x
          ((iteratedCovGrad (I := I) g₀ 2 2 (1 + α) Ĉq).toSection x))
        (B := fun β => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + β)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (1 + β) T₀).toSection x))
        (fun α => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 _ x _)
        (fun β => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 _ x _) hl'
      calc diagonalGridGrowthFactor (E := E) l' * ((n : ℝ) * ∑ α ∈ Finset.range (l' + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (1 + α)) x
              ((iteratedCovGrad (I := I) g₀ 2 2 (1 + α) Ĉq).toSection x) *
              ∑ β ∈ Finset.range (l' + 1 - α),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + β)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (1 + β) T₀).toSection x))
          ≤ diagonalGridGrowthFactor (E := E) l' * ((n : ℝ) * gridj) := by
            refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) l')
            exact mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg _)
        _ ≤ diagonalGridGrowthFactor (E := E) j * ((n : ℝ) * gridj) := by
            refine mul_le_mul_of_nonneg_right (hGd_mono hl') ?_
            exact mul_nonneg (Nat.cast_nonneg _) hgridj_nn
        _ = diagonalGridGrowthFactor (E := E) j * (n : ℝ) * gridj := by ring
    have hDT := hCDT (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2) Cf'
      (covGrad (I := I) (M := M) g₀ 0 2 T₀)) j x
    refine le_trans hDT ?_
    have hsum_le : ∑ l' ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + l') x
          ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) l'
            (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2) Cf'
              (covGrad (I := I) (M := M) g₀ 0 2 T₀))).toSection x) ≤
        ((j + 1 : ℕ) : ℝ) * (diagonalGridGrowthFactor (E := E) j * (n : ℝ) * gridj) := by
      have h1 : ∀ l' ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + l') x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) l'
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2) Cf'
                (covGrad (I := I) (M := M) g₀ 0 2 T₀))).toSection x) ≤
          diagonalGridGrowthFactor (E := E) j * (n : ℝ) * gridj :=
        fun l' hl' => hY l' (by have := Finset.mem_range.mp hl'; omega)
      refine le_trans (Finset.sum_le_sum h1) (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc diagonalGridGrowthFactor (E := E) j * CDT * ∑ l' ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + l') x
          ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) l'
            (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2) Cf'
              (covGrad (I := I) (M := M) g₀ 0 2 T₀))).toSection x)
        ≤ diagonalGridGrowthFactor (E := E) j * CDT *
            (((j + 1 : ℕ) : ℝ) * (diagonalGridGrowthFactor (E := E) j * (n : ℝ) * gridj)) := by
          refine mul_le_mul_of_nonneg_left hsum_le ?_
          exact mul_nonneg (appCcGdiag_nonneg (E := E) j) hCDT_nn
      _ = G j * gridj := by
          rw [hG_def]
          push_cast
          ring
  constructor
  · refine hcore (iteratedCovGrad (I := I) g₀ 0 2 j
      (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
        (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
        (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
          (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
            (covGrad (I := I) (M := M) g₀ 2 2 Ĉq))
          (covGrad (I := I) (M := M) g₀ 0 2 T₀)))) ?_
    refine hYgrid (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
      (covGrad (I := I) (M := M) g₀ 2 2 Ĉq)) ?_
    intro α x
    have h1 := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 2 (2 + 1)
      (covGrad (I := I) (M := M) g₀ 2 2 Ĉq) α x
    refine le_trans h1 ?_
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (Nat.cast_nonneg _)
    rw [covGrad_eq_iteratedCovGrad_one (I := I) (M := M) g₀ 2 2 Ĉq]
    exact riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 2 2 1 α Ĉq x
  · refine hcore (iteratedCovGrad (I := I) g₀ 0 2 j
      (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
        (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
        (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
          (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
            (slotExtend (I := I) (M := M) g₀ 2 2 Ĉq))
          (covGrad (I := I) (M := M) g₀ 0 2 T₀)))) ?_
    refine hYgrid (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
      (slotExtend (I := I) (M := M) g₀ 2 2 Ĉq)) ?_
    intro α x
    have hconv : riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 1) ((2 + 2) + α) x
        ((iteratedCovGrad (I := I) g₀ (2 + 1) (2 + 2) α
          (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
            (slotExtend (I := I) (M := M) g₀ 2 2 Ĉq))).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 1) ((2 + 1) + (1 + α)) x
          ((iteratedCovGrad (I := I) g₀ (2 + 1) (2 + 1) (1 + α)
            (slotExtend (I := I) (M := M) g₀ 2 2 Ĉq)).toSection x) := by
      rw [covGrad_eq_iteratedCovGrad_one (I := I) (M := M) g₀ (2 + 1) (2 + 1)
        (slotExtend (I := I) (M := M) g₀ 2 2 Ĉq)]
      exact riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ (2 + 1) (2 + 1) 1 α
        (slotExtend (I := I) (M := M) g₀ 2 2 Ĉq) x
    rw [hconv]
    exact rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 2 2 Ĉq (1 + α) x

end BalLadder

end Spectral
end Analysis
end DifferentialGeometry

end
