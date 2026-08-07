import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNorm
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature

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
  [T2Space M]

open DifferentialGeometry.Integral.Measure in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem iteratedCovGrad_comp_l2_sq_eq_rs
    (g₀ : SmoothRiemannianMetric I M) (r s m l : ℕ) (W : SmoothCcTensor g₀ r s) :
    ‖iteratedCovGrad (I := I) g₀ r (s + m) l (iteratedCovGrad (I := I) g₀ r s m W)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ r s (m + l) W‖ ^ 2 := by
  have hbridgeL : ‖iteratedCovGrad (I := I) g₀ r (s + m) l
        (iteratedCovGrad (I := I) g₀ r s m W)‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r ((s + m) + l) x
        ((iteratedCovGrad (I := I) g₀ r (s + m) l
          (iteratedCovGrad (I := I) g₀ r s m W)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ r
      ((s + m) + l)
      (iteratedCovGrad (I := I) g₀ r (s + m) l (iteratedCovGrad (I := I) g₀ r s m W))
  have hbridgeR : ‖iteratedCovGrad (I := I) g₀ r s (m + l) W‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r (s + (m + l)) x
        ((iteratedCovGrad (I := I) g₀ r s (m + l) W).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ r
      (s + (m + l)) (iteratedCovGrad (I := I) g₀ r s (m + l) W)
  rw [hbridgeL, hbridgeR]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  have hrw := riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ r s m l W x
  simpa only [Nat.add_assoc] using hrw

theorem exists_coeffAction_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le_of_lowOrder
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (_ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) :
    ∃ Cm : ℕ → ℝ, (∀ q, 0 ≤ Cm q) ∧
      ∀ (m : ℕ), m ≤ 1 →
      ∀ (C : SmoothCcTensor g₀ (2 + m) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ∀ q : ℕ, q + (Module.finrank ℝ E / 2 + 3) ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 C
                (iteratedCovGrad (I := I) g₀ 0 2 m T₀))‖ ≤
            Cm q * Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
  classical
  have hrsub : ∀ k l : ℕ, k ≤ l → Finset.range k ⊆ Finset.range l :=
    fun k l hkl x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hkl)
  have hB2 : ∀ m i : ℕ, ∃ Csh : ℝ, 0 ≤ Csh ∧
      ∀ (T : SmoothCcTensor g₀ (2 + m) (2 + i)) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) (2 + i) x (T.toSection x) ≤
          Csh ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g₀ (2 + m) (2 + i) j T‖ ^ 2 :=
    fun m i =>
      exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
        (I := I) (M := M) g₀ (2 + m) (2 + i)
  choose Csh2 hCsh2_nn hCsh2 using hB2
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ (a + 2)
  set B : ℝ := C2 * R₀ with hB_def
  have hB_nn : 0 ≤ B := mul_nonneg hC2_nn hR₀
  set Lam : ℕ → ℕ → ℝ := fun m i => (Csh2 m i) ^ 2 *
    ((∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2), Kc (i + j)) * (1 + B ^ 2))
    with hLam_def
  have hLam_nn : ∀ m i, 0 ≤ Lam m i := by
    intro m i
    rw [hLam_def]
    have h1 : 0 ≤ ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2), Kc (i + j) :=
      Finset.sum_nonneg (fun j _ => hKc_nn _)
    have h2 : (0 : ℝ) ≤ 1 + B ^ 2 := by positivity
    exact mul_nonneg (sq_nonneg _) (mul_nonneg h1 h2)
  set D : ℕ → ℕ → ℝ := fun m q => Real.sqrt (diagonalGridGrowthFactor (E := E) q *
    ∑ i ∈ Finset.range (q + 1), Lam m i) * ((q : ℝ) + 1) with hD_def
  have hD_nn : ∀ m q, 0 ≤ D m q := by
    intro m q
    rw [hD_def]
    exact mul_nonneg (Real.sqrt_nonneg _) (by positivity)
  refine ⟨fun q => D 0 q + D 1 q, fun q => add_nonneg (hD_nn 0 q) (hD_nn 1 q), ?_⟩
  intro m hm C T₀ hball henv q hband
  set S : ℝ := ∑ i ∈ Finset.range (q + 1 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  set W : SmoothCcTensor g₀ 0 (2 + m) := iteratedCovGrad (I := I) g₀ 0 2 m T₀ with hW_def
  have hball_sq : (∑ i ∈ Finset.range (a + 2 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) ≤ B ^ 2 := by
    have hsq_le : ∑ i ∈ Finset.range (a + 2 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 ≤
        (∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖) ^ 2 := by
      have hnn : ∀ i ∈ Finset.range (a + 2 + 1),
          (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ := fun i _ => norm_nonneg _
      have hstep : ∀ i ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 ≤
            ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ *
              (∑ j ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖) := by
        intro i hi
        rw [sq]
        exact mul_le_mul_of_nonneg_left (Finset.single_le_sum hnn hi) (norm_nonneg _)
      refine le_trans (Finset.sum_le_sum hstep) ?_
      rw [← Finset.sum_mul, sq]
    refine le_trans hsq_le ?_
    have hjets : ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ≤
        C2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ := hC2 T₀
    have hcast : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [hcast] at hjets
    have hjets2 : ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ≤
        B := by
      rw [hB_def]
      exact le_trans hjets (mul_le_mul_of_nonneg_left hball hC2_nn)
    have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (a + 2 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ :=
      Finset.sum_nonneg (fun i _ => norm_nonneg _)
    exact pow_le_pow_left₀ hsum_nn hjets2 2
  have hCoeff : ∀ i : ℕ, i ≤ q → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) (2 + i) x
        ((iteratedCovGrad (I := I) g₀ (2 + m) 2 i C).toSection x) ≤ Lam m i := by
    intro i hi x
    refine le_trans (hCsh2 m i (iteratedCovGrad (I := I) g₀ (2 + m) 2 i C) x) ?_
    rw [hLam_def]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have hterm : ∀ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
        ‖iteratedCovGrad (I := I) g₀ (2 + m) (2 + i) j
          (iteratedCovGrad (I := I) g₀ (2 + m) 2 i C)‖ ^ 2 ≤ Kc (i + j) * (1 + B ^ 2) := by
      intro j hj
      rw [iteratedCovGrad_comp_l2_sq_eq_rs (I := I) g₀ (2 + m) 2 i j C]
      refine le_trans (henv (i + j)) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hKc_nn _)
      have hjw : j < Module.finrank ℝ E / 2 + 2 := Finset.mem_range.mp hj
      have hwin : ∑ l ∈ Finset.range (i + j + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 ≤
          ∑ l ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (hrsub _ _ (show i + j + 2 ≤ a + 2 + 1 by omega))
          (fun l _ _ => sq_nonneg _)
      linarith [hball_sq]
    calc ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
          ‖iteratedCovGrad (I := I) g₀ (2 + m) (2 + i) j
            (iteratedCovGrad (I := I) g₀ (2 + m) 2 i C)‖ ^ 2
        ≤ ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2), Kc (i + j) * (1 + B ^ 2) :=
          Finset.sum_le_sum hterm
      _ = (∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2), Kc (i + j)) * (1 + B ^ 2) := by
          rw [← Finset.sum_mul]
  set Cpt : ℝ := Real.sqrt (diagonalGridGrowthFactor (E := E) q *
    ∑ i ∈ Finset.range (q + 1), Lam m i) with hCpt_def
  have hGq_nn : 0 ≤ diagonalGridGrowthFactor (E := E) q := appCcGdiag_nonneg (E := E) q
  have hSumLam_nn : 0 ≤ ∑ i ∈ Finset.range (q + 1), Lam m i :=
    Finset.sum_nonneg (fun i _ => hLam_nn m i)
  have hCpt_nn : 0 ≤ Cpt := Real.sqrt_nonneg _
  have hCpt_sq : Cpt ^ 2 = diagonalGridGrowthFactor (E := E) q * ∑ i ∈ Finset.range (q + 1), Lam m
    i := by
    rw [hCpt_def]
    exact Real.sq_sqrt (mul_nonneg hGq_nn hSumLam_nn)
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 0 2 q
          (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 C W)).toSection x) ≤
      Cpt ^ 2 * ∑ l ∈ Finset.range (q + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
          ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x) := by
    intro x
    refine le_trans
      (riemannianFiberNormSq_iteratedCovGrad_comp_diagonalProductGrid_le (I := I) (M := M) g₀
        (2 + m) 2 C W q x) ?_
    rw [hCpt_sq]
    have hb_nn : 0 ≤ ∑ l ∈ Finset.range (q + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
          ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x) :=
      Finset.sum_nonneg (fun l _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ _ _ _ _)
    have hstep : ∀ i ∈ Finset.range (q + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) (2 + i) x
            ((iteratedCovGrad (I := I) g₀ (2 + m) 2 i C).toSection x) *
          (∑ l ∈ Finset.range (q + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x)) ≤
        Lam m i * ∑ l ∈ Finset.range (q + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x) := by
      intro i hi
      have hi' : i ≤ q := by
        have := Finset.mem_range.mp hi
        omega
      have hinner : (∑ l ∈ Finset.range (q + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x)) ≤
          ∑ l ∈ Finset.range (q + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (hrsub _ _ (show q + 1 - i ≤ q + 1 by omega))
          (fun l _ _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ _ _ _ _)
      have hinner_nn : 0 ≤ ∑ l ∈ Finset.range (q + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x) :=
        Finset.sum_nonneg (fun l _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ _ _ _ _)
      exact mul_le_mul (hCoeff i hi' x) hinner hinner_nn (hLam_nn m i)
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) hGq_nn) ?_
    rw [← Finset.sum_mul, ← mul_assoc]
  have hPTLP := tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g₀
    (q + 1) (fun l => (2 + m) + l)
    (fun l => iteratedCovGrad (I := I) g₀ 0 (2 + m) l W)
    (iteratedCovGrad (I := I) g₀ 0 2 q (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 C W))
    Cpt hCpt_nn hpt
  have hWl : ∀ l ∈ Finset.range (q + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ≤ Real.sqrt S := by
    intro l hl
    have hl' : l ≤ q := by
      have := Finset.mem_range.mp hl
      omega
    have hsq : ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) T₀‖ ^ 2 := by
      rw [hW_def]
      exact iteratedCovGrad_comp_l2_sq_eq_rs (I := I) g₀ 0 2 m l T₀
    have hin : ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) T₀‖ ^ 2 ≤ S := by
      rw [hS_def]
      exact Finset.single_le_sum
        (f := fun i => ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2)
        (fun i _ => sq_nonneg _)
        (Finset.mem_range.mpr (show m + l < q + 1 + 1 by omega))
    calc ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖
        = Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) T₀‖ ^ 2) := by rw [hsq]
      _ ≤ Real.sqrt S := Real.sqrt_le_sqrt hin
  have hsumW : ∑ l ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ≤
      ((q : ℝ) + 1) * Real.sqrt S := by
    have := Finset.sum_le_card_nsmul (Finset.range (q + 1))
      (fun l => ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖) (Real.sqrt S) hWl
    rw [Finset.card_range, nsmul_eq_mul] at this
    calc ∑ l ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖
        ≤ ((q + 1 : ℕ) : ℝ) * Real.sqrt S := this
      _ = ((q : ℝ) + 1) * Real.sqrt S := by push_cast; ring
  refine le_trans hPTLP ?_
  have hfin : Cpt * (∑ l ∈ Finset.range (q + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖) ≤ Cpt * (((q : ℝ) + 1) * Real.sqrt S) :=
    mul_le_mul_of_nonneg_left hsumW hCpt_nn
  refine le_trans hfin ?_
  have hDm : Cpt * (((q : ℝ) + 1) * Real.sqrt S) = D m q * Real.sqrt S := by
    rw [hD_def, hCpt_def]
    ring
  rw [hDm]
  have hDle : D m q ≤ D 0 q + D 1 q := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with h | h
    · rw [h]; have := hD_nn 1 q; linarith
    · rw [h]; have := hD_nn 0 q; linarith
  exact mul_le_mul_of_nonneg_right hDle (Real.sqrt_nonneg _)

open DifferentialGeometry.Integral.Measure in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem iteratedCovGrad_comp_l2_sq_eq
    (g₀ : SmoothRiemannianMetric I M) (m l : ℕ) (W : SmoothCcTensor g₀ 0 2) :
    ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m W)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) W‖ ^ 2 := by
  have hbridgeL : ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
        (iteratedCovGrad (I := I) g₀ 0 2 m W)‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
        ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
          (iteratedCovGrad (I := I) g₀ 0 2 m W)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ ((2 + m) + l)
      (iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m W))
  have hbridgeR : ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) W‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + l)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (m + l) W).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (2 + (m + l))
      (iteratedCovGrad (I := I) g₀ 0 2 (m + l) W)
  rw [hbridgeL, hbridgeR]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  have hrw := riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 m l W x
  simpa only [Nat.add_assoc] using hrw

open DifferentialGeometry.Integral.Measure in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem iteratedCovGrad_comp_jetSum_le
    (g₀ : SmoothRiemannianMetric I M) (p m : ℕ) (W : SmoothCcTensor g₀ 0 2) :
    (∑ l ∈ Finset.range (p + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m W)‖ ^ 2) ≤
      ∑ i ∈ Finset.range (p + m + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 := by
  rw [show (∑ l ∈ Finset.range (p + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m W)‖ ^ 2) =
      ∑ l ∈ Finset.range (p + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) W‖ ^ 2 from
    Finset.sum_congr rfl (fun l _ => iteratedCovGrad_comp_l2_sq_eq (I := I) g₀ m l W)]
  set f : ℕ → ℝ := fun i => ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 with hf_def
  have hf_nn : ∀ i, 0 ≤ f i := fun i => sq_nonneg _
  have himg : (Finset.range (p + 1)).image (fun l => m + l) ⊆ Finset.range (p + m + 1) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨l, hl, rfl⟩ := hi
    rw [Finset.mem_range] at hl ⊢
    omega
  have hinj : ∀ l₁ ∈ Finset.range (p + 1), ∀ l₂ ∈ Finset.range (p + 1),
      m + l₁ = m + l₂ → l₁ = l₂ := fun l₁ _ l₂ _ h => by omega
  calc (∑ l ∈ Finset.range (p + 1), f (m + l))
      = ∑ i ∈ (Finset.range (p + 1)).image (fun l => m + l), f i :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ i ∈ Finset.range (p + m + 1), f i :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun i _ _ => hf_nn i)

theorem exists_coeffAction_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le_of_highOrder
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (Λ : ℝ) (hΛ_nn : 0 ≤ Λ) :
    ∃ Cm : ℕ → ℝ, (∀ q, 0 ≤ Cm q) ∧
      ∀ (m : ℕ), m ≤ 1 →
      ∀ (C : SmoothCcTensor g₀ (2 + m) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (C.toSection x) ≤ Λ ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ∀ q : ℕ, a ≤ q + (Module.finrank ℝ E / 2 + 3) →
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 C
                (iteratedCovGrad (I := I) g₀ 0 2 m T₀))‖ ≤
            Cm q * Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
  classical
  have hrsub : ∀ k l : ℕ, k ≤ l → Finset.range k ⊆ Finset.range l :=
    fun k l hkl x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hkl)
  have hE : ∀ m q : ℕ, ∃ CE : ℝ, 0 ≤ CE ∧
      ∀ (Φ : SmoothCcTensor g₀ (2 + m) 2) (W : SmoothCcTensor g₀ 0 (2 + m)) (ΛΦ ΛW : ℝ),
        0 ≤ ΛΦ → 0 ≤ ΛW →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (Φ.toSection x) ≤
          ΛΦ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x (W.toSection x) ≤
          ΛW ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 Φ W)‖ ^ 2 ≤
          CE * (ΛW ^ 2 * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Φ‖ ^ 2
              + ΛΦ ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2) :=
    fun m q => ccTensorContract_topOrder_l2_twoArm_mixed_le (I := I) (M := M) g₀ (2 + m) 2 q
  choose CE hCE_nn hCE using hE
  have hB : ∀ m : ℕ, ∃ Csh : ℝ, 0 ≤ Csh ∧
      ∀ (T : SmoothCcTensor g₀ 0 (2 + m)) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x (T.toSection x) ≤
          Csh ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) j T‖ ^ 2 :=
    fun m =>
      exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
        (I := I) (M := M) g₀ 0 (2 + m)
  choose Csh hCsh_nn hCsh using hB
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ (a + 2)
  set B : ℝ := C2 * R₀ with hB_def
  have hB_nn : 0 ≤ B := mul_nonneg hC2_nn hR₀
  set D : ℕ → ℕ → ℝ := fun m q => Real.sqrt (CE m q *
    ((Csh m) ^ 2 * (∑ i ∈ Finset.range (q + 1), Kc i) * (1 + B ^ 2) + Λ ^ 2)) with hD_def
  have hD_nn : ∀ m q, 0 ≤ D m q := fun m q => Real.sqrt_nonneg _
  refine ⟨fun q => D 0 q + D 1 q, fun q => add_nonneg (hD_nn 0 q) (hD_nn 1 q), ?_⟩
  intro m hm C T₀ hball hsup henv q hband
  set S : ℝ := ∑ i ∈ Finset.range (q + 1 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  set W : SmoothCcTensor g₀ 0 (2 + m) := iteratedCovGrad (I := I) g₀ 0 2 m T₀ with hW_def
  set SW : ℝ := ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) j W‖ ^ 2 with hSW_def
  have hSW_nn : 0 ≤ SW := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  set ΛW : ℝ := Csh m * Real.sqrt SW with hΛW_def
  have hΛW_nn : 0 ≤ ΛW := mul_nonneg (hCsh_nn m) (Real.sqrt_nonneg _)
  have hWsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
      (W.toSection x) ≤ ΛW ^ 2 := by
    intro x
    have h := hCsh m W x
    rw [hΛW_def, mul_pow, Real.sq_sqrt hSW_nn, hSW_def]
    exact h
  have hMain := hCE m q C W Λ ΛW hΛ_nn hΛW_nn hsup hWsup
  have hSW_case : SW ≤ ∑ i ∈ Finset.range (Module.finrank ℝ E / 2 + 1 + m + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 := by
    have h := iteratedCovGrad_comp_jetSum_le (I := I) g₀ (Module.finrank ℝ E / 2 + 1) m T₀
    rw [hSW_def, hW_def]
    exact h
  have hSW_le_S : SW ≤ S := by
    refine le_trans hSW_case ?_
    rw [hS_def]
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (hrsub _ _ (show Module.finrank ℝ E / 2 + 1 + m + 1 ≤ q + 1 + 1 by omega))
      (fun i _ _ => sq_nonneg _)
  have hSW_le_B : SW ≤ B ^ 2 := by
    refine le_trans hSW_case ?_
    have hsub : ∑ i ∈ Finset.range (Module.finrank ℝ E / 2 + 1 + m + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 ≤
        ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (hrsub _ _ (show Module.finrank ℝ E / 2 + 1 + m + 1 ≤ a + 2 + 1 by omega))
        (fun i _ _ => sq_nonneg _)
    refine le_trans hsub ?_
    have hsq_le : ∑ i ∈ Finset.range (a + 2 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 ≤
        (∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖) ^ 2 := by
      have hnn : ∀ i ∈ Finset.range (a + 2 + 1),
          (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ := fun i _ => norm_nonneg _
      have hstep : ∀ i ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 ≤
            ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ *
              (∑ j ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖) := by
        intro i hi
        rw [sq]
        exact mul_le_mul_of_nonneg_left
          (Finset.single_le_sum hnn hi) (norm_nonneg _)
      refine le_trans (Finset.sum_le_sum hstep) ?_
      rw [← Finset.sum_mul, sq]
    refine le_trans hsq_le ?_
    have hjets : ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ≤
        C2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ := hC2 T₀
    have hcast : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [hcast] at hjets
    have hjets2 : ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ≤
        B := by
      rw [hB_def]
      exact le_trans hjets (mul_le_mul_of_nonneg_left hball hC2_nn)
    have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (a + 2 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ :=
      Finset.sum_nonneg (fun i _ => norm_nonneg _)
    exact pow_le_pow_left₀ hsum_nn hjets2 2
  have hSigC : ∑ i ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2 ≤
      (∑ i ∈ Finset.range (q + 1), Kc i) * (1 + S) := by
    have hstep : ∀ i ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2 ≤ Kc i * (1 + S) := by
      intro i hi
      rw [Finset.mem_range] at hi
      refine le_trans (henv i) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hKc_nn i)
      have hwin : ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 ≤
          S := by
        rw [hS_def]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (hrsub _ _ (show i + 2 ≤ q + 1 + 1 by omega))
          (fun j _ _ => sq_nonneg _)
      linarith
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.sum_mul]
  have hSigW : ∑ l ∈ Finset.range (q + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2 ≤ S := by
    have := iteratedCovGrad_comp_jetSum_le (I := I) g₀ q m T₀
    rw [← hW_def] at this
    refine le_trans this ?_
    rw [hS_def]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (hrsub _ _ (show q + m + 1 ≤ q + 1 + 1 by omega))
      (fun i _ _ => sq_nonneg _)
  have hcore : ‖iteratedCovGrad (I := I) g₀ 0 2 q
      (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 C W)‖ ^ 2 ≤ (D m q) ^ 2 * S := by
    have hΛW_sq : ΛW ^ 2 = (Csh m) ^ 2 * SW := by
      rw [hΛW_def, mul_pow, Real.sq_sqrt hSW_nn]
    have h1 : ΛW ^ 2 * (∑ i ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2) ≤
        (Csh m) ^ 2 * ((∑ i ∈ Finset.range (q + 1), Kc i) * (SW + SW * S)) := by
      rw [hΛW_sq]
      have hKcS_nn : 0 ≤ (∑ i ∈ Finset.range (q + 1), Kc i) :=
        Finset.sum_nonneg (fun i _ => hKc_nn i)
      calc (Csh m) ^ 2 * SW * (∑ i ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2)
          ≤ (Csh m) ^ 2 * SW * ((∑ i ∈ Finset.range (q + 1), Kc i) * (1 + S)) := by
            refine mul_le_mul_of_nonneg_left hSigC ?_
            positivity
        _ = (Csh m) ^ 2 * ((∑ i ∈ Finset.range (q + 1), Kc i) * (SW + SW * S)) := by ring
    have h2 : SW + SW * S ≤ (1 + B ^ 2) * S := by
      have ha' : SW * S ≤ B ^ 2 * S := mul_le_mul_of_nonneg_right hSW_le_B hS_nn
      have hb' : SW ≤ S := hSW_le_S
      have : (1 + B ^ 2) * S = S + B ^ 2 * S := by ring
      linarith
    have h3 : (Csh m) ^ 2 * ((∑ i ∈ Finset.range (q + 1), Kc i) * (SW + SW * S)) ≤
        (Csh m) ^ 2 * ((∑ i ∈ Finset.range (q + 1), Kc i) * ((1 + B ^ 2) * S)) := by
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      refine mul_le_mul_of_nonneg_left h2 ?_
      exact Finset.sum_nonneg (fun i _ => hKc_nn i)
    have h4 : Λ ^ 2 * (∑ l ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2) ≤ Λ ^ 2 * S :=
      mul_le_mul_of_nonneg_left hSigW (sq_nonneg _)
    have hD_sq : (D m q) ^ 2 = CE m q *
        ((Csh m) ^ 2 * (∑ i ∈ Finset.range (q + 1), Kc i) * (1 + B ^ 2) + Λ ^ 2) := by
      rw [hD_def]
      refine Real.sq_sqrt ?_
      have hKcS_nn : 0 ≤ ∑ i ∈ Finset.range (q + 1), Kc i :=
        Finset.sum_nonneg (fun i _ => hKc_nn i)
      have h6 : 0 ≤ (Csh m) ^ 2 * (∑ i ∈ Finset.range (q + 1), Kc i) * (1 + B ^ 2) := by
        refine mul_nonneg (mul_nonneg (sq_nonneg _) hKcS_nn) ?_
        have := sq_nonneg B
        linarith
      exact mul_nonneg (hCE_nn m q) (by linarith [sq_nonneg Λ])
    calc ‖iteratedCovGrad (I := I) g₀ 0 2 q
          (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 C W)‖ ^ 2
        ≤ CE m q * (ΛW ^ 2 * ∑ i ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2
            + Λ ^ 2 * ∑ l ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2) := hMain
      _ ≤ CE m q * ((Csh m) ^ 2 * ((∑ i ∈ Finset.range (q + 1), Kc i) * ((1 + B ^ 2) * S))
            + Λ ^ 2 * S) := by
          refine mul_le_mul_of_nonneg_left ?_ (hCE_nn m q)
          have := le_trans h1 h3
          linarith
      _ = (CE m q * ((Csh m) ^ 2 * (∑ i ∈ Finset.range (q + 1), Kc i) * (1 + B ^ 2)
            + Λ ^ 2)) * S := by ring
      _ = (D m q) ^ 2 * S := by rw [hD_sq]
  have hfinal : ‖iteratedCovGrad (I := I) g₀ 0 2 q
      (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 C W)‖ ≤ D m q * Real.sqrt S := by
    have h1 : ‖iteratedCovGrad (I := I) g₀ 0 2 q
        (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 C W)‖ =
        Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 q
          (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 C W)‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    rw [h1]
    refine le_trans (Real.sqrt_le_sqrt hcore) ?_
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hD_nn m q)]
  refine le_trans hfinal ?_
  have hDle : D m q ≤ D 0 q + D 1 q := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with h | h
    · rw [h]; have := hD_nn 1 q; linarith
    · rw [h]; have := hD_nn 0 q; linarith
  exact mul_le_mul_of_nonneg_right hDle (Real.sqrt_nonneg _)

theorem exists_coeffAction_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (Λ : ℝ) (hΛ_nn : 0 ≤ Λ) :
    ∃ Cm : ℕ → ℝ, (∀ q, 0 ≤ Cm q) ∧
      ∀ (m : ℕ), m ≤ 1 →
      ∀ (C : SmoothCcTensor g₀ (2 + m) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (C.toSection x) ≤ Λ ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ∀ q : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 C
                (iteratedCovGrad (I := I) g₀ 0 2 m T₀))‖ ≤
            Cm q * Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
  classical
  obtain ⟨CmA, hCmA_nn, hA⟩ :=
    exists_coeffAction_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le_of_lowOrder
      (I := I) (M := M) g₀ a ha_super hR₀ Kc hKc_nn
  obtain ⟨CmB, hCmB_nn, hB⟩ :=
    exists_coeffAction_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le_of_highOrder
      (I := I) (M := M) g₀ a ha_super hR₀ Kc hKc_nn Λ hΛ_nn
  refine ⟨fun q => CmA q + CmB q,
    fun q => add_nonneg (hCmA_nn q) (hCmB_nn q), ?_⟩
  intro m hm C T₀ hball hsup henv q
  have hsqrt_nn : 0 ≤ Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := Real.sqrt_nonneg _
  rcases le_total (q + (Module.finrank ℝ E / 2 + 3)) a with hband | hband
  · refine le_trans (hA m hm C T₀ hball henv q hband) ?_
    have := mul_le_mul_of_nonneg_right
      (show CmA q ≤ CmA q + CmB q by have := hCmB_nn q; linarith) hsqrt_nn
    linarith
  · refine le_trans (hB m hm C T₀ hball hsup henv q hband) ?_
    have := mul_le_mul_of_nonneg_right
      (show CmB q ≤ CmA q + CmB q by have := hCmA_nn q; linarith) hsqrt_nn
    linarith

theorem
    exists_deTurckSmoothRemainderDiff_sub_principalCometricArm_smallThirdArm_iteratedCovGrad_jet_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ εC : ℝ, 0 ≤ εC ∧
      (0 ≤ δ → εC ≤ 32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * (δ / (1 - δ))) ∧
      (0 ≤ δ → εC ≤ 28 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ∧
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
    ∃ εa : ℝ, 0 ≤ εa ∧
      2 * Real.sqrt (Module.finrank ℝ E) * εa ≤
        32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 ∧
    ∃ Λa : ℝ, 0 ≤ Λa ∧
    ∃ Clow : ℕ → ℝ, (∀ q, 0 ≤ Clow q) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2)
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w
            v)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∃ (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (C₀ : SmoothCcTensor g₀ (2 + 0) 2),
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂.toSection x) ≤ εC ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤
              Λa ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
                εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) ∧
          ∀ q : ℕ,
            ‖iteratedCovGrad (I := I) g₀ 0 2 q
                (deTurckSmoothRemainder (I := I) g₀ g_bg T₀
                    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) -
                  deTurckSmoothRemainder (I := I) g₀ g_bg
                    (0 : SmoothCcTensor g₀ 0 2)
                    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                    (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                      (by
                        rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                            from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                          tensorHs_norm_smul]
                        simpa using hR₀)) -
                  deTurckPrincipalCometricArm (I := I) (M := M) g₀
                    (tensorSectionRealizeMetric (I := I) g₀ T₀
                      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                      (hδ_fibre T₀ hball)) T₀ -
                  operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) -
                  operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀
                    (iteratedCovGrad (I := I) g₀ 0 2 0 T₀))‖ ≤
              Clow q * Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
  classical
  obtain ⟨εC, hεC_nn, hεC_cap, hεC_cap', Kc, hKc_nn, εa, hεa_nn, hεa_cap, Λ, hΛ_nn, hL1⟩ :=
    exists_deTurckSmoothRemainderDiff_sub_principalCometricArm_threeArmCoeffAction_coeffJetEnvelope
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨Cm, hCm_nn, hM2⟩ :=
    exists_coeffAction_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le
      (I := I) (M := M) g₀ a ha_super hR₀ Kc hKc_nn Λ hΛ_nn
  refine ⟨εC, hεC_nn, hεC_cap, hεC_cap', Kc, hKc_nn, εa, hεa_nn, hεa_cap, Λ, hΛ_nn,
    Cm, hCm_nn, fun T₀ hTsymm hball => ?_⟩
  obtain ⟨C₀, C₁, C₂, hid, hC₂sup, hC₀sup, hC₁sup, hC₀jet, hC₁jet, hC₂jet⟩ :=
    hL1 T₀ hTsymm hball
  refine ⟨C₂, C₀, hC₂sup, hC₂jet, hC₀sup, hC₀jet, fun q => ?_⟩
  have hsplit :
      (deTurckSmoothRemainder (I := I) g₀ g_bg T₀
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) -
          deTurckSmoothRemainder (I := I) g₀ g_bg
            (0 : SmoothCcTensor g₀ 0 2)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
              (by
                rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                    from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                  tensorHs_norm_smul]
                simpa using hR₀)) -
          deTurckPrincipalCometricArm (I := I) (M := M) g₀
            (tensorSectionRealizeMetric (I := I) g₀ T₀
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
              (hδ_fibre T₀ hball)) T₀ -
          operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
            (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) -
          operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀
            (iteratedCovGrad (I := I) g₀ 0 2 0 T₀)) =
        operatorFieldApply (I := I) (M := M) g₀ (2 + 1) 2 C₁
          (iteratedCovGrad (I := I) g₀ 0 2 1 T₀) := by
    rw [sub_eq_iff_eq_add, sub_eq_iff_eq_add, hid]
    abel
  rw [hsplit]
  exact hM2 1 (by omega) C₁ T₀ hball hC₁sup hC₁jet q

theorem
    exists_smoothCcToTensorHs_deTurckRemainderDiff_sub_principalCometricArm_smallThirdArm_tame_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ εC : ℝ, 0 ≤ εC ∧
      (0 ≤ δ → εC ≤ 32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * (δ / (1 - δ))) ∧
      (0 ≤ δ → εC ≤ 28 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ∧
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
    ∃ εa : ℝ, 0 ≤ εa ∧
      2 * Real.sqrt (Module.finrank ℝ E) * εa ≤
        32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 ∧
    ∃ Λa : ℝ, 0 ≤ Λa ∧
    ∃ Ctame : ℕ → ℝ, (∀ k, 0 ≤ Ctame k) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2)
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w
            v)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∃ (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (C₀ : SmoothCcTensor g₀ (2 + 0) 2),
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂.toSection x) ≤ εC ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤
              Λa ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
                εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) ∧
          ∀ k : ℕ,
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
                (deTurckSmoothRemainder (I := I) g₀ g_bg T₀
                    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) -
                  deTurckSmoothRemainder (I := I) g₀ g_bg
                    (0 : SmoothCcTensor g₀ 0 2)
                    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                    (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                      (by
                        rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                            from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                          tensorHs_norm_smul]
                        simpa using hR₀)) -
                  deTurckPrincipalCometricArm (I := I) (M := M) g₀
                    (tensorSectionRealizeMetric (I := I) g₀ T₀
                      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                      (hδ_fibre T₀ hball)) T₀ -
                  operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) -
                  operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀
                    (iteratedCovGrad (I := I) g₀ 0 2 0 T₀))‖ ≤
              Ctame k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖ := by
  classical
  obtain ⟨εC, hεC_nn, hεC_cap, hεC_cap', Kc, hKc_nn, εa, hεa_nn, hεa_cap, Λa, hΛa_nn,
    Clow, hClow_nn, hjet⟩ :=
    exists_deTurckSmoothRemainderDiff_sub_principalCometricArm_smallThirdArm_iteratedCovGrad_jet_le
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨Ctame, hCtame_nn, hCtame⟩ :=
    exists_smoothCcToTensorHs_real_le_of_iteratedCovGrad_jet_window
      (I := I) (M := M) g₀ a (by omega) Clow hClow_nn
  refine ⟨εC, hεC_nn, hεC_cap, hεC_cap', Kc, hKc_nn, εa, hεa_nn, hεa_cap, Λa, hΛa_nn,
    Ctame, hCtame_nn, fun T₀ hTsymm hball => ?_⟩
  obtain ⟨C₂, C₀, hC₂sup, hC₂jet, hC₀sup, hC₀jet, hwin⟩ := hjet T₀ hTsymm hball
  exact ⟨C₂, C₀, hC₂sup, hC₂jet, hC₀sup, hC₀jet, fun k => hCtame k _ T₀ hwin⟩

theorem exists_smoothCcToTensorHs_coeffAction_fibreSmallCoeff_opNorm_le_zero
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (_ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (_hR₀ : 0 ≤ R₀)
    (εC : ℝ) (hεC_nn : 0 ≤ εC) (Kc : ℕ → ℝ) (_hKc_nn : ∀ i, 0 ≤ Kc i) :
    ∃ Cop : ℝ, 0 ≤ Cop ∧
      ∀ (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂.toSection x) ≤ εC ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
            (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
              (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))‖ ≤
          deTurckArmFibreConst (Module.finrank ℝ E) * εC *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ +
            Cop * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := by
  classical
  obtain ⟨Ccross, hCcross_nn, hcross⟩ := exists_Ccross_for_secondCovGrad (I := I) (M := M) g₀
  obtain ⟨C21, hC21_nn, hC21⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ 1
  refine ⟨εC * Real.sqrt Ccross * (2 * C21),
    mul_nonneg (mul_nonneg hεC_nn (Real.sqrt_nonneg _)) (by linarith), ?_⟩
  intro C₂ T₀ hball hsup hjets
  set W₂ : SmoothCcTensor g₀ 0 (2 + 2) := iteratedCovGrad (I := I) g₀ 0 2 2 T₀ with hW₂_def
  set P : SmoothCcTensor g₀ 0 2 :=
    operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂ W₂ with hP_def
  have hLHS_eq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ) P‖ = ‖P‖ := by
    rw [smoothCcToTensorHs_zero_norm_eq (I := I) (M := M) g₀ P, SmoothCcTensor.norm_toL2]
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤
        εC ^ 2 * ∑ i ∈ Finset.range 1,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 2) x (W₂.toSection x) := by
    intro x
    have hgrid := riemannianFiberNormSq_iteratedCovGrad_comp_diagonalProductGrid_le
      (I := I) (M := M) g₀ (2 + 2) 2 C₂ W₂ 0 x
    rw [show Finset.range (0 + 1) = Finset.range 1 from rfl, Finset.sum_range_one] at hgrid
    rw [show Finset.range (0 + 1 - 0) = Finset.range 1 from rfl,
      Finset.sum_range_one] at hgrid
    rw [show diagonalGridGrowthFactor (E := E) 0 = 1 by simp [diagonalGridGrowthFactor], one_mul]
      at hgrid
    rw [Finset.sum_range_one]
    have hW_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 2) x
        (W₂.toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ _ _ _ _
    refine le_trans hgrid ?_
    exact mul_le_mul_of_nonneg_right (hsup x) hW_nn
  have hprod : ‖P‖ ≤ εC * ‖W₂‖ := by
    have hPTLP := tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g₀
      1 (fun _ => 2 + 2) (fun _ => W₂) P εC hεC_nn hpt
    rw [Finset.sum_range_one] at hPTLP
    exact hPTLP
  clear_value W₂ P
  have hweitz := weitzenbock_integrated_covGrad_l2_normSq (I := I) (M := M) g₀ 2 T₀
  have hcrossT := hcross T₀
  set nHess : ℝ := tensorL2Norm (I := I) (M := M) g₀ 0 (2 + 1 + 1)
    (covGrad (I := I) (M := M) g₀ 0 (2 + 1)
      (covGrad (I := I) (M := M) g₀ 0 2 T₀)).toFun with hnHess_def
  set nGrad : ℝ := tensorL2Norm (I := I) (M := M) g₀ 0 (2 + 1)
    (covGrad (I := I) (M := M) g₀ 0 2 T₀).toFun with hnGrad_def
  set nLap : ℝ := tensorL2Norm (I := I) (M := M) g₀ 0 2
    (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀).toFun with hnLap_def
  set nT : ℝ := tensorL2Norm (I := I) (M := M) g₀ 0 2 T₀.toFun with hnT_def
  have hnHess_nn : 0 ≤ nHess := tensorL2Norm_nonneg (I := I) (M := M) g₀ 0 (2 + 1 + 1) _
  have hnGrad_nn : 0 ≤ nGrad := tensorL2Norm_nonneg (I := I) (M := M) g₀ 0 (2 + 1) _
  have hnLap_nn : 0 ≤ nLap := tensorL2Norm_nonneg (I := I) (M := M) g₀ 0 2 _
  have hnT_nn : 0 ≤ nT := tensorL2Norm_nonneg (I := I) (M := M) g₀ 0 2 _
  clear_value nHess nGrad nLap nT
  have hW₂_norm : ‖W₂‖ = nHess := by
    have hW2eq : W₂ = covGrad (I := I) (M := M) g₀ 0 (2 + 1)
        (covGrad (I := I) (M := M) g₀ 0 2 T₀) := by
      rw [hW₂_def]
      rw [iteratedCovGrad_succ (I := I) (M := M) g₀ 0 2 1 T₀,
        iteratedCovGrad_succ (I := I) (M := M) g₀ 0 2 0 T₀,
        iteratedCovGrad_zero (I := I) (M := M) g₀ 0 2 T₀]
    rw [hW2eq, SmoothCcTensor.norm_def]
    exact hnHess_def.symm
  have hstep1 : nHess ^ 2 ≤ nLap ^ 2 + Ccross * (nGrad ^ 2 + nT * nGrad) := by
    linarith [hweitz, hcrossT]
  have hstep2 : nHess ^ 2 ≤ (nLap + Real.sqrt Ccross * (nGrad + nT)) ^ 2 := by
    have hsq : Real.sqrt Ccross ^ 2 = Ccross := Real.sq_sqrt hCcross_nn
    have hexp : (nLap + Real.sqrt Ccross * (nGrad + nT)) ^ 2 =
        nLap ^ 2 + 2 * nLap * (Real.sqrt Ccross * (nGrad + nT)) +
          Ccross * (nGrad + nT) ^ 2 := by
      rw [show (nLap + Real.sqrt Ccross * (nGrad + nT)) ^ 2 =
        nLap ^ 2 + 2 * nLap * (Real.sqrt Ccross * (nGrad + nT)) +
          Real.sqrt Ccross ^ 2 * (nGrad + nT) ^ 2 by ring, hsq]
    rw [hexp]
    have hc1 : 0 ≤ 2 * nLap * (Real.sqrt Ccross * (nGrad + nT)) := by positivity
    have hc2 : nGrad ^ 2 + nT * nGrad ≤ (nGrad + nT) ^ 2 := by nlinarith
    have hc3 : Ccross * (nGrad ^ 2 + nT * nGrad) ≤ Ccross * (nGrad + nT) ^ 2 :=
      mul_le_mul_of_nonneg_left hc2 hCcross_nn
    linarith [hstep1]
  have hHess_le : nHess ≤ nLap + Real.sqrt Ccross * (nGrad + nT) := by
    have hrhs_nn : 0 ≤ nLap + Real.sqrt Ccross * (nGrad + nT) := by positivity
    calc nHess = Real.sqrt (nHess ^ 2) := (Real.sqrt_sq hnHess_nn).symm
      _ ≤ Real.sqrt ((nLap + Real.sqrt Ccross * (nGrad + nT)) ^ 2) :=
          Real.sqrt_le_sqrt hstep2
      _ = nLap + Real.sqrt Ccross * (nGrad + nT) := Real.sqrt_sq hrhs_nn
  have hLap_le : nLap ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ := by
    have h1 : nLap = ‖rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀‖ := by
      rw [hnLap_def, SmoothCcTensor.norm_def]
    have h2 : ‖rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ := by
      rw [smoothCcToTensorHs_zero_norm_eq, SmoothCcTensor.norm_toL2]
    have h3 := smoothCcToTensorHs_rawTensorConnLapSmooth_le (I := I) (M := M) g₀ (0 : ℝ) T₀
    have h4 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℝ) + 2) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by norm_num) T₀
    rw [h1, h2]
    rw [h4] at h3
    exact h3
  have hjets1 : ∀ j : ℕ, j < 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
        C21 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := by
    intro j hj
    have hsum := hC21 T₀
    have hcast : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by norm_num) T₀
    rw [hcast] at hsum
    refine le_trans ?_ hsum
    exact Finset.single_le_sum
      (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖)
      (fun i _ => norm_nonneg _) (Finset.mem_range.mpr hj)
  have hnT_le : nT ≤ C21 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := by
    have h0 : nT = ‖iteratedCovGrad (I := I) g₀ 0 2 0 T₀‖ := by
      rw [hnT_def, iteratedCovGrad_zero (I := I) (M := M) g₀ 0 2 T₀,
        SmoothCcTensor.norm_def]
    rw [h0]
    exact hjets1 0 (by norm_num)
  have hnGrad_le : nGrad ≤ C21 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := by
    have h1 : iteratedCovGrad (I := I) g₀ 0 2 1 T₀ =
        covGrad (I := I) (M := M) g₀ 0 2 T₀ := by
      rw [iteratedCovGrad_succ (I := I) (M := M) g₀ 0 2 0 T₀,
        iteratedCovGrad_zero (I := I) (M := M) g₀ 0 2 T₀]
    have h0 : nGrad = ‖iteratedCovGrad (I := I) g₀ 0 2 1 T₀‖ := by
      rw [hnGrad_def, h1, SmoothCcTensor.norm_def]
    rw [h0]
    exact hjets1 1 (by norm_num)
  have hfibre1 : (1 : ℝ) ≤ deTurckArmFibreConst (Module.finrank ℝ E) :=
    one_le_deTurckArmFibreConst (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Module.finrank ℝ E)))
  have hHs2_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ := norm_nonneg _
  have hHs1_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := norm_nonneg _
  have hchain : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ) P‖ ≤
      εC * (‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ +
        Real.sqrt Ccross * (2 * C21 *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖)) := by
    rw [hLHS_eq]
    refine le_trans hprod ?_
    rw [hW₂_norm]
    refine le_trans (mul_le_mul_of_nonneg_left hHess_le hεC_nn) ?_
    refine mul_le_mul_of_nonneg_left ?_ hεC_nn
    have hGT : nGrad + nT ≤ 2 * C21 *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := by
      linarith [hnGrad_le, hnT_le]
    have := mul_le_mul_of_nonneg_left hGT (Real.sqrt_nonneg Ccross)
    linarith [hLap_le]
  refine le_trans hchain ?_
  have hexpand : εC * (‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ +
      Real.sqrt Ccross * (2 * C21 *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖)) =
      εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ +
        εC * Real.sqrt Ccross * (2 * C21) *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := by ring
  rw [hexpand]
  have h1 : εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ ≤
      deTurckArmFibreConst (Module.finrank ℝ E) * εC *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ := by
    have h2 : (1 : ℝ) * εC ≤ deTurckArmFibreConst (Module.finrank ℝ E) * εC :=
      mul_le_mul_of_nonneg_right hfibre1 hεC_nn
    have h3 := mul_le_mul_of_nonneg_right h2 hHs2_nn
    calc εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖
        = 1 * εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ := by ring
      _ ≤ deTurckArmFibreConst (Module.finrank ℝ E) * εC *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ := h3
  linarith [h1]

theorem exists_smoothCcToTensorHs_coeffAction_fibreSmallCoeff_opNorm_le_succ
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (εC : ℝ) (hεC_nn : 0 ≤ εC) (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) :
    ∃ Cop : ℕ → ℝ, (∀ m, 0 ≤ Cop m) ∧
      ∀ (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂.toSection x) ≤ εC ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1)
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
                (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))‖ ≤
            deTurckArmFibreConst (Module.finrank ℝ E) * εC *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ +
              Cop m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ := by
  classical
  obtain ⟨Clower, hClower_nn, hfam⟩ :=
    exists_coeffContraction_secondCovGrad_smallFibreCoeff_Hs_family_le (I := I) (M := M) g₀ a
      (by omega) hR₀ εC hεC_nn Kc hKc_nn
  refine ⟨fun m => Clower (m + 1), fun m => hClower_nn (m + 1), ?_⟩
  intro C₂ T₀ hball hsup hjets m
  have hbase := hfam C₂ T₀ hball hsup hjets (m + 1) T₀
    ⟨0, (oneMinusConnLapSmoothIter_zero (I := I) (M := M) (T := T₀)).symm⟩
  have hΔ : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 : ℕ) : ℝ)
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ := by
    have h1 := smoothCcToTensorHs_rawTensorConnLapSmooth_le (I := I) (M := M) g₀
      (((m + 1 : ℕ) : ℝ)) T₀
    have h2 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((m + 1 : ℕ) : ℝ) + 2) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [h2] at h1
    exact h1
  have hcastL : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 : ℕ) : ℝ)
      (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
        (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1)
        (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
          (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) _
  have hcastQ : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 + 1 : ℕ) : ℝ) T₀‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
  rw [hcastL, hcastQ] at hbase
  have hfibre1 : (1 : ℝ) ≤ deTurckArmFibreConst (Module.finrank ℝ E) :=
    one_le_deTurckArmFibreConst (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Module.finrank ℝ E)))
  have hH3_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ :=
    norm_nonneg _
  have htop : εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 : ℕ) : ℝ)
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ≤
      deTurckArmFibreConst (Module.finrank ℝ E) * εC *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ := by
    have hstep1 : εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 : ℕ) : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ≤
        εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ :=
      mul_le_mul_of_nonneg_left hΔ hεC_nn
    have hstep2 : εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ ≤
        deTurckArmFibreConst (Module.finrank ℝ E) * εC *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ := by
      have h2 : (1 : ℝ) * εC ≤ deTurckArmFibreConst (Module.finrank ℝ E) * εC :=
        mul_le_mul_of_nonneg_right hfibre1 hεC_nn
      have h3 := mul_le_mul_of_nonneg_right h2 hH3_nn
      calc εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖
          = 1 * εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ := by ring
        _ ≤ deTurckArmFibreConst (Module.finrank ℝ E) * εC *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ := h3
    exact le_trans hstep1 hstep2
  linarith [hbase, htop]

theorem exists_smoothCcToTensorHs_coeffAction_fibreSmallCoeff_opNorm_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (εC : ℝ) (hεC_nn : 0 ≤ εC) (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) :
    ∃ Cop : ℕ → ℝ, (∀ m, 0 ≤ Cop m) ∧
      ∀ (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂.toSection x) ≤ εC ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
                (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))‖ ≤
            deTurckArmFibreConst (Module.finrank ℝ E) * εC *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ +
              Cop m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ := by
  classical
  obtain ⟨Cop0, hCop0_nn, h0⟩ :=
    exists_smoothCcToTensorHs_coeffAction_fibreSmallCoeff_opNorm_le_zero
      (I := I) (M := M) g₀ a ha_super hR₀ εC hεC_nn Kc hKc_nn
  obtain ⟨Cops, hCops_nn, hs⟩ :=
    exists_smoothCcToTensorHs_coeffAction_fibreSmallCoeff_opNorm_le_succ
      (I := I) (M := M) g₀ a ha_super hR₀ εC hεC_nn Kc hKc_nn
  refine ⟨fun m => match m with
    | 0 => Cop0
    | (k + 1) => Cops k, fun m => ?_, fun C₂ T₀ hball hsup hjets m => ?_⟩
  · match m with
    | 0 => exact hCop0_nn
    | (k + 1) => exact hCops_nn k
  · match m with
    | 0 =>
      have hb := h0 C₂ T₀ hball hsup hjets
      have hnormL := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((0 : ℕ) : ℝ) = (0 : ℝ) by norm_num)
        (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
          (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))
      have hnorm2 := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((0 : ℕ) : ℝ) + 2 = (2 : ℝ) by norm_num) T₀
      have hnorm1 := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((0 : ℕ) : ℝ) + 1 = (1 : ℝ) by norm_num) T₀
      rw [hnormL, hnorm2, hnorm1]
      exact hb
    | (k + 1) =>
      have hb := hs C₂ T₀ hball hsup hjets k
      have hnormL := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring)
        (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
          (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))
      have hnorm2 := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((k + 1 : ℕ) : ℝ) + 2 = (k : ℝ) + 3 by push_cast; ring) T₀
      have hnorm1 := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 by push_cast; ring) T₀
      rw [hnormL, hnorm2, hnorm1]
      exact hb

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    in
private lemma gFibreOpBound_delta_nonneg [Nonempty M] (g₀ : SmoothRiemannianMetric I M)
    {δ : ℝ}
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hfb : metricCauchySchwarzBound (I := I) (M := M) g₀ h δ) : 0 ≤ δ := by
  classical
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  obtain ⟨n, e, hn, horth, hpars, hexpand, hrfns⟩ :=
    tangent_frame_expansion (I := I) (M := M) g₀ x
  have hn_pos : 0 < n := by
    rw [hn]
    have : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
    rw [this]
    exact Nat.pos_of_ne_zero (NeZero.ne _)
  set i0 : Fin n := ⟨0, hn_pos⟩ with hi0_def
  have hb := hfb x (e i0) (e i0)
  have hgi : g₀.inner x (e i0) (e i0) = 1 := by
    rw [horth i0 i0, if_pos rfl]
  rw [hgi, Real.sqrt_one, mul_one, mul_one] at hb
  exact le_trans (abs_nonneg _) hb


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private lemma riemannianFiberNormSq_le_of_ccTensorBilinSymm_gFibreOpBound [Nonempty M]
    (g₀ : SmoothRiemannianMetric I M) {δ : ℝ}
    (T₀ : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w v)
    (hfibre : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T₀.toSection x) ≤
      (Module.finrank ℝ E : ℝ) * δ ^ 2 := by
  classical
  intro x
  have hop : ∀ v w : TangentSpace I x,
      |smoothCcTensorBilinForm (I := I) g₀ T₀ x v w| ≤
        δ * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
    intro v w
    have h := hfibre x v w
    have heq : ccTensorBilinSymm (I := I) g₀ T₀ x v w =
        smoothCcTensorBilinForm (I := I) g₀ T₀ x v w := by
      rw [ccTensorBilinSymm_apply, hTsymm x v w]; ring
    rwa [heq] at h
  obtain ⟨n, e, hn, horth, hpars, hexpand, hrfns⟩ :=
    tangent_frame_expansion (I := I) (M := M) g₀ x
  have hcomp_fiber : ∀ (i j : Fin n),
      smoothCcTensorBilinForm (I := I) g₀ T₀ x (e i) (e j) =
        fiberNormSqComponent (I := I) (M := M) g₀ x 0 2 (T₀.toSection x) n e
          (default : Fin 0 → Fin n) (![i, j] : Fin 2 → Fin n) := by
    intro i j
    have hconst : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k : Fin 0 => g₀.inner x (e ((default : Fin 0 → Fin n) k))) :
          Tensor0SBundle.Tensor0SSpace 0 I x) =
        ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) := by
      apply Tensor0SBundle.tensor0SSpace_ext
      intro u
      change ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k : Fin 0 => g₀.inner x (e ((default : Fin 0 → Fin n) k)))) u =
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) u
      rw [show ((ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) u : ℝ) = 1 from rfl]
      change (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ)
          (fun k => g₀.inner x (e ((default : Fin 0 → Fin n) k)) (u k)) = 1
      rw [ContinuousMultilinearMap.mkPiAlgebra_apply]
      exact Finset.prod_of_isEmpty _
    rw [ccTensorBilin_apply]
    unfold fiberNormSqComponent
    rw [hconst]
    have htuple : (fun k => e ((![i, j] : Fin 2 → Fin n) k)) =
        (![e i, e j] : Fin 2 → TangentSpace I x) := by
      funext k; fin_cases k <;> rfl
    rw [htuple]
    change ccTensorModel (I := I) g₀ T₀ x ![e i, e j] =
      ((T₀.toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
        ![e i, e j] : ℝ)
    unfold ccTensorModel
    rw [ccTensorMultilinear_apply]
    rfl
  have hbridge : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T₀.toSection x) =
      ∑ a : Fin n, ∑ b : Fin n, (smoothCcTensorBilinForm (I := I) g₀ T₀ x (e a) (e b)) ^ 2 := by
    rw [riemannianFiberNormSq_eq_sum_component_sq (I := I) (M := M) g₀ x e hrfns
      (T₀.toSection x) (default : Fin 0 → Fin n)]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [hcomp_fiber a b]
  rw [hbridge]
  have hrow : ∀ a : Fin n,
      ∑ b : Fin n, (smoothCcTensorBilinForm (I := I) g₀ T₀ x (e a) (e b)) ^ 2 ≤ δ ^ 2 := by
    intro a
    set c : Fin n → ℝ := fun b => smoothCcTensorBilinForm (I := I) g₀ T₀ x (e a) (e b) with hc_def
    set S : ℝ := ∑ b : Fin n, (c b) ^ 2 with hS_def
    have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun b _ => sq_nonneg _)
    set u : TangentSpace I x := ∑ b : Fin n, c b • e b with hu_def
    have hval : smoothCcTensorBilinForm (I := I) g₀ T₀ x (e a) u = S := by
      have hexp : smoothCcTensorBilinForm (I := I) g₀ T₀ x (e a) u =
          ∑ b : Fin n, c b * smoothCcTensorBilinForm (I := I) g₀ T₀ x (e a) (e b) := by
        rw [hu_def, map_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [map_smul, smul_eq_mul]
      rw [hexp, hS_def]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      change c b * c b = (c b) ^ 2
      ring
    have hgiu : ∀ i : Fin n, g₀.inner x (e i) u = c i := by
      intro i
      have hexp : g₀.inner x (e i) u =
          ∑ b : Fin n, c b * g₀.inner x (e i) (e b) := by
        rw [hu_def, map_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [map_smul, smul_eq_mul]
      rw [hexp]
      rw [Finset.sum_congr rfl (fun b _ => by rw [horth i b])]
      simp
    have hguu : g₀.inner x u u = S := by
      rw [← hpars u, hS_def]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hgiu i]
    have hgee : g₀.inner x (e a) (e a) = 1 := by rw [horth a a, if_pos rfl]
    have hopau := hop (e a) u
    rw [hgee, Real.sqrt_one, mul_one, hguu, hval] at hopau
    have hSle : S ≤ δ * Real.sqrt S := le_trans (le_abs_self S) hopau
    have hsqrtS : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS_nn
    nlinarith [hSle, hsqrtS, sq_nonneg (Real.sqrt S - δ), Real.sqrt_nonneg S]
  calc ∑ a : Fin n, ∑ b : Fin n, (smoothCcTensorBilinForm (I := I) g₀ T₀ x (e a) (e b)) ^ 2
      ≤ ∑ _a : Fin n, δ ^ 2 := Finset.sum_le_sum (fun a _ => hrow a)
    _ = (n : ℝ) * δ ^ 2 := by rw
                                [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (Module.finrank ℝ E : ℝ) * δ ^ 2 := by
        rw [show n = Module.finrank ℝ E from hn]

private lemma coeffAction_arm0_oneMinusConnLapIter_l2_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i)
    (εa : ℝ) (hεa_nn : 0 ≤ εa) (Λa : ℝ) (_hΛa_nn : 0 ≤ Λa) :
    ∃ Kop : ℕ → ℝ, (∀ p, 0 ≤ Kop p) ∧
      ∀ (C₀ : SmoothCcTensor g₀ (2 + 0) 2) (T₀ : SmoothCcTensor g₀ 0 2) (B : ℝ),
        0 ≤ B →
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T₀.toSection x) ≤ B ^ 2) →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤ Λa ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ p : ℕ,
          ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 T₀))‖ ≤
            B * εa *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 2) T₀‖ +
              Kop p *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 1) T₀‖ ∧
          ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 T₀))‖ ^ 2 +
            ‖covGrad (I := I) (M := M) g₀ 0 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p
                (operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀
                  (iteratedCovGrad (I := I) g₀ 0 2 0 T₀)))‖ ^ 2 ≤
            (B * εa *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 3) T₀‖ +
              Kop p *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 2) T₀‖) ^ 2 := by
  classical
  obtain ⟨KTe, hKTe_nn, hKTe⟩ := exists_connLapIterate_appCc_sobolevHs_bound (I := I) (M := M) g₀ a
    ha_super hR₀
    Kc hKc_nn εa hεa_nn
  obtain ⟨KTo, hKTo_nn, hKTo⟩ := exists_connLapIterate_appCc_covGrad_sobolevHs_bound_odd (I := I)
    (M := M) g₀ a ha_super hR₀
    Kc hKc_nn εa hεa_nn
  obtain ⟨KZ, hKZ_nn, hKZ⟩ := exists_deTurckRemainder_connLapIterate_sobolevHs_bound (I := I)
    (M := M) g₀ a ha_super hR₀
    Kc hKc_nn εa hεa_nn
  refine ⟨fun p => KTe p + KTo p +
      2 * ∑ q ∈ Finset.range p, KZ q (p - 1 - q),
    fun p => by
      have h1 : (0:ℝ) ≤ ∑ q ∈ Finset.range p, KZ q (p - 1 - q) :=
        Finset.sum_nonneg (fun q _ => hKZ_nn q (p - 1 - q))
      have := hKTe_nn p
      have := hKTo_nn p
      linarith, ?_⟩
  intro C₀ T₀ B hB hball hdata _hsup henv p
  set fT : ℕ → ℝ := fun k => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) T₀‖
    with hfT_def
  have hfT_nn : ∀ k, 0 ≤ fT k := fun k => norm_nonneg _
  have hfT_mono : ∀ {k k' : ℕ}, k ≤ k' → fT k ≤ fT k' := fun {k k'} h =>
    smoothCcToTensorHs_norm_mono_of_le (I := I) (M := M) g₀ T₀ h
  have hKZsum_nn : (0:ℝ) ≤ ∑ q ∈ Finset.range p, KZ q (p - 1 - q) :=
    Finset.sum_nonneg (fun q _ => hKZ_nn q (p - 1 - q))
  have htransport := bal_transport (I := I) (M := M) g₀ C₀ T₀ p
  have hA_eq : oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p
      (operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀
        (iteratedCovGrad (I := I) g₀ 0 2 0 T₀)) =
      operatorFieldApply (I := I) (M := M) g₀ 2 2 (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p C₀)
        T₀ +
        ∑ q ∈ Finset.range p, oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p - 1 - q)
          (-(operatorFieldApply (I := I) (M := M) g₀ 2 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))
            - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
              (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                    (covGrad (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀))
            - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
              (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                    (slotExtend (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀))) := htransport
  have hStop := hKTe C₀ T₀ B hB hball hdata henv p
  have hSodd := hKTo C₀ T₀ B hB hball hdata henv p
  have hZbound : ∀ q ∈ Finset.range p,
      ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p - 1 - q)
          (-(operatorFieldApply (I := I) (M := M) g₀ 2 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))
            - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
              (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                    (covGrad (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀))
            - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
              (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                    (slotExtend (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀)))‖ ≤
        KZ q (p - 1 - q) * fT (2 * p + 1) ∧
      ‖covGrad (I := I) (M := M) g₀ 0 2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p - 1 - q)
          (-(operatorFieldApply (I := I) (M := M) g₀ 2 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))
            - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
              (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                    (covGrad (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀))
            - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
              (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                    (slotExtend (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀))))‖ ≤
        KZ q (p - 1 - q) * fT (2 * p + 2) := by
    intro q hq
    have hqp := Finset.mem_range.mp hq
    have h := hKZ C₀ T₀ hball henv q (p - 1 - q)
    have hidx1 : (2 * (p - 1 - q) + 2 * q + 3 : ℕ) = 2 * p + 1 := by omega
    have hidx2 : (2 * (p - 1 - q) + 2 * q + 4 : ℕ) = 2 * p + 2 := by omega
    rw [hidx1, hidx2] at h
    exact h
  set Zf : ℕ → SmoothCcTensor g₀ 0 2 := fun q =>
    oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p - 1 - q)
      (-(operatorFieldApply (I := I) (M := M) g₀ 2 2
        (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))
        - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
          (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
            (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
              (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                (covGrad (I := I) (M := M) g₀ 2 2
                  (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
              (covGrad (I := I) (M := M) g₀ 0 2 T₀))
        - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
          (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
            (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
              (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                (slotExtend (I := I) (M := M) g₀ 2 2
                  (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
              (covGrad (I := I) (M := M) g₀ 0 2 T₀)))
    with hZf_def
  constructor
  · have hgc2 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 2) T₀‖ =
        fT (2 * p + 2) :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    have hgc1 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 1) T₀‖ =
        fT (2 * p + 1) :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [hgc2, hgc1, hA_eq]
    refine le_trans (norm_add_le _ _) ?_
    have hsum : ‖∑ q ∈ Finset.range p, Zf q‖ ≤ ∑ q ∈ Finset.range p, ‖Zf q‖ :=
      norm_sum_le (Finset.range p) Zf
    have hsum2 : ∑ q ∈ Finset.range p, ‖Zf q‖ ≤
        (∑ q ∈ Finset.range p, KZ q (p - 1 - q)) * fT (2 * p + 1) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun q hq => (hZbound q hq).1)
    have htopfe : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 2 : ℕ) : ℝ) T₀‖ =
        fT (2 * p + 2) := rfl
    have htopfo : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 1 : ℕ) : ℝ) T₀‖ =
        fT (2 * p + 1) := rfl
    rw [htopfe, htopfo] at hStop
    have hKTo_extra : (0:ℝ) ≤ KTo p * fT (2 * p + 1) :=
      mul_nonneg (hKTo_nn p) (hfT_nn _)
    have hKZ_extra : (0:ℝ) ≤ (∑ q ∈ Finset.range p, KZ q (p - 1 - q)) * fT (2 * p + 1) :=
      mul_nonneg hKZsum_nn (hfT_nn _)
    nlinarith [hStop, le_trans hsum hsum2]
  · have hgc3 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 3) T₀‖ =
        fT (2 * p + 3) :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    have hgc2 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 2) T₀‖ =
        fT (2 * p + 2) :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [hgc3, hgc2, hA_eq]
    set Xp : SmoothCcTensor g₀ 0 2 := operatorFieldApply (I := I) (M := M) g₀ 2 2
      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p C₀) T₀ with hXp_def
    set S : SmoothCcTensor g₀ 0 2 := ∑ q ∈ Finset.range p, Zf q with hS_def
    have hcovsplit : covGrad (I := I) (M := M) g₀ 0 2 (Xp + S) =
        covGrad (I := I) (M := M) g₀ 0 2 Xp + covGrad (I := I) (M := M) g₀ 0 2 S :=
      covGrad_add (I := I) (M := M) g₀ 0 2 Xp S
    have hnorm1 : ‖Xp + S‖ ≤ ‖Xp‖ + ‖S‖ := norm_add_le _ _
    have hnorm2 : ‖covGrad (I := I) (M := M) g₀ 0 2 (Xp + S)‖ ≤
        ‖covGrad (I := I) (M := M) g₀ 0 2 Xp‖ + ‖covGrad (I := I) (M := M) g₀ 0 2 S‖ := by
      rw [hcovsplit]
      exact norm_add_le _ _
    have hmono := bal_sqrt_mono_pair (norm_nonneg (Xp + S))
      (norm_nonneg (covGrad (I := I) (M := M) g₀ 0 2 (Xp + S))) hnorm1 hnorm2
    have htwo := bal_sqrt_pair_two ‖Xp‖ ‖S‖ ‖covGrad (I := I) (M := M) g₀ 0 2 Xp‖
      ‖covGrad (I := I) (M := M) g₀ 0 2 S‖ (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) (norm_nonneg _)
    have hSpair : Real.sqrt (‖S‖ ^ 2 + ‖covGrad (I := I) (M := M) g₀ 0 2 S‖ ^ 2) ≤
        ‖S‖ + ‖covGrad (I := I) (M := M) g₀ 0 2 S‖ := by
      have h := bal_sqrt_pair_two ‖S‖ 0 0 ‖covGrad (I := I) (M := M) g₀ 0 2 S‖
        (norm_nonneg _) (le_refl 0) (le_refl 0) (norm_nonneg _)
      simpa using h
    have hSnorm : ‖S‖ ≤ (∑ q ∈ Finset.range p, KZ q (p - 1 - q)) * fT (2 * p + 2) := by
      rw [hS_def]
      refine le_trans (norm_sum_le _ _) ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun q hq => ?_)
      refine le_trans (hZbound q hq).1 ?_
      exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hKZ_nn q (p - 1 - q))
    have hGSnorm : ‖covGrad (I := I) (M := M) g₀ 0 2 S‖ ≤
        (∑ q ∈ Finset.range p, KZ q (p - 1 - q)) * fT (2 * p + 2) := by
      rw [hS_def]
      have hmapc : covGrad (I := I) (M := M) g₀ 0 2 (∑ q ∈ Finset.range p, Zf q) =
          ∑ q ∈ Finset.range p, covGrad (I := I) (M := M) g₀ 0 2 (Zf q) :=
        map_sum (AddMonoidHom.mk' (covGrad (I := I) (M := M) g₀ 0 2)
          (covGrad_add (I := I) (M := M) g₀ 0 2)) Zf (Finset.range p)
      rw [hmapc]
      refine le_trans (norm_sum_le _ _) ?_
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun q hq => (hZbound q hq).2)
    have htopfo : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 3 : ℕ) : ℝ) T₀‖ =
        fT (2 * p + 3) := rfl
    have htopfe : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 2 : ℕ) : ℝ) T₀‖ =
        fT (2 * p + 2) := rfl
    rw [htopfo, htopfe] at hSodd
    have hchain : Real.sqrt (‖Xp + S‖ ^ 2 +
        ‖covGrad (I := I) (M := M) g₀ 0 2 (Xp + S)‖ ^ 2) ≤
        B * εa * fT (2 * p + 3) +
          (KTe p + KTo p + 2 * ∑ q ∈ Finset.range p, KZ q (p - 1 - q)) *
            fT (2 * p + 2) := by
      refine le_trans hmono (le_trans htwo ?_)
      have hKTe_extra : (0:ℝ) ≤ KTe p * fT (2 * p + 2) :=
        mul_nonneg (hKTe_nn p) (hfT_nn _)
      have h1 := le_trans hSpair (add_le_add hSnorm hGSnorm)
      linear_combination hSodd + h1 + hKTe_extra
    have hLHS_nn : 0 ≤ ‖Xp + S‖ ^ 2 +
        ‖covGrad (I := I) (M := M) g₀ 0 2 (Xp + S)‖ ^ 2 := by positivity
    have hRHS_nn : 0 ≤ B * εa * fT (2 * p + 3) +
        (KTe p + KTo p + 2 * ∑ q ∈ Finset.range p, KZ q (p - 1 - q)) * fT (2 * p + 2) := by
      have h1 : (0:ℝ) ≤ B * εa * fT (2 * p + 3) :=
        mul_nonneg (mul_nonneg hB hεa_nn) (hfT_nn _)
      have h2 : (0:ℝ) ≤ (KTe p + KTo p +
          2 * ∑ q ∈ Finset.range p, KZ q (p - 1 - q)) * fT (2 * p + 2) := by
        have := hKTe_nn p
        have := hKTo_nn p
        exact mul_nonneg (by linarith) (hfT_nn _)
      exact add_nonneg h1 h2
    have hsq : ‖Xp + S‖ ^ 2 + ‖covGrad (I := I) (M := M) g₀ 0 2 (Xp + S)‖ ^ 2 =
        Real.sqrt (‖Xp + S‖ ^ 2 +
          ‖covGrad (I := I) (M := M) g₀ 0 2 (Xp + S)‖ ^ 2) ^ 2 :=
      (Real.sq_sqrt hLHS_nn).symm
    rw [hsq]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hchain 2

private lemma exists_smoothCcToTensorHs_coeffAction_arm0_opNorm_le_of_dataBound
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i)
    (εa : ℝ) (hεa_nn : 0 ≤ εa) (Λa : ℝ) (hΛa_nn : 0 ≤ Λa) :
    ∃ Cop : ℕ → ℝ, (∀ m, 0 ≤ Cop m) ∧
      ∀ (C₀ : SmoothCcTensor g₀ (2 + 0) 2) (T₀ : SmoothCcTensor g₀ 0 2) (B : ℝ),
        0 ≤ B →
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T₀.toSection x) ≤ B ^ 2) →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤ Λa ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 T₀))‖ ≤
            B * εa *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ +
              Cop m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ := by
  classical
  obtain ⟨Kop, hKop_nn, hKop⟩ :=
    coeffAction_arm0_oneMinusConnLapIter_l2_le (I := I) (M := M) g₀ a ha_super hR₀
      Kc hKc_nn εa hεa_nn Λa hΛa_nn
  refine ⟨fun m => Kop (m / 2), fun m => hKop_nn (m / 2),
    fun C₀ T₀ B hB_nn hball hdata hsup henv m => ?_⟩
  have hlad := hKop C₀ T₀ B hB_nn hball hdata hsup henv
  rcases Nat.even_or_odd m with ⟨p, hp⟩ | ⟨p, hp⟩
  · have hm2 : m = 2 * p := by omega
    subst hm2
    have hidx : 2 * p / 2 = p := by omega
    simp only [hidx]
    have heven := smoothCcToTensorHs_even_norm_eq_toL2_iter (I := I) (M := M) g₀ p
      (operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 T₀))
    rw [SmoothCcTensor.norm_toL2] at heven
    rw [heven]
    exact (hlad p).1
  · subst hp
    have hidx : (2 * p + 1) / 2 = p := by omega
    simp only [hidx]
    set Y : SmoothCcTensor g₀ 0 2 :=
      operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀
        (iteratedCovGrad (I := I) g₀ 0 2 0 T₀) with hY_def
    have hodd := smoothCcToTensorHs_odd_norm_sq_eq_toL2_iter_add_covGrad
      (I := I) (M := M) g₀ p Y
    rw [SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_toL2] at hodd
    have h2 := (hlad p).2
    have hc2 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p + 1 : ℕ) : ℝ) + 2) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 3) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    have hc1 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p + 1 : ℕ) : ℝ) + 1) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 2) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [hc2, hc1]
    set R : ℝ := B * εa *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 3) T₀‖ +
      Kop p * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 2) T₀‖
      with hR_def
    have hR_nn : 0 ≤ R := by
      rw [hR_def]
      exact add_nonneg (mul_nonneg (mul_nonneg hB_nn hεa_nn) (norm_nonneg _))
        (mul_nonneg (hKop_nn p) (norm_nonneg _))
    have hsq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 1 : ℕ) : ℝ) Y‖ ^ 2 ≤
        R ^ 2 := by
      rw [hodd]
      exact h2
    calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 1 : ℕ) : ℝ) Y‖
        = Real.sqrt (‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 1 : ℕ) : ℝ) Y‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt hsq
      _ = R := Real.sqrt_sq hR_nn

private lemma exists_smoothCcToTensorHs_coeffAction_arm0_opNorm_le_of_gFibreOpBound
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i)
    (εa : ℝ) (hεa_nn : 0 ≤ εa) (Λa : ℝ) (hΛa_nn : 0 ≤ Λa) :
    ∃ Cop : ℕ → ℝ, (∀ m, 0 ≤ Cop m) ∧
      ∀ (C₀ : SmoothCcTensor g₀ (2 + 0) 2) (T₀ : SmoothCcTensor g₀ 0 2) (δ : ℝ),
        0 ≤ δ →
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w
            v) →
        metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤ Λa ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 T₀))‖ ≤
            Real.sqrt (Module.finrank ℝ E) * εa * δ *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ +
              Cop m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ := by
  classical
  obtain ⟨Cop, hCop_nn, hcore⟩ :=
    exists_smoothCcToTensorHs_coeffAction_arm0_opNorm_le_of_dataBound (I := I) (M := M) g₀ a
      ha_super hR₀ Kc hKc_nn
      εa hεa_nn Λa hΛa_nn
  refine ⟨Cop, hCop_nn, fun C₀ T₀ δ hδ_nn hball hTsymm hfibre hsup hjet m => ?_⟩
  rcases isEmpty_or_nonempty M with hM | hM
  · have hzero : ∀ (τ : ℝ) (X : SmoothCcTensor g₀ 0 2),
        smoothCcToTensorHs (I := I) (M := M) g₀ τ X = 0 := by
      intro τ X
      have hL2norm : ‖SmoothCcTensor.toL2 X‖ = 0 := by
        rw [SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_def,
          DifferentialGeometry.Integral.L2.tensorL2Norm,
          DifferentialGeometry.Integral.L2.tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      have hL2 : SmoothCcTensor.toL2 X = 0 := norm_eq_zero.mp hL2norm
      refine tensorHs.ext (funext fun i => ?_)
      rw [smoothCcToTensorHs_coeff, tensorHs.zero_coeff,
        hL2, tensorL2Coeff_eq_inner, inner_zero_right]
    rw [hzero, hzero, hzero]
    simp
  · haveI := hM
    have hB_nn : 0 ≤ Real.sqrt (Module.finrank ℝ E) * δ :=
      mul_nonneg (Real.sqrt_nonneg _) hδ_nn
    have hdata : ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T₀.toSection x) ≤
          (Real.sqrt (Module.finrank ℝ E) * δ) ^ 2 := by
      intro x
      have h := riemannianFiberNormSq_le_of_ccTensorBilinSymm_gFibreOpBound (I := I) (M := M) g₀ T₀
        hTsymm hfibre x
      have hsq : (Real.sqrt (Module.finrank ℝ E) * δ) ^ 2 =
          (Module.finrank ℝ E : ℝ) * δ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      rw [hsq]; exact h
    have hmain := hcore C₀ T₀ (Real.sqrt (Module.finrank ℝ E) * δ) hB_nn hball hdata hsup hjet m
    have htop : Real.sqrt (Module.finrank ℝ E) * δ * εa =
        Real.sqrt (Module.finrank ℝ E) * εa * δ := by ring
    rw [htop] at hmain
    exact hmain

private theorem exists_smoothCcToTensorHs_coeffAction_arm0_opNorm_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i)
    (εa : ℝ) (hεa_nn : 0 ≤ εa) (Λa : ℝ) (hΛa_nn : 0 ≤ Λa) :
    ∃ εB : ℝ, 0 ≤ εB ∧
      (0 ≤ δ → εB ≤ 2 * Real.sqrt (Module.finrank ℝ E) * εa * δ) ∧
    ∃ Cop : ℕ → ℝ, (∀ m, 0 ≤ Cop m) ∧
      ∀ (C₀ : SmoothCcTensor g₀ (2 + 0) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w
            v) →
        metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤
            Λa ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 T₀))‖ ≤
            εB * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ +
              Cop m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ := by
  classical
  obtain ⟨Cop, hCop_nn, hcore⟩ :=
    exists_smoothCcToTensorHs_coeffAction_arm0_opNorm_le_of_gFibreOpBound (I := I) (M := M) g₀ a
      ha_super hR₀
      Kc hKc_nn εa hεa_nn Λa hΛa_nn
  refine ⟨Real.sqrt (Module.finrank ℝ E) * εa * max δ 0,
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hεa_nn) (le_max_right _ _),
    fun hδ_nn => ?_, Cop, hCop_nn, fun C₀ T₀ hball hTsymm hfibre hsup hjet m => ?_⟩
  · rw [max_eq_left hδ_nn]
    have hnn : 0 ≤ Real.sqrt (Module.finrank ℝ E) * εa * δ :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hεa_nn) hδ_nn
    nlinarith [hnn]
  · rcases isEmpty_or_nonempty M with hM | hM
    · have hzero : ∀ (τ : ℝ) (X : SmoothCcTensor g₀ 0 2),
          smoothCcToTensorHs (I := I) (M := M) g₀ τ X = 0 := by
        intro τ X
        have hL2norm : ‖SmoothCcTensor.toL2 X‖ = 0 := by
          rw [SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_def,
            DifferentialGeometry.Integral.L2.tensorL2Norm,
            DifferentialGeometry.Integral.L2.tensorL2Inner,
            MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
        have hL2 : SmoothCcTensor.toL2 X = 0 := norm_eq_zero.mp hL2norm
        refine tensorHs.ext (funext fun i => ?_)
        rw [smoothCcToTensorHs_coeff, tensorHs.zero_coeff,
          hL2, tensorL2Coeff_eq_inner, inner_zero_right]
      rw [hzero, hzero, hzero]
      simp
    · haveI := hM
      have hδ_nn : 0 ≤ δ :=
        gFibreOpBound_delta_nonneg (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T₀) hfibre
      rw [max_eq_left hδ_nn]
      exact hcore C₀ T₀ δ hδ_nn hball hTsymm hfibre hsup hjet m

theorem exists_deTurckSmoothRemainderDiff_eq_principalCometricArm_add_smallThirdArm_add_tame
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ εwrap : ℝ, 0 ≤ εwrap ∧
      (0 ≤ δ → εwrap ≤ 32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 * (δ / (1 - δ))) ∧
    ∃ Cthird Ctame : ℕ → ℝ, (∀ k, 0 ≤ Cthird k) ∧ (∀ k, 0 ≤ Ctame k) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2)
        (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w
            v)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∃ third tame : SmoothCcTensor g₀ 0 2,
          deTurckSmoothRemainder (I := I) g₀ g_bg T₀
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) -
            deTurckSmoothRemainder (I := I) g₀ g_bg
              (0 : SmoothCcTensor g₀ 0 2)
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
              (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                (by
                  rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                      from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                    tensorHs_norm_smul]
                  simpa using hR₀)) =
            deTurckPrincipalCometricArm (I := I) (M := M) g₀
              (tensorSectionRealizeMetric (I := I) g₀ T₀
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)) T₀
              + third + tame ∧
          (∀ k : ℕ,
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) third‖ ≤
              εwrap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) + 1) T₀‖ +
                Cthird k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖) ∧
          (∀ k : ℕ,
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) tame‖ ≤
              Ctame k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖) := by
  classical
  obtain ⟨εC, hεC_nn, hεC_cap, hεC_cap', Kc, hKc_nn, εa, hεa_nn, hεa_cap, Λa, hΛa_nn,
    Ctame, hCtame_nn, htame⟩ :=
    exists_smoothCcToTensorHs_deTurckRemainderDiff_sub_principalCometricArm_smallThirdArm_tame_le
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨Cop, hCop_nn, hH3⟩ :=
    exists_smoothCcToTensorHs_coeffAction_fibreSmallCoeff_opNorm_le
      (I := I) (M := M) g₀ a ha_super hR₀ εC hεC_nn Kc hKc_nn
  obtain ⟨εB, hεB_nn, hεB_cap, CopB, hCopB_nn, hB'⟩ :=
    exists_smoothCcToTensorHs_coeffAction_arm0_opNorm_le
      (I := I) (M := M) g₀ a ha_super hR₀ (δ := δ) Kc hKc_nn εa hεa_nn Λa hΛa_nn
  refine ⟨deTurckArmFibreConst (Module.finrank ℝ E) * εC + εB,
    add_nonneg (mul_nonneg (deTurckArmFibreConst_nonneg _) hεC_nn) hεB_nn,
    fun hδ_nn => ?_,
    fun k => Cop (a + k - 1) + CopB (a + k - 1), Ctame,
    fun k => add_nonneg (hCop_nn _) (hCopB_nn _), hCtame_nn, fun T₀ hTsymm hball => ?_⟩
  · have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
    have hκ_nn : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn (by linarith)
    have hδκ : δ ≤ δ / (1 - δ) := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 - δ)]
      nlinarith [sq_nonneg δ]
    have hf_nn : 0 ≤ deTurckArmFibreConst (Module.finrank ℝ E) :=
      deTurckArmFibreConst_nonneg _
    have h1 : deTurckArmFibreConst (Module.finrank ℝ E) * εC ≤
        28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * (δ / (1 - δ)) := by
      calc deTurckArmFibreConst (Module.finrank ℝ E) * εC
          ≤ deTurckArmFibreConst (Module.finrank ℝ E) *
              (28 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) :=
            mul_le_mul_of_nonneg_left (hεC_cap' hδ_nn) hf_nn
        _ = 28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * (δ / (1 - δ)) := by ring
    have h2sq_nn : (0 : ℝ) ≤ 2 * Real.sqrt (Module.finrank ℝ E) * εa :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hεa_nn
    have h2 : εB ≤ (32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
        28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2) * (δ / (1 - δ)) := by
      refine le_trans (hεB_cap hδ_nn) ?_
      calc 2 * Real.sqrt (Module.finrank ℝ E) * εa * δ
          ≤ 2 * Real.sqrt (Module.finrank ℝ E) * εa * (δ / (1 - δ)) :=
            mul_le_mul_of_nonneg_left hδκ h2sq_nn
        _ ≤ (32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
              28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2) * (δ / (1 - δ)) :=
            mul_le_mul_of_nonneg_right hεa_cap hκ_nn
    calc deTurckArmFibreConst (Module.finrank ℝ E) * εC + εB
        ≤ 28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * (δ / (1 - δ)) +
            (32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
              28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2) * (δ / (1 - δ)) :=
          add_le_add h1 h2
      _ = 32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 * (δ / (1 - δ)) := by ring
  obtain ⟨C₂, C₀, hC₂sup, hC₂jet, hC₀sup, hC₀jet, hHsbound⟩ := htame T₀ hTsymm hball
  refine ⟨operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
    (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) +
      operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 T₀),
    deTurckSmoothRemainder (I := I) g₀ g_bg T₀
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) -
      deTurckSmoothRemainder (I := I) g₀ g_bg
        (0 : SmoothCcTensor g₀ 0 2)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
          (by
            rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
              tensorHs_norm_smul]
            simpa using hR₀)) -
      deTurckPrincipalCometricArm (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)) T₀ -
      operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) -
      operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 T₀),
    by abel, fun k => ?_, hHsbound⟩
  · have hm1 : (a : ℝ) + (k : ℝ) - 1 = ((a + k - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (show 1 ≤ a + k by omega)]; push_cast; ring
    have hm2 : (a : ℝ) + (k : ℝ) + 1 = ((a + k - 1 : ℕ) : ℝ) + 2 := by
      rw [← hm1]; ring
    have hm3 : (a : ℝ) + (k : ℝ) = ((a + k - 1 : ℕ) : ℝ) + 1 := by
      rw [← hm1]; ring
    rw [hm1, hm2, hm3, smoothCcToTensorHs_add]
    refine le_trans (norm_add_le _ _) ?_
    have hA := hH3 C₂ T₀ hball hC₂sup hC₂jet (a + k - 1)
    have hB2 := hB' C₀ T₀ hball hTsymm (hδ_fibre T₀ hball) hC₀sup hC₀jet (a + k - 1)
    linarith [hA, hB2]

end Spectral
end Analysis
end DifferentialGeometry

end
