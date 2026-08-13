import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffL2JetMoser
open DifferentialGeometry.Analysis.Sobolev

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle
    ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (linearizedRicciArm0BaseCoeff linearizedRicciArm1BaseCoeff)
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedFam)

private lemma norm_sq_le_two_sub {X : Type*} [SeminormedAddCommGroup X] (x y : X) :
    ‖x‖ ^ 2 ≤ 2 * ‖x - y‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    have := norm_sub_norm_le x y
    linarith
  nlinarith [h, norm_nonneg x, norm_nonneg (x - y), norm_nonneg y,
    sq_nonneg (‖x - y‖ - ‖y‖)]

private lemma sum_shift_le (g : ℕ → ℝ) (hg : ∀ j, 0 ≤ g j) (m c : ℕ) :
    ∑ i ∈ Finset.range m, g (i + c) ≤ ∑ j ∈ Finset.range (m + c), g j := by
  classical
  have hsub :
      (Finset.range m).map ⟨fun i => i + c, fun a b h => by simpa using h⟩ ⊆
        Finset.range (m + c) := by
    intro j hj
    rw [Finset.mem_map] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    rw [Finset.mem_range] at hi ⊢
    simp only [Function.Embedding.coeFn_mk]
    omega
  calc ∑ i ∈ Finset.range m, g (i + c)
      = ∑ j ∈ (Finset.range m).map ⟨fun i => i + c, fun a b h => by simpa using h⟩, g j := by
        rw [Finset.sum_map]; rfl
    _ ≤ ∑ j ∈ Finset.range (m + c), g j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hg j)

private lemma jetL2_sum_of_perOrder
    (a p : ℕ) (Ktop : ℝ) (hKtop : 0 ≤ Ktop) (Kc : ℕ → ℝ) (hKc : ∀ i, 0 ≤ Kc i)
    (f w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hper : ∀ i, i ≤ a →
        f i ≤ 2 * (Kc i * (1 + ∑ j ∈ Finset.range (i + p), w j)) + 2 * (Ktop * w (i + p))) :
    ∑ i ∈ Finset.range (a + 1), f i ≤
      2 * Ktop * (∑ j ∈ Finset.range (a + 1 + p), w j) +
      2 * (∑ i ∈ Finset.range (a + 1), Kc i) * (1 + ∑ j ∈ Finset.range (a + p), w j) := by
  refine le_trans (Finset.sum_le_sum (fun i hi =>
    hper i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))) ?_
  rw [Finset.sum_add_distrib]
  have hB : (∑ i ∈ Finset.range (a + 1), 2 * (Ktop * w (i + p))) ≤
      2 * Ktop * ∑ j ∈ Finset.range (a + 1 + p), w j := by
    have hrw : (∑ i ∈ Finset.range (a + 1), 2 * (Ktop * w (i + p)))
        = 2 * Ktop * ∑ i ∈ Finset.range (a + 1), w (i + p) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hrw]
    exact mul_le_mul_of_nonneg_left (sum_shift_le w hw (a + 1) p) (by linarith)
  have hA : (∑ i ∈ Finset.range (a + 1), 2 * (Kc i * (1 + ∑ j ∈ Finset.range (i + p), w j))) ≤
      2 * (∑ i ∈ Finset.range (a + 1), Kc i) * (1 + ∑ j ∈ Finset.range (a + p), w j) := by
    have hmono : ∀ i ∈ Finset.range (a + 1),
        2 * (Kc i * (1 + ∑ j ∈ Finset.range (i + p), w j)) ≤
          2 * (Kc i * (1 + ∑ j ∈ Finset.range (a + p), w j)) := by
      intro i hi
      have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hsub : Finset.range (i + p) ⊆ Finset.range (a + p) := by
        intro x hx
        rw [Finset.mem_range] at hx ⊢
        omega
      have hss : ∑ j ∈ Finset.range (i + p), w j ≤ ∑ j ∈ Finset.range (a + p), w j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hw j)
      have hKci := hKc i
      nlinarith [hss, hKci]
    refine le_trans (Finset.sum_le_sum hmono) (le_of_eq ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  linarith [hA, hB]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem linearizedRicciArm0BaseCoeff_realizedFam_jetL2_summed_topSeparated
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℝ, 0 ≤ Kc ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ∑ i ∈ Finset.range (a + 1),
              ‖iteratedCovGrad (I := I) g₀ 2 2 i
                (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤
            Ktop * (∑ j ∈ Finset.range (a + 3),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) +
            Kc * (1 + ∑ j ∈ Finset.range (a + 2),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨Ktop, hKtop_nn, Kc, hKc_nn, hbound⟩ :=
    linearizedRicciArm0BaseCoeff_realizedFam_jetL2_perOrder_topSeparated
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨2 * Ktop, by linarith, 2 * ∑ i ∈ Finset.range (a + 1), Kc i, ?_, ?_⟩
  · have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.range (a + 1)) => hKc_nn i)
    linarith
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs
  have hper : ∀ i, i ≤ a →
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤
        2 * (Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2))) +
        2 * (Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2)) := by
    intro i hi
    obtain ⟨Hd, _hpt, hL2h, hres⟩ :=
      hbound T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
    have hsplit := norm_sq_le_two_sub
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s)) Hd
    linarith [hsplit, hres, hL2h]
  exact jetL2_sum_of_perOrder a 2 Ktop hKtop_nn Kc hKc_nn
    (fun i => ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2)
    (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)
    (fun j => add_nonneg (sq_nonneg _) (sq_nonneg _)) hper

theorem linearizedRicciArm1BaseCoeff_realizedFam_jetL2_summed_topSeparated
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℝ, 0 ≤ Kc ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ∑ i ∈ Finset.range (a + 1),
              ‖iteratedCovGrad (I := I) g₀ 3 2 i
                (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤
            Ktop * (∑ j ∈ Finset.range (a + 2),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) +
            Kc * (1 + ∑ j ∈ Finset.range (a + 1),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨Ktop, hKtop_nn, Kc, hKc_nn, hbound⟩ :=
    linearizedRicciArm1BaseCoeff_realizedFam_jetL2_perOrder_topSeparated
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨2 * Ktop, by linarith, 2 * ∑ i ∈ Finset.range (a + 1), Kc i, ?_, ?_⟩
  · have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.range (a + 1)) => hKc_nn i)
    linarith
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs
  have hper : ∀ i, i ≤ a →
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
          (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤
        2 * (Kc i * (1 + ∑ j ∈ Finset.range (i + 1),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2))) +
        2 * (Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T'‖ ^ 2)) := by
    intro i hi
    obtain ⟨Hd, _hpt, hL2h, hres⟩ :=
      hbound T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
    have hsplit := norm_sq_le_two_sub
      (iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)) Hd
    linarith [hsplit, hres, hL2h]
  exact jetL2_sum_of_perOrder a 1 Ktop hKtop_nn Kc hKc_nn
    (fun i => ‖iteratedCovGrad (I := I) g₀ 3 2 i
      (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2)
    (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)
    (fun j => add_nonneg (sq_nonneg _) (sq_nonneg _)) hper

end DifferentialGeometry.Analysis.Sobolev
