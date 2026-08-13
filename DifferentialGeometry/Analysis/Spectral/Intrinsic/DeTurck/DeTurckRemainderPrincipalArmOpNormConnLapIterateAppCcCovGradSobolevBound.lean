import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNormConnLapIterateAppCcCovGradSobolevHighOrderBound
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

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma iteratedCovGrad_le_sq_envelope_product (g₀ : SmoothRiemannianMetric I M)
    (Kc CJ : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (εa : ℝ) (hεa_nn : 0 ≤ εa)
    (C₀ : SmoothCcTensor g₀ 2 2) (T₀ : SmoothCcTensor g₀ 0 2)
    (henv : ∀ i : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2 ≤
        Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
          εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2)
    (f : ℝ) (hf_nn : 0 ≤ f) (hCJ_nn : ∀ j, 0 ≤ CJ j) (b : ℕ)
    (hsum : ∑ j ∈ Finset.range (b + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
      (∑ j ∈ Finset.range (b + 2), CJ j) * f)
    (hend : ‖iteratedCovGrad (I := I) g₀ 0 2 (b + 2) T₀‖ ≤ CJ (b + 2) * f) :
    ‖iteratedCovGrad (I := I) g₀ 2 2 b C₀‖ ≤
      (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) +
        εa * CJ (b + 2)) * (1 + f) := by
  refine le_trans
    (iteratedCovGrad_le_of_sq_envelope_bound (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn C₀ T₀ henv b)
      ?_
  have hCJsum_nn : 0 ≤ ∑ j ∈ Finset.range (b + 2), CJ j :=
    Finset.sum_nonneg (fun j _ => hCJ_nn j)
  have hsum' : 1 + ∑ j ∈ Finset.range (b + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
      (1 + ∑ j ∈ Finset.range (b + 2), CJ j) * (1 + f) := by
    calc
      1 + ∑ j ∈ Finset.range (b + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
          1 + (∑ j ∈ Finset.range (b + 2), CJ j) * f := add_le_add_right hsum 1
      _ ≤ 1 + (∑ j ∈ Finset.range (b + 2), CJ j) * f +
          ((∑ j ∈ Finset.range (b + 2), CJ j) + f) :=
        le_add_of_nonneg_right (add_nonneg hCJsum_nn hf_nn)
      _ = (1 + ∑ j ∈ Finset.range (b + 2), CJ j) * (1 + f) := by ring
  have htop := mul_le_mul_of_nonneg_left hsum' (Real.sqrt_nonneg (Kc b))
  have hend' := mul_le_mul_of_nonneg_left hend hεa_nn
  have hf_le : f ≤ 1 + f := le_add_of_nonneg_left zero_le_one
  have htail : εa * (CJ (b + 2) * f) ≤ (εa * CJ (b + 2)) * (1 + f) := by
    calc
      εa * (CJ (b + 2) * f) = (εa * CJ (b + 2)) * f := by ring
      _ ≤ (εa * CJ (b + 2)) * (1 + f) :=
        mul_le_mul_of_nonneg_left hf_le (mul_nonneg hεa_nn (hCJ_nn (b + 2)))
  calc
    Real.sqrt (Kc b) *
          (1 + ∑ j ∈ Finset.range (b + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖) +
        εa * ‖iteratedCovGrad (I := I) g₀ 0 2 (b + 2) T₀‖ ≤
        Real.sqrt (Kc b) *
            ((1 + ∑ j ∈ Finset.range (b + 2), CJ j) * (1 + f)) +
          εa * (CJ (b + 2) * f) := add_le_add htop hend'
    _ ≤ Real.sqrt (Kc b) *
            ((1 + ∑ j ∈ Finset.range (b + 2), CJ j) * (1 + f)) +
          (εa * CJ (b + 2)) * (1 + f) := add_le_add_right htail _
    _ = (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) +
          εa * CJ (b + 2)) * (1 + f) := by ring


lemma exists_connLapIterate_appCc_covGrad_sobolevHs_bound_odd (g₀ : SmoothRiemannianMetric I M)
    (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (εa : ℝ) (hεa_nn : 0 ≤ εa) :
    ∃ KT : ℕ → ℝ, (∀ p, 0 ≤ KT p) ∧
      ∀ (C₀ : SmoothCcTensor g₀ 2 2) (T₀ : SmoothCcTensor g₀ 0 2) (B : ℝ), 0 ≤ B →
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T₀.toSection x) ≤ B ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ p : ℕ,
          Real.sqrt (‖operatorFieldApply (I := I) (M := M) g₀ 2 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p C₀) T₀‖ ^ 2 +
            ‖covGrad (I := I) (M := M) g₀ 0 2 (operatorFieldApply (I := I) (M := M) g₀ 2 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p C₀) T₀)‖ ^ 2) ≤
            B * εa * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 3 : ℕ) : ℝ) T₀‖ +
              KT p * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 2 : ℕ) : ℝ) T₀‖ := by
  classical
  obtain ⟨CC, hCC_nn, hCC⟩ := exists_iteratedCovGrad_oneMinusConnLapSmoothIter_le_mul_tensorHs
    (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn
  obtain ⟨CCS, hCCS_nn, hCCS⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_oneMinusConnLapSmoothIter_le_sq_tensorHs (I := I) (M := M)
    g₀ Kc hKc_nn εa hεa_nn
  obtain ⟨CJ, hCJ_nn, hCJ⟩ := exists_iteratedCovGrad_le_const_mul_tensorHs (I := I) (M := M) g₀
  obtain ⟨CDS0, hCDS0_nn, hCDS0⟩ := riemannianFiberNormSq_iteratedCovGrad_le_sq_tensorHs (I := I)
    (M := M) g₀
  obtain ⟨c22, hc22_nn, hc22⟩ := bal_Ccore (I := I) (M := M) g₀ 2 2
  have hgapfam := fun k : ℕ =>
    exists_iteratedCovGrad_l2NormSq_le_smoothCcToTensorHs_succ_add_lower
      (I := I) (M := M) g₀ k
  choose Cq hCq_nn hCq using hgapfam
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  set w : ℕ := n / 2 + 2 with hw_def
  set KE1 : ℕ → ℝ := fun p => (Real.sqrt (Kc (2 * p)) *
      (1 + ∑ j ∈ Finset.range (2 * p + 2), CJ j) + εa * CJ (2 * p + 2)) +
    c22 p * ∑ b ∈ Finset.range (2 * p),
      (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2))
    with hKE1_def
  set KE2 : ℕ → ℝ := fun p => (Real.sqrt (Kc (2 * p + 1)) *
      (1 + ∑ j ∈ Finset.range (2 * p + 3), CJ j) + εa * CJ (2 * p + 3)) +
    c22 p * ∑ b ∈ Finset.range (2 * p + 1),
      (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2))
    with hKE2_def
  have hterm_nn : ∀ b : ℕ, 0 ≤ Real.sqrt (Kc b) *
      (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2) := by
    intro b
    have h1 := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (b + 2)) => hCJ_nn j)
    exact add_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (add_nonneg zero_le_one h1))
      (mul_nonneg hεa_nn (hCJ_nn _))
  have hKE1_nn : ∀ p, 0 ≤ KE1 p := by
    intro p
    rw [hKE1_def]
    have h2 := Finset.sum_nonneg (fun b (_ : b ∈ Finset.range (2 * p)) => hterm_nn b)
    exact add_nonneg (hterm_nn _) (mul_nonneg (hc22_nn p) h2)
  have hKE2_nn : ∀ p, 0 ≤ KE2 p := by
    intro p
    rw [hKE2_def]
    have h2 := Finset.sum_nonneg (fun b (_ : b ∈ Finset.range (2 * p + 1)) => hterm_nn b)
    exact add_nonneg (hterm_nn _) (mul_nonneg (hc22_nn p) h2)
  refine ⟨fun p =>
      (CCS 0 p * CJ 0 + CCS 1 p * CJ 0 + Real.sqrt n * CCS 0 p * CJ 1) * (1 + R₀) +
      (CDS0 0 * R₀ * εa * Real.sqrt (1 + Cq (2 * p + 1) + Cq (2 * p + 2)) +
        CDS0 0 * (1 + R₀) * (KE1 p + KE2 p) +
        Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀)),
    fun p => ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ (CCS 0 p * CJ 0 + CCS 1 p * CJ 0 +
        Real.sqrt n * CCS 0 p * CJ 1) * (1 + R₀) := by
      have ha1 : (0:ℝ) ≤ CCS 0 p * CJ 0 := mul_nonneg (hCCS_nn 0 p) (hCJ_nn 0)
      have ha2 : (0:ℝ) ≤ CCS 1 p * CJ 0 := mul_nonneg (hCCS_nn 1 p) (hCJ_nn 0)
      have ha3 : (0:ℝ) ≤ Real.sqrt n * CCS 0 p * CJ 1 :=
        mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hCCS_nn 0 p)) (hCJ_nn 1)
      exact mul_nonneg (add_nonneg (add_nonneg ha1 ha2) ha3)
        (add_nonneg zero_le_one hR₀)
    have h2 : (0:ℝ) ≤ CDS0 0 * R₀ * εa *
        Real.sqrt (1 + Cq (2 * p + 1) + Cq (2 * p + 2)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (hCDS0_nn 0) hR₀) hεa_nn) (Real.sqrt_nonneg _)
    have h3 : (0:ℝ) ≤ CDS0 0 * (1 + R₀) * (KE1 p + KE2 p) :=
      mul_nonneg (mul_nonneg (hCDS0_nn 0) (add_nonneg zero_le_one hR₀))
        (add_nonneg (hKE1_nn p) (hKE2_nn p))
    have h4 : (0:ℝ) ≤ Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀) :=
      mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hCDS0_nn 1)) (hCC_nn 0 p))
        (add_nonneg zero_le_one hR₀)
    exact add_nonneg h1 (add_nonneg (add_nonneg h2 h3) h4)
  intro C₀ T₀ B hB hball hdata henv p
  by_cases hcase : w + 2 * p + 2 ≤ a + 2
  · exact bal_connLapIterate_appCc_covGrad_sobolevHs_bound_of_low_order
      (I := I) (M := M) (g₀ := g₀) (a := a) (hR₀ := hR₀)
      (Kc := Kc) (εa := εa) (hεa_nn := hεa_nn)
      (CC := CC) (hCC_nn := hCC_nn) (CCS := CCS) (hCCS_nn := hCCS_nn)
      (CJ := CJ) (hCJ_nn := hCJ_nn) (hCJ := hCJ)
      (CDS0 := CDS0) (hCDS0_nn := hCDS0_nn) (Cq := Cq)
      (n := n) (w := w) (hn_def := hn_def) (hCCS := hCCS)
      (KE1 := KE1) (KE2 := KE2) (hKE1_nn := hKE1_nn) (hKE2_nn := hKE2_nn)
      (C₀ := C₀) (T₀ := T₀) (B := B) (hB := hB)
      (hball := hball) (henv := henv) (p := p) (hcase := hcase)
  · exact bal_connLapIterate_appCc_covGrad_sobolevHs_bound_of_high_order
      (I := I) (M := M) (g₀ := g₀) (a := a) (ha_super := ha_super) (hR₀ := hR₀)
      (Kc := Kc) (hKc_nn := hKc_nn) (εa := εa) (hεa_nn := hεa_nn)
      (CC := CC) (hCC_nn := hCC_nn) (hCC := hCC)
      (CCS := CCS) (hCCS_nn := hCCS_nn)
      (CJ := CJ) (hCJ_nn := hCJ_nn) (hCJ := hCJ)
      (CDS0 := CDS0) (hCDS0_nn := hCDS0_nn)
      (n := n) (w := w) (hn_def := hn_def) (hn1 := hn1) (hw_def := hw_def)
      (hCDS0 := hCDS0) (c22 := c22) (hc22_nn := hc22_nn) (hc22 := hc22)
      (Cq := Cq) (hCq := hCq) (hCq_nn := hCq_nn)
      (KE1 := KE1) (KE2 := KE2) (hKE1_def := hKE1_def) (hKE2_def := hKE2_def)
      (hKE1_nn := hKE1_nn) (hKE2_nn := hKE2_nn)
      (C₀ := C₀) (T₀ := T₀) (B := B) (hB := hB)
      (hball := hball) (hdata := hdata) (henv := henv) (p := p) (hcase := hcase)

end BalLadder

end Spectral
end Analysis
end DifferentialGeometry

end
