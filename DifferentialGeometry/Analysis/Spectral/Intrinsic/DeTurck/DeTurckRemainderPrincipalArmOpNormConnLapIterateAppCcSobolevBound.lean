import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNormConnLapIterateAppCcSobolevHighOrderBound
open DifferentialGeometry.Analysis.Sobolev
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
  [T2Space M]

section BalLadder

variable (g₀ : SmoothRiemannianMetric I M)


lemma bal_slotExt_norm (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g₀ r s) :
    ‖slotExtend (I := I) (M := M) g₀ r s Φ‖ ≤
      Real.sqrt (Module.finrank ℝ E) * ‖Φ‖ := by
  have hsq := normSq_le_sum_normSq_of_pointwise_fiberNormSq_window (I := I) (M := M) g₀
    (slotExtend (I := I) (M := M) g₀ r s Φ) (Module.finrank ℝ E : ℝ) (Nat.cast_nonneg _)
    (fun _ => s) (fun _ => Φ) 1 (fun x => ?_)
  · rw [Finset.sum_range_one] at hsq
    refine le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    exact hsq
  · rw [Finset.sum_range_one]
    have h := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ r s Φ 0 x
    rw [show iteratedCovGrad (I := I) g₀ (r + 1) (s + 1) 0
        (slotExtend (I := I) (M := M) g₀ r s Φ) =
      slotExtend (I := I) (M := M) g₀ r s Φ from iteratedCovGrad_zero _ _ _ _] at h
    rw [show iteratedCovGrad (I := I) g₀ r s 0 Φ = Φ from iteratedCovGrad_zero _ _ _ _] at h
    exact h

private lemma bal_two_mul_add_one_cast (p : ℕ) :
    (((2 * p + 1 : ℕ) : ℝ) + 1) = ((2 * p + 2 : ℕ) : ℝ) := by
  push_cast
  ring

lemma exists_connLapIterate_appCc_sobolevHs_bound (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
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
          ‖operatorFieldApply (I := I) (M := M) g₀ 2 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p C₀) T₀‖ ≤
            B * εa * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 2 : ℕ) : ℝ) T₀‖ +
              KT p * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 1 : ℕ) : ℝ) T₀‖ := by
  classical
  obtain ⟨CCS, hCCS_nn, hCCS⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_oneMinusConnLapSmoothIter_le_sq_tensorHs (I := I) (M := M)
    g₀ Kc hKc_nn εa hεa_nn
  obtain ⟨CJ, hCJ_nn, hCJ⟩ := exists_iteratedCovGrad_le_const_mul_tensorHs (I := I) (M := M) g₀
  obtain ⟨CDS0, hCDS0_nn, hCDS0⟩ := riemannianFiberNormSq_iteratedCovGrad_le_sq_tensorHs (I := I)
    (M := M) g₀
  obtain ⟨c22, hc22_nn, hc22⟩ := bal_Ccore (I := I) (M := M) g₀ 2 2
  have hgapfam := fun k : ℕ => exists_iteratedCovGrad_succ_le_tensorHs_add_mul_tensorHs (I := I)
                                 (M := M) g₀ k
  choose Cg hCg_nn hCg using hgapfam
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  set w : ℕ := n / 2 + 2 with hw_def
  set KE1 : ℕ → ℝ := fun p => (Real.sqrt (Kc (2 * p)) *
      (1 + ∑ j ∈ Finset.range (2 * p + 2), CJ j) + εa * CJ (2 * p + 2)) +
    c22 p * ∑ b ∈ Finset.range (2 * p),
      (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2))
    with hKE1_def
  have hKE1_nn : ∀ p, 0 ≤ KE1 p := by
    intro p
    have h1 : ∀ b : ℕ, 0 ≤ Real.sqrt (Kc b) *
        (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2) := by
      intro b
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (b + 2)) => hCJ_nn j)
      have := Real.sqrt_nonneg (Kc b)
      have := hCJ_nn (b + 2)
      nlinarith
    rw [hKE1_def]
    have h2 := Finset.sum_nonneg (fun b (_ : b ∈ Finset.range (2 * p)) => h1 b)
    have := h1 (2 * p)
    have := hc22_nn p
    nlinarith
  refine ⟨fun p => CCS 0 p * (1 + R₀) * CJ 0 +
      (CDS0 0 * R₀ * εa * Cg (2 * p + 1) +
        CDS0 0 * (1 + R₀) * KE1 p),
    fun p => ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ CCS 0 p * (1 + R₀) * CJ 0 :=
      mul_nonneg (mul_nonneg (hCCS_nn 0 p) (by linarith)) (hCJ_nn 0)
    have h2 : (0:ℝ) ≤ CDS0 0 * R₀ * εa * Cg (2 * p + 1) :=
      mul_nonneg (mul_nonneg (mul_nonneg (hCDS0_nn 0) hR₀) hεa_nn) (hCg_nn _)
    have h3 : (0:ℝ) ≤ CDS0 0 * (1 + R₀) * KE1 p :=
      mul_nonneg (mul_nonneg (hCDS0_nn 0) (by linarith)) (hKE1_nn p)
    linarith
  intro C₀ T₀ B hB hball hdata henv p
  set fT : ℕ → ℝ := fun k => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) T₀‖
    with hfT_def
  have hfT_nn : ∀ k, 0 ≤ fT k := fun k => norm_nonneg _
  have hfT_mono : ∀ {k k' : ℕ}, k ≤ k' → fT k ≤ fT k' := fun {k k'} h =>
    smoothCcToTensorHs_norm_mono_of_le (I := I) (M := M) g₀ T₀ h
  have hfT_ball : ∀ k, k ≤ a + 2 → fT k ≤ R₀ := by
    intro k hk
    refine le_trans (hfT_mono hk) ?_
    have h2 : fT (a + 2) = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [h2]
    exact hball
  set Φp : SmoothCcTensor g₀ 2 2 := oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p C₀
    with hΦp_def
  by_cases hcase : w + 2 * p + 2 ≤ a + 2
  · have hsupΦ : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        (Φp.toSection x) ≤ (CCS 0 p * (1 + R₀)) ^ 2 := by
      intro x
      have h := hCCS C₀ T₀ henv 0 p x
      rw [show iteratedCovGrad (I := I) g₀ 2 2 0 Φp = Φp from
        iteratedCovGrad_zero _ _ _ _] at h
      refine le_trans h ?_
      have hf_le : fT (0 + w + 2 * p + 1) ≤ R₀ := hfT_ball _ (by omega)
      have h1 : CCS 0 p * (1 + fT (0 + w + 2 * p + 1)) ≤ CCS 0 p * (1 + R₀) := by
        refine mul_le_mul_of_nonneg_left ?_ (hCCS_nn 0 p)
        linarith
      refine pow_le_pow_left₀ ?_ h1 2
      have := hfT_nn (0 + w + 2 * p + 1)
      have := hCCS_nn 0 p
      nlinarith
    have hX : ‖operatorFieldApply (I := I) (M := M) g₀ 2 2 Φp T₀‖ ≤
        CCS 0 p * (1 + R₀) * ‖T₀‖ := by
      refine operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left (I := I) (M := M) g₀ 2 2
        Φp T₀ (CCS 0 p * (1 + R₀)) ?_ hsupΦ
      have := hCCS_nn 0 p
      nlinarith
    have hT0 : ‖T₀‖ ≤ CJ 0 * fT (2 * p + 1) := by
      have h := hCJ 0 T₀
      rw [show iteratedCovGrad (I := I) g₀ 0 2 0 T₀ = T₀ from
        iteratedCovGrad_zero _ _ _ _] at h
      refine le_trans h ?_
      exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCJ_nn 0)
    have htot : ‖operatorFieldApply (I := I) (M := M) g₀ 2 2 Φp T₀‖ ≤
        CCS 0 p * (1 + R₀) * CJ 0 * fT (2 * p + 1) := by
      refine le_trans hX ?_
      have h := mul_le_mul_of_nonneg_left hT0 (by
        have := hCCS_nn 0 p
        nlinarith : (0:ℝ) ≤ CCS 0 p * (1 + R₀))
      calc CCS 0 p * (1 + R₀) * ‖T₀‖
          ≤ CCS 0 p * (1 + R₀) * (CJ 0 * fT (2 * p + 1)) := h
        _ = CCS 0 p * (1 + R₀) * CJ 0 * fT (2 * p + 1) := by ring
    have hBεa_nn : 0 ≤ B * εa * fT (2 * p + 2) :=
      mul_nonneg (mul_nonneg hB hεa_nn) (hfT_nn _)
    have hrest_nn : 0 ≤ (CDS0 0 * R₀ * εa * Cg (2 * p + 1) +
        CDS0 0 * (1 + R₀) * KE1 p) * fT (2 * p + 1) := by
      have h2 : (0:ℝ) ≤ CDS0 0 * R₀ * εa * Cg (2 * p + 1) :=
        mul_nonneg (mul_nonneg (mul_nonneg (hCDS0_nn 0) hR₀) hεa_nn) (hCg_nn _)
      have h3 : (0:ℝ) ≤ CDS0 0 * (1 + R₀) * KE1 p :=
        mul_nonneg (mul_nonneg (hCDS0_nn 0) (by linarith)) (hKE1_nn p)
      exact mul_nonneg (by linarith) (hfT_nn _)
    calc ‖operatorFieldApply (I := I) (M := M) g₀ 2 2 Φp T₀‖
        ≤ CCS 0 p * (1 + R₀) * CJ 0 * fT (2 * p + 1) := htot
      _ ≤ B * εa * fT (2 * p + 2) +
          (CCS 0 p * (1 + R₀) * CJ 0 +
            (CDS0 0 * R₀ * εa * Cg (2 * p + 1) +
              CDS0 0 * (1 + R₀) * KE1 p)) * fT (2 * p + 1) := by
          have h1 : 0 ≤ (CDS0 0 * R₀ * εa * Cg (2 * p + 1) +
              CDS0 0 * (1 + R₀) * KE1 p) * fT (2 * p + 1) := hrest_nn
          nlinarith [hBεa_nn]
  · exact bal_connLapIterate_appCc_sobolevHs_bound_of_high_order
      (I := I) (M := M) (g₀ := g₀) (a := a) (ha_super := ha_super)
      (hR₀ := hR₀) (Kc := Kc) (hKc_nn := hKc_nn) (εa := εa)
      (hεa_nn := hεa_nn) (CCS := CCS) (hCCS_nn := hCCS_nn)
      (CJ := CJ) (hCJ_nn := hCJ_nn) (hCJ := hCJ)
      (CDS0 := CDS0) (hCDS0_nn := hCDS0_nn) (n := n) (w := w)
      (hn_def := hn_def) (hn1 := hn1) (hw_def := hw_def) (hCDS0 := hCDS0)
      (c22 := c22) (hc22_nn := hc22_nn) (hc22 := hc22)
      (Cg := Cg) (hCg_nn := hCg_nn) (hCg := hCg)
      (KE1 := KE1) (hKE1_def := hKE1_def) (hKE1_nn := hKE1_nn)
      (C₀ := C₀) (T₀ := T₀) (B := B) (hB := hB)
      (hdata := hdata) (henv := henv) (p := p) (fT := fT)
      (hfT_def := hfT_def) (hfT_nn := hfT_nn) (hfT_mono := hfT_mono)
      (hfT_ball := hfT_ball) (Φp := Φp) (hΦp_def := hΦp_def)
      (hcase := hcase)

end BalLadder

end Spectral
end Analysis
end DifferentialGeometry

end
