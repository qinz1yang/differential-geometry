import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNormConnLapIterateAppCcSobolevBound
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

lemma bal_connLapIterate_appCc_covGrad_sobolevHs_bound_of_low_order
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (εa : ℝ) (hεa_nn : 0 ≤ εa)
    (CC : ℕ → ℕ → ℝ) (hCC_nn : ∀ γ q, 0 ≤ CC γ q)
    (CCS : ℕ → ℕ → ℝ) (hCCS_nn : ∀ γ q, 0 ≤ CCS γ q)
    (CJ : ℕ → ℝ) (hCJ_nn : ∀ j, 0 ≤ CJ j)
    (hCJ : ∀ (j : ℕ) (T : SmoothCcTensor g₀ 0 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤
        CJ j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (j : ℝ) T‖)
    (CDS0 : ℕ → ℝ) (hCDS0_nn : ∀ β, 0 ≤ CDS0 β)
    (Cq : ℕ → ℝ) (n w : ℕ) [NeZero n]
    (hn_def : n = Module.finrank ℝ E)
    (hCCS : ∀ (C₀ : SmoothCcTensor g₀ 2 2) (T₀ : SmoothCcTensor g₀ 0 2),
      (∀ i : ℕ,
        ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2 ≤
          Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
            εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
      ∀ (γ q : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + γ) x
            ((iteratedCovGrad (I := I) g₀ 2 2 γ
              (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)).toSection x) ≤
          (CCS γ q * (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀
            ((γ + w + 2 * q + 1 : ℕ) : ℝ) T₀‖)) ^ 2)
    (KE1 KE2 : ℕ → ℝ) (hKE1_nn : ∀ p, 0 ≤ KE1 p)
    (hKE2_nn : ∀ p, 0 ≤ KE2 p)
    (C₀ : SmoothCcTensor g₀ 2 2) (T₀ : SmoothCcTensor g₀ 0 2)
    (B : ℝ) (hB : 0 ≤ B)
    (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀)
    (henv : ∀ i : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2 ≤
        Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
          εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2)
    (p : ℕ) (hcase : w + 2 * p + 2 ≤ a + 2) :
    Real.sqrt (‖operatorFieldApply (I := I) (M := M) g₀ 2 2
        (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p C₀) T₀‖ ^ 2 +
      ‖covGrad (I := I) (M := M) g₀ 0 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p C₀) T₀)‖ ^ 2) ≤
      B * εa * ‖smoothCcToTensorHs (I := I) (M := M) g₀
        ((2 * p + 3 : ℕ) : ℝ) T₀‖ +
      ((CCS 0 p * CJ 0 + CCS 1 p * CJ 0 + Real.sqrt n * CCS 0 p * CJ 1) *
          (1 + R₀) +
        (CDS0 0 * R₀ * εa * Real.sqrt (1 + Cq (2 * p + 1) + Cq (2 * p + 2)) +
          CDS0 0 * (1 + R₀) * (KE1 p + KE2 p) +
          Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀))) *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀
          ((2 * p + 2 : ℕ) : ℝ) T₀‖ := by
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
  set Xp : SmoothCcTensor g₀ 0 2 := operatorFieldApply (I := I) (M := M) g₀ 2 2 Φp T₀ with hXp_def
  have hsplit : covGrad (I := I) (M := M) g₀ 0 2 Xp =
      operatorFieldApply (I := I) (M := M) g₀ 2 (2 + 1) (covGrad (I := I) (M := M) g₀ 2 2 Φp) T₀ +
        operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 1)
          (slotExtend (I := I) (M := M) g₀ 2 2 Φp) (covGrad (I := I) (M := M) g₀ 0 2 T₀) :=
    covGrad_operatorFieldApply_eq (I := I) (M := M) g₀ 2 2 Φp T₀
  set f₂ : ℝ := fT (2 * p + 2) with hf₂_def
  have hf₂_nn : 0 ≤ f₂ := hfT_nn _
  have hT0f : ‖T₀‖ ≤ CJ 0 * f₂ := by
    have h := hCJ 0 T₀
    rw [show iteratedCovGrad (I := I) g₀ 0 2 0 T₀ = T₀ from
      iteratedCovGrad_zero _ _ _ _] at h
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCJ_nn 0)
  have hGT0f : ‖covGrad (I := I) (M := M) g₀ 0 2 T₀‖ ≤ CJ 1 * f₂ := by
    have h := hCJ 1 T₀
    rw [show iteratedCovGrad (I := I) g₀ 0 2 1 T₀ =
      covGrad (I := I) (M := M) g₀ 0 2 T₀ from
        (covGrad_eq_iteratedCovGrad_one (I := I) (M := M) g₀ 0 2 T₀).symm] at h
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCJ_nn 1)
  have hsupΦ0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
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
  have hsupΦ1 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + 1) x
      ((covGrad (I := I) (M := M) g₀ 2 2 Φp).toSection x) ≤
      (CCS 1 p * (1 + R₀)) ^ 2 := by
    intro x
    have h := hCCS C₀ T₀ henv 1 p x
    rw [show iteratedCovGrad (I := I) g₀ 2 2 1 Φp =
      covGrad (I := I) (M := M) g₀ 2 2 Φp from
        (covGrad_eq_iteratedCovGrad_one (I := I) (M := M) g₀ 2 2 Φp).symm] at h
    refine le_trans h ?_
    have hf_le : fT (1 + w + 2 * p + 1) ≤ R₀ := hfT_ball _ (by omega)
    have h1 : CCS 1 p * (1 + fT (1 + w + 2 * p + 1)) ≤ CCS 1 p * (1 + R₀) := by
      refine mul_le_mul_of_nonneg_left ?_ (hCCS_nn 1 p)
      linarith
    refine pow_le_pow_left₀ ?_ h1 2
    have := hfT_nn (1 + w + 2 * p + 1)
    have := hCCS_nn 1 p
    nlinarith
  have hsupSE : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 1) (2 + 1) x
      ((slotExtend (I := I) (M := M) g₀ 2 2 Φp).toSection x) ≤
      (Real.sqrt n * (CCS 0 p * (1 + R₀))) ^ 2 := by
    intro x
    have h := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 2 2 Φp 0 x
    rw [show iteratedCovGrad (I := I) g₀ (2 + 1) (2 + 1) 0
        (slotExtend (I := I) (M := M) g₀ 2 2 Φp) =
      slotExtend (I := I) (M := M) g₀ 2 2 Φp from iteratedCovGrad_zero _ _ _ _] at h
    rw [show iteratedCovGrad (I := I) g₀ 2 2 0 Φp = Φp from
      iteratedCovGrad_zero _ _ _ _] at h
    refine le_trans h ?_
    rw [← hn_def]
    have h2 := hsupΦ0 x
    have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
    have hns : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    calc
      (n : ℝ) * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          (Φp.toSection x) ≤ (n : ℝ) * (CCS 0 p * (1 + R₀)) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 hns
      _ = Real.sqrt n ^ 2 * (CCS 0 p * (1 + R₀)) ^ 2 := by rw [hsq]
      _ = (Real.sqrt n * (CCS 0 p * (1 + R₀))) ^ 2 := by ring
  have hXb : ‖Xp‖ ≤ CCS 0 p * (1 + R₀) * (CJ 0 * f₂) := by
    have hn0' : (0:ℝ) ≤ CCS 0 p * (1 + R₀) :=
      mul_nonneg (hCCS_nn 0 p) (by linarith)
    have h := operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left (I := I) (M := M) g₀ 2 2
      Φp T₀ (CCS 0 p * (1 + R₀)) hn0' hsupΦ0
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_left hT0f hn0'
  have hGXb : ‖covGrad (I := I) (M := M) g₀ 0 2 Xp‖ ≤
      CCS 1 p * (1 + R₀) * (CJ 0 * f₂) +
        Real.sqrt n * (CCS 0 p * (1 + R₀)) * (CJ 1 * f₂) := by
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have hn1' : (0:ℝ) ≤ CCS 1 p * (1 + R₀) :=
      mul_nonneg (hCCS_nn 1 p) (by linarith)
    have hn2' : (0:ℝ) ≤ Real.sqrt n * (CCS 0 p * (1 + R₀)) :=
      mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (hCCS_nn 0 p) (by linarith))
    have h1 := operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left (I := I) (M := M) g₀ 2
      (2 + 1) (covGrad (I := I) (M := M) g₀ 2 2 Φp) T₀ (CCS 1 p * (1 + R₀))
      hn1' hsupΦ1
    have h2 := operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left (I := I) (M := M) g₀
      (2 + 1) (2 + 1) (slotExtend (I := I) (M := M) g₀ 2 2 Φp)
      (covGrad (I := I) (M := M) g₀ 0 2 T₀) (Real.sqrt n * (CCS 0 p * (1 + R₀)))
      hn2' hsupSE
    have h1' : CCS 1 p * (1 + R₀) * ‖T₀‖ ≤ CCS 1 p * (1 + R₀) * (CJ 0 * f₂) :=
      mul_le_mul_of_nonneg_left hT0f hn1'
    have h2' : Real.sqrt n * (CCS 0 p * (1 + R₀)) *
        ‖covGrad (I := I) (M := M) g₀ 0 2 T₀‖ ≤
        Real.sqrt n * (CCS 0 p * (1 + R₀)) * (CJ 1 * f₂) :=
      mul_le_mul_of_nonneg_left hGT0f hn2'
    linarith [le_trans h1 h1', le_trans h2 h2']
  have hpair : Real.sqrt (‖Xp‖ ^ 2 + ‖covGrad (I := I) (M := M) g₀ 0 2 Xp‖ ^ 2) ≤
      ‖Xp‖ + ‖covGrad (I := I) (M := M) g₀ 0 2 Xp‖ := by
    have h := bal_sqrt_pair_two ‖Xp‖ 0 0 ‖covGrad (I := I) (M := M) g₀ 0 2 Xp‖
      (norm_nonneg _) (le_refl 0) (le_refl 0) (norm_nonneg _)
    simpa using h
  refine le_trans hpair ?_
  have hBεa_nn : 0 ≤ B * εa * fT (2 * p + 3) :=
    mul_nonneg (mul_nonneg hB hεa_nn) (hfT_nn _)
  have henv_nn : (0:ℝ) ≤ (CDS0 0 * R₀ * εa *
      Real.sqrt (1 + Cq (2 * p + 1) + Cq (2 * p + 2)) +
      CDS0 0 * (1 + R₀) * (KE1 p + KE2 p) +
      Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀)) * f₂ := by
    have h2 : (0:ℝ) ≤ CDS0 0 * R₀ * εa *
        Real.sqrt (1 + Cq (2 * p + 1) + Cq (2 * p + 2)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (hCDS0_nn 0) hR₀) hεa_nn) (Real.sqrt_nonneg _)
    have h3 : (0:ℝ) ≤ CDS0 0 * (1 + R₀) * (KE1 p + KE2 p) :=
      mul_nonneg (mul_nonneg (hCDS0_nn 0) (add_nonneg zero_le_one hR₀))
        (add_nonneg (hKE1_nn p) (hKE2_nn p))
    have h4 : (0:ℝ) ≤ Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀) :=
      mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hCDS0_nn 1)) (hCC_nn 0 p))
        (add_nonneg zero_le_one hR₀)
    exact mul_nonneg (add_nonneg (add_nonneg h2 h3) h4) hf₂_nn
  simp only [hf₂_def, hfT_def] at hXb hGXb henv_nn
  let A : ℝ := (CCS 0 p * CJ 0 + CCS 1 p * CJ 0 +
    Real.sqrt n * CCS 0 p * CJ 1) * (1 + R₀)
  let V : ℝ := CDS0 0 * R₀ * εa *
      Real.sqrt (1 + Cq (2 * p + 1) + Cq (2 * p + 2)) +
    CDS0 0 * (1 + R₀) * (KE1 p + KE2 p) +
    Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀)
  have hnonneg : 0 ≤ B * εa * fT (2 * p + 3) +
      V * ‖smoothCcToTensorHs (I := I) (M := M) g₀
        ((2 * p + 2 : ℕ) : ℝ) T₀‖ := add_nonneg hBεa_nn henv_nn
  calc
    ‖Xp‖ + ‖covGrad (I := I) (M := M) g₀ 0 2 Xp‖ ≤
        CCS 0 p * (1 + R₀) *
            (CJ 0 * ‖smoothCcToTensorHs (I := I) (M := M) g₀
              ((2 * p + 2 : ℕ) : ℝ) T₀‖) +
          (CCS 1 p * (1 + R₀) *
              (CJ 0 * ‖smoothCcToTensorHs (I := I) (M := M) g₀
                ((2 * p + 2 : ℕ) : ℝ) T₀‖) +
            Real.sqrt n * (CCS 0 p * (1 + R₀)) *
              (CJ 1 * ‖smoothCcToTensorHs (I := I) (M := M) g₀
                ((2 * p + 2 : ℕ) : ℝ) T₀‖)) := add_le_add hXb hGXb
    _ = A * ‖smoothCcToTensorHs (I := I) (M := M) g₀
        ((2 * p + 2 : ℕ) : ℝ) T₀‖ := by ring
    _ ≤ A * ‖smoothCcToTensorHs (I := I) (M := M) g₀
          ((2 * p + 2 : ℕ) : ℝ) T₀‖ +
        (B * εa * fT (2 * p + 3) +
          V * ‖smoothCcToTensorHs (I := I) (M := M) g₀
            ((2 * p + 2 : ℕ) : ℝ) T₀‖) := le_add_of_nonneg_right hnonneg
    _ = B * εa * fT (2 * p + 3) +
        (A + V) * ‖smoothCcToTensorHs (I := I) (M := M) g₀
          ((2 * p + 2 : ℕ) : ℝ) T₀‖ := by ring

end BalLadder

end Spectral
end Analysis
end DifferentialGeometry

end
