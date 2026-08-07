import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNormConnLapIterateAppCcCovGradSobolevLowOrderBound
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

lemma bal_sqrt_pair_high_order_bound
    (u₂ u₃ f₁ f₂ f₃ c₁ c₂ : ℝ)
    (hf₁_nn : 0 ≤ f₁) (hf₂_nn : 0 ≤ f₂) (hf₃_nn : 0 ≤ f₃)
    (hc₁_nn : 0 ≤ c₁) (hc₂_nn : 0 ≤ c₂)
    (hf₁f₂ : f₁ ≤ f₂) (hf₂f₃ : f₂ ≤ f₃)
    (hgap₂ : u₂ ^ 2 ≤ f₂ ^ 2 + c₁ * f₁ ^ 2)
    (hgap₃ : u₃ ^ 2 ≤ f₃ ^ 2 + c₂ * f₂ ^ 2) :
    Real.sqrt (u₂ ^ 2 + u₃ ^ 2) ≤
      f₃ + Real.sqrt (1 + c₁ + c₂) * f₂ := by
  have hsq : Real.sqrt (1 + c₁ + c₂) ^ 2 = 1 + c₁ + c₂ :=
    Real.sq_sqrt (by linarith)
  have hcross : 0 ≤ 2 * f₃ * (Real.sqrt (1 + c₁ + c₂) * f₂) := by
    exact mul_nonneg (mul_nonneg (by positivity) hf₃_nn)
      (mul_nonneg (Real.sqrt_nonneg _) hf₂_nn)
  have hf₁sq : f₁ ^ 2 ≤ f₂ ^ 2 := by nlinarith
  have hf₂sq : f₂ ^ 2 ≤ f₃ ^ 2 := by nlinarith
  have hsum : u₂ ^ 2 + u₃ ^ 2 ≤
      (f₃ + Real.sqrt (1 + c₁ + c₂) * f₂) ^ 2 := by
    nlinarith
  calc
    Real.sqrt (u₂ ^ 2 + u₃ ^ 2) ≤
        Real.sqrt ((f₃ + Real.sqrt (1 + c₁ + c₂) * f₂) ^ 2) :=
      Real.sqrt_le_sqrt hsum
    _ = f₃ + Real.sqrt (1 + c₁ + c₂) * f₂ :=
      Real.sqrt_sq (add_nonneg hf₃_nn (mul_nonneg (Real.sqrt_nonneg _) hf₂_nn))

lemma bal_sqrt_pair_high_order_close
    (x₀ x₁ B Bm εa u₂ u₃ f₂ f₃ R₀ CqP KE1 KE2 CDS00 CDS01 sqrtN CC0 D : ℝ)
    (hx₀_nn : 0 ≤ x₀) (hx₁_nn : 0 ≤ x₁) (hBm_nn : 0 ≤ Bm)
    (hεa_nn : 0 ≤ εa) (hu₂_nn : 0 ≤ u₂) (hu₃_nn : 0 ≤ u₃)
    (hf₂_nn : 0 ≤ f₂) (hf₃_nn : 0 ≤ f₃) (hR₀ : 0 ≤ R₀)
    (hCqP_nn : 0 ≤ CqP) (hKE1_nn : 0 ≤ KE1) (hKE2_nn : 0 ≤ KE2)
    (hCDS01_nn : 0 ≤ CDS01)
    (hsqrtN_nn : 0 ≤ sqrtN) (hCC0_nn : 0 ≤ CC0) (hD_nn : 0 ≤ D)
    (hX : x₀ ≤ Bm * εa * u₂ + Bm * (KE1 * (1 + f₂)))
    (hGX : x₁ ≤ Bm * εa * u₃ +
      (Bm * (KE2 * (1 + f₂)) + sqrtN * CDS01 * CC0 * (1 + R₀) * f₂))
    (hupair : Real.sqrt (u₂ ^ 2 + u₃ ^ 2) ≤ f₃ + CqP * f₂)
    (hBm_le_B : Bm ≤ B) (hBm_leC : Bm ≤ CDS00 * R₀)
    (hBm_le_f₂ : Bm ≤ CDS00 * f₂) :
    Real.sqrt (x₀ ^ 2 + x₁ ^ 2) ≤
      B * εa * f₃ +
        (D * (1 + R₀) +
          (CDS00 * R₀ * εa * CqP + CDS00 * (1 + R₀) * (KE1 + KE2) +
            sqrtN * CDS01 * CC0 * (1 + R₀))) * f₂ := by
  set s₀ : ℝ := Bm * (KE1 * (1 + f₂)) with hs₀_def
  set s₁ : ℝ := Bm * (KE2 * (1 + f₂)) +
    sqrtN * CDS01 * CC0 * (1 + R₀) * f₂ with hs₁_def
  have hs₀_nn : 0 ≤ s₀ := by
    rw [hs₀_def]
    exact mul_nonneg hBm_nn (mul_nonneg hKE1_nn (by linarith))
  have hs₁_nn : 0 ≤ s₁ := by
    rw [hs₁_def]
    have h1 : (0 : ℝ) ≤ Bm * (KE2 * (1 + f₂)) :=
      mul_nonneg hBm_nn (mul_nonneg hKE2_nn (by linarith))
    have h2 : (0 : ℝ) ≤ sqrtN * CDS01 * CC0 * (1 + R₀) * f₂ :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hsqrtN_nn hCDS01_nn)
        hCC0_nn) (by linarith)) hf₂_nn
    exact add_nonneg h1 h2
  have hBεu_nn : ∀ v : ℝ, 0 ≤ v → 0 ≤ Bm * εa * v := fun v hv =>
    mul_nonneg (mul_nonneg hBm_nn hεa_nn) hv
  have hmono := bal_sqrt_mono_pair hx₀_nn hx₁_nn hX hGX
  have htwo := bal_sqrt_pair_two (Bm * εa * u₂) s₀ (Bm * εa * u₃) s₁
    (hBεu_nn u₂ hu₂_nn) hs₀_nn (hBεu_nn u₃ hu₃_nn) hs₁_nn
  have hfactor : Real.sqrt ((Bm * εa * u₂) ^ 2 + (Bm * εa * u₃) ^ 2) =
      Bm * εa * Real.sqrt (u₂ ^ 2 + u₃ ^ 2) := by
    have h1 : (Bm * εa * u₂) ^ 2 + (Bm * εa * u₃) ^ 2 =
        (Bm * εa) ^ 2 * (u₂ ^ 2 + u₃ ^ 2) := by ring
    rw [h1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hBm_nn hεa_nn)]
  have hs01 : Real.sqrt (s₀ ^ 2 + s₁ ^ 2) ≤ s₀ + s₁ := by
    have h := bal_sqrt_pair_two s₀ 0 0 s₁ hs₀_nn (le_refl 0) (le_refl 0) hs₁_nn
    simpa [Real.sqrt_sq hs₀_nn, Real.sqrt_sq hs₁_nn] using h
  have hchain : Real.sqrt (x₀ ^ 2 + x₁ ^ 2) ≤
      Bm * εa * f₃ + Bm * εa * (CqP * f₂) + (s₀ + s₁) := by
    have h1 : Bm * εa * Real.sqrt (u₂ ^ 2 + u₃ ^ 2) ≤
        Bm * εa * (f₃ + CqP * f₂) :=
      mul_le_mul_of_nonneg_left hupair (mul_nonneg hBm_nn hεa_nn)
    refine le_trans hmono (le_trans htwo ?_)
    rw [hfactor]
    refine le_trans (add_le_add h1 hs01) (le_of_eq ?_)
    ring
  have hsplit1 : Bm * εa * f₃ ≤ B * εa * f₃ := by
    have h := mul_le_mul_of_nonneg_right hBm_le_B hεa_nn
    exact mul_le_mul_of_nonneg_right h hf₃_nn
  have hsplit2 : Bm * εa * (CqP * f₂) ≤ CDS00 * R₀ * εa * CqP * f₂ := by
    have h1 : Bm * εa ≤ CDS00 * R₀ * εa :=
      mul_le_mul_of_nonneg_right hBm_leC hεa_nn
    have h2 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hCqP_nn hf₂_nn)
    calc
      Bm * εa * (CqP * f₂) ≤ CDS00 * R₀ * εa * (CqP * f₂) := h2
      _ = CDS00 * R₀ * εa * CqP * f₂ := by ring
  have hsplits₀ : s₀ ≤ CDS00 * (1 + R₀) * KE1 * f₂ := by
    rw [hs₀_def]
    have h1 : Bm * KE1 ≤ CDS00 * f₂ * KE1 :=
      mul_le_mul_of_nonneg_right hBm_le_f₂ hKE1_nn
    have h2 : Bm * (KE1 * f₂) ≤ CDS00 * R₀ * (KE1 * f₂) :=
      mul_le_mul_of_nonneg_right hBm_leC (mul_nonneg hKE1_nn hf₂_nn)
    linarith
  have hsplits₁ : s₁ ≤ CDS00 * (1 + R₀) * KE2 * f₂ +
      sqrtN * CDS01 * CC0 * (1 + R₀) * f₂ := by
    rw [hs₁_def]
    have h1 : Bm * KE2 ≤ CDS00 * f₂ * KE2 :=
      mul_le_mul_of_nonneg_right hBm_le_f₂ hKE2_nn
    have h2 : Bm * (KE2 * f₂) ≤ CDS00 * R₀ * (KE2 * f₂) :=
      mul_le_mul_of_nonneg_right hBm_leC (mul_nonneg hKE2_nn hf₂_nn)
    linarith
  have hcrude_nn : (0 : ℝ) ≤ D * (1 + R₀) * f₂ :=
    mul_nonneg (mul_nonneg hD_nn (by linarith)) hf₂_nn
  have hring : (D * (1 + R₀) +
        (CDS00 * R₀ * εa * CqP + CDS00 * (1 + R₀) * (KE1 + KE2) +
          sqrtN * CDS01 * CC0 * (1 + R₀))) * f₂ =
      D * (1 + R₀) * f₂ +
        (CDS00 * R₀ * εa * CqP * f₂ +
          (CDS00 * (1 + R₀) * KE1 * f₂ + CDS00 * (1 + R₀) * KE2 * f₂) +
          sqrtN * CDS01 * CC0 * (1 + R₀) * f₂) := by ring
  rw [hring]
  linarith

lemma bal_sqrt_pair_high_order_finish
    (x₀ x₁ B Bm εa u₂ u₃ f₁ f₂ f₃ R₀ KE1 KE2 CDS00 CDS01 sqrtN CC0 D c₁ c₂ : ℝ)
    (hx₀_nn : 0 ≤ x₀) (hx₁_nn : 0 ≤ x₁) (hBm_nn : 0 ≤ Bm)
    (hεa_nn : 0 ≤ εa) (hu₂_nn : 0 ≤ u₂) (hu₃_nn : 0 ≤ u₃)
    (hf₁_nn : 0 ≤ f₁) (hf₂_nn : 0 ≤ f₂) (hf₃_nn : 0 ≤ f₃)
    (hR₀ : 0 ≤ R₀) (hKE1_nn : 0 ≤ KE1) (hKE2_nn : 0 ≤ KE2)
    (hCDS01_nn : 0 ≤ CDS01) (hsqrtN_nn : 0 ≤ sqrtN)
    (hCC0_nn : 0 ≤ CC0) (hD_nn : 0 ≤ D) (hc₁_nn : 0 ≤ c₁) (hc₂_nn : 0 ≤ c₂)
    (hf₁f₂ : f₁ ≤ f₂) (hf₂f₃ : f₂ ≤ f₃)
    (hgap₂ : u₂ ^ 2 ≤ f₂ ^ 2 + c₁ * f₁ ^ 2)
    (hgap₃ : u₃ ^ 2 ≤ f₃ ^ 2 + c₂ * f₂ ^ 2)
    (hX : x₀ ≤ Bm * εa * u₂ + Bm * (KE1 * (1 + f₂)))
    (hGX : x₁ ≤ Bm * εa * u₃ +
      (Bm * (KE2 * (1 + f₂)) + sqrtN * CDS01 * CC0 * (1 + R₀) * f₂))
    (hBm_le_B : Bm ≤ B) (hBm_leC : Bm ≤ CDS00 * R₀)
    (hBm_le_f₂ : Bm ≤ CDS00 * f₂) :
    Real.sqrt (x₀ ^ 2 + x₁ ^ 2) ≤
      B * εa * f₃ +
        (D * (1 + R₀) +
          (CDS00 * R₀ * εa * Real.sqrt (1 + c₁ + c₂) +
            CDS00 * (1 + R₀) * (KE1 + KE2) +
            sqrtN * CDS01 * CC0 * (1 + R₀))) * f₂ := by
  have hupair := bal_sqrt_pair_high_order_bound u₂ u₃ f₁ f₂ f₃ c₁ c₂
    hf₁_nn hf₂_nn hf₃_nn hc₁_nn hc₂_nn hf₁f₂ hf₂f₃ hgap₂ hgap₃
  exact bal_sqrt_pair_high_order_close x₀ x₁ B Bm εa u₂ u₃ f₂ f₃ R₀
    (Real.sqrt (1 + c₁ + c₂)) KE1 KE2 CDS00 CDS01 sqrtN CC0 D hx₀_nn hx₁_nn
    hBm_nn hεa_nn hu₂_nn hu₃_nn hf₂_nn hf₃_nn hR₀ (Real.sqrt_nonneg _)
    hKE1_nn hKE2_nn hCDS01_nn hsqrtN_nn hCC0_nn hD_nn hX hGX hupair
    hBm_le_B hBm_leC hBm_le_f₂

lemma bal_connLap_iterate_composed_bound
    (x φ top low Bm εa u f k e c q KE : ℝ)
    (hBm_nn : 0 ≤ Bm) (hf_nn : 0 ≤ f) (hc_nn : 0 ≤ c) (he_nn : 0 ≤ e)
    (hX : x ≤ φ * Bm) (hφ : φ ≤ top + c * low)
    (htop : top ≤ k * (1 + f) + εa * u)
    (hlow : low ≤ q * (1 + f)) (hKE : KE = (k + e) + c * q) :
    x ≤ Bm * εa * u + Bm * (KE * (1 + f)) := by
  have hc := mul_le_mul_of_nonneg_left hlow hc_nn
  have hbase : k + c * q ≤ (k + e) + c * q := by linarith
  have hmul := mul_le_mul_of_nonneg_right hbase
    (show (0 : ℝ) ≤ 1 + f by linarith)
  have hφ' : φ ≤ εa * u + KE * (1 + f) := by
    refine le_trans hφ (le_trans (add_le_add htop hc) ?_)
    rw [hKE]
    calc
      k * (1 + f) + εa * u + c * (q * (1 + f)) =
          εa * u + (k + c * q) * (1 + f) := by ring
      _ ≤ εa * u + ((k + e) + c * q) * (1 + f) := add_le_add (le_refl _) hmul
  calc
    x ≤ φ * Bm := hX
    _ ≤ (εa * u + KE * (1 + f)) * Bm := mul_le_mul_of_nonneg_right hφ' hBm_nn
    _ = Bm * εa * u + Bm * (KE * (1 + f)) := by ring

lemma bal_connLapIterate_appCc_covGrad_sobolevHs_bound_of_high_order
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (εa : ℝ) (hεa_nn : 0 ≤ εa)
    (CC : ℕ → ℕ → ℝ) (hCC_nn : ∀ γ q, 0 ≤ CC γ q)
    (hCC : ∀ (C₀ : SmoothCcTensor g₀ 2 2) (T₀ : SmoothCcTensor g₀ 0 2),
      (∀ i : ℕ,
        ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2 ≤
          Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
            εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
      ∀ (γ q : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 2 2 γ
          (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)‖ ≤
        CC γ q * (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀
          ((γ + 2 * q + 2 : ℕ) : ℝ) T₀‖))
    (CCS : ℕ → ℕ → ℝ) (hCCS_nn : ∀ γ q, 0 ≤ CCS γ q)
    (CJ : ℕ → ℝ) (hCJ_nn : ∀ j, 0 ≤ CJ j)
    (hCJ : ∀ (j : ℕ) (T : SmoothCcTensor g₀ 0 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤
        CJ j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (j : ℝ) T‖)
    (CDS0 : ℕ → ℝ) (hCDS0_nn : ∀ β, 0 ≤ CDS0 β)
    (n w : ℕ) [NeZero n] (hn_def : n = Module.finrank ℝ E)
    (hn1 : 1 ≤ n) (hw_def : w = n / 2 + 2)
    (hCDS0 : ∀ (T₀ : SmoothCcTensor g₀ 0 2) (β : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + β) x
          ((iteratedCovGrad (I := I) g₀ 0 2 β T₀).toSection x) ≤
        (CDS0 β * ‖smoothCcToTensorHs (I := I) (M := M) g₀
          ((β + (n / 2 + 1) : ℕ) : ℝ) T₀‖) ^ 2)
    (c22 : ℕ → ℝ) (hc22_nn : ∀ p, 0 ≤ c22 p)
    (hc22 : ∀ (p : ℕ) (S : SmoothCcTensor g₀ 2 2),
      ‖oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p S‖ ≤
          ‖iteratedCovGrad (I := I) g₀ 2 2 (2 * p) S‖ +
            c22 p * ∑ b ∈ Finset.range (2 * p),
              ‖iteratedCovGrad (I := I) g₀ 2 2 b S‖ ∧
        ‖covGrad (I := I) (M := M) g₀ 2 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p S)‖ ≤
          ‖iteratedCovGrad (I := I) g₀ 2 2 (2 * p + 1) S‖ +
            c22 p * ∑ b ∈ Finset.range (2 * p + 1),
              ‖iteratedCovGrad (I := I) g₀ 2 2 b S‖)
    (Cq : ℕ → ℝ)
    (hCq : ∀ (k : ℕ) (u : SmoothCcTensor g₀ 0 2),
      ‖(iteratedCovGrad (I := I) g₀ 0 2 (k + 1) u).toL2‖ ^ 2 ≤
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℝ) + 1) u‖ ^ 2 +
          Cq k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (k : ℝ) u‖ ^ 2)
    (hCq_nn : ∀ k, 0 ≤ Cq k)
    (KE1 KE2 : ℕ → ℝ)
    (hKE1_def : KE1 = fun p =>
      (Real.sqrt (Kc (2 * p)) * (1 + ∑ j ∈ Finset.range (2 * p + 2), CJ j) +
        εa * CJ (2 * p + 2)) +
      c22 p * ∑ b ∈ Finset.range (2 * p),
        (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) +
          εa * CJ (b + 2)))
    (hKE2_def : KE2 = fun p =>
      (Real.sqrt (Kc (2 * p + 1)) * (1 + ∑ j ∈ Finset.range (2 * p + 3), CJ j) +
        εa * CJ (2 * p + 3)) +
      c22 p * ∑ b ∈ Finset.range (2 * p + 1),
        (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) +
          εa * CJ (b + 2)))
    (hKE1_nn : ∀ p, 0 ≤ KE1 p) (hKE2_nn : ∀ p, 0 ≤ KE2 p)
    (C₀ : SmoothCcTensor g₀ 2 2) (T₀ : SmoothCcTensor g₀ 0 2)
    (B : ℝ) (hB : 0 ≤ B)
    (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀)
    (hdata : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T₀.toSection x) ≤ B ^ 2)
    (henv : ∀ i : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2 ≤
        Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
          εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2)
    (p : ℕ) (hcase : ¬ w + 2 * p + 2 ≤ a + 2) :
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
  set Bh : ℝ := CDS0 0 * fT (0 + (n / 2 + 1)) with hBh_def
  have hBh_nn : 0 ≤ Bh := mul_nonneg (hCDS0_nn 0) (hfT_nn _)
  set Bm : ℝ := min B Bh with hBm_def
  have hBm_nn : 0 ≤ Bm := le_min hB hBh_nn
  have hBm_pt : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
      (T₀.toSection x) ≤ Bm ^ 2 := by
    intro x
    rcases le_total B Bh with h | h
    · rw [hBm_def, min_eq_left h]
      exact hdata x
    · rw [hBm_def, min_eq_right h]
      have hd := hCDS0 T₀ 0 x
      rw [show iteratedCovGrad (I := I) g₀ 0 2 0 T₀ = T₀ from
        iteratedCovGrad_zero _ _ _ _] at hd
      exact hd
  have hBm_le_B : Bm ≤ B := min_le_left _ _
  have hBm_le_Bh : Bm ≤ Bh := min_le_right _ _
  have hBh_le : Bh ≤ CDS0 0 * R₀ := by
    rw [hBh_def]
    exact mul_le_mul_of_nonneg_left (hfT_ball _ (by omega)) (hCDS0_nn 0)
  have hBh_le_f₂ : Bh ≤ CDS0 0 * f₂ := by
    rw [hBh_def, hf₂_def]
    exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCDS0_nn 0)
  set u₂ : ℝ := ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * p + 2) T₀‖ with hu₂_def
  set u₃ : ℝ := ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * p + 3) T₀‖ with hu₃_def
  have hu₂_nn : 0 ≤ u₂ := norm_nonneg _
  have hu₃_nn : 0 ≤ u₃ := norm_nonneg _
  have hone_aux : ∀ (X : ℝ), 0 ≤ X → 1 + X * f₂ ≤ (1 + X) * (1 + f₂) := by
    intro X hX
    nlinarith
  have henvsum : ∀ (k : ℕ), k ≤ 2 * p + 3 →
      ∑ j ∈ Finset.range k, ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
        (∑ j ∈ Finset.range k, CJ j) * f₂ := by
    intro k hk
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun j hj => ?_)
    have hjk := Finset.mem_range.mp hj
    refine le_trans (hCJ j T₀) ?_
    rw [hf₂_def]
    exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCJ_nn j)
  have henvC : ∀ (b : ℕ), b + 2 ≤ 2 * p + 3 → b + 2 ≤ 2 * p + 2 →
      ‖iteratedCovGrad (I := I) g₀ 2 2 b C₀‖ ≤
        (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2)) *
          (1 + f₂) := by
    intro b hb hb2
    refine le_trans (iteratedCovGrad_le_of_sq_envelope_bound (I := I) (M := M) g₀ Kc hKc_nn εa
      hεa_nn C₀ T₀ henv b) ?_
    have hs := henvsum (b + 2) hb
    have hCJsum_nn : (0:ℝ) ≤ ∑ j ∈ Finset.range (b + 2), CJ j :=
      Finset.sum_nonneg (fun j _ => hCJ_nn j)
    have h1 : 1 + ∑ j ∈ Finset.range (b + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
        (1 + ∑ j ∈ Finset.range (b + 2), CJ j) * (1 + f₂) := by
      refine le_trans ?_ (hone_aux _ hCJsum_nn)
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg (Kc b))
    have h3 : ‖iteratedCovGrad (I := I) g₀ 0 2 (b + 2) T₀‖ ≤ CJ (b + 2) * f₂ := by
      refine le_trans (hCJ (b + 2) T₀) ?_
      rw [hf₂_def]
      exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCJ_nn (b + 2))
    have h4 := mul_le_mul_of_nonneg_left h3 hεa_nn
    have hf₂_le : f₂ ≤ 1 + f₂ := by linarith
    have h5 : εa * (CJ (b + 2) * f₂) ≤ εa * CJ (b + 2) * (1 + f₂) := by
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left hf₂_le (mul_nonneg hεa_nn (hCJ_nn (b + 2)))
    calc
      Real.sqrt (Kc b) *
            (1 + ∑ j ∈ Finset.range (b + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖) +
          εa * ‖iteratedCovGrad (I := I) g₀ 0 2 (b + 2) T₀‖
          ≤ Real.sqrt (Kc b) *
              ((1 + ∑ j ∈ Finset.range (b + 2), CJ j) * (1 + f₂)) +
            εa * (CJ (b + 2) * f₂) := add_le_add h2 h4
      _ ≤ Real.sqrt (Kc b) *
              ((1 + ∑ j ∈ Finset.range (b + 2), CJ j) * (1 + f₂)) +
            εa * CJ (b + 2) * (1 + f₂) := add_le_add (le_refl _) h5
      _ = (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) +
            εa * CJ (b + 2)) * (1 + f₂) := by ring
  have hXb : ‖Xp‖ ≤ Bm * εa * u₂ + Bm * (KE1 p * (1 + f₂)) := by
    have hX : ‖Xp‖ ≤ ‖Φp‖ * Bm :=
      operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_right (I := I) (M := M) g₀ 2 2
        Φp T₀ Bm hBm_nn hBm_pt
    have hΦcore := (hc22 p C₀).1
    have htopC : ‖iteratedCovGrad (I := I) g₀ 2 2 (2 * p) C₀‖ ≤
        (Real.sqrt (Kc (2 * p)) * (1 + ∑ j ∈ Finset.range (2 * p + 2), CJ j)) *
          (1 + f₂) + εa * u₂ := by
      refine le_trans (iteratedCovGrad_le_of_sq_envelope_bound (I := I) (M := M) g₀ Kc hKc_nn εa
        hεa_nn C₀ T₀ henv
        (2 * p)) ?_
      have hs := henvsum (2 * p + 2) (by omega)
      have hCJsum_nn : (0:ℝ) ≤ ∑ j ∈ Finset.range (2 * p + 2), CJ j :=
        Finset.sum_nonneg (fun j _ => hCJ_nn j)
      have h1 : 1 + ∑ j ∈ Finset.range (2 * p + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
          (1 + ∑ j ∈ Finset.range (2 * p + 2), CJ j) * (1 + f₂) := by
        refine le_trans ?_ (hone_aux _ hCJsum_nn)
        linarith
      have h2 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg (Kc (2 * p)))
      have h2' : Real.sqrt (Kc (2 * p)) *
            (1 + ∑ j ∈ Finset.range (2 * p + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖) ≤
          Real.sqrt (Kc (2 * p)) *
            (1 + ∑ j ∈ Finset.range (2 * p + 2), CJ j) * (1 + f₂) := by
        simpa [mul_assoc] using h2
      change Real.sqrt (Kc (2 * p)) *
            (1 + ∑ j ∈ Finset.range (2 * p + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖) + εa * u₂ ≤ _
      exact add_le_add h2' (le_refl _)
    have hlowC : ∑ b ∈ Finset.range (2 * p), ‖iteratedCovGrad (I := I) g₀ 2 2 b C₀‖ ≤
        (∑ b ∈ Finset.range (2 * p),
          (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) +
            εa * CJ (b + 2))) * (1 + f₂) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun b hb => ?_)
      have hb2p := Finset.mem_range.mp hb
      exact henvC b (by omega) (by omega)
    exact bal_connLap_iterate_composed_bound
      ‖Xp‖ ‖Φp‖ ‖iteratedCovGrad (I := I) g₀ 2 2 (2 * p) C₀‖
      (∑ b ∈ Finset.range (2 * p), ‖iteratedCovGrad (I := I) g₀ 2 2 b C₀‖)
      Bm εa u₂ f₂
      (Real.sqrt (Kc (2 * p)) * (1 + ∑ j ∈ Finset.range (2 * p + 2), CJ j))
      (εa * CJ (2 * p + 2)) (c22 p)
      (∑ b ∈ Finset.range (2 * p),
        (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2)))
      (KE1 p) hBm_nn hf₂_nn (hc22_nn p) (mul_nonneg hεa_nn (hCJ_nn _))
      hX hΦcore htopC hlowC (congrFun hKE1_def p)
  have hGXb : ‖covGrad (I := I) (M := M) g₀ 0 2 Xp‖ ≤
      Bm * εa * u₃ + (Bm * (KE2 p * (1 + f₂)) +
        Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀) * f₂) := by
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have hp1 : ‖operatorFieldApply (I := I) (M := M) g₀ 2 (2 + 1)
        (covGrad (I := I) (M := M) g₀ 2 2 Φp) T₀‖ ≤
        Bm * εa * u₃ + Bm * (KE2 p * (1 + f₂)) := by
      have hX := operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_right (I := I) (M := M) g₀
        2 (2 + 1) (covGrad (I := I) (M := M) g₀ 2 2 Φp) T₀ Bm hBm_nn hBm_pt
      have hΦcore := (hc22 p C₀).2
      have htopC : ‖iteratedCovGrad (I := I) g₀ 2 2 (2 * p + 1) C₀‖ ≤
          (Real.sqrt (Kc (2 * p + 1)) *
            (1 + ∑ j ∈ Finset.range (2 * p + 3), CJ j)) * (1 + f₂) + εa * u₃ := by
        refine le_trans (iteratedCovGrad_le_of_sq_envelope_bound (I := I) (M := M) g₀ Kc hKc_nn εa
          hεa_nn C₀ T₀ henv
          (2 * p + 1)) ?_
        have hs := henvsum (2 * p + 3) (by omega)
        have hCJsum_nn : (0:ℝ) ≤ ∑ j ∈ Finset.range (2 * p + 3), CJ j :=
          Finset.sum_nonneg (fun j _ => hCJ_nn j)
        have h1 : 1 + ∑ j ∈ Finset.range (2 * p + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
            (1 + ∑ j ∈ Finset.range (2 * p + 3), CJ j) * (1 + f₂) := by
          refine le_trans ?_ (hone_aux _ hCJsum_nn)
          linarith
        have h2 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg (Kc (2 * p + 1)))
        have h2' : Real.sqrt (Kc (2 * p + 1)) *
              (1 + ∑ j ∈ Finset.range (2 * p + 3),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖) ≤
            Real.sqrt (Kc (2 * p + 1)) *
              (1 + ∑ j ∈ Finset.range (2 * p + 3), CJ j) * (1 + f₂) := by
          simpa [mul_assoc] using h2
        change Real.sqrt (Kc (2 * p + 1)) *
              (1 + ∑ j ∈ Finset.range (2 * p + 3),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖) + εa * u₃ ≤ _
        exact add_le_add h2' (le_refl _)
      have hlowC : ∑ b ∈ Finset.range (2 * p + 1),
          ‖iteratedCovGrad (I := I) g₀ 2 2 b C₀‖ ≤
          (∑ b ∈ Finset.range (2 * p + 1),
            (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) +
              εa * CJ (b + 2))) * (1 + f₂) := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum (fun b hb => ?_)
        have hb2p := Finset.mem_range.mp hb
        exact henvC b (by omega) (by omega)
      exact bal_connLap_iterate_composed_bound
        ‖operatorFieldApply (I := I) (M := M) g₀ 2 (2 + 1)
          (covGrad (I := I) (M := M) g₀ 2 2 Φp) T₀‖
        ‖covGrad (I := I) (M := M) g₀ 2 2 Φp‖
        ‖iteratedCovGrad (I := I) g₀ 2 2 (2 * p + 1) C₀‖
        (∑ b ∈ Finset.range (2 * p + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 b C₀‖)
        Bm εa u₃ f₂
        (Real.sqrt (Kc (2 * p + 1)) *
          (1 + ∑ j ∈ Finset.range (2 * p + 3), CJ j))
        (εa * CJ (2 * p + 3)) (c22 p)
        (∑ b ∈ Finset.range (2 * p + 1),
          (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2)))
        (KE2 p) hBm_nn hf₂_nn (hc22_nn p) (mul_nonneg hεa_nn (hCJ_nn _))
        hX hΦcore htopC hlowC (congrFun hKE2_def p)
    have hp2 : ‖operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 1)
        (slotExtend (I := I) (M := M) g₀ 2 2 Φp)
        (covGrad (I := I) (M := M) g₀ 0 2 T₀)‖ ≤
        Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀) * f₂ := by
      have hdsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
          ((covGrad (I := I) (M := M) g₀ 0 2 T₀).toSection x) ≤
          (CDS0 1 * fT (1 + (n / 2 + 1))) ^ 2 := by
        intro x
        have hd := hCDS0 T₀ 1 x
        rw [show iteratedCovGrad (I := I) g₀ 0 2 1 T₀ =
          covGrad (I := I) (M := M) g₀ 0 2 T₀ from
            (covGrad_eq_iteratedCovGrad_one (I := I) (M := M) g₀ 0 2 T₀).symm] at hd
        exact hd
      have hX := operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_right (I := I) (M := M) g₀
        (2 + 1) (2 + 1) (slotExtend (I := I) (M := M) g₀ 2 2 Φp)
        (covGrad (I := I) (M := M) g₀ 0 2 T₀) (CDS0 1 * fT (1 + (n / 2 + 1)))
        (mul_nonneg (hCDS0_nn 1) (hfT_nn _)) hdsup
      have hse : ‖slotExtend (I := I) (M := M) g₀ 2 2 Φp‖ ≤
          Real.sqrt n * ‖Φp‖ := by
        simpa [hn_def] using bal_slotExt_norm (I := I) (M := M) g₀ 2 2 Φp
      have hΦpl2 : ‖Φp‖ ≤ CC 0 p * (1 + fT (0 + 2 * p + 2)) := by
        have h := hCC C₀ T₀ henv 0 p
        rw [show iteratedCovGrad (I := I) g₀ 2 2 0 Φp = Φp from
          iteratedCovGrad_zero _ _ _ _] at h
        exact h
      have hprod : fT (1 + (n / 2 + 1)) * (1 + fT (0 + 2 * p + 2)) ≤ (1 + R₀) * f₂ := by
        have hm1 : fT (1 + (n / 2 + 1)) ≤ f₂ := by
          rw [hf₂_def]
          exact hfT_mono (by omega)
        have hm2 : fT (1 + (n / 2 + 1)) * fT (0 + 2 * p + 2) ≤ R₀ * f₂ := by
          have hb1 : fT (1 + (n / 2 + 1)) ≤ R₀ := hfT_ball _ (by omega)
          have hm3 : fT (0 + 2 * p + 2) ≤ f₂ := by
            rw [hf₂_def]
            exact hfT_mono (by omega)
          have := mul_le_mul hb1 hm3 (hfT_nn _) hR₀
          linarith
        calc
          fT (1 + (n / 2 + 1)) * (1 + fT (0 + 2 * p + 2)) =
              fT (1 + (n / 2 + 1)) +
                fT (1 + (n / 2 + 1)) * fT (0 + 2 * p + 2) := by ring
          _ ≤ f₂ + R₀ * f₂ := add_le_add hm1 hm2
          _ = (1 + R₀) * f₂ := by ring
      calc ‖operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 1)
            (slotExtend (I := I) (M := M) g₀ 2 2 Φp)
            (covGrad (I := I) (M := M) g₀ 0 2 T₀)‖
          ≤ ‖slotExtend (I := I) (M := M) g₀ 2 2 Φp‖ *
            (CDS0 1 * fT (1 + (n / 2 + 1))) := hX
        _ ≤ (Real.sqrt n * ‖Φp‖) * (CDS0 1 * fT (1 + (n / 2 + 1))) := by
            refine mul_le_mul_of_nonneg_right hse ?_
            exact mul_nonneg (hCDS0_nn 1) (hfT_nn _)
        _ ≤ (Real.sqrt n * (CC 0 p * (1 + fT (0 + 2 * p + 2)))) *
            (CDS0 1 * fT (1 + (n / 2 + 1))) := by
            refine mul_le_mul_of_nonneg_right ?_
              (mul_nonneg (hCDS0_nn 1) (hfT_nn _))
            exact mul_le_mul_of_nonneg_left hΦpl2 (Real.sqrt_nonneg _)
        _ = Real.sqrt n * CC 0 p * CDS0 1 *
            (fT (1 + (n / 2 + 1)) * (1 + fT (0 + 2 * p + 2))) := by ring
        _ ≤ Real.sqrt n * CC 0 p * CDS0 1 * ((1 + R₀) * f₂) := by
            refine mul_le_mul_of_nonneg_left hprod ?_
            exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hCC_nn 0 p)) (hCDS0_nn 1)
        _ = Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀) * f₂ := by ring
    calc
      ‖operatorFieldApply (I := I) (M := M) g₀ 2 (2 + 1)
            (covGrad (I := I) (M := M) g₀ 2 2 Φp) T₀‖ +
          ‖operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 1)
            (slotExtend (I := I) (M := M) g₀ 2 2 Φp)
            (covGrad (I := I) (M := M) g₀ 0 2 T₀)‖
          ≤ (Bm * εa * u₃ + Bm * (KE2 p * (1 + f₂))) +
            Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀) * f₂ := add_le_add hp1 hp2
      _ = Bm * εa * u₃ + (Bm * (KE2 p * (1 + f₂)) +
            Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀) * f₂) := by ring
  have hgap₂ : u₂ ^ 2 ≤ fT (2 * p + 2) ^ 2 + Cq (2 * p + 1) * fT (2 * p + 1) ^ 2 := by
    have h := hCq (2 * p + 1) T₀
    rw [SmoothCcTensor.norm_toL2] at h
    have hc : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p + 1 : ℕ) : ℝ) + 1) T₀‖ =
        fT (2 * p + 2) :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [hc] at h
    exact h
  have hgap₃ : u₃ ^ 2 ≤ fT (2 * p + 3) ^ 2 + Cq (2 * p + 2) * fT (2 * p + 2) ^ 2 := by
    have h := hCq (2 * p + 2) T₀
    rw [SmoothCcTensor.norm_toL2] at h
    have hc : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p + 2 : ℕ) : ℝ) + 1) T₀‖ =
        fT (2 * p + 3) :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [hc] at h
    exact h
  have hD_nn : (0 : ℝ) ≤ CCS 0 p * CJ 0 + CCS 1 p * CJ 0 +
      Real.sqrt n * CCS 0 p * CJ 1 := by
    have ha1 : (0:ℝ) ≤ CCS 0 p * CJ 0 := mul_nonneg (hCCS_nn 0 p) (hCJ_nn 0)
    have ha2 : (0:ℝ) ≤ CCS 1 p * CJ 0 := mul_nonneg (hCCS_nn 1 p) (hCJ_nn 0)
    have ha3 : (0:ℝ) ≤ Real.sqrt n * CCS 0 p * CJ 1 :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hCCS_nn 0 p)) (hCJ_nn 1)
    linarith
  have hfinal := bal_sqrt_pair_high_order_finish
    (x₀ := ‖Xp‖) (x₁ := ‖covGrad (I := I) (M := M) g₀ 0 2 Xp‖)
    (B := B) (Bm := Bm) (εa := εa) (u₂ := u₂) (u₃ := u₃)
    (f₁ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 1 : ℕ) : ℝ) T₀‖)
    (f₂ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 2 : ℕ) : ℝ) T₀‖)
    (f₃ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 3 : ℕ) : ℝ) T₀‖)
    (R₀ := R₀)
    (KE1 := KE1 p) (KE2 := KE2 p) (CDS00 := CDS0 0) (CDS01 := CDS0 1)
    (sqrtN := Real.sqrt n) (CC0 := CC 0 p)
    (D := CCS 0 p * CJ 0 + CCS 1 p * CJ 0 + Real.sqrt n * CCS 0 p * CJ 1)
    (c₁ := Cq (2 * p + 1)) (c₂ := Cq (2 * p + 2))
    (norm_nonneg _) (norm_nonneg _) hBm_nn hεa_nn hu₂_nn hu₃_nn (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) hR₀ (hKE1_nn p) (hKE2_nn p) (hCDS0_nn 1)
    (Real.sqrt_nonneg _) (hCC_nn 0 p) hD_nn (hCq_nn _) (hCq_nn _)
    (hfT_mono (Nat.le_succ _)) (hfT_mono (Nat.le_succ _)) hgap₂ hgap₃
    hXb hGXb hBm_le_B
    (le_trans hBm_le_Bh hBh_le) (le_trans hBm_le_Bh hBh_le_f₂)
  exact hfinal

end BalLadder

end Spectral
end Analysis
end DifferentialGeometry

end
