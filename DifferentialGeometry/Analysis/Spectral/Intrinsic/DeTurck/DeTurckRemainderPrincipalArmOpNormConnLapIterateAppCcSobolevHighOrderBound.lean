import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNormConnLapIterateJetLadderMixedBlocks
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


private lemma bal_two_mul_add_one_cast_high (p : ℕ) :
    (((2 * p + 1 : ℕ) : ℝ) + 1) = ((2 * p + 2 : ℕ) : ℝ) := by
  push_cast
  ring

lemma bal_connLapIterate_appCc_sobolevHs_bound_of_high_order
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (εa : ℝ) (hεa_nn : 0 ≤ εa)
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
    (Cg : ℕ → ℝ) (hCg_nn : ∀ k, 0 ≤ Cg k)
    (hCg : ∀ (k : ℕ) (u : SmoothCcTensor g₀ 0 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 (k + 1) u‖ ≤
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℝ) + 1) u‖ +
          Cg k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (k : ℝ) u‖)
    (KE1 : ℕ → ℝ)
    (hKE1_def : KE1 = fun p =>
      (Real.sqrt (Kc (2 * p)) * (1 + ∑ j ∈ Finset.range (2 * p + 2), CJ j) +
        εa * CJ (2 * p + 2)) +
      c22 p * ∑ b ∈ Finset.range (2 * p),
        (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) +
          εa * CJ (b + 2)))
    (hKE1_nn : ∀ p, 0 ≤ KE1 p)
    (C₀ : SmoothCcTensor g₀ 2 2) (T₀ : SmoothCcTensor g₀ 0 2)
    (B : ℝ) (hB : 0 ≤ B)
    (hdata : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T₀.toSection x) ≤ B ^ 2)
    (henv : ∀ i : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2 ≤
        Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
          εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2)
    (p : ℕ) (fT : ℕ → ℝ)
    (hfT_def : fT = fun k : ℕ =>
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) T₀‖)
    (hfT_nn : ∀ k, 0 ≤ fT k)
    (hfT_mono : ∀ {k k' : ℕ}, k ≤ k' → fT k ≤ fT k')
    (hfT_ball : ∀ k, k ≤ a + 2 → fT k ≤ R₀)
    (Φp : SmoothCcTensor g₀ 2 2)
    (hΦp_def : Φp = oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p C₀)
    (hcase : ¬ w + 2 * p + 2 ≤ a + 2) :
    ‖operatorFieldApply (I := I) (M := M) g₀ 2 2 Φp T₀‖ ≤
      B * εa * ‖smoothCcToTensorHs (I := I) (M := M) g₀
        ((2 * p + 2 : ℕ) : ℝ) T₀‖ +
      (CCS 0 p * (1 + R₀) * CJ 0 +
        (CDS0 0 * R₀ * εa * Cg (2 * p + 1) +
          CDS0 0 * (1 + R₀) * KE1 p)) *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀
          ((2 * p + 1 : ℕ) : ℝ) T₀‖ := by
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
      rw [show 0 + (n / 2 + 1) = n / 2 + 1 from by omega] at hd
      rw [hBh_def, zero_add, congrFun hfT_def (n / 2 + 1)]
      exact hd
  have hX : ‖operatorFieldApply (I := I) (M := M) g₀ 2 2 Φp T₀‖ ≤ ‖Φp‖ * Bm :=
    operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_right (I := I) (M := M) g₀ 2 2
      Φp T₀ Bm hBm_nn hBm_pt
  have hΦcore := (hc22 p C₀).1
  rw [← hΦp_def] at hΦcore
  have henvsum : ∀ (k : ℕ), k ≤ 2 * p + 2 →
      ∑ j ∈ Finset.range k, ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
        (∑ j ∈ Finset.range k, CJ j) * fT (2 * p + 1) := by
    intro k hk
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun j hj => ?_)
    have hjk := Finset.mem_range.mp hj
    refine le_trans (hCJ j T₀) ?_
    exact mul_le_mul_of_nonneg_left
      ((congrFun hfT_def j).symm.le.trans (hfT_mono (by omega))) (hCJ_nn j)
  set f₁ : ℝ := fT (2 * p + 1) with hf₁_def
  have hf₁_nn : 0 ≤ f₁ := hfT_nn _
  set u : ℝ := ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * p + 2) T₀‖ with hu_def
  have hu_nn : 0 ≤ u := norm_nonneg _
  have hone_aux : ∀ (X : ℝ), 0 ≤ X → 1 + X * f₁ ≤ (1 + X) * (1 + f₁) := by
    intro X hX
    nlinarith
  have htopC : ‖iteratedCovGrad (I := I) g₀ 2 2 (2 * p) C₀‖ ≤
      (Real.sqrt (Kc (2 * p)) * (1 + ∑ j ∈ Finset.range (2 * p + 2), CJ j)) *
        (1 + f₁) + εa * u := by
    refine le_trans (iteratedCovGrad_le_of_sq_envelope_bound (I := I) (M := M) g₀ Kc hKc_nn εa
      hεa_nn C₀ T₀ henv
      (2 * p)) ?_
    have hs := henvsum (2 * p + 2) (by omega)
    have hCJsum_nn : (0:ℝ) ≤ ∑ j ∈ Finset.range (2 * p + 2), CJ j :=
      Finset.sum_nonneg (fun j _ => hCJ_nn j)
    have h1 : 1 + ∑ j ∈ Finset.range (2 * p + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
        (1 + ∑ j ∈ Finset.range (2 * p + 2), CJ j) * (1 + f₁) := by
      refine le_trans ?_ (hone_aux _ hCJsum_nn)
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg (Kc (2 * p)))
    have hueq : ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * p + 2) T₀‖ = u := rfl
    nlinarith [hεa_nn, hu_nn]
  have hlowC : ∑ b ∈ Finset.range (2 * p), ‖iteratedCovGrad (I := I) g₀ 2 2 b C₀‖ ≤
      (∑ b ∈ Finset.range (2 * p),
        (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2))) *
        (1 + f₁) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun b hb => ?_)
    have hb2p := Finset.mem_range.mp hb
    refine le_trans (iteratedCovGrad_le_of_sq_envelope_bound (I := I) (M := M) g₀ Kc hKc_nn εa
      hεa_nn C₀ T₀ henv b) ?_
    have hs := henvsum (b + 2) (by omega)
    have hCJsum_nn : (0:ℝ) ≤ ∑ j ∈ Finset.range (b + 2), CJ j :=
      Finset.sum_nonneg (fun j _ => hCJ_nn j)
    have h1 : 1 + ∑ j ∈ Finset.range (b + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
        (1 + ∑ j ∈ Finset.range (b + 2), CJ j) * (1 + f₁) := by
      refine le_trans ?_ (hone_aux _ hCJsum_nn)
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg (Kc b))
    have h3 : ‖iteratedCovGrad (I := I) g₀ 0 2 (b + 2) T₀‖ ≤ CJ (b + 2) * f₁ := by
      refine le_trans (hCJ (b + 2) T₀) ?_
      exact mul_le_mul_of_nonneg_left
        ((congrFun hfT_def (b + 2)).symm.le.trans (hfT_mono (by omega)))
        (hCJ_nn (b + 2))
    have h4 := mul_le_mul_of_nonneg_left h3 hεa_nn
    have h2' : Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖) ≤
          Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) *
            (1 + f₁) := by
      simpa only [mul_assoc] using h2
    calc
      Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖) +
          εa * ‖iteratedCovGrad (I := I) g₀ 0 2 (b + 2) T₀‖ ≤
          Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) *
            (1 + f₁) + εa * (CJ (b + 2) * f₁) := add_le_add h2' h4
      _ ≤ Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) *
            (1 + f₁) + εa * CJ (b + 2) * (1 + f₁) := by
        have heps : εa * (CJ (b + 2) * f₁) ≤ εa * CJ (b + 2) * (1 + f₁) := by
          calc
          εa * (CJ (b + 2) * f₁) = (εa * CJ (b + 2)) * f₁ := by ring
          _ ≤ (εa * CJ (b + 2)) * (1 + f₁) :=
            mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hεa_nn (hCJ_nn _))
        exact add_le_add_right heps _
      _ = (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) +
            εa * CJ (b + 2)) * (1 + f₁) := by ring
  have hkey : ‖Φp‖ ≤ εa * u + KE1 p * (1 + f₁) := by
    refine le_trans hΦcore ?_
    have h5 := mul_le_mul_of_nonneg_left hlowC (hc22_nn p)
    rw [hKE1_def]
    let A : ℝ := Real.sqrt (Kc (2 * p)) *
      (1 + ∑ j ∈ Finset.range (2 * p + 2), CJ j)
    let C : ℝ := εa * CJ (2 * p + 2)
    let D : ℝ := c22 p * ∑ b ∈ Finset.range (2 * p),
      (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) +
        εa * CJ (b + 2))
    let F : ℝ := 1 + f₁
    have hF_nn : 0 ≤ F := by dsimp [F]; linarith
    have hC_nn : 0 ≤ C := by exact mul_nonneg hεa_nn (hCJ_nn _)
    have htopC' : ‖iteratedCovGrad (I := I) g₀ 2 2 (2 * p) C₀‖ ≤
        A * F + εa * u := by
      simpa only [A, F] using htopC
    have h5' : c22 p * ∑ b ∈ Finset.range (2 * p),
        ‖iteratedCovGrad (I := I) g₀ 2 2 b C₀‖ ≤ D * F := by
      simpa only [D, F, mul_assoc] using h5
    have hAD : (A + D) * F ≤ (A + C + D) * F :=
      mul_le_mul_of_nonneg_right (by linarith) hF_nn
    change ‖iteratedCovGrad (I := I) g₀ 2 2 (2 * p) C₀‖ +
        c22 p * ∑ b ∈ Finset.range (2 * p),
          ‖iteratedCovGrad (I := I) g₀ 2 2 b C₀‖ ≤
      εa * u + (A + C + D) * F
    calc
      ‖iteratedCovGrad (I := I) g₀ 2 2 (2 * p) C₀‖ +
          c22 p * ∑ b ∈ Finset.range (2 * p),
            ‖iteratedCovGrad (I := I) g₀ 2 2 b C₀‖ ≤
        (A * F + εa * u) + D * F := add_le_add htopC' h5'
      _ = εa * u + (A + D) * F := by ring
      _ ≤ εa * u + (A + C + D) * F := add_le_add_right hAD _
  have hgap := hCg (2 * p + 1) T₀
  have hc1 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p + 1 : ℕ) : ℝ) + 1) T₀‖ =
      fT (2 * p + 2) :=
    (smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
      (bal_two_mul_add_one_cast_high p) T₀).trans
        (congrFun hfT_def (2 * p + 2)).symm
  rw [hc1] at hgap
  have hf₁_eq := Eq.trans hf₁_def (congrFun hfT_def (2 * p + 1))
  have hgap' : u ≤ fT (2 * p + 2) + Cg (2 * p + 1) * f₁ := by
    calc
      u = _ := hu_def
      _ ≤ _ := hgap
      _ = _ := congrArg (fun z : ℝ => fT (2 * p + 2) + Cg (2 * p + 1) * z) hf₁_eq.symm
  have hBm_le_B : Bm ≤ B := min_le_left _ _
  have hBm_le_Bh : Bm ≤ Bh := min_le_right _ _
  have hBh_le : Bh ≤ CDS0 0 * R₀ := by
    rw [hBh_def]
    refine mul_le_mul_of_nonneg_left ?_ (hCDS0_nn 0)
    exact hfT_ball _ (by omega)
  have hBh_le_f₁ : Bh ≤ CDS0 0 * f₁ := by
    rw [hBh_def, hf₁_def]
    refine mul_le_mul_of_nonneg_left ?_ (hCDS0_nn 0)
    exact hfT_mono (by omega)
  have hfinal : ‖Φp‖ * Bm ≤
      B * εa * fT (2 * p + 2) +
        (CDS0 0 * R₀ * εa * Cg (2 * p + 1) + CDS0 0 * (1 + R₀) * KE1 p) * f₁ := by
    have hexp : ‖Φp‖ * Bm ≤ (εa * u + KE1 p * (1 + f₁)) * Bm :=
      mul_le_mul_of_nonneg_right hkey hBm_nn
    have h1 : εa * u * Bm ≤ εa * (fT (2 * p + 2) + Cg (2 * p + 1) * f₁) * Bm := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgap' hεa_nn) hBm_nn
    have h2 : εa * fT (2 * p + 2) * Bm ≤ εa * fT (2 * p + 2) * B :=
      mul_le_mul_of_nonneg_left hBm_le_B (mul_nonneg hεa_nn (hfT_nn _))
    have h3 : εa * (Cg (2 * p + 1) * f₁) * Bm ≤
        εa * (Cg (2 * p + 1) * f₁) * (CDS0 0 * R₀) :=
      mul_le_mul_of_nonneg_left (le_trans hBm_le_Bh hBh_le)
        (mul_nonneg hεa_nn (mul_nonneg (hCg_nn _) hf₁_nn))
    have h4 : KE1 p * 1 * Bm ≤ KE1 p * (CDS0 0 * f₁) := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_left (le_trans hBm_le_Bh hBh_le_f₁) (hKE1_nn p)
    have h5 : KE1 p * f₁ * Bm ≤ KE1 p * f₁ * (CDS0 0 * R₀) :=
      mul_le_mul_of_nonneg_left (le_trans hBm_le_Bh hBh_le)
        (mul_nonneg (hKE1_nn p) hf₁_nn)
    calc
      ‖Φp‖ * Bm ≤ (εa * u + KE1 p * (1 + f₁)) * Bm := hexp
      _ = εa * u * Bm + (KE1 p * 1 * Bm + KE1 p * f₁ * Bm) := by ring
      _ ≤ εa * (fT (2 * p + 2) + Cg (2 * p + 1) * f₁) * Bm +
          (KE1 p * (CDS0 0 * f₁) + KE1 p * f₁ * (CDS0 0 * R₀)) :=
        add_le_add h1 (add_le_add h4 h5)
      _ = (εa * fT (2 * p + 2) * Bm + εa * (Cg (2 * p + 1) * f₁) * Bm) +
          (KE1 p * (CDS0 0 * f₁) + KE1 p * f₁ * (CDS0 0 * R₀)) := by ring
      _ ≤ (εa * fT (2 * p + 2) * B +
          εa * (Cg (2 * p + 1) * f₁) * (CDS0 0 * R₀)) +
          (KE1 p * (CDS0 0 * f₁) + KE1 p * f₁ * (CDS0 0 * R₀)) :=
        add_le_add (add_le_add h2 h3) le_rfl
      _ = B * εa * fT (2 * p + 2) +
          (CDS0 0 * R₀ * εa * Cg (2 * p + 1) +
            CDS0 0 * (1 + R₀) * KE1 p) * f₁ := by ring
  refine le_trans hX ?_
  simp only [hfT_def, hf₁_def] at hfinal
  refine le_trans hfinal ?_
  have hextra : 0 ≤ CCS 0 p * (1 + R₀) * CJ 0 *
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 1 : ℕ) : ℝ) T₀‖ :=
    mul_nonneg (mul_nonneg (mul_nonneg (hCCS_nn 0 p) (by linarith)) (hCJ_nn 0))
      (norm_nonneg _)
  nlinarith [hextra]


end BalLadder

end Spectral
end Analysis
end DifferentialGeometry

end
