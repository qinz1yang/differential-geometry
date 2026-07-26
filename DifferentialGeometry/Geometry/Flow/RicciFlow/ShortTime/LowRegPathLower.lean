import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffUniformBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2H3Principal
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H1H2AppCc

/-!
# Low-regularity lower Ricci--DeTurck path arms

This module contains the dimension-three Sobolev estimate used after the
Ricci--DeTurck path slope has been split into its order-zero and order-one
coefficient arms.  Production of those coefficients from the low-regularity
metric family remains in the coefficient layer.
-/

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [T2Space M] [SigmaCompactSpace M]

/-- In dimension three, uniformly controlled order-zero and order-one
coefficient arms act from spectral `H2` to spectral `H1`.

The order-zero coefficient needs a pointwise bound and one `L2` covariant
derivative.  The order-one coefficient needs a pointwise bound and its
covariant derivatives through order two. -/
theorem lower_coeff_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ₀ : SmoothCcTensor g 2 2) (Φ₁ : SmoothCcTensor g 3 2)
        (U : SmoothCcTensor g 0 2) (B₀ B₀' B₁ : ℝ),
        0 ≤ B₀ → 0 ≤ B₀' → 0 ≤ B₁ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 2 2 x
              (Φ₀.toSection x) ≤ B₀ ^ 2) →
        ‖covGrad (I := I) (M := M) g 2 2 Φ₀‖ ≤ B₀' →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 3 2 x
              (Φ₁.toSection x) ≤ B₁ ^ 2) →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 3 2 j Φ₁‖ ^ 2) ≤ B₁ ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
            (appCc (I := I) (M := M) g 2 2 Φ₀ U +
              appCc (I := I) (M := M) g 3 2 Φ₁
                (covGrad (I := I) (M := M) g 0 2 U))‖ ≤
          C * (B₀ + B₀' + B₁) *
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
  obtain ⟨C₀, hC₀, hzero⟩ := appCc_c1_h2_h1 (I := I) (M := M) hDim g 2 2
  obtain ⟨C₁, hC₁, hone⟩ := appCc_h2_cov_h1 (I := I) (M := M) hDim g 1 2
  refine ⟨C₀ + C₁, add_nonneg hC₀ hC₁, ?_⟩
  intro Φ₀ Φ₁ U B₀ B₀' B₁ hB₀ hB₀' hB₁ hΦ₀ hΦ₀' hΦ₁ hΦ₁'
  have hzero' := hzero Φ₀ U B₀ B₀' hB₀ hB₀' hΦ₀ hΦ₀'
  have hone' := hone Φ₁ U B₁ hB₁ hΦ₁ hΦ₁'
  have hsum : 0 ≤ B₀ + B₀' + B₁ := by positivity
  have hnorm : 0 ≤
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := norm_nonneg _
  rw [ccTensorToHs_add]
  calc
    _ ≤
        ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
            (appCc (I := I) (M := M) g 2 2 Φ₀ U)‖ +
          ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
            (appCc (I := I) (M := M) g 3 2 Φ₁
              (covGrad (I := I) (M := M) g 0 2 U))‖ := norm_add_le _ _
    _ ≤ C₀ * (B₀ + B₀') *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ +
        C₁ * B₁ *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ :=
      add_le_add hzero' hone'
    _ ≤ C₀ * (B₀ + B₀' + B₁) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ +
        C₁ * (B₀ + B₀' + B₁) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) hC₀) hnorm
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) hC₁) hnorm
    _ = (C₀ + C₁) * (B₀ + B₀' + B₁) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by ring

/-- In dimension three, integral `H1` control of the order-zero coefficient
and integral `H2` control of the order-one coefficient are sufficient for the
lower Ricci--DeTurck path arms to act from spectral `H2` to spectral `H1`.

Unlike `lower_coeff_h1`, this statement has no pointwise hypothesis on the
order-zero coefficient.  The pointwise bound needed by the order-one arm is a
consequence of its mixed-tensor `H2` jet. -/
theorem lower_jet_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ₀ : SmoothCcTensor g 2 2) (Φ₁ : SmoothCcTensor g 3 2)
        (U : SmoothCcTensor g 0 2) (A₀ A₁ : ℝ),
        0 ≤ A₀ → 0 ≤ A₁ →
        (∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g 2 2 j Φ₀‖ ^ 2) ≤ A₀ ^ 2 →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 3 2 j Φ₁‖ ^ 2) ≤ A₁ ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
            (appCc (I := I) (M := M) g 2 2 Φ₀ U +
              appCc (I := I) (M := M) g 3 2 Φ₁
                (covGrad (I := I) (M := M) g 0 2 U))‖ ≤
          C * (A₀ + A₁) *
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
  obtain ⟨C₀, hC₀, hzero⟩ := appCc_h1_h2_h1 (I := I) (M := M) hDim g 2 2
  obtain ⟨C₁, hC₁, hone⟩ := appCc_h2_cov_h1 (I := I) (M := M) hDim g 1 2
  obtain ⟨Cp, hCp, hp⟩ :=
    DifferentialGeometry.PDE.RicciFlow.
      exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
        (I := I) (M := M) g 3 2
  let K : ℝ := 1 + Cp
  refine ⟨C₀ + C₁ * K, add_nonneg hC₀ (mul_nonneg hC₁ (by dsimp [K]; linarith)), ?_⟩
  intro Φ₀ Φ₁ U A₀ A₁ hA₀ hA₁ hΦ₀ hΦ₁
  have hK : 0 ≤ K := by dsimp [K]; linarith
  have hKone : 1 ≤ K := by dsimp [K]; linarith
  have hzero' := hzero Φ₀ U A₀ hA₀ hΦ₀
  have hrange :
      Finset.range (Module.finrank ℝ E / 2 + 2) = Finset.range 3 := by
    rw [hDim]
  have hpoint : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 3 2 x
          (Φ₁.toSection x) ≤ (K * A₁) ^ 2 := by
    intro x
    have hpx := hp Φ₁ x
    rw [hrange] at hpx
    calc
      riemannianFiberNormSq (I := I) (M := M) g 3 2 x
          (Φ₁.toSection x)
          ≤ Cp ^ 2 * (∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g 3 2 j Φ₁‖ ^ 2) := hpx
      _ ≤ Cp ^ 2 * A₁ ^ 2 :=
        mul_le_mul_of_nonneg_left hΦ₁ (sq_nonneg Cp)
      _ = (Cp * A₁) ^ 2 := by ring
      _ ≤ (K * A₁) ^ 2 := by
        apply pow_le_pow_left₀ (mul_nonneg hCp hA₁)
        exact mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) hA₁
  have hjet : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 3 2 j Φ₁‖ ^ 2) ≤ (K * A₁) ^ 2 := by
    refine hΦ₁.trans ?_
    have hA₁K : A₁ ≤ K * A₁ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hKone hA₁
    exact pow_le_pow_left₀ hA₁ hA₁K 2
  have hone' := hone Φ₁ U (K * A₁) (mul_nonneg hK hA₁) hpoint hjet
  have hnorm : 0 ≤
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := norm_nonneg _
  rw [ccTensorToHs_add]
  calc
    _ ≤
        ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
            (appCc (I := I) (M := M) g 2 2 Φ₀ U)‖ +
          ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
            (appCc (I := I) (M := M) g 3 2 Φ₁
              (covGrad (I := I) (M := M) g 0 2 U))‖ := norm_add_le _ _
    _ ≤ C₀ * A₀ *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ +
        C₁ * (K * A₁) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ :=
      add_le_add hzero' hone'
    _ ≤ C₀ * (A₀ + A₁) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ +
        (C₁ * K) * (A₀ + A₁) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) hC₀) hnorm
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by nlinarith) (mul_nonneg hC₁ hK)) hnorm
    _ = (C₀ + C₁ * K) * (A₀ + A₁) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
