import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.LinearTerms
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.Embedding.H2PointwiseUniform
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.Bochner.LaplacianIterateLadder
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Application.MixedTensorSecondOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Path.RemainderConvexBounds

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private lemma two_mul_le_eps {η x y : ℝ} (hη : 0 < η) :
    2 * x * y ≤ η * x ^ 2 + η⁻¹ * y ^ 2 := by
  have hinv : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  have hs := mul_nonneg hinv (sq_nonneg (η * x - y))
  have hexpand :
      η⁻¹ * (η * x - y) ^ 2 =
        η * x ^ 2 - 2 * x * y + η⁻¹ * y ^ 2 := by
    field_simp [ne_of_gt hη]
    ring
  rw [hexpand] at hs
  linarith

theorem low1_pair_h4_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ C0 C1 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T : SmoothCcTensor g 0 2)
          (hδ : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T) δ₀)
          (hδZ : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g
              (0 : SmoothCcTensor g 0 2)) δ₀)
          {R : ℝ}, 0 ≤ R → R ≤ 1 →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
          let D1 := ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M) g gBase T 0
            hδ₀_lt hδ hδ₀_lt hδZ
          let Y := operatorFieldApply (I := I) (M := M) g 3 2 D1
            (iteratedCovGrad (I := I) g 0 2 1 T)
          2 * |tensorL2Inner (I := I) (M := M) g 0 2
              (oneMinusConnLapSmooth (I := I) g 0 2
                (oneMinusConnLapSmooth (I := I) g 0 2 T)).toFun
              (oneMinusConnLapSmooth (I := I) g 0 2 Y).toFun| ≤
            C0 * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ *
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ +
              C1 * R *
                ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 := by
  classical
  obtain ⟨B0, B1, hB0, hB1, hcoeff⟩ :=
    ricciDeTurckRemainderFirstOrderPathIntegral_h2_uniform_bound (I := I) (M := M) hDim gBase hΛ
      hδ₀_nonneg hδ₀_lt
  obtain ⟨Capp, hCapp, happ⟩ :=
    operatorFieldApplication_h23_h2_uniform (I := I) (M := M) hDim gBase hΛ
  let C0 : ℝ := 2 * Capp * B0 1
  let C1 : ℝ := 2 * Capp * B1 1
  have hC0 : 0 ≤ C0 := by
    dsimp only [C0]
    exact mul_nonneg (mul_nonneg (by norm_num) hCapp) (hB0 1 zero_le_one)
  have hC1 : 0 ≤ C1 := by
    dsimp only [C1]
    exact mul_nonneg (mul_nonneg (by norm_num) hCapp) (hB1 1 zero_le_one)
  refine ⟨C0, C1, hC0, hC1, ?_⟩
  intro g hEq hjet T hδ hδZ R hR hR1 hT2
  let D1 : SmoothCcTensor g 3 2 :=
    ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M) g gBase T 0
      hδ₀_lt hδ hδ₀_lt hδZ
  let Y : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 3 2 D1
      (iteratedCovGrad (I := I) g 0 2 1 T)
  let x : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let z : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  let A : ℝ := B0 1 + B1 1 * y
  have hx : 0 ≤ x := norm_nonneg _
  have hy : 0 ≤ y := norm_nonneg _
  have hz : 0 ≤ z := norm_nonneg _
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact add_nonneg (hB0 1 zero_le_one)
      (mul_nonneg (hB1 1 zero_le_one) hy)
  have hT2one : x ≤ 1 := by
    exact hT2.trans hR1
  have hzeroHs (σ : ℝ) :
      ccTensorToHs (I := I) (M := M) g 2 σ
          (0 : SmoothCcTensor g 0 2) = 0 := by
    have h := ccTensorToHs_smul (I := I) (M := M) g 2 σ 0 T
    simpa using h
  have hD1 :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 3 2 j D1‖ ^ 2) ≤ A ^ 2 := by
    have hraw := hcoeff g hEq hjet T 0 hδ hδZ 1 y
      zero_le_one hy hT2one (by rw [hzeroHs, norm_zero]; exact zero_le_one)
      (le_refl y) (by rw [hzeroHs, norm_zero]; exact hy)
    simpa only [D1, A, x, y] using hraw
  have hY :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
        Capp * A * y := by
    simpa only [Y, D1, y] using happ g hEq hjet D1 T A hA hD1
  let LT : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 T
  let L2T : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 LT
  let LY : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 Y
  have hL2T : ‖L2T‖ = z := by
    have heven := smoothCcToTensorHs_even_norm_eq_toL2_iter
      (I := I) (M := M) g 2 T
    change ‖smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) T‖ =
      ‖SmoothCcTensor.toL2 L2T‖ at heven
    rw [SmoothCcTensor.norm_toL2] at heven
    simpa only [z,
      norm_ccHs_eq_smoothHs] using heven.symm
  have hLY : ‖LY‖ =
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ := by
    have heven := smoothCcToTensorHs_even_norm_eq_toL2_iter
      (I := I) (M := M) g 1 Y
    change ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) Y‖ =
      ‖SmoothCcTensor.toL2 LY‖ at heven
    rw [SmoothCcTensor.norm_toL2] at heven
    simpa only [
      norm_ccHs_eq_smoothHs] using heven.symm
  have hpair :
      |tensorL2Inner (I := I) (M := M) g 0 2 L2T.toFun LY.toFun| ≤
        ‖L2T‖ * ‖LY‖ := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M) L2T LY]
    exact abs_real_inner_le_norm L2T LY
  have hinterp : y ^ 2 ≤ x * z := by
    dsimp only [x, y, z]
    exact ccTensorToHs_norm_three_sq_le_norm_two_mul_norm_four
      (I := I) (M := M) g 2 T
  have hy2Rz : y ^ 2 ≤ R * z := by
    exact hinterp.trans (mul_le_mul_of_nonneg_right hT2 hz)
  change
    2 * |tensorL2Inner (I := I) (M := M) g 0 2 L2T.toFun LY.toFun| ≤
      C0 * z * y + C1 * R * z ^ 2
  calc
    2 * |tensorL2Inner (I := I) (M := M) g 0 2 L2T.toFun LY.toFun|
        ≤ 2 * (‖L2T‖ * ‖LY‖) :=
      mul_le_mul_of_nonneg_left hpair (by norm_num)
    _ ≤ 2 * (z * (Capp * A * y)) := by
      rw [hL2T, hLY]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hY hz) (by norm_num)
    _ = C0 * z * y + C1 * z * y ^ 2 := by
      dsimp only [C0, C1, A]
      ring
    _ ≤ C0 * z * y + C1 * z * (R * z) := by
      exact add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left hy2Rz (mul_nonneg hC1 hz))
    _ = C0 * z * y + C1 * R * z ^ 2 := by ring

theorem low1_pair_abs_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1) :
    ∀ {η : ℝ}, 0 < η →
      ∃ ρ G : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 0 ≤ G ∧
        ∀ g : SmoothRiemannianMetric I M,
          MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
          (∀ a : ℕ, a ≤ 3 →
            MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
          ∀ (T : SmoothCcTensor g 0 2)
            (hδ : gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g T) δ₀)
            (hδZ : gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g
                (0 : SmoothCcTensor g 0 2)) δ₀)
            {R : ℝ}, 0 ≤ R → R ≤ ρ →
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
            let D1 := ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M) g gBase T 0
              hδ₀_lt hδ hδ₀_lt hδZ
            let Y := operatorFieldApply (I := I) (M := M) g 3 2 D1
              (iteratedCovGrad (I := I) g 0 2 1 T)
            2 * |tensorL2Inner (I := I) (M := M) g 0 2
                (oneMinusConnLapSmooth (I := I) g 0 2
                  (oneMinusConnLapSmooth (I := I) g 0 2 T)).toFun
                (oneMinusConnLapSmooth (I := I) g 0 2 Y).toFun| ≤
              η * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
                G * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 := by
  intro η hη
  obtain ⟨C0, C1, hC0, hC1, hpair⟩ :=
    low1_pair_h4_uniform (I := I) (M := M) hDim gBase hΛ
      hδ₀_nonneg hδ₀_lt
  let e : ℝ := η / 2
  let D : ℝ := 2 * (C1 + 1)
  let ρ : ℝ := min 1 (η / D)
  let G : ℝ := e⁻¹ * C0 ^ 2
  have he : 0 < e := by
    dsimp only [e]
    positivity
  have hD : 0 < D := by
    dsimp only [D]
    positivity
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    exact lt_min zero_lt_one (div_pos hη hD)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hG : 0 ≤ G := by
    dsimp only [G]
    exact mul_nonneg (inv_nonneg.mpr he.le) (sq_nonneg C0)
  refine ⟨ρ, G, hρ, hρ1, hG, ?_⟩
  intro g hEq hjet T hδ hδZ R hR hRρ hT2
  let D1 : SmoothCcTensor g 3 2 :=
    ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M) g gBase T 0
      hδ₀_lt hδ hδ₀_lt hδZ
  let Y : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 3 2 D1
      (iteratedCovGrad (I := I) g 0 2 1 T)
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let z : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  have hy : 0 ≤ y := norm_nonneg _
  have hz : 0 ≤ z := norm_nonneg _
  have hR1 : R ≤ 1 := hRρ.trans hρ1
  have hquant := hpair g hEq hjet T hδ hδZ hR hR1 hT2
  have hRsmall : R ≤ η / D := hRρ.trans (min_le_right _ _)
  have hRD : R * D ≤ η := (le_div_iff₀ hD).mp hRsmall
  have hC1R : C1 * R ≤ e := by
    dsimp only [D] at hRD
    dsimp only [e]
    nlinarith [mul_nonneg hC1 hR]
  have hlin : C0 * z * y ≤ e * z ^ 2 + G * y ^ 2 := by
    calc
      C0 * z * y ≤ 2 * z * (C0 * y) := by
        nlinarith [mul_nonneg hC0 (mul_nonneg hz hy)]
      _ ≤ e * z ^ 2 + e⁻¹ * (C0 * y) ^ 2 := two_mul_le_eps he
      _ = e * z ^ 2 + G * y ^ 2 := by
        dsimp only [G]
        ring
  have htop : C1 * R * z ^ 2 ≤ e * z ^ 2 :=
    mul_le_mul_of_nonneg_right hC1R (sq_nonneg z)
  change
    2 * |tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmooth (I := I) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2 T)).toFun
        (oneMinusConnLapSmooth (I := I) g 0 2 Y).toFun| ≤
      η * z ^ 2 + G * y ^ 2
  calc
    _ ≤ C0 * z * y + C1 * R * z ^ 2 := by
      simpa only [D1, Y, y, z] using hquant
    _ ≤ (e * z ^ 2 + G * y ^ 2) + e * z ^ 2 :=
      add_le_add hlin htop
    _ = η * z ^ 2 + G * y ^ 2 := by
      dsimp only [e]
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
