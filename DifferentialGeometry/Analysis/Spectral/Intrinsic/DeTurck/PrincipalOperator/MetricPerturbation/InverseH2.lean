import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecificLimits.Normed
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Defs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalOperator.MetricPerturbation.H2
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Application.SecondOrderSobolevBound

noncomputable section

open Bundle Manifold
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private abbrev metricH2 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev rank4H2 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 4 (2 : ℝ)

private abbrev rank4End (g : SmoothRiemannianMetric I M) :=
  rank4H2 (I := I) (M := M) g →L[ℝ] rank4H2 (I := I) (M := M) g

private local instance rank4EndNorm
    (g : SmoothRiemannianMetric I M) :
    NormedAddCommGroup (rank4End (I := I) (M := M) g) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance rank4EndSpace
    (g : SmoothRiemannianMetric I M) :
    NormedSpace ℝ (rank4End (I := I) (M := M) g) :=
  ContinuousLinearMap.toNormedSpace

private lemma inv_add_sub_one_le
    {R : Type*} [NormedRing R] [CompleteSpace R]
    (B : R) (hnorm1 : ‖(1 : R)‖ ≤ 1)
    (hhalf : ‖B‖ ≤ (1 : ℝ) / 2) :
    ‖Ring.inverse (1 + B) - 1‖ ≤ 2 * ‖B‖ := by
  have hB0 : 0 ≤ ‖B‖ := norm_nonneg _
  have hlt : ‖B‖ < 1 := hhalf.trans_lt (by norm_num)
  have hneg : ‖-B‖ < 1 := by
    simpa only [norm_neg] using hlt
  have hu : IsUnit (1 + B) := by
    have h := isUnit_one_sub_of_norm_lt_one (x := -B) hneg
    simpa only [sub_neg_eq_add] using h
  have hinv :
      ‖Ring.inverse (1 + B)‖ ≤ (1 - ‖B‖)⁻¹ := by
    have hseries := tsum_geometric_le_of_norm_lt_one (-B) hneg
    rw [geom_series_eq_inverse (-B) hneg] at hseries
    have hseries' :
        ‖Ring.inverse (1 + B)‖ ≤
          ‖(1 : R)‖ - 1 + (1 - ‖B‖)⁻¹ := by
      simpa only [sub_neg_eq_add, norm_neg] using hseries
    exact hseries'.trans (by linarith)
  have hden : 0 < 1 - ‖B‖ := by
    linarith
  have hinv2 : (1 - ‖B‖)⁻¹ ≤ 2 := by
    have h : (1 : ℝ) * (1 - ‖B‖)⁻¹ ≤ 2 := by
      rw [mul_inv_le_iff₀ hden]
      linarith
    simpa only [one_mul] using h
  have hcorr :
      Ring.inverse (1 + B) - 1 =
        -(Ring.inverse (1 + B) * B) := by
    calc
      _ = Ring.inverse (1 + B) -
          Ring.inverse (1 + B) * (1 + B) := by
            rw [Ring.inverse_mul_cancel (1 + B) hu]
      _ = _ := by noncomm_ring
  rw [hcorr, norm_neg]
  calc
    ‖Ring.inverse (1 + B) * B‖ ≤
        ‖Ring.inverse (1 + B)‖ * ‖B‖ :=
      norm_mul_le _ _
    _ ≤ (1 - ‖B‖)⁻¹ * ‖B‖ :=
      mul_le_mul_of_nonneg_right hinv hB0
    _ ≤ 2 * ‖B‖ :=
      mul_le_mul_of_nonneg_right hinv2 hB0

private lemma inv_add_le_two
    {R : Type*} [NormedRing R] [CompleteSpace R]
    (B : R) (hnorm1 : ‖(1 : R)‖ ≤ 1)
    (hhalf : ‖B‖ ≤ (1 : ℝ) / 2) :
    ‖Ring.inverse (1 + B)‖ ≤ 2 := by
  have hcorr := inv_add_sub_one_le B hnorm1 hhalf
  calc
    ‖Ring.inverse (1 + B)‖ =
        ‖(Ring.inverse (1 + B) - 1) + 1‖ := by
      congr 1
      abel
    _ ≤ ‖Ring.inverse (1 + B) - 1‖ + ‖(1 : R)‖ :=
      norm_add_le _ _
    _ ≤ 2 * ‖B‖ + 1 := add_le_add hcorr hnorm1
    _ ≤ 2 := by linarith

noncomputable def inverseMetricPerturbationCorrectionH2
    (g : SmoothRiemannianMetric I M)
    (T : metricH2 (I := I) (M := M) g) :
    rank4End (I := I) (M := M) g :=
  Ring.inverse (1 + metricPerturbationOperatorH2 (I := I) (M := M) g T) - 1

theorem inverseMetricPerturbationCorrectionH2_mul
    (g : SmoothRiemannianMetric I M)
    (T : metricH2 (I := I) (M := M) g)
    (hT : ‖metricPerturbationOperatorH2 (I := I) (M := M) g T‖ < 1) :
    (1 + inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g T) *
        (1 + metricPerturbationOperatorH2 (I := I) (M := M) g T) = 1 := by
  let B := metricPerturbationOperatorH2 (I := I) (M := M) g T
  have hneg : ‖-B‖ < 1 := by
    simpa only [norm_neg, B] using hT
  have hu : IsUnit (1 + B) := by
    have h := isUnit_one_sub_of_norm_lt_one (x := -B) hneg
    simpa only [sub_neg_eq_add] using h
  rw [inverseMetricPerturbationCorrectionH2]
  change (1 + (Ring.inverse (1 + B) - 1)) * (1 + B) = 1
  have hone : 1 + (Ring.inverse (1 + B) - 1) =
      Ring.inverse (1 + B) := by
    abel
  rw [hone]
  exact Ring.inverse_mul_cancel (1 + B) hu

theorem exists_inverseMetricPerturbationCorrectionH2_norm_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ T : metricH2 (I := I) (M := M) g, ‖T‖ ≤ ρ →
        ‖metricPerturbationOperatorH2 (I := I) (M := M) g T‖ ≤ (1 : ℝ) / 2 ∧
          ‖inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g T‖ ≤ C * ‖T‖ := by
  obtain ⟨C₀, hC₀, hpert⟩ :=
    metricPerturbationOperatorH2_norm_bound (I := I) (M := M) hDim g
  let ρ : ℝ := (2 * (C₀ + 1))⁻¹
  let C : ℝ := 2 * C₀
  have hden : 0 < 2 * (C₀ + 1) := by
    positivity
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    positivity
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T hT
  have hCrho : C₀ * ρ ≤ (1 : ℝ) / 2 := by
    dsimp only [ρ]
    rw [mul_inv_le_iff₀ hden]
    nlinarith
  have hsmall :
      ‖metricPerturbationOperatorH2 (I := I) (M := M) g T‖ ≤ (1 : ℝ) / 2 := by
    calc
      _ ≤ C₀ * ‖T‖ := hpert T
      _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hT hC₀
      _ ≤ _ := hCrho
  refine ⟨hsmall, ?_⟩
  calc
    ‖inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g T‖ ≤
        2 * ‖metricPerturbationOperatorH2 (I := I) (M := M) g T‖ := by
      have hnorm1 :
          ‖(1 : rank4End (I := I) (M := M) g)‖ ≤ 1 := by
        change ‖ContinuousLinearMap.id ℝ
          (rank4H2 (I := I) (M := M) g)‖ ≤ 1
        exact ContinuousLinearMap.norm_id_le
      exact inv_add_sub_one_le
        (metricPerturbationOperatorH2 (I := I) (M := M) g T) hnorm1 hsmall
    _ ≤ 2 * (C₀ * ‖T‖) :=
      mul_le_mul_of_nonneg_left (hpert T) (by norm_num)
    _ = C * ‖T‖ := by
      dsimp only [C]
      ring

theorem exists_inverseMetricPerturbationCorrectionH2_lipschitz_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ T U : metricH2 (I := I) (M := M) g,
        ‖T‖ ≤ ρ → ‖U‖ ≤ ρ →
          ‖inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g T -
              inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g U‖ ≤
            C * ‖T - U‖ := by
  obtain ⟨C₀, hC₀, hpert⟩ :=
    metricPerturbationOperatorH2_norm_bound (I := I) (M := M) hDim g
  let ρ : ℝ := (2 * (C₀ + 1))⁻¹
  let C : ℝ := 4 * C₀
  have hden : 0 < 2 * (C₀ + 1) := by
    positivity
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    positivity
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hCrho : C₀ * ρ ≤ (1 : ℝ) / 2 := by
    dsimp only [ρ]
    rw [mul_inv_le_iff₀ hden]
    nlinarith
  have hsmall :
      ∀ T : metricH2 (I := I) (M := M) g, ‖T‖ ≤ ρ →
        ‖metricPerturbationOperatorH2 (I := I) (M := M) g T‖ ≤ (1 : ℝ) / 2 := by
    intro T hT
    calc
      _ ≤ C₀ * ‖T‖ := hpert T
      _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hT hC₀
      _ ≤ _ := hCrho
  have hnorm1 :
      ‖(1 : rank4End (I := I) (M := M) g)‖ ≤ 1 := by
    change ‖ContinuousLinearMap.id ℝ
      (rank4H2 (I := I) (M := M) g)‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U hT hU
  have hhalfT := hsmall T hT
  have hhalfU := hsmall U hU
  have hltT :
      ‖metricPerturbationOperatorH2 (I := I) (M := M) g T‖ < 1 :=
    hhalfT.trans_lt (by norm_num)
  have hltU :
      ‖metricPerturbationOperatorH2 (I := I) (M := M) g U‖ < 1 :=
    hhalfU.trans_lt (by norm_num)
  have hunitT :
      IsUnit (1 + metricPerturbationOperatorH2 (I := I) (M := M) g T) := by
    have h := isUnit_one_sub_of_norm_lt_one
      (x := -metricPerturbationOperatorH2 (I := I) (M := M) g T) (by
        simpa only [norm_neg] using hltT)
    simpa only [sub_neg_eq_add] using h
  have hunitU :
      IsUnit (1 + metricPerturbationOperatorH2 (I := I) (M := M) g U) := by
    have h := isUnit_one_sub_of_norm_lt_one
      (x := -metricPerturbationOperatorH2 (I := I) (M := M) g U) (by
        simpa only [norm_neg] using hltU)
    simpa only [sub_neg_eq_add] using h
  have hinvT :
      ‖Ring.inverse
          (1 + metricPerturbationOperatorH2 (I := I) (M := M) g T)‖ ≤ 2 :=
    inv_add_le_two
      (metricPerturbationOperatorH2 (I := I) (M := M) g T) hnorm1 hhalfT
  have hinvU :
      ‖Ring.inverse
          (1 + metricPerturbationOperatorH2 (I := I) (M := M) g U)‖ ≤ 2 :=
    inv_add_le_two
      (metricPerturbationOperatorH2 (I := I) (M := M) g U) hnorm1 hhalfU
  have hmid :
      ‖(1 + metricPerturbationOperatorH2 (I := I) (M := M) g U) -
          (1 + metricPerturbationOperatorH2 (I := I) (M := M) g T)‖ ≤
        C₀ * ‖T - U‖ := by
    calc
      _ = ‖metricPerturbationOperatorH2 (I := I) (M := M) g U -
          metricPerturbationOperatorH2 (I := I) (M := M) g T‖ := by
        congr 1
        abel
      _ = ‖metricPerturbationOperatorH2 (I := I) (M := M) g (U - T)‖ := by
        rw [map_sub]
      _ = ‖metricPerturbationOperatorH2 (I := I) (M := M) g (T - U)‖ := by
        have hsub : U - T = -(T - U) := by abel
        rw [hsub, map_neg, norm_neg]
      _ ≤ C₀ * ‖T - U‖ := hpert (T - U)
  have hcorr :
      inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g T -
          inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g U =
        Ring.inverse (1 + metricPerturbationOperatorH2 (I := I) (M := M) g T) -
          Ring.inverse (1 + metricPerturbationOperatorH2 (I := I) (M := M) g U) := by
    rw [inverseMetricPerturbationCorrectionH2, inverseMetricPerturbationCorrectionH2]
    abel
  rw [hcorr, Ring.inverse_sub_inverse
    (show IsUnit (1 + metricPerturbationOperatorH2 (I := I) (M := M) g T) ↔
        IsUnit (1 + metricPerturbationOperatorH2 (I := I) (M := M) g U) from
      ⟨fun _ => hunitU, fun _ => hunitT⟩)]
  let X : rank4End (I := I) (M := M) g :=
    Ring.inverse (1 + metricPerturbationOperatorH2 (I := I) (M := M) g T)
  let Y : rank4End (I := I) (M := M) g :=
    (1 + metricPerturbationOperatorH2 (I := I) (M := M) g U) -
      (1 + metricPerturbationOperatorH2 (I := I) (M := M) g T)
  let Z : rank4End (I := I) (M := M) g :=
    Ring.inverse (1 + metricPerturbationOperatorH2 (I := I) (M := M) g U)
  have hX : ‖X‖ ≤ 2 := by
    simpa only [X] using hinvT
  have hY : ‖Y‖ ≤ C₀ * ‖T - U‖ := by
    simpa only [Y] using hmid
  have hZ : ‖Z‖ ≤ 2 := by
    simpa only [Z] using hinvU
  change ‖X * Y * Z‖ ≤ C * ‖T - U‖
  calc
    _ ≤ ‖X * Y‖ * ‖Z‖ :=
      norm_mul_le (X * Y) Z
    _ ≤ (‖X‖ * ‖Y‖) * ‖Z‖ :=
      mul_le_mul_of_nonneg_right
        (norm_mul_le X Y)
        (norm_nonneg _)
    _ ≤ (2 * ‖Y‖) * ‖Z‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hX (norm_nonneg _))
        (norm_nonneg _)
    _ ≤ (2 * (C₀ * ‖T - U‖)) * ‖Z‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hY (by norm_num))
        (norm_nonneg _)
    _ ≤ (2 * (C₀ * ‖T - U‖)) * 2 := by
      exact mul_le_mul_of_nonneg_left hZ
        (mul_nonneg (by norm_num) (mul_nonneg hC₀ (norm_nonneg _)))
    _ = C * ‖T - U‖ := by
      dsimp only [C]
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
