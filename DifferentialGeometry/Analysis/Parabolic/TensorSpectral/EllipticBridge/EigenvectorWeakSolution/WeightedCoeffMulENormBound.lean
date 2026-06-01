import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartWeightedMemLp

/-!
# Explicit-norm bound for a `C^∞`-coefficient weighted-`L²` product

The qualitative lemma `memLp_weighted_contDiffOn_mul` establishes that, for a
coefficient `c : EuclN → ℝ` that is `C^∞` on the open chart target and an `L²`
function `w` supported (almost everywhere, for the chart-pulled weighted measure)
in a compact subset `K` of the chart target, the product `fun y => c y * w y` is
again `MemLp 2` with respect to the chart-pulled weighted measure restricted to
`chartTargetEuclid α`.

Its proof internally extracts a sup bound `∃ C ≥ 0, ∀ y ∈ K, ‖c y‖ ≤ C` for the
coefficient on the compact set `K` — via `IsCompact.bddAbove_image` — but then
discards that constant, recording only the membership conclusion.

This file records the quantitative twin. The same sup bound `C` controls the
`eLpNorm` of the product:

```
eLpNorm (fun y => c y * w y) 2 μw ≤ ENNReal.ofReal C * eLpNorm w 2 μw,
```

where `μw = (chartPulledWeightedMeasure g α).restrict (chartTargetEuclid α)`. On
`K` the pointwise bound `‖c y‖ ≤ C` gives `‖c y * w y‖ ≤ ‖C • w y‖`; off `K` the
function `w` vanishes almost everywhere, so both sides vanish. Monotonicity of
`eLpNorm` under an almost-everywhere norm domination, together with the
homogeneity `eLpNorm (C • w) 2 μw = ‖C‖ₑ * eLpNorm w 2 μw` and the conversion
`‖C‖ₑ = ENNReal.ofReal C` for `C ≥ 0`, yields the stated estimate.

## Main result

* `eLpNorm_weighted_contDiffOn_mul_le` — the directly-usable quantitative form:
  the `eLpNorm` of the `C^∞`-coefficient product is bounded by an explicit
  constant (the coefficient's sup over `K`) times the `eLpNorm` of `w`.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

section ExplicitNormBound

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

set_option linter.unusedVariables false

/-- **Explicit-norm bound for a `C^∞`-coefficient weighted-`L²` product.** Let
`c : EuclN → ℝ` be `C^∞` on the open chart target `chartTargetEuclid α`, let
`w : EuclN → ℝ` be `MemLp 2` with respect to the chart-pulled weighted measure
restricted to `chartTargetEuclid α`, and suppose `w` vanishes almost everywhere
(with respect to that weighted restricted measure) off a compact subset
`K ⊆ chartTargetEuclid α`. Then there is a nonnegative constant `C` with

```
eLpNorm (fun y => c y * w y) 2 μw ≤ ENNReal.ofReal C * eLpNorm w 2 μw,
```

where `μw = (chartPulledWeightedMeasure g α).restrict (chartTargetEuclid α)`.

The constant `C` is the sup of `‖c‖` over the compact set `K`. On `K` the
pointwise bound `‖c y‖ ≤ C` gives `‖c y * w y‖ ≤ ‖C • w y‖`; off `K` the function
`w` vanishes almost everywhere, so both `c y * w y` and `C • w y` vanish.
Monotonicity of `eLpNorm` under an almost-everywhere norm domination, the
homogeneity `eLpNorm (C • w) 2 μw = ‖C‖ₑ * eLpNorm w 2 μw`, and the conversion
`‖C‖ₑ = ENNReal.ofReal C` for `C ≥ 0` give the estimate.

This is the quantitative twin of `memLp_weighted_contDiffOn_mul`: that lemma
records only the `MemLp` membership of the product; this lemma exposes the
explicit constant controlling its `eLpNorm`. The signature deliberately mirrors
that companion (same hypothesis block `hc`, `hK_*`, `hw`, `hw_zero`); the
measurability hypothesis `hK_meas` and the membership hypothesis `hw` are kept
for that parity even though the `eLpNorm` estimate, established by pointwise
domination, does not consume them. -/
theorem eLpNorm_weighted_contDiffOn_mul_le
    (g : SmoothRiemannianMetric I M) (α : M)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K) (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    {w : EuclN → ℝ}
    (hw : MemLp w 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)))
    (hw_zero : ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ K → w y = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (fun y => c y * w y) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          eLpNorm w 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  have hcontOn_K : ContinuousOn c K := hc.continuousOn.mono hK_in
  have hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ‖c y‖ ≤ C := by
    by_cases hK_empty : K = ∅
    · exact ⟨0, le_refl _, fun y hy => absurd (hK_empty ▸ hy) (Set.notMem_empty y)⟩
    · obtain ⟨C₀, hC₀⟩ := hK_compact.bddAbove_image hcontOn_K.norm
      exact ⟨max C₀ 0, le_max_right _ _,
        fun y hy => (hC₀ ⟨y, hy, rfl⟩).trans (le_max_left _ _)⟩
  obtain ⟨C, hC_nn, hC_bd⟩ := hbdd
  refine ⟨C, hC_nn, ?_⟩
  have h_dom : ∀ᵐ y ∂μw, ‖c y * w y‖ ≤ ‖(C : ℝ) • w y‖ := by
    filter_upwards [hw_zero] with y hy
    by_cases hyK : y ∈ K
    · have hlhs : ‖c y * w y‖ = ‖c y‖ * ‖w y‖ := norm_mul _ _
      have hrhs : ‖(C : ℝ) • w y‖ = C * ‖w y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC_nn]
      rw [hlhs, hrhs]
      exact mul_le_mul_of_nonneg_right (hC_bd y hyK) (norm_nonneg _)
    · rw [hy hyK, mul_zero, smul_zero, norm_zero]
  have h_mono :
      eLpNorm (fun y => c y * w y) 2 μw ≤ eLpNorm (fun y => (C : ℝ) • w y) 2 μw :=
    eLpNorm_mono_ae (μ := μw) h_dom
  have h_smul :
      eLpNorm (fun y => (C : ℝ) • w y) 2 μw
        = ENNReal.ofReal C * eLpNorm w 2 μw := by
    have h := eLpNorm_const_smul (μ := μw) (p := 2) (C : ℝ) w
    rw [Real.enorm_of_nonneg hC_nn] at h
    simpa only [Pi.smul_apply] using h
  calc
    eLpNorm (fun y => c y * w y) 2 μw
        ≤ eLpNorm (fun y => (C : ℝ) • w y) 2 μw := h_mono
    _ = ENNReal.ofReal C * eLpNorm w 2 μw := h_smul

/-- **Uniform-constant explicit-norm bound for a `C^∞`-coefficient weighted-`L²`
product.** Let `c : EuclN → ℝ` be `C^∞` on the open chart target
`chartTargetEuclid α` and let `K ⊆ chartTargetEuclid α` be compact. Then there is
a single nonnegative constant `C` — the sup of `‖c‖` over `K`, depending only on
`c` and `K` — such that for *every* `w : EuclN → ℝ` that is `MemLp 2` with
respect to the chart-pulled weighted measure restricted to `chartTargetEuclid α`
and vanishes almost everywhere (for that measure) off `K`,

```
eLpNorm (fun y => c y * w y) 2 μw ≤ ENNReal.ofReal C * eLpNorm w 2 μw,
```

where `μw = (chartPulledWeightedMeasure g α).restrict (chartTargetEuclid α)`.

This is the constant-uniform form of `eLpNorm_weighted_contDiffOn_mul_le`: the
constant of that per-`w` bound is the coefficient's sup over the compact set `K`,
which does not depend on `w`, so it can be exhibited once, before the
universally quantified `w`. -/
theorem eLpNorm_weighted_contDiffOn_mul_le_uniform
    (g : SmoothRiemannianMetric I M) (α : M)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K) (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ w : EuclN → ℝ,
        MemLp w 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α)) →
        (∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)), y ∉ K → w y = 0) →
        eLpNorm (fun y => c y * w y) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            eLpNorm w 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  have hcontOn_K : ContinuousOn c K := hc.continuousOn.mono hK_in
  have hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ‖c y‖ ≤ C := by
    by_cases hK_empty : K = ∅
    · exact ⟨0, le_refl _, fun y hy => absurd (hK_empty ▸ hy) (Set.notMem_empty y)⟩
    · obtain ⟨C₀, hC₀⟩ := hK_compact.bddAbove_image hcontOn_K.norm
      exact ⟨max C₀ 0, le_max_right _ _,
        fun y hy => (hC₀ ⟨y, hy, rfl⟩).trans (le_max_left _ _)⟩
  obtain ⟨C, hC_nn, hC_bd⟩ := hbdd
  refine ⟨C, hC_nn, fun w hw hw_zero => ?_⟩
  have h_dom : ∀ᵐ y ∂μw, ‖c y * w y‖ ≤ ‖(C : ℝ) • w y‖ := by
    filter_upwards [hw_zero] with y hy
    by_cases hyK : y ∈ K
    · have hlhs : ‖c y * w y‖ = ‖c y‖ * ‖w y‖ := norm_mul _ _
      have hrhs : ‖(C : ℝ) • w y‖ = C * ‖w y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC_nn]
      rw [hlhs, hrhs]
      exact mul_le_mul_of_nonneg_right (hC_bd y hyK) (norm_nonneg _)
    · rw [hy hyK, mul_zero, smul_zero, norm_zero]
  have h_mono :
      eLpNorm (fun y => c y * w y) 2 μw ≤ eLpNorm (fun y => (C : ℝ) • w y) 2 μw :=
    eLpNorm_mono_ae (μ := μw) h_dom
  have h_smul :
      eLpNorm (fun y => (C : ℝ) • w y) 2 μw
        = ENNReal.ofReal C * eLpNorm w 2 μw := by
    have h := eLpNorm_const_smul (μ := μw) (p := 2) (C : ℝ) w
    rw [Real.enorm_of_nonneg hC_nn] at h
    simpa only [Pi.smul_apply] using h
  calc
    eLpNorm (fun y => c y * w y) 2 μw
        ≤ eLpNorm (fun y => (C : ℝ) • w y) 2 μw := h_mono
    _ = ENNReal.ofReal C * eLpNorm w 2 μw := h_smul

end ExplicitNormBound

section ElaborationTest

variable (g : SmoothRiemannianMetric I M) (α : M)

example {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K) (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    {w : EuclN → ℝ}
    (hw : MemLp w 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)))
    (hw_zero : ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ K → w y = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (fun y => c y * w y) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          eLpNorm w 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α)) :=
  eLpNorm_weighted_contDiffOn_mul_le (I := I) (M := M) g α hc
    hK_compact hK_meas hK_in hw hw_zero

end ElaborationTest

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
