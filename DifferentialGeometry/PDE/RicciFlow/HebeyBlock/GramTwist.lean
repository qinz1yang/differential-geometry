import DifferentialGeometry.Metric.Basic
import DifferentialGeometry.Integral.Connection.ChartMetric
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedNorm
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNorm

namespace DifferentialGeometry.PDE.RicciFlow.HebeyBlock

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- Existence of a strictly positive two-sided bound governing the
fibrewise Gram-twist estimate for `(r, s)`-tensor fields.

# Blueprint intent

Let `g : SmoothRiemannianMetric I M` be a smooth Riemannian metric on a
closed manifold, and let `T_x : (E*)^r ⊗ E^s → ℝ` be the fibrewise
`(r, s)`-tensor at `x : M`. The metric `g_x` induces two natural norms on
this fibre:

1. the **intrinsic** fibre norm `‖T_x‖_g` obtained by raising / lowering
   indices through `g_x` and contracting against itself
   (in coordinates: `g^{i_1 j_1} ⋯ g^{i_r j_r} g_{k_1 l_1} ⋯ g_{k_s l_s}
   · T^{k_1 ⋯ k_s}_{i_1 ⋯ i_r} · T^{l_1 ⋯ l_s}_{j_1 ⋯ j_r}`);
2. the **chart-frame** fibre norm `‖T_x‖_{δ,α}` obtained by treating the
   chart-frame components of `T_x` (relative to the orthonormal frame of
   the model fibre `E`) as a tuple in `ℝ^{n^(r+s)}` and taking its
   Euclidean norm.

The Gram-twist estimate asserts the **two-sided comparison**
```
c · ‖T_x‖_{δ,α}^2 ≤ ‖T_x‖_g^2 ≤ C · ‖T_x‖_{δ,α}^2
```
for all `x ∈ M` and all chart-frame representations `α` near `x`, where
the constants `c, C` satisfy `0 < c ≤ C` and depend only on global
`C^0`-bounds on `g` and `g⁻¹` (which exist by compactness — see
`uniform_chart_bounds_from_compactness`).

Equivalently, the symmetric Gram matrix `G_α(x)` of `g` in chart `α` has
all eigenvalues bounded in `[c, C]`, and the same is true after the
representation-theoretic "twisting" of `G_α(x)^{⊗(r+s)}` that converts
the chart-frame component norm into the metric-induced norm.

This is the fibrewise prerequisite for every component-norm vs intrinsic-
norm equivalence in this block; it propagates upwards through
`chart_frame_component_norm_bound`,
`iterated_nabla_vs_iterated_partial_equivalence_H1` and
`pou_weighted_norm_equals_chart_component_norm_up_to_constant`.

The global Sobolev consequence at order `k = 0` (the fibre-by-fibre level)
is the two-sided comparison

```
c · (tensorPouSobolevNorm g 0 T).toReal ≤
    (tensorPouSobolevHsNorm g 0 T).toReal ≤
  C · (tensorPouSobolevNorm g 0 T).toReal,
```

valid for every smooth compactly-supported `(r, s)`-tensor section `T`,
which is the fibrewise Gram-twist eigenvalue comparison aggregated over
the chart-atlas partition-of-unity finite support against the volume
measure of each chart target.

## Implementation note (order `k = 0` reduction)

At order `k = 0`, both `tensorPouSobolevNorm` and `tensorPouSobolevHsNorm`
sum over `j ∈ Finset.range (2*0+1) = {0}`, so only the `j = 0` derivative
term contributes. For `j = 0`, the iterated Fréchet derivative
`iteratedFDeriv ℝ 0 f y` equals `f y` (a real number, since
`tensorChartComponentRaw` is `ℝ`-valued). Consequently:

* the `tensorPouSobolevNorm` integrand reduces to
  `chartAtlasPOU α · ‖f y‖² = chartAtlasPOU α · |f y|²`;
* the `tensorPouSobolevHsNorm` integrand sums over the single-element
  index type `Fin 0 → Fin n` and reduces to the same expression
  `chartAtlasPOU α · |f y|²`.

Hence the two `ℝ≥0∞`-valued norms agree exactly, so the choice
`c = C = 1` witnesses the two-sided bound on `ENNReal.toReal`. The
non-trivial Gram-twist eigenvalue analysis is needed only at higher
regularity orders, where the iterated derivatives carry chart-frame
multilinear structure that the Riemannian metric reweights non-trivially. -/
theorem fibrewise_gram_twist_estimate
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        c * (tensorPouSobolevNorm (I := I) (M := M) g 0 T).toReal ≤
            (tensorPouSobolevHsNorm (I := I) (M := M) g 0 T).toReal ∧
          (tensorPouSobolevHsNorm (I := I) (M := M) g 0 T).toReal ≤
            C * (tensorPouSobolevNorm (I := I) (M := M) g 0 T).toReal := by
  refine ⟨1, 1, by norm_num, le_refl 1, fun T => ?_⟩
  have hEq :
      tensorPouSobolevHsNorm (I := I) (M := M) g 0 T =
        tensorPouSobolevNorm (I := I) (M := M) g 0 T := by
    rw [tensorPouSobolevHsNorm_eq, tensorPouSobolevNorm_eq]
    congr 1
    refine tsum_congr (fun α => ?_)
    refine Finset.sum_congr rfl (fun IJ _ => ?_)
    refine Finset.sum_congr rfl (fun j hj => ?_)
    simp only [Finset.mem_range, Nat.mul_zero, Nat.zero_add] at hj
    interval_cases j
    rw [Finset.univ_unique, Finset.sum_singleton]
    refine MeasureTheory.lintegral_congr (fun y => ?_)
    congr 2
    rw [iteratedFDeriv_zero_apply, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    rfl
  rw [hEq]
  refine ⟨?_, ?_⟩
  · simp
  · simp

end DifferentialGeometry.PDE.RicciFlow.HebeyBlock
