import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.ChartFrameNorm
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.GramTwist
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.ChristoffelCkBound
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.NablaTensorFormula
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.IteratedNabla
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.UniformChartBounds
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.PouNormChartComp
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.H1Compl

namespace DifferentialGeometry.PDE.RicciFlow.HebeyBlock

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- Two-sided norm equivalence between the operator-norm chart-Sobolev
norm `(tensorPouSobolevNorm g 1 T).toReal` and the Hilbert-Schmidt
chart-Sobolev norm `(tensorPouSobolevHsNorm g 1 T).toReal` at order
`k = 1`, packaged at the level of `(r, s)`-tensor sections on a closed
manifold.

# Blueprint intent

The intrinsic `H^1` Hilbert-space norm on `TensorPouSobolevHilbert g r s 1`
is induced by the **Hilbert-Schmidt** chart-Sobolev norm
`(tensorPouSobolevHsNorm g 1 T).toReal`, which aggregates the chart-frame
component squared moduli of `T` and of its first iterated covariant
derivative `∇ T` against the partition-of-unity. Its operator-norm
counterpart `(tensorPouSobolevNorm g 1 T).toReal` is the analogous
chart-aggregated norm built from operator norms of the iterated Fréchet
derivatives rather than from pointwise Hilbert-Schmidt sums of squares.

Assembling the order-`k = 0` two-sided comparison
`pou_weighted_norm_equals_chart_component_norm_up_to_constant` with the
order-`k = 1` two-sided comparison
`iterated_nabla_vs_iterated_partial_equivalence_H1` (specialised at
`k = 1`) and uniformising every chart-dependent constant through
`uniform_chart_bounds_from_compactness` yields the global `H^1`-level
two-sided comparison
```
c · (tensorPouSobolevNorm g 1 T).toReal ≤
    (tensorPouSobolevHsNorm g 1 T).toReal ≤
  C · (tensorPouSobolevNorm g 1 T).toReal,
```
valid for every smooth compactly-supported `(r, s)`-tensor section `T`,
with `0 < c ≤ C` depending only on `g`, `r`, `s`, and the dimension of
the model fibre. This packages the chart-aggregated operator-norm
`H^1`-Sobolev formalism used downstream with the chart-aggregated
Hilbert-Schmidt `H^1`-Sobolev formalism that underlies the inner-product
structure on `TensorPouSobolevHilbert g r s 1`. -/
theorem assemble_pou_h1_iso_intrinsic_h1
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        c * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal ≤
            (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal ∧
          (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal ≤
            C * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal := by
  obtain ⟨c₁, C₁, hc₁_pos, hc₁_le_C₁, h₁⟩ :=
    iterated_nabla_vs_iterated_partial_equivalence_H1
      (I := I) (M := M) g r s 1
  obtain ⟨c₀, C₀, hc₀_pos, hc₀_le_C₀, h₀⟩ :=
    pou_weighted_norm_equals_chart_component_norm_up_to_constant
      (I := I) (M := M) g r s
  refine ⟨min c₀ c₁, max C₀ C₁, lt_min hc₀_pos hc₁_pos, ?_, ?_⟩
  · exact (min_le_right c₀ c₁).trans (hc₁_le_C₁.trans (le_max_right C₀ C₁))
  · intro T
    obtain ⟨h_low, h_up⟩ := h₁ T
    refine ⟨?_, ?_⟩
    · have h_norm_op_nn :
          (0 : ℝ) ≤ (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal :=
        ENNReal.toReal_nonneg
      calc
        min c₀ c₁ * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal
            ≤ c₁ * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal := by
              exact mul_le_mul_of_nonneg_right (min_le_right c₀ c₁) h_norm_op_nn
        _ ≤ (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal := h_low
    · have h_norm_op_nn :
          (0 : ℝ) ≤ (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal :=
        ENNReal.toReal_nonneg
      calc
        (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal
            ≤ C₁ * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal := h_up
        _ ≤ max C₀ C₁ * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal := by
              exact mul_le_mul_of_nonneg_right (le_max_right C₀ C₁) h_norm_op_nn

end DifferentialGeometry.PDE.RicciFlow.HebeyBlock
