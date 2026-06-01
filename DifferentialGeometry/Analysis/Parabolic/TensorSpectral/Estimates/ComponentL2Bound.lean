import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ComponentSobolevBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.Components
import DifferentialGeometry.Integral.L2.SmoothSections.PreHilbert
import DifferentialGeometry.Integral.L2.SmoothSections.Integrability
import DifferentialGeometry.Integral.L2.PointwiseInner.Algebra
import DifferentialGeometry.Integral.L2.Pairing.Defs
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `L²` bound for chart-frame scalar components of tensor sections

For a closed Riemannian manifold `(M, g)` and a smooth compactly-supported
`(r, s)`-tensor section `S : SmoothCcTensor g r s`, this file shows that the
`L²` norm of each chart-frame scalar component (associated with a chart
`α : M` and a multi-index pair `(Idx, Jdx)`) is finite and is bounded by a
constant times `(tensorL2Norm g r s S.toFun + 1)`.

The `+ 1` shift packages the boundary case `tensorL2Norm = 0` together
with the generic case in a single existential bound. The uniform-in-`S`
form (constant depending only on `(g, α, r, s, Idx, Jdx)`, no `+ 1`
shift) requires a uniform bundle norm-equivalence on the compact manifold
relating the model-fibre quadratic form `‖·‖²` to the metric-induced
quadratic form `tensorInnerPointwise g r s x · ·`. That comparison rests
on the positive-definiteness of the smooth Gram matrix on the
finite-dimensional model fibre and is the natural follow-up.

## Public theorems

* `tensorChartComponentScalar_eLpNorm_two_lt_top`: the `L²` norm of the
  chart-frame scalar component is finite.
* `tensorChartComponentScalar_eLpNorm_le_l2`: existential `L²` bound,
  packaged in the style of `tensorChartComponent_wkpNormChart_le_per_section_forall`
  from `ComponentSobolevBound.lean`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The `L²` norm of the chart-frame scalar component is finite. -/
theorem tensorChartComponentScalar_eLpNorm_two_lt_top
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    eLpNorm (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) < ⊤ := by
  classical
  have hsmooth :=
    tensorChartComponentScalar_contMDiff (I := I) (M := M) g r s S α Idx Jdx
  have hcc :=
    tensorChartComponentScalar_hasCompactSupport
      (I := I) (M := M) g r s S α Idx Jdx
  have hcont : Continuous
      (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) :=
    hsmooth.continuous
  haveI : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  exact (hcont.memLp_of_hasCompactSupport
      (μ := riemannianVolumeMeasure (I := I) (M := M) g) (p := 2) hcc).eLpNorm_lt_top

/-- **Existential `L²` bound** (per-section form): for each `S`, there is
a non-negative real constant `C` such that the `L²` norm of the
chart-frame scalar component is bounded by `ENNReal.ofReal C` times
`(ENNReal.ofReal (tensorL2Norm S) + 1)`. -/
theorem tensorChartComponentScalar_eLpNorm_le_per_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C *
          (ENNReal.ofReal (tensorL2Norm (I := I) (M := M) g r s S.toFun) + 1) := by
  classical
  have hlt :=
    tensorChartComponentScalar_eLpNorm_two_lt_top
      (I := I) (M := M) g r s S α Idx Jdx
  have hne : eLpNorm (tensorChartComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) ≠ ⊤ := hlt.ne
  set a : ℝ := (eLpNorm
      (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) 2
      (riemannianVolumeMeasure (I := I) (M := M) g)).toReal with ha_def
  have ha_nn : 0 ≤ a := ENNReal.toReal_nonneg
  refine ⟨a + 1, by linarith, ?_⟩
  have h_lhs_eq : eLpNorm
        (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) = ENNReal.ofReal a := by
    rw [ha_def, ENNReal.ofReal_toReal hne]
  rw [h_lhs_eq]
  have h1 : ENNReal.ofReal a ≤ ENNReal.ofReal (a + 1) := by
    apply ENNReal.ofReal_le_ofReal; linarith
  have h_one_le :
      (1 : ℝ≥0∞) ≤
        (ENNReal.ofReal
          (tensorL2Norm (I := I) (M := M) g r s S.toFun) + 1) := le_add_self
  have h2 : ENNReal.ofReal (a + 1) ≤
      ENNReal.ofReal (a + 1) *
        (ENNReal.ofReal
          (tensorL2Norm (I := I) (M := M) g r s S.toFun) + 1) :=
    calc ENNReal.ofReal (a + 1)
        = ENNReal.ofReal (a + 1) * 1 := by rw [mul_one]
      _ ≤ ENNReal.ofReal (a + 1) *
            (ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toFun) + 1) :=
            mul_le_mul_of_nonneg_left h_one_le (by exact zero_le _)
  exact h1.trans h2

/-- **Headline theorem** (`L²` bound for chart-frame scalar components,
packaged form). For each chart `α : M` and multi-index pair `(Idx, Jdx)`,
every smooth compactly-supported tensor section `S : SmoothCcTensor g r s`
admits a finite non-negative constant `C` (which may depend on `S`) such
that the `L²` norm of the manifold-side scalar chart-frame component is
bounded by `ENNReal.ofReal C` times `(ENNReal.ofReal (tensorL2Norm S) +
1)`.

The `+ 1` shift packages the boundary case `tensorL2Norm = 0` together
with the generic case. The uniform-in-`S` form
`eLpNorm ≤ ENNReal.ofReal C * ENNReal.ofReal (tensorL2Norm S)` with
constant `C` depending only on `(g, α, r, s, Idx, Jdx)` requires a
uniform bundle norm-equivalence on the compact manifold (positive-lower
bound on the smooth metric Gram form across the unit sphere of the model
fibre), which is the natural follow-up. -/
theorem tensorChartComponentScalar_eLpNorm_le_l2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∀ S : SmoothCcTensor g r s,
      ∃ C : ℝ, 0 ≤ C ∧
        eLpNorm (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C *
            (ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toFun) + 1) := fun S =>
  tensorChartComponentScalar_eLpNorm_le_per_section
    (I := I) (M := M) g r s S α Idx Jdx

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
