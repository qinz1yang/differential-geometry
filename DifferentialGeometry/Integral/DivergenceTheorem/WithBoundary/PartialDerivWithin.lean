import DifferentialGeometry.Integral.DivergenceTheorem.LocalFormula
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.TangentCone.Basic
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

/-!
# Within-set partial derivatives in a model basis

This file establishes the chart-target-level analytic foundation for the
divergence operator on manifolds whose local model `I : ModelWithCorners ℝ E H`
may have a non-trivial boundary (the chart target need not be open in `E`).

The Fréchet partial derivative `partialDeriv` from
`Integral/DivergenceTheorem/LocalFormula.lean` is defined as
`fderiv ℝ u y (chartModelBasis E i)`. On a chart target that is not open in
`E`, `fderiv` is the wrong notion at boundary points: a function may be smooth
in the within-the-target sense without admitting a Fréchet derivative on a full
ambient neighbourhood. The replacement is the `fderivWithin` evaluated against
the same model-basis vector. Under
`UniqueDiffOn ℝ (extChartAt I α).target` (provided by Mathlib's
`uniqueDiffOn_extChartAt_target`), this within-derivative is uniquely
determined and agrees with the Fréchet derivative at every point of the
interior.

## Main definition

* `partialDerivWithin s i u y` : the within-derivative of `u : E → ℝ` on the
  set `s ⊆ E`, at the point `y`, evaluated against the `i`-th model-basis
  vector `(chartModelBasis E) i`.

## Main results

### Comparison with the Fréchet partial derivative

* `partialDerivWithin_eq_partialDeriv_of_isOpen` — on an open set, the
  within-derivative coincides with the Fréchet derivative.
* `partialDerivWithin_eq_partialDeriv_of_mem_interior` — at any interior point
  of the carrying set, the same identity holds.
* `partialDerivWithin_extChartAt_target_eq_partialDeriv` — specialised to the
  interior of an extended-chart target.

### Congruence

* `partialDerivWithin_congr` — the within-derivative depends only on the
  values of the integrand on the carrying set.
* `partialDerivWithin_congr_of_eqOn_of_mem` — convenience variant requiring
  only `EqOn` plus `y ∈ s`.

### Smoothness propagation

* `partialDerivWithin_contDiffOn_of_uniqueDiffOn` — under
  `ContDiffOn ℝ (m+1) u s` and `UniqueDiffOn ℝ s`, the within-partial
  derivative is `ContDiffOn ℝ m` on `s`.
* `partialDerivWithin_contDiffOn_top_of_uniqueDiffOn` — the convenient
  `m = ∞` specialisation, bypassing the `m+1 ≤ ⊤` bookkeeping at the call
  site.
* `partialDerivWithin_contDiffOn_of_isOpen` — open-set specialisation.

### Pointwise algebraic identities (Leibniz)

* `partialDerivWithin_add` — additivity.
* `partialDerivWithin_smul` — `ℝ`-scalar Leibniz rule.
* `partialDerivWithin_mul` — Leibniz product rule for real-valued functions.

### Convenience re-exports for chart targets

* `uniqueDiffOn_extChartAt_target_apply` — `UniqueDiffOn` applied at a single
  point of the chart target.
-/

noncomputable section

open Set
open scoped Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]

/-- Within-set partial derivative of `u : E → ℝ` at `y : E` in the direction of
the `i`-th model-basis vector, computed on `s ⊆ E`.

On a set `s` for which `UniqueDiffOn ℝ s` holds (in particular, on
`(extChartAt I α).target` thanks to `uniqueDiffOn_extChartAt_target`), this
within-derivative is the canonical replacement for the ordinary Fréchet
partial derivative `partialDeriv` from the boundaryless local-formula file. At
points of the interior of `s` it coincides with `partialDeriv`; at boundary
points of `s` it is well-defined while `fderiv` is not. -/
def partialDerivWithin (s : Set E) (i : Fin (Module.finrank ℝ E))
    (u : E → ℝ) (y : E) : ℝ :=
  fderivWithin ℝ u s y ((chartModelBasis E) i)

/-- Unfolding lemma — the within-partial derivative is the within-Fréchet
derivative evaluated on the model-basis vector. -/
@[simp] lemma partialDerivWithin_def (s : Set E)
    (i : Fin (Module.finrank ℝ E)) (u : E → ℝ) (y : E) :
    partialDerivWithin (E := E) s i u y =
      fderivWithin ℝ u s y ((chartModelBasis E) i) := rfl

section ComparisonWithFDeriv

variable {s : Set E} {i : Fin (Module.finrank ℝ E)} {u : E → ℝ} {y : E}

/-- On an open set, the within-partial derivative equals the Fréchet partial
derivative. Direct consequence of `fderivWithin_of_isOpen`. -/
lemma partialDerivWithin_eq_partialDeriv_of_isOpen
    (hs : IsOpen s) (hy : y ∈ s) :
    partialDerivWithin (E := E) s i u y = partialDeriv (E := E) i u y := by
  unfold partialDerivWithin partialDeriv
  rw [fderivWithin_of_isOpen hs hy]

/-- At any interior point of the carrying set, the within-partial derivative
equals the Fréchet partial derivative. Strictly generalises
`partialDerivWithin_eq_partialDeriv_of_isOpen`. -/
lemma partialDerivWithin_eq_partialDeriv_of_mem_interior
    (hy : y ∈ interior s) :
    partialDerivWithin (E := E) s i u y = partialDeriv (E := E) i u y := by
  have hnhds : s ∈ 𝓝 y :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hy) interior_subset
  unfold partialDerivWithin partialDeriv
  rw [fderivWithin_of_mem_nhds hnhds]

/-- Congruence: the within-partial derivative depends only on the values of
`u` on the carrying set. The hypothesis `u y = v y` is the same one
`fderivWithin_congr` requires. -/
lemma partialDerivWithin_congr {u v : E → ℝ}
    (huv : EqOn u v s) (hy : u y = v y) :
    partialDerivWithin (E := E) s i u y =
      partialDerivWithin (E := E) s i v y := by
  unfold partialDerivWithin
  rw [fderivWithin_congr huv hy]

/-- Convenience variant: when `y ∈ s`, the pointwise hypothesis `u y = v y` is
implied by `EqOn`. -/
lemma partialDerivWithin_congr_of_eqOn_of_mem {u v : E → ℝ}
    (huv : EqOn u v s) (hy : y ∈ s) :
    partialDerivWithin (E := E) s i u y =
      partialDerivWithin (E := E) s i v y :=
  partialDerivWithin_congr huv (huv hy)

/-- Re-statement of the definition as `fderivWithin … applied to the basis
vector`. Useful when the goal has been unfolded part-way. -/
lemma partialDerivWithin_eq_fderivWithin_basis
    (s : Set E) (i : Fin (Module.finrank ℝ E)) (u : E → ℝ) (y : E) :
    partialDerivWithin (E := E) s i u y =
      fderivWithin ℝ u s y ((chartModelBasis E) i) := rfl

end ComparisonWithFDeriv

section Smoothness

variable {m n : WithTop ℕ∞} {s : Set E} {u : E → ℝ}
  {i : Fin (Module.finrank ℝ E)}

/-- Smoothness of the within-partial derivative of order `m`, assuming the
function is `C^n` for some `m + 1 ≤ n` and the carrying set satisfies
`UniqueDiffOn ℝ s`.

This is the workhorse: chart targets satisfy `UniqueDiffOn` via
`uniqueDiffOn_extChartAt_target`, regardless of whether the model has a
boundary. -/
lemma partialDerivWithin_contDiffOn_of_uniqueDiffOn
    (hu : ContDiffOn ℝ n u s) (hs : UniqueDiffOn ℝ s) (hmn : m + 1 ≤ n) :
    ContDiffOn ℝ m (partialDerivWithin (E := E) s i u) s := by
  have hfderiv : ContDiffOn ℝ m (fderivWithin ℝ u s) s :=
    hu.fderivWithin hs hmn
  have hconst : ContDiffOn ℝ m
      (fun _ : E => (chartModelBasis E) i) s := contDiffOn_const
  exact hfderiv.clm_apply hconst

/-- The `m = ∞` specialisation of `partialDerivWithin_contDiffOn_of_uniqueDiffOn`.
The hypothesis `(⊤ : ℕ∞) + 1 ≤ ⊤` reduces by `ENat.coe_top_add_one` to
`(⊤ : ℕ∞) ≤ ⊤`, which holds. -/
lemma partialDerivWithin_contDiffOn_top_of_uniqueDiffOn
    (hu : ContDiffOn ℝ ∞ u s) (hs : UniqueDiffOn ℝ s) :
    ContDiffOn ℝ ∞ (partialDerivWithin (E := E) s i u) s :=
  partialDerivWithin_contDiffOn_of_uniqueDiffOn (n := ∞) (m := ∞) hu hs
    (by rw [ENat.coe_top_add_one])

/-- Open-set specialisation of `partialDerivWithin_contDiffOn_of_uniqueDiffOn`.
The unique-differentiability hypothesis is supplied by `IsOpen.uniqueDiffOn`. -/
lemma partialDerivWithin_contDiffOn_of_isOpen
    (hu : ContDiffOn ℝ n u s) (hs : IsOpen s) (hmn : m + 1 ≤ n) :
    ContDiffOn ℝ m (partialDerivWithin (E := E) s i u) s :=
  partialDerivWithin_contDiffOn_of_uniqueDiffOn hu hs.uniqueDiffOn hmn

/-- The `m = ∞` open-set specialisation. -/
lemma partialDerivWithin_contDiffOn_top_of_isOpen
    (hu : ContDiffOn ℝ ∞ u s) (hs : IsOpen s) :
    ContDiffOn ℝ ∞ (partialDerivWithin (E := E) s i u) s :=
  partialDerivWithin_contDiffOn_of_isOpen (n := ∞) (m := ∞) hu hs
    (by rw [ENat.coe_top_add_one])

end Smoothness

section LeibnizIdentities

variable {s : Set E} {y : E} {i : Fin (Module.finrank ℝ E)}

/-- Additivity of the within-partial derivative. -/
lemma partialDerivWithin_add (u v : E → ℝ)
    (hs : UniqueDiffWithinAt ℝ s y)
    (hu : DifferentiableWithinAt ℝ u s y)
    (hv : DifferentiableWithinAt ℝ v s y) :
    partialDerivWithin (E := E) s i (fun y => u y + v y) y =
      partialDerivWithin (E := E) s i u y +
        partialDerivWithin (E := E) s i v y := by
  unfold partialDerivWithin
  rw [fderivWithin_fun_add hs hu hv]
  rfl

/-- `ℝ`-scalar Leibniz rule for the within-partial derivative. The `c y` is
the scalar function and `u` is the vector-valued function (here `E → ℝ`). -/
lemma partialDerivWithin_smul (c : E → ℝ) (u : E → ℝ)
    (hs : UniqueDiffWithinAt ℝ s y)
    (hc : DifferentiableWithinAt ℝ c s y)
    (hu : DifferentiableWithinAt ℝ u s y) :
    partialDerivWithin (E := E) s i (fun y => c y • u y) y =
      c y • partialDerivWithin (E := E) s i u y +
        partialDerivWithin (E := E) s i c y • u y := by
  unfold partialDerivWithin
  rw [fderivWithin_fun_smul hs hc hu]
  simp [ContinuousLinearMap.smulRight_apply, smul_eq_mul, mul_comm]

/-- Leibniz product rule for the within-partial derivative of a product of
real-valued functions. -/
lemma partialDerivWithin_mul (u v : E → ℝ)
    (hs : UniqueDiffWithinAt ℝ s y)
    (hu : DifferentiableWithinAt ℝ u s y)
    (hv : DifferentiableWithinAt ℝ v s y) :
    partialDerivWithin (E := E) s i (fun y => u y * v y) y =
      u y * partialDerivWithin (E := E) s i v y +
        v y * partialDerivWithin (E := E) s i u y := by
  unfold partialDerivWithin
  rw [fderivWithin_fun_mul hs hu hv]
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]

end LeibnizIdentities

section ChartTarget

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The chart-target carrier `(extChartAt I α).target` satisfies
`UniqueDiffWithinAt ℝ` at every one of its points, regardless of whether the
model `I` has a boundary. Convenience pointwise re-export of Mathlib's
`uniqueDiffOn_extChartAt_target`. -/
lemma uniqueDiffOn_extChartAt_target_apply (α : M) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    UniqueDiffWithinAt ℝ (extChartAt I α).target y :=
  uniqueDiffOn_extChartAt_target α y hy

/-- On the interior of an extended-chart target, the within-partial derivative
in the direction of the `i`-th model-basis vector coincides with the Fréchet
partial derivative `partialDeriv` of the boundaryless theory. This is the key
bridge: chart-formula identities proved with `partialDeriv` on the open
interior transport verbatim to the with-boundary set-up using
`partialDerivWithin (extChartAt I α).target`. -/
theorem partialDerivWithin_extChartAt_target_eq_partialDeriv
    (α : M) (i : Fin (Module.finrank ℝ E)) (u : E → ℝ)
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    partialDerivWithin (E := E) (extChartAt I α).target i u y =
      partialDeriv (E := E) i u y :=
  partialDerivWithin_eq_partialDeriv_of_mem_interior hy

end ChartTarget

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
