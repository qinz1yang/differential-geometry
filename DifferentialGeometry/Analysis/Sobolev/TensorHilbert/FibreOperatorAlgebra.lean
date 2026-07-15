import DifferentialGeometry.Analysis.Integration.L2.Hilbert.Inherited
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.BanachAlgebraSmoothness

/-! # The `L²`-operator Banach algebra carrier for the realized inverse-Gram Neumann series

This file fixes, for a closed Riemannian manifold `(M, g₀)`, the concrete **complete unital normed
algebra** through which the realized metric's inverse Gram fires the imported Banach-algebra Neumann
smoothness spine (`Analysis.Sobolev.TensorHilbert.BanachAlgebraSmoothness`).

## The carrier and why it is the sound one

`FibreOpL2Algebra g₀ := TensorL2 0 2 g₀ →L[ℝ] TensorL2 0 2 g₀` — the algebra of bounded operators
on the metric `L²` Hilbert space of `(0,2)`-tensor fields, with **operator composition** as the ring
product.  Mathlib supplies, with no work, all three structures the Neumann spine demands:

* `NormedRing` (`ContinuousLinearMap.toNormedRing` on an endomorphism algebra),
* `NormedAlgebra ℝ` (`ContinuousLinearMap.toNormedAlgebra`),
* `CompleteSpace` (the codomain `TensorL2 0 2 g₀` is a Hilbert space, hence complete).

This carrier is the **chart-independent** one.  The naïve alternative — a `BoundedContinuousFunction M`
into a fixed *model* fibre-operator algebra (`E →L[ℝ] E`-type) read off through the bundle
trivialization — is mathematically **unsound** for the smallness domination the spine needs: the
*model* fibre operator norm is the trivialization-image (chart-selection-dependent) norm, which is
**unbounded** on a non-parallelizable manifold (e.g. `S²`), so no uniform `‖·‖ < 1` ball exists for it
(this is the exact obstruction the library records at
`DeTurck.Nonlinearity.bddAbove_gNorm_range`'s docstring, and the per-point-only
`HebeyBlock.modelNorm_le_gNorm_pointwise` whose constant blows up across charts).  The only uniformly
bounded, chart-independent currency is the intrinsic `g₀`-fibre norm; the realized perturbation enters
the inverse Gram as **multiplication on `L²`**, whose operator norm is dominated by the `g₀`-fibre
**sup** norm of the perturbation field — exactly the supercritical-embedding bound.  Hence the
`L²`-operator algebra, not a model-fibre `BoundedContinuousFunction`, is the sound carrier.

## What this file ships (sorry-free) and what it interfaces

* `FibreOpL2Algebra` + its `NormedRing` / `NormedAlgebra ℝ` / `CompleteSpace` instance witnesses.
* The Neumann inverse-Gram smoothness **specialized to this concrete carrier**: given any continuous
  linear perturbation map `L : E →L[ℝ] FibreOpL2Algebra g₀` landing strictly inside the open unit ball
  on a set `s`, the inverse Gram `x ↦ Ring.inverse (1 − L x) · c` (and any fixed entry read-off
  `Φ ∘ ·`) is `ContDiffOn ℝ ∞` on `s` — a thin instantiation of the imported spine
  (`contDiffOn_oneSub_inverse_clm_mul_const`,
  `contDiffOn_continuousLinearMap_comp_oneSub_inverse_clm`) demonstrating it fires on `A`.
* The smallness-transport bridge: a uniform sup bound `‖L x‖ ≤ δ` with `δ < 1` feeds the spine's
  strict `‖L x‖ < 1` hypothesis (this is the shape the realized perturbation's
  `gFibreOpBound … δ`-to-`L²`-operator-norm bound, once the multiplication operator is built, plugs
  into).

The genuinely **deep** remaining input — the concrete perturbation CLM
`T ↦ (multiplication by the `g₀`-sharp of `ccTensorBilinSymm g₀ T` on `TensorL2 0 2 g₀`)`, with its
operator-norm `≤ g₀`-fibre-sup `≤ C · ‖T.toHs q‖` bound — is the `L²`-multiplication-operator Nemytskii
stratum the retag consumer itself defers (`RealizedRetagChartSobolevSmoothness`'s module docstring:
"the chart-Sobolev product-smoothness layer … presently unbuilt at the `toHs` level").  It is **not**
supplied here; this file provides the carrier and the spine wiring the deep CLM lands into. -/

noncomputable section

open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis.FibreOperatorAlgebra

open DifferentialGeometry.Analysis.BanachAlgebraSmoothness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [InnerProductSpace ℝ E]

/-- **The `L²`-operator Banach-algebra carrier of the realized inverse Gram.**

For a closed Riemannian manifold `(M, g₀)`, `FibreOpL2Algebra g₀` is the algebra of bounded linear
operators on the metric `L²` Hilbert space `TensorL2 0 2 g₀` of `(0,2)`-tensor fields, with operator
composition as product and the operator norm.  It is the concrete complete unital normed algebra the
realized metric's inverse-Gram Neumann series lives in: the realized perturbation acts by `L²`
multiplication, and the inverse Gram is its Banach-algebra `Ring.inverse (1 − ·)`. -/
abbrev FibreOpL2Algebra (g₀ : SmoothRiemannianMetric I M) : Type _ :=
  Integral.L2.TensorL2 0 2 g₀ →L[ℝ] Integral.L2.TensorL2 0 2 g₀

/-- The carrier is a `NormedRing` (operator composition product, operator norm):
`ContinuousLinearMap.toNormedRing` on the endomorphism algebra of the `L²` Hilbert space. -/
instance instNormedRingFibreOpL2Algebra (g₀ : SmoothRiemannianMetric I M) :
    NormedRing (FibreOpL2Algebra (I := I) (M := M) g₀) :=
  inferInstanceAs (NormedRing (Integral.L2.TensorL2 0 2 g₀ →L[ℝ] Integral.L2.TensorL2 0 2 g₀))

/-- The carrier is a `NormedAlgebra ℝ`: `ContinuousLinearMap.toNormedAlgebra`. -/
instance instNormedAlgebraFibreOpL2Algebra (g₀ : SmoothRiemannianMetric I M) :
    NormedAlgebra ℝ (FibreOpL2Algebra (I := I) (M := M) g₀) :=
  inferInstanceAs (NormedAlgebra ℝ (Integral.L2.TensorL2 0 2 g₀ →L[ℝ] Integral.L2.TensorL2 0 2 g₀))

/-- The carrier is complete: the codomain `TensorL2 0 2 g₀` is a Hilbert space, hence the operator
algebra into it is a complete normed space (`ContinuousLinearMap` into a complete space is
complete). -/
instance instCompleteSpaceFibreOpL2Algebra (g₀ : SmoothRiemannianMetric I M) :
    CompleteSpace (FibreOpL2Algebra (I := I) (M := M) g₀) :=
  inferInstanceAs (CompleteSpace (Integral.L2.TensorL2 0 2 g₀ →L[ℝ] Integral.L2.TensorL2 0 2 g₀))

section Neumann

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Dom : Type*} [NormedAddCommGroup Dom] [NormedSpace ℝ Dom]

set_option linter.unusedSectionVars false

/-- **The realized inverse Gram is `C^∞` on a smallness ball, in the concrete `L²`-operator carrier.**

Given a continuous linear perturbation map `L : Dom →L[ℝ] FibreOpL2Algebra g₀` that lands strictly
inside the open unit ball on `s` (`‖L x‖ < 1` for `x ∈ s`) and a fixed base operator `c`, the inverse
Gram
`x ↦ Ring.inverse (1 − L x) · c`
is `ContDiffOn ℝ n` on `s`.  This is the imported Neumann spine
`BanachAlgebraSmoothness.contDiffOn_oneSub_inverse_clm_mul_const` instantiated on the concrete carrier
`A = FibreOpL2Algebra g₀`: `1 − L x` is a unit (uniformly-convergent Neumann series of the small `L²`
operator `L x`), its inverse is `C^∞`, and right-multiplying by the constant base inverse `c` keeps it
`C^∞`.  With `c` the base inverse Gram `g₀⁻¹` (as an `L²` operator) and `L` the realized perturbation
multiplication this is the realized metric's full inverse Gram `(1 + g₀⁻¹·h)⁻¹ · g₀⁻¹`. -/
theorem contDiffOn_inverseGram_clm
    (g₀ : SmoothRiemannianMetric I M) {s : Set Dom}
    {L : Dom →L[ℝ] FibreOpL2Algebra (I := I) (M := M) g₀}
    {c : FibreOpL2Algebra (I := I) (M := M) g₀} {n : WithTop ℕ∞}
    (hlt : ∀ x ∈ s, ‖L x‖ < 1) :
    ContDiffOn ℝ n (fun x => Ring.inverse (1 - L x) * c) s :=
  contDiffOn_oneSub_inverse_clm_mul_const (A := FibreOpL2Algebra (I := I) (M := M) g₀) hlt

/-- **A single inverse-Gram entry / multiplier is `C^∞`, in the concrete `L²`-operator carrier.**

Reading off one entry or contraction `Φ : FibreOpL2Algebra g₀ →L[ℝ] F` of the inverse Gram keeps it
`ContDiffOn ℝ n`.  Imported spine
`BanachAlgebraSmoothness.contDiffOn_continuousLinearMap_comp_oneSub_inverse_clm` on the concrete
carrier: `C^∞` is preserved by post-composition with the continuous linear `Φ`.  This is the form the
realized retag's Christoffel / Ricci / Lie numerators consume the inverse-Gram entries in. -/
theorem contDiffOn_inverseGram_entry_clm
    (g₀ : SmoothRiemannianMetric I M) {s : Set Dom}
    {L : Dom →L[ℝ] FibreOpL2Algebra (I := I) (M := M) g₀}
    {c : FibreOpL2Algebra (I := I) (M := M) g₀}
    (Φ : FibreOpL2Algebra (I := I) (M := M) g₀ →L[ℝ] F) {n : WithTop ℕ∞}
    (hlt : ∀ x ∈ s, ‖L x‖ < 1) :
    ContDiffOn ℝ n (fun x => Φ (Ring.inverse (1 - L x) * c)) s :=
  contDiffOn_continuousLinearMap_comp_oneSub_inverse_clm
    (A := FibreOpL2Algebra (I := I) (M := M) g₀) Φ hlt

/-- **Smallness transport: a uniform sub-unit sup bound feeds the strict Neumann hypothesis.**

If the perturbation CLM `L` satisfies a *uniform* operator-norm bound `‖L x‖ ≤ δ` on `s` with
`δ < 1` (the shape produced by the realized perturbation's `g₀`-fibre-operator smallness
`gFibreOpBound … δ`, once transported through the `L²`-multiplication operator-norm-by-fibre-sup
bound), then the inverse Gram `x ↦ Ring.inverse (1 − L x) · c` is `ContDiffOn ℝ n` on `s`.  The
uniform `≤ δ < 1` bound implies the strict `‖L x‖ < 1` the Neumann spine needs, so this is
`contDiffOn_inverseGram_clm`.  This is the precise interface the realized fibre-small ball plugs into:
the ball radius `ρ` is chosen so the supercritical embedding `H^q ↪ C⁰` forces `δ < 1`. -/
theorem contDiffOn_inverseGram_of_uniform_bound
    (g₀ : SmoothRiemannianMetric I M) {s : Set Dom}
    {L : Dom →L[ℝ] FibreOpL2Algebra (I := I) (M := M) g₀}
    {c : FibreOpL2Algebra (I := I) (M := M) g₀} {δ : ℝ} {n : WithTop ℕ∞}
    (hδ : δ < 1) (hbound : ∀ x ∈ s, ‖L x‖ ≤ δ) :
    ContDiffOn ℝ n (fun x => Ring.inverse (1 - L x) * c) s :=
  contDiffOn_inverseGram_clm (I := I) (M := M) g₀
    (fun x hx => lt_of_le_of_lt (hbound x hx) hδ)

end Neumann

end DifferentialGeometry.Analysis.FibreOperatorAlgebra

end
