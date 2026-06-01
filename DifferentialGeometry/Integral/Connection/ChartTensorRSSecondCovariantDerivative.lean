import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivativeAgreement
import DifferentialGeometry.Integral.Connection.Curvature

/-!
# Chart-coordinate expression for the second covariant derivative on the
`(r, s)`-tensor bundle

Given a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, a smooth
`(r, s)`-tensor section `T`, and a smooth tangent vector field `X`, this file
expresses the operator
`cov_RS (covApply cov_RS X T) y :
  TangentSpace I y →L[ℝ] TensorRSSpace r s I y`
at a chart-α Levi-Civita good-set point `y` in chart α coordinates.

The right-hand side is the chart-frame value
`chartTensorRSCovariantDerivative r s g α (covApply cov_RS X T) X' y`
for the second-derivative direction `X'`. Unfolded via
`chartTensorRSCovariantDerivative_def`, this is the difference of three
chart-coordinate pieces evaluated on the chart-α-trivialised representation of
the section `covApply cov_RS X T`:

* the intrinsic chart Fréchet derivative piece, which is the Fréchet derivative
  of the chart-trivialised representation of `covApply cov_RS X T` along the
  chart push-forward of `X'(y)` — this is the source of the `∂_a ∂_b T^I_J`
  contributions once one unfolds the chart-trivialised representation of
  `covApply cov_RS X T` itself via the first-derivative formula
  `chartTensorRSCovariantDerivative_eq_abstract_on_chartLeviCivitaGoodSet`;
* the sum over input slots `k : Fin r` of the upper-slot Christoffel correction
  applied to `covApply cov_RS X T` (a Γ-correction from the *outer*
  `cov_RS` application);
* the sum over output slots `l : Fin s` of the lower-slot Christoffel correction
  applied to `covApply cov_RS X T` (also a Γ-correction from the *outer*
  `cov_RS` application).

Two Γ-corrections appear overall, one from each `cov_RS` application: the
inner one is folded into the chart-trivialised representation of
`covApply cov_RS X T` via the first-derivative formula
`chartTensorRSCovariantDerivative_eq_abstract_on_chartLeviCivitaGoodSet` (which expresses
`covApply cov_RS X T b = cov_RS T b (X b)` in chart coordinates with one
Γ-correction), and the outer one appears as the explicit input-slot and
output-slot Christoffel corrections in the chart-frame definition of
`chartTensorRSCovariantDerivative` for `covApply cov_RS X T`.

## Main result

* `chartTensorRSSecondCovariantDerivative_eq_abstract` — the chart-coordinate
  agreement for the second covariant derivative.

## Implementation

The proof is a direct application of the first-derivative agreement
`chartTensorRSCovariantDerivative_eq_abstract_on_chartLeviCivitaGoodSet` to the smooth `(r, s)`-tensor
section `covApply cov_RS X T`. Smoothness of `covApply cov_RS X T` is supplied
by `covApply_contMDiffOn` from globally smooth `T` and `X`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators
open Tensor0SBundle

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-- Globally smooth `(r, s)`-tensor section `covApply cov_RS X T = b ↦
cov_RS T b (X b)`, derived from globally smooth `T` and `X`. -/
private lemma covApply_covRS_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) X T y)) := by
  classical
  have hT_plus : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      ((∞ : WithTop ℕ∞) + 1)
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]
    exact hT_total
  have hOn :
      ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)) X T y)) Set.univ :=
    covApply_contMDiffOn
      (cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)) hX hT_plus
  intro b
  exact hOn.contMDiffAt (Filter.univ_mem)

/-- **Chart-coordinate expression for the second covariant derivative.**

For a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, a smooth
`(r, s)`-tensor section `T`, smooth tangent vector fields `X` (inner) and `X'`
(outer), and a chart-α Levi-Civita good-set point `y`, the value
`cov_RS (covApply cov_RS X T) y (X' y) : TensorRSSpace r s I y`
of the second covariant derivative along the pair `(X, X')` at `y` agrees with
the chart-frame value
`chartTensorRSCovariantDerivative r s g α (covApply cov_RS X T) X' y`,
which decomposes (via `chartTensorRSCovariantDerivative_def`) as the intrinsic
chart Fréchet derivative of the chart-trivialised representation of
`covApply cov_RS X T` along the chart push-forward of `X'(y)`, plus the sum
over input slots `k : Fin r` of the upper-slot Christoffel correction applied
to `covApply cov_RS X T`, minus the sum over output slots `l : Fin s` of the
lower-slot Christoffel correction applied to `covApply cov_RS X T`.

Each Christoffel correction here uses `chartLeviCivitaParallelCLM g α y X'`
(i.e. the *outer* direction `X'`); the *inner* Γ-correction (one for each
chart-coordinate `∂_a` acting on `(cov_RS T (X))^I_J`) is folded into the
chart-trivialised representation of `covApply cov_RS X T` via the first-
derivative agreement `chartTensorRSCovariantDerivative_eq_abstract_on_chartLeviCivitaGoodSet` applied to
the smooth section `covApply cov_RS X T`. Two Γ-corrections appear overall,
one from each `cov_RS` application.

The intrinsic-Fréchet-derivative piece, evaluated at any vector
`v ∈ TangentSpace I y`, is the chart-α-trivialised Fréchet derivative
`tensorRSIntrinsicChartCLM r s α (covApply cov_RS X T) y v` of the
chart-trivialised representation of `covApply cov_RS X T`; this is the source
of the second-partial `∂_a ∂_b T^I_J` contributions, once one further unfolds
the chart-trivialised representation of `covApply cov_RS X T` via the first-
derivative formula `chartTensorRSCovariantDerivative_eq_abstract_on_chartLeviCivitaGoodSet`. -/
theorem chartTensorRSSecondCovariantDerivative_eq_abstract
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T :
      letI _h_top : TopologicalSpace
          (TotalSpace (TensorRSModel r s ℝ E)
            (fun x : M => TensorRSSpace r s I x)) :=
        tensorRSBundle_topology r s
      letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
          (fun x : M => TensorRSSpace r s I x) :=
        tensorRSBundle_fiber r s
      Cₛ^∞⟮I; TensorRSModel r s ℝ E,
        fun b => TensorRSSpace r s I b⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (X' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {y : M} (hy : y ∈ chartLeviCivitaGoodSet (I := I) α) :
    (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun
      (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)) X.toFun T.toFun) y (X'.toFun y) =
      chartTensorRSCovariantDerivative (I := I) r s g α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)) X.toFun T.toFun) X'.toFun y := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  have hCovApply_smooth :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)) X.toFun T.toFun y)) :=
    covApply_covRS_contMDiff (I := I) g r s T.contMDiff X.contMDiff
  set S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      fun b : M => TensorRSSpace r s I b⟯ :=
    { toFun := covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)) X.toFun T.toFun
      contMDiff_toFun := hCovApply_smooth } with hS_def
  have hFirst :=
    chartTensorRSCovariantDerivative_eq_abstract_on_chartLeviCivitaGoodSet (I := I) (M := M)
      g r s α S X' (b := y) hy
  have hS_toFun : S.toFun =
      covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)) X.toFun T.toFun := by
    rw [hS_def]
  rw [hS_toFun] at hFirst
  exact hFirst.symm

end Connection
end Integral
end DifferentialGeometry

end
