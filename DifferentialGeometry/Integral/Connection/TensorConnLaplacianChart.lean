import DifferentialGeometry.Integral.Connection.TensorConnLaplacian
import DifferentialGeometry.Integral.Connection.ChartTensorRSSecondCovariantDerivative

/-!
# Chart-frame expansion of the raw tensor connection Laplacian

Given a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, a smooth
`(r, s)`-tensor section `T`, and a chart-α Levi-Civita good-set point `y`, this
file expresses the value `rawTensorConnLap g r s T.toFun y` as a finite trace
indexed by `i : Fin n` (with `n := Module.finrank ℝ E`), summing two
contributions per index:

* The chart-frame value
  `chartTensorRSCovariantDerivative r s g α
      (covApply cov_RS B_i T.toFun) B_i y`,
  where `B_i = smoothOrthoFrame g y i` is the `i`-th smooth orthonormal frame
  section at the centre `y`. Unfolded via
  `chartTensorRSCovariantDerivative_def`, this is the intrinsic chart Fréchet
  derivative of the chart-trivialised representation of `covApply cov_RS B_i T`
  along the chart push-forward of `B_i y`, plus the sum over input slots
  `k : Fin r` of the upper-slot Christoffel correction applied to
  `covApply cov_RS B_i T`, minus the sum over output slots `l : Fin s` of the
  lower-slot Christoffel correction applied to `covApply cov_RS B_i T`.
* The inner-Levi-Civita Γ-correction
  `cov_RS T.toFun y ((LeviCivita g).toFun B_i y (B_i y))`
  produced by the tangent-bundle Levi-Civita connection `LeviCivita g` acting
  on `B_i` along itself at `y`.

The difference of these two pieces, summed over `i`, is the raw connection
Laplacian. Unfolding the chart-frame piece via `chartTensorRSCovariantDerivative_def`
yields the textbook chart-coordinate expression
$$
  (\Delta_\nabla T)^I_J(y) = g^{ab}(y) \cdot \bigl[\partial_a \partial_b T^I_J(y)
    + (\text{Christoffel terms in $a$ and $b$})\bigr].
$$
The `g^{ab}(y)` factor is encoded geometrically by the `g_y`-orthonormal frame
`smoothOrthoFrame g y` (which carries the inverse Gram coefficients into the
finite trace).

## Main result

* `rawTensorConnLap_eq_chart` — chart-frame expansion of the raw tensor
  connection Laplacian.

## Implementation

The proof combines two existing facts:

1. The definitional restatement `rawTensorConnLap_frame_trace`, which
   expresses `rawTensorConnLap g r s T.toFun y` as the finite trace
   `∑ i, (cov_RS (covApply cov_RS B_i T) y (B_i y) -
            cov_RS T y ((LeviCivita g) B_i y (B_i y)))`
   with `B_i = smoothOrthoFrame g y i`. Here the centre of the frame is the
   evaluation point `y` itself, which is what makes the orthogonality of the
   frame at `y` automatic.

2. The chart-coordinate agreement
   `chartTensorRSSecondCovariantDerivative_eq_abstract`, which rewrites the
   first summand of each `i` as the chart-frame value
   `chartTensorRSCovariantDerivative r s g α (covApply cov_RS B_i T) B_i y`,
   valid at chart-α Levi-Civita good-set points `y`. The smoothness witnesses
   for `B_i` come from `smoothOrthoFrame_smooth`, which packages
   `smoothOrthoFrame g y i` as a smooth section
   `Cₛ^∞⟮I; E, TangentSpace I⟯`.
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

/-- The `i`-th smooth orthonormal frame at the centre `y`, packaged as a smooth
section `Cₛ^∞⟮I; E, TangentSpace I⟯`. Used to feed
`chartTensorRSSecondCovariantDerivative_eq_abstract`, which expects globally
smooth vector-field arguments. -/
private noncomputable def smoothOrthoFrameAsSection
    (g : SmoothRiemannianMetric I M) (y : M) (i : Fin (Module.finrank ℝ E)) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨smoothOrthoFrame (I := I) g y i, smoothOrthoFrame_smooth (I := I) g y i⟩

@[simp]
private lemma smoothOrthoFrameAsSection_toFun
    (g : SmoothRiemannianMetric I M) (y : M)
    (i : Fin (Module.finrank ℝ E)) :
    (smoothOrthoFrameAsSection (I := I) g y i).toFun =
      smoothOrthoFrame (I := I) g y i := rfl

/-- **Chart-frame expansion of the raw tensor connection Laplacian.**

For a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, a smooth
`(r, s)`-tensor section `T`, and a chart-α Levi-Civita good-set point `y`, the
value `rawTensorConnLap g r s T.toFun y` admits the textbook chart-frame
expansion as a finite trace over `i : Fin n` (with `n := Module.finrank ℝ E`)
of the difference between the chart-frame second covariant derivative
`chartTensorRSCovariantDerivative r s g α (covApply cov_RS B_i T) B_i y` and the
inner Levi-Civita Γ-correction
`cov_RS T y ((LeviCivita g) B_i y (B_i y))`, where `B_i = smoothOrthoFrame g y i`
is the `i`-th smooth orthonormal frame section at the centre `y`.

Unfolding the chart-frame piece via `chartTensorRSCovariantDerivative_def`
yields the textbook chart-coordinate expression of the connection Laplacian as
`g^{ab}(y) · [∂_a ∂_b T^I_J(y) + Christoffel terms]`. The `g^{ab}(y)` factor is
encoded geometrically by the `g_y`-orthonormal frame `smoothOrthoFrame g y`,
which carries the inverse Gram coefficients into the finite trace. -/
theorem rawTensorConnLap_eq_chart
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
    {y : M} (hy : y ∈ chartLeviCivitaGoodSet (I := I) α) :
    rawTensorConnLap (I := I) g r s T.toFun y =
      ∑ i : Fin (Module.finrank ℝ E),
        (chartTensorRSCovariantDerivative (I := I) r s g α
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
              (smoothOrthoFrame (I := I) g y i) T.toFun)
            (smoothOrthoFrame (I := I) g y i) y -
          (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun T.toFun y
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g y i) y
              (smoothOrthoFrame (I := I) g y i y))) := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  rw [rawTensorConnLap_frame_trace (I := I) g r s T.toFun y]
  refine Finset.sum_congr rfl ?_
  intro i _
  set Bi : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      smoothOrthoFrameAsSection (I := I) g y i with hBi_def
  have hSecond :=
    chartTensorRSSecondCovariantDerivative_eq_abstract
      (I := I) (M := M) g r s α T Bi Bi (y := y) hy
  have hBi_toFun : Bi.toFun = smoothOrthoFrame (I := I) g y i := by
    rw [hBi_def]
    rfl
  rw [hBi_toFun] at hSecond
  rw [hSecond]

end Connection
end Integral
end DifferentialGeometry

end
