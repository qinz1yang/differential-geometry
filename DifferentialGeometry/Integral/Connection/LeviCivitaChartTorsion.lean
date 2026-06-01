import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import DifferentialGeometry.Integral.Connection.LeviCivitaChartLocal
import DifferentialGeometry.Integral.Connection.ChartLieBracket

/-!
# Torsion-free property of the chart-local Levi-Civita covariant derivative

The chart-local Levi-Civita covariant derivative
`chartLeviCivita g α : (Π x : M, TangentSpace I x) →
  (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)`,
defined chart-by-chart at the basepoint `α : M` (see
`LeviCivitaChartLocal.lean`), satisfies the torsion-free identity on its open
*good set*:
$$
  \nabla_X Y - \nabla_Y X = [X, Y]
$$
when both sections `X, Y` are manifold-differentiable at the evaluation point.

In Mathlib's notation, with `cov := chartLeviCivita g α`, the identity reads
$$
  \mathrm{cov}\,Y\,x\,(X x) - \mathrm{cov}\,X\,x\,(Y x) =
    \mathrm{mlieBracket}\,I\,X\,Y\,x.
$$

## Proof outline

1. Expand both `chartLeviCivita g α Y x (X x)` and
   `chartLeviCivita g α X x (Y x)` via `chartLeviCivita_apply`. Each is
   `trivFromE α x` applied to a sum of two pieces:
   - a Fréchet-derivative term coming from the chart-trivialised
     representation, and
   - a Christoffel-correction term `christoffelCorrection α x ...`.

2. The Christoffel-correction terms cancel in the difference. By the symmetry
   `chartChristoffel_symm` (the Christoffel symbol of the second kind is
   symmetric in its lower indices `i, j`), the two correction sums turn out to
   be equal after a relabeling of the summation indices, leaving zero in the
   difference.

3. What remains is the chart-α-coordinate Lie bracket:
   $$
     \mathrm{trivFromE}\,\alpha\,x\bigl(
       \mathrm{fderiv}\,\mathbb{R}\,(Y^E_\alpha \circ \varphi_\alpha^{-1})
         (\varphi_\alpha\,x)(\mathrm{trivToE}\,\alpha\,x\,(X x))
       - \mathrm{fderiv}\,\mathbb{R}\,(X^E_\alpha \circ \varphi_\alpha^{-1})
         (\varphi_\alpha\,x)(\mathrm{trivToE}\,\alpha\,x\,(Y x))\bigr).
   $$
   This is identified with `mlieBracket I X Y x` via the chart-α-generalised
   identity `mlieBracket_eq_chart_fderiv_diff_general` proved in
   `ChartLieBracket.lean`.

The torsion-free property is the second of the two characterising axioms of
the Levi-Civita connection (the first being metric compatibility, treated in a
separate file). Together with the additivity and Leibniz rule axioms verified
in `LeviCivitaChartLocal.lean`, the chart-local construction is shown to be
the Levi-Civita connection on the open good set at `α`.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-- **Symmetry-cancellation of the Christoffel correction.** For two
tangent vectors `v, w : TangentSpace I x`, the Christoffel-correction CLMs
satisfy
$$
  \mathrm{christoffelCorrection}\,g\,\alpha\,x\,(\mathrm{trivToE}\,\alpha\,x\,w)\,v
  =
  \mathrm{christoffelCorrection}\,g\,\alpha\,x\,(\mathrm{trivToE}\,\alpha\,x\,v)\,w.
$$
This is the chart-coordinate manifestation of the torsion-free property of
the Levi-Civita Christoffel symbol. -/
lemma christoffelCorrection_symm_cancel
    (g : SmoothRiemannianMetric I M) (α : M) (x : M) (v w : TangentSpace I x) :
    christoffelCorrection (I := I) g α x (trivToE (I := I) α x w) v =
      christoffelCorrection (I := I) g α x (trivToE (I := I) α x v) w := by
  classical
  rw [christoffelCorrection_apply, christoffelCorrection_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [chartChristoffel_symm (I := I) g α j i k (extChartAt I α x)]
  congr 1
  ring

set_option linter.unusedVariables false in
/-- **Torsion-free property of the chart-local Levi-Civita.** On the good set
at `α`, the chart-local Levi-Civita covariant derivative `chartLeviCivita g α`
satisfies the classical torsion-free identity in Mathlib's convention:
$$
  (\mathrm{chartLeviCivita}\,g\,\alpha)\,Y\,x\,(X x)
  - (\mathrm{chartLeviCivita}\,g\,\alpha)\,X\,x\,(Y x)
  = \mathrm{mlieBracket}\,I\,X\,Y\,x.
$$
The proof expands both terms on the LHS via `chartLeviCivita_apply`, observes
that the Christoffel-correction terms cancel (by
`christoffelCorrection_symm_cancel`, which uses the symmetry of the Christoffel
symbol of the second kind in its lower indices), and identifies the remaining
Fréchet-derivative difference with the manifold Lie bracket via
`mlieBracket_eq_chart_fderiv_diff_general` (the chart-α-coordinate form of
the Lie-bracket-as-Fréchet-derivative identity). -/
theorem chartLeviCivita_torsion_free_on (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ {X Y : Π x : M, TangentSpace I x} {x : M},
      MDiffAt (T% X) x → MDiffAt (T% Y) x →
      x ∈ chartLeviCivitaGoodSet (I := I) α →
      chartLeviCivita (I := I) g α Y x (X x)
        - chartLeviCivita (I := I) g α X x (Y x) =
        VectorField.mlieBracket I X Y x := by
  intro X Y x hX hY hx
  classical
  have hx_src : x ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hx
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  have hx_int : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx
  rw [chartLeviCivita_apply (I := I) g α Y hx (X x)]
  rw [chartLeviCivita_apply (I := I) g α X hx (Y x)]
  rw [← map_sub]
  have hreorg :
      (fderiv ℝ (chartE_section_repr (I := I) α Y ∘ (extChartAt I α).symm)
            (extChartAt I α x) (trivToE (I := I) α x (X x))
        + christoffelCorrection (I := I) g α x
            (chartE_section_repr (I := I) α Y x) (X x))
      - (fderiv ℝ (chartE_section_repr (I := I) α X ∘ (extChartAt I α).symm)
            (extChartAt I α x) (trivToE (I := I) α x (Y x))
        + christoffelCorrection (I := I) g α x
            (chartE_section_repr (I := I) α X x) (Y x))
      =
      (fderiv ℝ (chartE_section_repr (I := I) α Y ∘ (extChartAt I α).symm)
            (extChartAt I α x) (trivToE (I := I) α x (X x))
        - fderiv ℝ (chartE_section_repr (I := I) α X ∘ (extChartAt I α).symm)
            (extChartAt I α x) (trivToE (I := I) α x (Y x))) := by
    have hY_repr : chartE_section_repr (I := I) α Y x =
        trivToE (I := I) α x (Y x) :=
      chartE_section_repr_eq_trivToE (I := I) α Y x
    have hX_repr : chartE_section_repr (I := I) α X x =
        trivToE (I := I) α x (X x) :=
      chartE_section_repr_eq_trivToE (I := I) α X x
    rw [hY_repr, hX_repr]
    have hcancel :
        christoffelCorrection (I := I) g α x (trivToE (I := I) α x (Y x)) (X x) =
          christoffelCorrection (I := I) g α x (trivToE (I := I) α x (X x)) (Y x) :=
      christoffelCorrection_symm_cancel (I := I) g α x (X x) (Y x)
    rw [hcancel]
    abel
  rw [hreorg]
  exact (mlieBracket_eq_chart_fderiv_diff_general (I := I) α x X Y
    hx_src hx_base hx_int hX hY).symm

end Connection
end Integral
end DifferentialGeometry
