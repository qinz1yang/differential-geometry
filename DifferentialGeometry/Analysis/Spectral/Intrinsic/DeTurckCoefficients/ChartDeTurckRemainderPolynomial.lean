import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartLieDerivStructuralDifference
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieMatrixChartBridge
import DifferentialGeometry.Geometry.Connection.ChartBridge.RiemannBasisIdentityOffCentre
import DifferentialGeometry.Geometry.Flow.LieDerivativeChartFrameIdentity
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonDeTurckPullback

/-!
# The chart-coordinate-polynomial form of the DeTurck–Ricci remainder

For a fixed chart base point `α` on a smooth manifold `M`, a fixed background metric
`g_bg`, and two smooth Riemannian metrics `g₁, g₂` (chart Grams `G₁, G₂`), this file
assembles the chart-frame scalar carrier of the DeTurck–Ricci right-hand side and
expresses its **difference** as an explicit finite sum of products of chart components
of `g₁ − g₂` (Gram entries and their first/second chart partial derivatives) with plain
(undifferenced) inverse-Gram / Gram-partial / Christoffel(-derivative) data of `g₁` or
`g₂`.  Every summand of the difference carries exactly one metric-difference factor
whose chart-jet order is at most `2` on the difference data, which is precisely the
shape the per-field Moser-tame `L²` product estimates consume.

## The chart-scalar DeTurck–Ricci carrier

The intrinsic DeTurck–Ricci right-hand side decomposes pointwise as
`deTurckRicciRHS g_bg g x = -2 · Rc(g)_x + (𝓛_{W(g)} g)_x`
(`deTurckRicciRHS_apply`), with `W(g) = deTurckVF g g_bg`.  Reading off its
chart-`α` frame components on the Levi-Civita good set gives the chart scalar
`chartDeTurckRicciRHS g g_bg α i k = -2 · chartRicciTensor g α i k +
  chartLieDeTurckComp g g_bg α i k`,
where `chartRicciTensor` is the classical coordinate Ricci scalar and
`chartLieDeTurckComp` is the classical coordinate DeTurck Lie-summand
`(𝓛_{W(g)} g)_{ik}`.  This identification is recorded by
`deTurckRicciRHS_chartBasisVecFiber_eq_chartDeTurckRicciRHS`: at a good-set point `x`,
the chart-basis matrix entry of the genuine intrinsic operator equals this chart
scalar evaluated at `ϕ_α x`.

## The chart-polynomial remainder identity

Subtracting at two metrics and applying the two master single-difference-factor
decompositions
* `chartRicciTensor_sub_eq_christoffelDiff` (the Ricci half), and
* `chartLieDeTurckComp_sub_eq` (the Lie/DeTurck-vector-field half),
yields `chartDeTurckRicciRHS_sub_eq`: the chart DeTurck–Ricci remainder as
`-2 · (Ricci structural difference) + (Lie structural difference)`.  Each structural
difference is a finite sum of products in which a single factor is a Christoffel,
Christoffel-derivative, Gram, Gram-first-partial, or DeTurck-vector-field-component
(-partial) **difference** — each of those in turn a single-Gram-difference object via
`invGramOnE_sub_eq`, `gramBracket_sub_eq`, `gramBracketDeriv_sub_eq`,
`chartChristoffel_sub_eq`, `partialDeriv_chartChristoffel_sub_eq`,
`chartDeTurckVFComp_sub_eq`, `partialDeriv_chartDeTurckVFComp_sub_eq` — so every
monomial of the remainder is a product of factors of chart-jet order `≤ 2` on
`g₁ − g₂`.

The companion `chartDeTurckRicciRHS_sub_eq_principalSymbol_add_lowerOrder` exhibits the
same remainder with the genuinely-second-order Ricci principal symbol
`ricciDiffPrincipalSymbol` (the `Δ`-linearization, linear in `∂²(g₁−g₂)`) split off,
leaving the first-order-and-below remainder explicit.  This is the bridge consumed by
the downstream Nemytskii / Sobolev development of the continuous, non-gated DeTurck
nonlinearity.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Set Matrix
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurckCoefficients

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]

/-! ### The chart-scalar DeTurck–Ricci carrier -/

/-- **The chart-frame scalar DeTurck–Ricci right-hand side.**  The classical coordinate
read-off of the intrinsic `deTurckRicciRHS g_bg g`: at chart base point `α`, frame
indices `(i, k)`, and chart coordinate `y`, it is
`-2 · chartRicciTensor g α i k y + chartLieDeTurckComp g g_bg α i k y`, i.e. the chart
scalar `-2 · Rc(g)_{ik} + (𝓛_{W(g)} g)_{ik}` of `deTurckRicciRHS_apply` with
`W(g) = deTurckVF g g_bg`. -/
def chartDeTurckRicciRHS (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  -2 * chartRicciTensor (I := I) g α i k y +
    chartLieDeTurckComp (I := I) g g_bg α i k y

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] [I.Boundaryless] in
/-- Unfolding lemma for `chartDeTurckRicciRHS`. -/
theorem chartDeTurckRicciRHS_def (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckRicciRHS (I := I) g g_bg α i k y =
      -2 * chartRicciTensor (I := I) g α i k y +
        chartLieDeTurckComp (I := I) g g_bg α i k y := rfl

/-- **The chart scalar is the genuine chart read-off of the intrinsic operator.**  At a
chart-`α` Levi-Civita good-set point `x`, the matrix entry of the intrinsic
`deTurckRicciRHS g_bg g` on the chart basis vectors `(eᵢ, eₖ)` equals the chart scalar
`chartDeTurckRicciRHS g g_bg α i k` evaluated at `ϕ_α x`.

This grounds the chart-scalar carrier against the sealed intrinsic object: the chart
polynomial below is not a free-standing definition but the coordinate expression of the
true DeTurck–Ricci right-hand side.  It chains the intrinsic split
`deTurckRicciRHS_apply` with the two chart read-off legs
`ricciTensor_chartBasisVec_alpha_eq` (Ricci) and
`chartLieDerivMetricMatrix_eq_lieDerivMetric_chartBasis` ∘
`chartLieDerivMetricMatrix_deTurckVF_eq_chartLieDeTurckComp` (Lie/DeTurck). -/
theorem deTurckRicciRHS_chartBasisVecFiber_eq_chartDeTurckRicciRHS
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet (I := I) α) :
    DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg g x
          (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) α i x)
          (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) α k x) =
      chartDeTurckRicciRHS (I := I) g g_bg α i k (extChartAt I α x) := by
  classical
  rw [DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS_apply]
  rw [DifferentialGeometry.Integral.Connection.ricciTensor_chartBasisVec_alpha_eq
      (I := I) g α i k hx]
  rw [← DifferentialGeometry.PDE.DeTurck.chartLieDerivMetricMatrix_eq_lieDerivMetric_chartBasis
      (I := I) g (DifferentialGeometry.PDE.DeTurck.deTurckVF (I := I) g g_bg) α i k x hx]
  rw [chartLieDerivMetricMatrix_deTurckVF_eq_chartLieDeTurckComp (I := I) g g_bg α i k hx]
  rw [chartDeTurckRicciRHS_def]

/-! ### The chart-polynomial remainder identity -/

omit [BoundarylessManifold I M] in
/-- **Master chart-polynomial DeTurck–Ricci remainder identity.**

At every chart-coordinate point `y`, the chart DeTurck–Ricci remainder
`chartDeTurckRicciRHS g₁ g_bg α i k y − chartDeTurckRicciRHS g₂ g_bg α i k y` equals
`-2` times the master single-difference-factor Ricci decomposition
(`chartRicciTensor_sub_eq_christoffelDiff`) plus the master single-difference-factor
DeTurck Lie-summand decomposition (`chartLieDeTurckComp_sub_eq`).

The right-hand side is an explicit finite sum of products: every summand carries exactly
one Christoffel / Christoffel-derivative / Gram / Gram-first-partial / DeTurck
vector-field-component(-partial) **difference** factor (a single `g₁ − g₂` jet of
chart order `≤ 2`), the remaining factors being plain (undifferenced) chart Christoffel,
Gram, or DeTurck-vector-field-component data of `g₁` or `g₂`.  This is the chart
polynomial whose monomials the Moser-tame `L²` product estimates majorise term by term. -/
theorem chartDeTurckRicciRHS_sub_eq
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckRicciRHS (I := I) g₁ g_bg α i k y -
        chartDeTurckRicciRHS (I := I) g₂ g_bg α i k y =
      -2 *
          ((∑ j : Fin (Module.finrank ℝ E),
              ((partialDeriv (E := E) j (chartChristoffel (I := I) g₁ α i k j) y -
                    partialDeriv (E := E) j (chartChristoffel (I := I) g₂ α i k j) y) -
                (partialDeriv (E := E) k (chartChristoffel (I := I) g₁ α i j j) y -
                  partialDeriv (E := E) k (chartChristoffel (I := I) g₂ α i j j) y))) +
            (∑ j : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
              (((chartChristoffel (I := I) g₁ α j m j y -
                      chartChristoffel (I := I) g₂ α j m j y) *
                    chartChristoffel (I := I) g₁ α i k m y +
                  chartChristoffel (I := I) g₂ α j m j y *
                    (chartChristoffel (I := I) g₁ α i k m y -
                      chartChristoffel (I := I) g₂ α i k m y)) -
                ((chartChristoffel (I := I) g₁ α k m j y -
                      chartChristoffel (I := I) g₂ α k m j y) *
                    chartChristoffel (I := I) g₁ α i j m y +
                  chartChristoffel (I := I) g₂ α k m j y *
                    (chartChristoffel (I := I) g₁ α i j m y -
                      chartChristoffel (I := I) g₂ α i j m y))))) +
        ((∑ kk : Fin (Module.finrank ℝ E),
            ((chartDeTurckVFComp (I := I) g₁ g_bg α kk y -
                  chartDeTurckVFComp (I := I) g₂ g_bg α kk y) *
                partialDeriv (E := E) kk (chartGramOnE (I := I) g₁ α i k) y +
              chartDeTurckVFComp (I := I) g₂ g_bg α kk y *
                (partialDeriv (E := E) kk (chartGramOnE (I := I) g₁ α i k) y -
                  partialDeriv (E := E) kk (chartGramOnE (I := I) g₂ α i k) y))) +
          (∑ kk : Fin (Module.finrank ℝ E),
              ((chartGramOnE (I := I) g₁ α kk k y - chartGramOnE (I := I) g₂ α kk k y) *
                  partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α kk) y +
                chartGramOnE (I := I) g₂ α kk k y *
                  (partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α kk) y -
                    partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₂ g_bg α kk) y))) +
            (∑ kk : Fin (Module.finrank ℝ E),
              ((chartGramOnE (I := I) g₁ α i kk y - chartGramOnE (I := I) g₂ α i kk y) *
                  partialDeriv (E := E) k (chartDeTurckVFComp (I := I) g₁ g_bg α kk) y +
                chartGramOnE (I := I) g₂ α i kk y *
                  (partialDeriv (E := E) k (chartDeTurckVFComp (I := I) g₁ g_bg α kk) y -
                    partialDeriv (E := E) k (chartDeTurckVFComp (I := I) g₂ g_bg α kk) y)))) := by
  classical
  rw [chartDeTurckRicciRHS_def, chartDeTurckRicciRHS_def]
  rw [show -2 * chartRicciTensor (I := I) g₁ α i k y +
            chartLieDeTurckComp (I := I) g₁ g_bg α i k y -
          (-2 * chartRicciTensor (I := I) g₂ α i k y +
            chartLieDeTurckComp (I := I) g₂ g_bg α i k y) =
        -2 * (chartRicciTensor (I := I) g₁ α i k y - chartRicciTensor (I := I) g₂ α i k y) +
          (chartLieDeTurckComp (I := I) g₁ g_bg α i k y -
            chartLieDeTurckComp (I := I) g₂ g_bg α i k y) from by ring]
  rw [chartRicciTensor_sub_eq_christoffelDiff (I := I) g₁ g₂ α i k y,
    chartLieDeTurckComp_sub_eq (I := I) g₁ g₂ g_bg α i k y]

/-! ### The remainder with the `Δ`-linearization split off -/

omit [BoundarylessManifold I M] in
/-- **Chart DeTurck–Ricci remainder with the Ricci principal symbol (`Δ`-linearization)
split off.**

At every chart-coordinate point `y`, the chart DeTurck–Ricci remainder equals `-2`
times the second-order Ricci principal symbol `ricciDiffPrincipalSymbol` (the genuinely
`∂²(g₁−g₂)`-linear `Δ`-linearization) plus an explicit lower-order remainder: `-2` times
the Ricci first-order remainder `chartRicciDiffFirstOrderRemainder` and Ricci
`Γ·Γ`-difference, plus the full DeTurck Lie-summand structural difference
`chartLieDeTurckComp_sub_eq`.  Each lower-order term is a product carrying a single
metric-difference factor of chart-jet order `≤ 1` (the `∂²`-difference appears only
inside the principal symbol), exhibiting the affine-in-`∂²(g₁−g₂)` structure consumed by
the Sobolev tame-product development. -/
theorem chartDeTurckRicciRHS_sub_eq_principalSymbol_add_lowerOrder
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckRicciRHS (I := I) g₁ g_bg α i k y -
        chartDeTurckRicciRHS (I := I) g₂ g_bg α i k y =
      -2 * ricciDiffPrincipalSymbol (I := I) g₁ g₂ α i k y +
        (-2 *
            (chartRicciDiffFirstOrderRemainder (I := I) g₁ g₂ α i k y +
              (chartRicciFirstOrderTerm (I := I) g₁ α i k y -
                chartRicciFirstOrderTerm (I := I) g₂ α i k y)) +
          ((∑ kk : Fin (Module.finrank ℝ E),
              ((chartDeTurckVFComp (I := I) g₁ g_bg α kk y -
                    chartDeTurckVFComp (I := I) g₂ g_bg α kk y) *
                  partialDeriv (E := E) kk (chartGramOnE (I := I) g₁ α i k) y +
                chartDeTurckVFComp (I := I) g₂ g_bg α kk y *
                  (partialDeriv (E := E) kk (chartGramOnE (I := I) g₁ α i k) y -
                    partialDeriv (E := E) kk (chartGramOnE (I := I) g₂ α i k) y))) +
            (∑ kk : Fin (Module.finrank ℝ E),
                ((chartGramOnE (I := I) g₁ α kk k y - chartGramOnE (I := I) g₂ α kk k y) *
                    partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α kk) y +
                  chartGramOnE (I := I) g₂ α kk k y *
                    (partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α kk) y -
                      partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₂ g_bg α kk) y))) +
              (∑ kk : Fin (Module.finrank ℝ E),
                ((chartGramOnE (I := I) g₁ α i kk y - chartGramOnE (I := I) g₂ α i kk y) *
                    partialDeriv (E := E) k (chartDeTurckVFComp (I := I) g₁ g_bg α kk) y +
                  chartGramOnE (I := I) g₂ α i kk y *
                    (partialDeriv (E := E) k (chartDeTurckVFComp (I := I) g₁ g_bg α kk) y -
                      partialDeriv (E := E) k (chartDeTurckVFComp (I := I) g₂ g_bg α kk) y))))) := by
  classical
  rw [chartDeTurckRicciRHS_def, chartDeTurckRicciRHS_def]
  rw [show -2 * chartRicciTensor (I := I) g₁ α i k y +
            chartLieDeTurckComp (I := I) g₁ g_bg α i k y -
          (-2 * chartRicciTensor (I := I) g₂ α i k y +
            chartLieDeTurckComp (I := I) g₂ g_bg α i k y) =
        -2 * (chartRicciTensor (I := I) g₁ α i k y - chartRicciTensor (I := I) g₂ α i k y) +
          (chartLieDeTurckComp (I := I) g₁ g_bg α i k y -
            chartLieDeTurckComp (I := I) g₂ g_bg α i k y) from by ring]
  rw [chartRicciTensor_sub_eq_principalSymbol_add_lowerOrder (I := I) g₁ g₂ α i k y,
    chartLieDeTurckComp_sub_eq (I := I) g₁ g₂ g_bg α i k y]
  ring

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
