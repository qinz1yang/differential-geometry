import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.BaseFChartMemWkp22
import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.ChosenFChartDerivMemW1p
import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.TwiceDifferentiatedIdentity
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartPushed.MemWkpFourSmooth
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.PowH2kBridge
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.PowH4Bridge

/-!
# Truly unconditional chart-`H⁴` regularity of the chart-pushed function

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` and
an element `u_h ∈ laplacianDomainPow g 2`, the canonical chart-pushed POU-cut
representative `chartPushed POU α (H1ComplToLp g u_h).coeFn` lies in
`MemWkp 4 2 (chartTargetEuclid α)` unconditionally. The corresponding
per-chart `ChartSideH2kBridge g 2` and manifold-level `MemWkpChart g 4 2`
headlines follow.

## Composition strategy

The chart-`H⁴` discharge factors through the twice-differentiated
chart-bilinear variational identity. The hypothesis-bearing assemblies
in `ChartPushedMemWkpFourSmooth` expose the family of those
identities as a per-pair (or per-α-per-pair) hypothesis; this file
assembles that family by composing three unconditional ingredients:

1. `base_f_chart_memWkp_two_two` — unconditional
   chart-`H²` of `base.f_chart` on the chart target.
2. `chosenFChartDeriv_memW1p_truly_unconditional` — unconditional
   `MemW1p 2` of the chart-side once-differentiated derivative,
   given step 1.
3. `twice_differentiated_variational_identity_holds` — the twice-
   differentiated chart-bilinear variational identity, given step 2.

Step 3 produces the exact per-pair hypothesis required by the
`ChartPushedMemWkpFourSmooth` constructors; composing through
the chain yields the truly unconditional headlines.

## Main results

* `chartPushed_memWkp_four_two_of_laplacianDomainPow_two` — the chart-
  `H⁴` regularity of the chart-pushed function on the full chart target.
* `chartSideH2kBridge_two_of_laplacianDomainPow_two` — the per-chart
  `ChartSideH2kBridge g 2` predicate for the canonical function
  representative.
* `laplacianDomainPow_memWkpChart_four_two_of_laplacianDomainPow_two` —
  the manifold-level `MemWkpChart g 4 2` membership together with finite
  chart-based norm.
* `chartSideH4Bridge_of_laplacianDomainPow_two` — the equivalent
  formulation as a `ChartSideH4Bridge`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartPushedMemWkpFour

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChosenThirdMixedPartialChartPushed
open DifferentialGeometry.Analysis.Laplacian.FChartEffTwiceDef
open DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22
open DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p
open DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity
open DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The family of twice-differentiated chart-bilinear variational identities
for `u_h ∈ laplacianDomainPow g 2` at a fixed chart point `α : M`. Indexed
by ordered direction pairs `(l₁, l₂)` and the test function `ψ`. -/
private lemma twice_diff_identities_at
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    ∀ l₁ l₂ : Fin (Module.finrank ℝ E),
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ l₂ y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN))
        + (∫ y in chartTargetEuclid (I := I) (M := M) α,
            densityOnEuclid (I := I) g α y *
              chosenSecondPartialChartPushedU
                (I := I) (M := M) g α u_h l₁ l₂ y * ψ y
            ∂(volume : Measure EuclN)) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            fChartEffTwice (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
          ∂(volume : Measure EuclN) := by
  intro l₁ l₂ ψ hψ_smooth hψ_cs hψ_supp
  have h_base_f_chart_memWkp22 :=
    base_f_chart_memWkp_two_two
      (I := I) (M := M) g α hu_h
  have h_chosenFChartDeriv_memW1p :=
    chosenFChartDeriv_memW1p_truly_unconditional
      (I := I) (M := M) g α hu_h l₁ h_base_f_chart_memWkp22
  exact twice_differentiated_variational_identity_holds
    (I := I) (M := M) g α hu_h l₁ l₂ h_chosenFChartDeriv_memW1p
    hψ_smooth hψ_cs hψ_supp

/-- **Headline: truly unconditional chart-`H⁴` of the chart-pushed function.**

For a closed Riemannian manifold `(M, g)`, a chart point `α : M`, and
`u_h ∈ laplacianDomainPow g 2`, the canonical chart-pushed POU-cut
representative `chartPushed POU α (H1ComplToLp g u_h).coeFn` lies in
`MemWkp 4 2 (chartTargetEuclid α)`, with no further hypotheses.

Proof: instantiate the per-pair family of twice-differentiated chart-bilinear
variational identities by composing the three unconditional ingredients
(`base.f_chart ∈ MemWkp 2 2`, `chosenFChartDeriv ∈ MemW1p 2`, twice-differentiated
identity), then apply
`chartPushed_memWkp_four_two_of_laplacianDomainPow_two_of_twice_diff_identities`. -/
theorem chartPushed_memWkp_four_two_of_laplacianDomainPow_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 4 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
  chartPushed_memWkp_four_two_of_laplacianDomainPow_two_of_twice_diff_identities
    (I := I) (M := M) g α hu_h
    (twice_diff_identities_at (I := I) (M := M) g α hu_h)

/-- **Headline: truly unconditional `ChartSideH2kBridge g 2` for the canonical
function representative.**

For `u_h ∈ laplacianDomainPow g 2`, the per-chart `MemWkp (2*2) 2` predicate
`ChartSideH2kBridge g 2 ((H1ComplToLp g u_h).coeFn)` holds, with no further
hypotheses.

Proof: instantiate the α-indexed family of twice-differentiated chart-
bilinear variational identities (one per chart point `α : M` and ordered
pair `(l₁, l₂)`) by composing the three unconditional ingredients at each
`α`, then apply `chartSideH2kBridge_two_of_twice_diff_identities`. -/
theorem chartSideH2kBridge_two_of_laplacianDomainPow_two
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    ChartSideH2kBridge (I := I) (M := M) g 2
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) :=
  chartSideH2kBridge_two_of_twice_diff_identities
    (I := I) (M := M) g hu_h
    (fun α => twice_diff_identities_at (I := I) (M := M) g α hu_h)

/-- **Headline: truly unconditional manifold-level `MemWkpChart g 4 2`.**

For `u_h ∈ laplacianDomainPow g 2`, the canonical function representative
`(H1ComplToLp g u_h).coeFn` lies in `MemWkpChart g 4 2` with finite chart-
based norm, unconditionally.

Proof: assemble the per-chart `ChartSideH2kBridge g 2` predicate from
the chain of unconditional discharges, then apply
`laplacianDomainPow_memWkpChart_four_two_of_twice_diff_identities`. -/
theorem laplacianDomainPow_memWkpChart_four_two_of_laplacianDomainPow_two
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 4 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 4 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ :=
  laplacianDomainPow_memWkpChart_four_two_of_twice_diff_identities
    (I := I) (M := M) g hu_h
    (fun α => twice_diff_identities_at (I := I) (M := M) g α hu_h)

/-- **Headline (equivalent form): truly unconditional `ChartSideH4Bridge`.**

For `u_h ∈ laplacianDomainPow g 2`, the predicate `ChartSideH4Bridge` for
the canonical function representative holds unconditionally.

This is the equivalent reformulation of
`chartSideH2kBridge_two_of_laplacianDomainPow_two` through the structural
identity `2 * 2 = 4`. -/
theorem chartSideH4Bridge_of_laplacianDomainPow_two
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH4Bridge.ChartSideH4Bridge
      (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) :=
  chartSideH4Bridge_of_chartSideH2kBridge_two (I := I) (M := M) g
    (chartSideH2kBridge_two_of_laplacianDomainPow_two
      (I := I) (M := M) g hu_h)

end ChartPushedMemWkpFour
end Laplacian
end Analysis
end DifferentialGeometry

end
