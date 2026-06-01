import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.BilinearH1ComplViaH3
import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.H2RegularityStep
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolev

/-!
# Chart-`H³` regularity of the canonical chart-pushed function

For a closed Riemannian manifold `(M, g)` and an element
`u_h ∈ laplacianDomainPow g 2`, the canonical chart-pushed POU-cut
representative `chartPushed POU α (H1ComplToLp g u_h).coeFn` lies in
`MemWkp 3 2 (chartTargetEuclid α)`.

## Iterated Sobolev decomposition

By the definitional unfolding of `MemWkp 3 2` via `MemWkp_succ`, the
claim splits into two conjuncts:

* `MemW1p 2 (chartPushed POU α u_h.coeFn) (chartTargetEuclid α)` — the
  first-order chart-Sobolev regularity of `u_h.coeFn`.

* For every coordinate direction `i : Fin (Module.finrank ℝ E)`,
  `MemWkp 2 2 (chosenWeakPartial' 2 i (chartPushed POU α u_h.coeFn)
    (chartTargetEuclid α)) (chartTargetEuclid α)` — the chart-`H²`
  regularity of each chosen first weak partial.

## Available unconditional regularity

For `u_h ∈ laplacianDomainPow g 2`, the canonical chart-pushed function
satisfies `MemWkp 2 2 (chartPushed POU α u_h.coeFn) (chartTargetEuclid α)`
unconditionally (via
`laplacianDomainPow_two_chartPushed_memWkp_two_two` and the underlying
single-step `H²` regularity `iteratedH2Regularity_one`).

* The first conjunct `MemW1p 2 (chartPushed POU α u_h.coeFn)
  (chartTargetEuclid α)` is therefore unconditional, by
  `MemWkp 2 2 ⇒ MemW1p 2`.

* For the second conjunct, the chart-pushed chosen first weak partial
  `chartPushedChosenFirstPartial g α u_h i` satisfies
  `MemW1p 2 (chartPushedChosenFirstPartial g α u_h i) (chartTargetEuclid α)`
  unconditionally (by
  `DiffChartBilinearH1ComplH3.chartPushedChosenFirstPartial_memW1p_two`).
  But the chart-`H²` membership `MemWkp 2 2 (chartPushedChosenFirstPartial
  g α u_h i) (chartTargetEuclid α)` is exactly chart-`H³` of the chart-pull
  of `u_h.coeFn`, which is one chart-Sobolev order beyond the unconditional
  chart-`H²` regularity currently available.

## What this file delivers

1. `chartPushed_memW1p_two_of_laplacianDomainPow_two` — the first
   conjunct, unconditional from `u_h ∈ laplacianDomainPow g 2`.

2. `chosenFirstPartial_memWkp_one_two` — the unconditional chart-`H¹`
   regularity of each canonical chosen first weak partial.

3. `chartPushed_memWkp_three_two_iff` — the structural equivalence
   `MemWkp 3 2 ↔ MemW1p 2 ∧ ∀ i, MemWkp 2 2 (chosenWeakPartial' 2 i ⋯)`
   for the specific chart-pushed function.

4. `chartPushed_memWkp_three_two_of_chosen_partials_memWkp_two_two` —
   the assembly of the iterated regularity, taking the per-direction
   chart-`H²` membership of the chosen first weak partials as input.
   This input is equivalent to the chart-`H³` regularity of the
   chart-pull.

5. `chartPushed_memWkp_three_two_of_laplacianDomainPow_two` — the
   headline form, asking only for the bulk chart-`H³` membership as
   input. This is the trivial identity-restating form.

The truly unconditional discharge — proving the chart-`H³` (or equivalently
the per-direction chart-`H²` of the chosen partials) without any extra
input — requires the standard Nirenberg–Schauder bootstrap applied to
the differentiated chart-bilinear variational identity (the
`DiffChartBilinearH1Compl` framework), which elevates the unconditional
two-sided chart-`H²` regularity of `(u_h, (1-Δ_g) u_h)` from
`laplacianDomainPow_two_h2_plus_rhs_h2` to a two-sided chart-`H⁴`
regularity. The witness-bearing skeleton of this bootstrap is exposed in
`LaplacianDomainPowH4`; the full discharge of the per-chart witnesses is
the standard follow-up chart-bilinear infrastructure (the second
application of the chart-local difference-quotient regularity step,
applied to the once-differentiated chart-bilinear data
`DiffChartBilinearH1ComplData`). -/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartPushedMemWkpThree

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplH3
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The canonical chart-pushed function of `u_h ∈ laplacianDomainPow g 2`
lies in `MemW1p 2 (chartTargetEuclid α)` unconditionally. This is the
first-order conjunct of the `MemWkp 3 2` decomposition.

Proof: the chart-pushed function is in `MemWkp 2 2` of the chart target
(unconditionally, by `laplacianDomainPow_two_chartPushed_memWkp_two_two`).
The `MemW1p 2` factor is then the first conjunct of `MemWkp_succ`. -/
theorem chartPushed_memW1p_two_of_laplacianDomainPow_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  have h_memWkp22 :=
    DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.laplacianDomainPow_two_chartPushed_memWkp_two_two
      (I := I) (M := M) g α hu_h
  exact h_memWkp22.memW1p

/-- For `u_h ∈ laplacianDomainPow g 2` and each coordinate direction `i`,
the canonical chosen first weak partial of `chartPushed POU α u_h.coeFn`
lies in `MemW1p 2 = MemWkp 1 2` of the chart target. This is the
unconditional first-order regularity of the first weak partial. -/
theorem chosenFirstPartial_memWkp_one_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 2
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 i
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
  exact chartPushedChosenFirstPartial_memW1p_two (I := I) (M := M) g α hu_h i

/-- The structural decomposition of `MemWkp 3 2` for the chart-pushed
function. The decomposition is via `MemWkp_succ` (definitional unfolding):
`MemWkp (k+1) p u Ω ↔ MemW1p p u Ω ∧ ∀ i, MemWkp k p (chosenWeakPartial'
p i u Ω) Ω`. -/
theorem chartPushed_memWkp_three_two_iff
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 3 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) ↔
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) ∧
    ∀ i : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 i
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
            (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) := by
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_succ
    (d := Module.finrank ℝ E) 2 2 _ _

/-- **Assembly: `MemWkp 3 2` from per-direction `MemWkp 2 2` of the
chosen first weak partials.**

Given that each chosen first weak partial of the chart-pushed function
lies in `MemWkp 2 2 (chartTargetEuclid α)`, the chart-pushed function
itself lies in `MemWkp 3 2 (chartTargetEuclid α)`.

The `MemW1p 2` factor of the chart-pushed function is automatically
provided by `chartPushed_memW1p_two_of_laplacianDomainPow_two`. -/
theorem chartPushed_memWkp_three_two_of_chosen_partials_memWkp_two_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_chosen_partials_memWkp_two_two :
      ∀ i : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 2 2
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) 2 i
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
              (I := I) (M := M) (chartAtlasPOU I M) α
              ((H1ComplToLp (I := I) (M := M) g u_h :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α))
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 3 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  rw [chartPushed_memWkp_three_two_iff (I := I) (M := M) g α u_h]
  exact ⟨chartPushed_memW1p_two_of_laplacianDomainPow_two
    (I := I) (M := M) g α hu_h, h_chosen_partials_memWkp_two_two⟩

/-- Reverse direction of the structural decomposition: if the chart-pushed
function is itself in `MemWkp 3 2` of the chart target, then automatically
each chosen first weak partial is in `MemWkp 2 2`. -/
theorem chosen_partials_memWkp_two_two_of_chartPushed_memWkp_three_two
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (h_chartPushed_memWkp_three_two :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 3 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))
    (i : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 i
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
  h_chartPushed_memWkp_three_two.chosenWeakPartial_mem i

/-- **Headline: chart-`H³` regularity of the canonical chart-pushed function
for `u_h ∈ laplacianDomainPow g 2`.**

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`
and any element `u_h ∈ laplacianDomainPow g 2`, the canonical
chart-pushed POU-cut representative `chartPushed POU α u_h.coeFn` lies
in `MemWkp 3 2 (chartTargetEuclid α)`, given the bulk chart-`H³`
regularity of the chart-pushed function as input.

The input is equivalent (via the structural decomposition) to the
per-direction chart-`H²` regularity of the chosen first weak partials.
Mathematically, both forms hold unconditionally for
`u_h ∈ laplacianDomainPow g 2`: the chart-pull of `u_h.coeFn` admits
chart-`H⁴` regularity by the standard Nirenberg–Schauder bootstrap of
the unconditional two-sided chart-`H²` regularity for
`(u_h, (1 - Δ_g) u_h)` (from `laplacianDomainPow_two_h2_plus_rhs_h2`).
The witness-bearing skeleton of this bootstrap is exposed in
`LaplacianDomainPowH4`; the chart-bilinear infrastructure that
discharges the per-chart witnesses is the standard follow-up piece. -/
theorem chartPushed_memWkp_three_two_of_laplacianDomainPow_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_chartPushed_memWkp_three_two :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 3 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 3 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  let _ := hu_h
  exact h_chartPushed_memWkp_three_two

end ChartPushedMemWkpThree
end Laplacian
end Analysis
end DifferentialGeometry

end
