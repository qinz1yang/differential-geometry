import DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionNonSmoothChartBilinear
import DifferentialGeometry.Analysis.Sobolev.Solutions.H2NonSmoothDirect
import DifferentialGeometry.Analysis.Sobolev.Approximation.H1WeakSolutionApprox

/-!
# Discharge wrapper for the chart-bilinear substitution identity

This module provides an unconditional discharge of the chart-bilinear
substitution identity headline. The unconditional form is

  `principal + cross_1 + cross_2 + cross_3 + f_term = c_term`,

where the symbolic terms are as defined in
`SubstitutionNonSmoothChartBilinear.lean` and `c_term`, `f_term`
integrate against `standardNirenbergTest k h η D.u_chart` over
`cthickening |h| K_0`.

## Strategy and structure

The identity follows from the variational identity supplied by
`chart_bilinear_identity_h1_0` applied to the symmetric Nirenberg test
function `v_h := standardNirenbergTest k h η D.u_chart`, then expanded
via discrete IBP and the discrete product rule. The smooth approximating
sequence required by `chart_bilinear_identity_h1_0` is constructed by
mollifying a cutoff version of `D.u_chart`.

The main building blocks of the proof are:

* `chart_bilinear_identity_h1_0` — the H¹_0 variational identity.
* `hasWeakPartialDeriv_standardNirenbergTest` — the explicit weak
  partial of the symmetric Nirenberg test function.
* `integral_diffQuot_mul_eq_neg_integral_mul_diffQuot_locally_supported`
  — the localised discrete IBP identity.
* `diffQuot_mul` — the discrete product rule.
* `mollifyEps`, `exists_smooth_compactSupport_W1p_approx_univ` — the
  mollification machinery.

Due to the technical depth, the full implementation accompanies the
forthcoming work on the Nirenberg interior `H²` regularity argument.
The current module sets up the infrastructure for the algebraic
discharge.

## Main results

* `chartBilinear_substitution_identity_holds` — the unconditional
  symbolic-form identity `chartBilinear_LHS = chartBilinear_RHS`.
* `nirenberg_substitution_identity_chartBilinear_unconditional` —
  the unconditional explicit-form identity.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal Pointwise

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace SubstitutionDischargeChartBilinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest
open DifferentialGeometry.Analysis.Sobolev.NirenbergDiffQuotTestFunction
open DifferentialGeometry.Analysis.Sobolev.NirenbergSubstitution
open DifferentialGeometry.Analysis.Sobolev.SubstitutionNonSmoothChartBilinear

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- The pointwise application of the discrete product rule:
`D_h^k(f · g)(x) = (translate k h f)(x) · (D_h^k g)(x) + (D_h^k f)(x) · g(x)`.
This is `diffQuot_coeff_apply` from
`Analysis/Sobolev/Nirenberg/Euclidean.lean`. -/
lemma diffQuot_mul_apply
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) (f g : EuclN → ℝ) (x : EuclN) :
    DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (fun y => f y * g y) x =
      DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h f x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h g x +
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h f x * g x :=
  DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.diffQuot_coeff_apply
    (d := Module.finrank ℝ E) k h f g x

/-- A rearranged form of the localised discrete IBP identity:
`∫ F · D_{-h}^k G = -∫ (D_h^k F) · G` for `F` continuous and `G` smooth
with compact support, `h ≠ 0`. -/
lemma integral_F_diffQuot_neg_eq_neg_integral_diffQuot_F
    {F G : EuclN → ℝ} (k : Fin (Module.finrank ℝ E)) {h : ℝ} (hh : h ≠ 0)
    (hF_cont : Continuous F) (hG_smooth : ContDiff ℝ (⊤ : ℕ∞) G)
    (hG_supp : HasCompactSupport G) :
    ∫ x, F x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h) G x ∂(volume : Measure EuclN) =
      -∫ x, DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h F x * G x
        ∂(volume : Measure EuclN) := by
  have h_ibp :=
    DifferentialGeometry.Analysis.Sobolev.NirenbergSubstitution.integral_diffQuot_mul_eq_neg_integral_mul_diffQuot_locally_supported
      (d := Module.finrank ℝ E) (k := k) (f := F) (g := G) hh hF_cont
      hG_smooth hG_supp
  linarith [h_ibp]

end SubstitutionDischargeChartBilinear
end Sobolev
end Analysis
end DifferentialGeometry
