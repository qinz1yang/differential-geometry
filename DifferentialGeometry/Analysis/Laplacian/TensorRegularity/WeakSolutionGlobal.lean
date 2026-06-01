import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.ChartWeakIdentity
import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.SourcePairing
import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.ChartIntegrationByParts

/-!
# The per-component scalar weak-solution headline from the global weak equation

For a smooth Riemannian metric `g` on a closed manifold `(M, g)`, a chart center
`α : M`, tensor ranks `(r, s)`, and a component multi-index `P₀`, this file
derives the genuine, unconditional per-component scalar weak-solution headline of
the connection Laplacian on `(r, s)`-tensor sections.

The companion file `WeakSolution.lean` proves the hypothesis-bearing form
`tensorComponent_isSmoothWeakSolution_of_chartIdentity`: it *takes* a chart
bilinear identity for the principal-part form `tensorPrincipalForm` and concludes
the Euclidean chart component is a smooth weak solution. This file supplies that
chart bilinear identity from the genuine analytic input — the global `H^1` weak
equation of the connection Laplacian — and ships the unconditional headline
`tensorComponent_isSmoothWeakSolution`.

## The derivation

Given the global weak equation `∫_M ⟨∇T, ∇v⟩ dμ_g = ⟨F, v⟩_{L²}` for every smooth
compactly-supported test section `v`, the chart bilinear identity is obtained by
substituting the inverse-Gram-rotated test section `rotatedTestSection g r s α P₀
χ` for `v`, where `χ := chartTestPullback I α φ` is the manifold-side chart bump
attached to a Euclidean test function `φ`.

* The left-hand side chart-pulls (`tensorCovDerivPointwiseInner_integral_chart_pull`)
  to a chart-Euclidean integral of `densityOnEuclid · (covPrincipalIntegrand +
  covLowerOrderIntegrand)`.
* The principal part collapses (`covPrincipalIntegrand_rotated_collapse`) to the
  single-component scalar elliptic principal integrand plus the first-order
  rotation remainder `covPrincipalRotationRemainder`.
* The scalar elliptic principal integrand, density-weighted, is the
  `principalIntegrand` of `tensorPrincipalForm` (`weightedInvGram_principalIntegrand_eq`,
  valid on the compact chart-interior set `K`), hence its chart-target integral
  is `tensorPrincipalForm.bilin`.
* The component-coupled lower-order remainder collapses to a test-bump value term
  plus a test-bump-gradient term; the gradient term is integrated by parts
  (`chartTarget_integral_byParts`), moving the derivative onto the smooth
  coefficient.
* The right-hand side chart-pulls (`tensorL2Inner_rotatedTestSection_chart_pull`)
  to a chart-Euclidean integral of `densityOnEuclid · χ̃ · sourcePairingCoeff`.

Collecting the non-principal contributions produces the explicit
test-function-independent right-hand side `tensorComponentWeakRHS`.

## Main definitions

* `tensorComponentWeakRHS g r s T F α hK hK_target P₀` — the explicit,
  test-function-independent Euclidean right-hand side of the per-component scalar
  weak equation: `densityOnEuclid · sourcePairingCoeff` (the source contribution)
  minus the density-weighted rotation-remainder coefficient minus the
  density-weighted lower-order value coefficient plus the integration-by-parts
  divergence of the density-weighted lower-order gradient coefficient, extended by
  `0` off the Euclidean chart target.

## Main results

* `tensorComponentWeakRHS_contDiff` — the explicit right-hand side is globally
  `C^∞`.
* `tensorComponent_isSmoothWeakSolution` — the unconditional headline: from the
  global `H^1` weak equation of the connection Laplacian, the Euclidean chart
  component `tensorComponentEuclid g r s T α P₀` is a smooth weak solution of the
  principal-part elliptic bilinear form `tensorPrincipalForm` with right-hand
  side `tensorComponentWeakRHS`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Matrix
open Tensor0SBundle

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- The collapsed Christoffel-correction coefficient: the value, on the chart
target, of `covDerivLowerOrderTerm g r s (rotatedTestSection …) α l Q.1 Q.2`
divided by the chart-pushed bump. By `covDerivLowerOrderTerm_def` and the rotated
test section's raw-component identity it is the finite sum over component
multi-index pairs `p` of `covDerivLowerOrderCoeff` against the inverse-Gram entry
`covChartMetricGramInv g r s α · p P₀`. -/
noncomputable def lowerOrderRotationLOCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    (l : Fin (Module.finrank ℝ E)) (Q : CompIdx E r s) :
    EuclN → ℝ :=
  fun y =>
    ∑ p : CompIdx E r s,
      covDerivLowerOrderCoeff (I := I) (M := M) g r s α l Q.1 p.1 Q.2 p.2 y *
        covChartMetricGramInv (I := I) (M := M) g r s α y p P₀

/-- **The lower-order gradient coefficient of the rotated lower-order
remainder.** The coefficient multiplying the chart-Euclidean partial `∂_l χ̃` of
the chart-pushed bump. It collects, from the `LO_T · ∂_l(raw v_Q)` cross group,
exactly the Leibniz contribution where `∂_l` falls on the chart-pushed bump.

It is a plain function `EuclideanSpace ℝ (Fin n) → ℝ` — first-order in `T`, with
`C^∞` coefficients. -/
noncomputable def covLowerOrderRotationGradCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    (l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    ∑ P : CompIdx E r s,
      ∑ Q : CompIdx E r s,
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          ∑ k : Fin (Module.finrank ℝ E),
            chartInvGramEuclid (I := I) g α k l y *
              covDerivLowerOrderTerm (I := I) (M := M) g r s T α k P.1 P.2 y *
              covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀

/-- Unfolding lemma for `covLowerOrderRotationGradCoeff`. -/
lemma covLowerOrderRotationGradCoeff_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    (l : Fin (Module.finrank ℝ E)) (y : EuclN) :
    covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y =
      ∑ P : CompIdx E r s,
        ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            ∑ k : Fin (Module.finrank ℝ E),
              chartInvGramEuclid (I := I) g α k l y *
                covDerivLowerOrderTerm (I := I) (M := M) g r s T α k P.1 P.2 y *
                covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀ := rfl

/-- **The lower-order value coefficient of the rotated lower-order remainder.**
The coefficient multiplying the chart-pushed bump `χ̃` itself. It collects the
three groups in which no chart-Euclidean derivative falls on the chart-pushed
bump: the `∂_k(raw T_P) · LO_v` group, the Leibniz contribution of the
`LO_T · ∂_l(raw v_Q)` group where `∂_l` falls on the inverse-Gram coefficient,
and the pure `LO_T · LO_v` group.

It is a plain function `EuclideanSpace ℝ (Fin n) → ℝ` with `C^∞` coefficients. -/
noncomputable def covLowerOrderRotationValueCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s) : EuclN → ℝ :=
  fun y =>
    ∑ P : CompIdx E r s,
      ∑ Q : CompIdx E r s,
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramEuclid (I := I) g α k l y *
                (euclidPartial (E := E) k
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M)
                          g r s T α P.1 P.2)) y *
                    lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q y
                  + covDerivLowerOrderTerm (I := I) (M := M)
                        g r s T α k P.1 P.2 y *
                      euclidPartial (E := E) l
                        (gramInvEntry (I := I) (M := M) g r s α Q P₀) y
                  + covDerivLowerOrderTerm (I := I) (M := M)
                        g r s T α k P.1 P.2 y *
                      lowerOrderRotationLOCoeff (I := I) (M := M)
                        g r s α P₀ l Q y)

/-- Unfolding lemma for `covLowerOrderRotationValueCoeff`. -/
lemma covLowerOrderRotationValueCoeff_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s) (y : EuclN) :
    covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y =
      ∑ P : CompIdx E r s,
        ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramEuclid (I := I) g α k l y *
                  (euclidPartial (E := E) k
                        (chartPushedRaw I α
                          (tensorChartComponentRaw (I := I) (M := M)
                            g r s T α P.1 P.2)) y *
                      lowerOrderRotationLOCoeff (I := I) (M := M)
                        g r s α P₀ l Q y
                    + covDerivLowerOrderTerm (I := I) (M := M)
                          g r s T α k P.1 P.2 y *
                        euclidPartial (E := E) l
                          (gramInvEntry (I := I) (M := M) g r s α Q P₀) y
                    + covDerivLowerOrderTerm (I := I) (M := M)
                          g r s T α k P.1 P.2 y *
                        lowerOrderRotationLOCoeff (I := I) (M := M)
                          g r s α P₀ l Q y) := rfl

/-- On the Euclidean chart target the Christoffel correction
`covDerivLowerOrderTerm g r s (rotatedTestSection …) α l Q.1 Q.2` equals the
collapsed coefficient `lowerOrderRotationLOCoeff` times the chart-pushed bump. -/
private lemma covDerivLowerOrderTerm_rotatedTestSection_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (l : Fin (Module.finrank ℝ E)) (Q : CompIdx E r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    covDerivLowerOrderTerm (I := I) (M := M) g r s
        (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
        α l Q.1 Q.2 y =
      lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q y *
        chartPushedRaw I α χ y := by
  classical
  rw [covDerivLowerOrderTerm_def, lowerOrderRotationLOCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [rotatedTestSection_chartComp (I := I) (M := M) g r s α P₀ hχs hχt p hy]
  ring

/-- **The rotated lower-order collapse.** On the Euclidean chart target the
component-coupled lower-order remainder `covLowerOrderIntegrand g r s T
(rotatedTestSection g r s α P₀ χ) α` collapses to
`covLowerOrderRotationValueCoeff · χ̃ + ∑_l covLowerOrderRotationGradCoeff l · ∂_l χ̃`.

The chart-Euclidean partial `∂_l χ̃` arises solely from the Leibniz contribution
of the `LO_T · ∂_l(raw v_Q)` cross group in which `∂_l` falls on the chart-pushed
bump; every other group contributes the chart-pushed bump undifferentiated. -/
theorem covLowerOrderIntegrand_rotated_collapse
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    covLowerOrderIntegrand (I := I) (M := M) g r s T
        (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt) α y =
      covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y *
          chartPushedRaw I α χ y +
        ∑ l : Fin (Module.finrank ℝ E),
          covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
            euclidPartial (E := E) l (chartPushedRaw I α χ) y := by
  classical
  rw [covLowerOrderIntegrand_def, covLowerOrderRotationValueCoeff_def]
  unfold covLowerOrderRotationGradCoeff
  have hleibniz : ∀ Q : CompIdx E r s, ∀ l : Fin (Module.finrank ℝ E),
      euclidPartial (E := E) l
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s
              (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
              α Q.1 Q.2)) y =
        euclidPartial (E := E) l
            (gramInvEntry (I := I) (M := M) g r s α Q P₀) y *
          chartPushedRaw I α χ y +
        covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀ *
          euclidPartial (E := E) l (chartPushedRaw I α χ) y := fun Q l =>
    euclidPartial_chartPushedRaw_rotatedTestSection_eqOn (I := I) (M := M)
      g r s α P₀ hχs hχt Q l hy
  have hsummand : ∀ P Q : CompIdx E r s, ∀ k l : Fin (Module.finrank ℝ E),
      chartInvGramEuclid (I := I) g α k l y *
          (euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M)
                    g r s T α P.1 P.2)) y *
              covDerivLowerOrderTerm (I := I) (M := M) g r s
                (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
                α l Q.1 Q.2 y
            + covDerivLowerOrderTerm (I := I) (M := M) g r s T α k P.1 P.2 y *
                euclidPartial (E := E) l
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s
                      (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
                      α Q.1 Q.2)) y
            + covDerivLowerOrderTerm (I := I) (M := M) g r s T α k P.1 P.2 y *
                covDerivLowerOrderTerm (I := I) (M := M) g r s
                  (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
                  α l Q.1 Q.2 y) =
        chartInvGramEuclid (I := I) g α k l y *
            (euclidPartial (E := E) k
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M)
                      g r s T α P.1 P.2)) y *
                lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q y
              + covDerivLowerOrderTerm (I := I) (M := M)
                    g r s T α k P.1 P.2 y *
                  euclidPartial (E := E) l
                    (gramInvEntry (I := I) (M := M) g r s α Q P₀) y
              + covDerivLowerOrderTerm (I := I) (M := M)
                    g r s T α k P.1 P.2 y *
                  lowerOrderRotationLOCoeff (I := I) (M := M)
                    g r s α P₀ l Q y) * chartPushedRaw I α χ y +
          chartInvGramEuclid (I := I) g α k l y *
              covDerivLowerOrderTerm (I := I) (M := M) g r s T α k P.1 P.2 y *
              covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀ *
            euclidPartial (E := E) l (chartPushedRaw I α χ) y := by
    intro P Q k l
    rw [covDerivLowerOrderTerm_rotatedTestSection_eq (I := I) (M := M)
      g r s α P₀ hχs hχt l Q hy, hleibniz Q l]
    ring
  rw [Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => by
    rw [Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl
      (fun l _ => hsummand P Q k l))]))]
  have hsplit : ∀ P Q : CompIdx E r s,
      (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          (chartInvGramEuclid (I := I) g α k l y *
              (euclidPartial (E := E) k
                    (chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M)
                        g r s T α P.1 P.2)) y *
                  lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q y
                + covDerivLowerOrderTerm (I := I) (M := M)
                      g r s T α k P.1 P.2 y *
                    euclidPartial (E := E) l
                      (gramInvEntry (I := I) (M := M) g r s α Q P₀) y
                + covDerivLowerOrderTerm (I := I) (M := M)
                      g r s T α k P.1 P.2 y *
                    lowerOrderRotationLOCoeff (I := I) (M := M)
                      g r s α P₀ l Q y) * chartPushedRaw I α χ y +
            chartInvGramEuclid (I := I) g α k l y *
                covDerivLowerOrderTerm (I := I) (M := M) g r s T α k P.1 P.2 y *
                covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀ *
              euclidPartial (E := E) l (chartPushedRaw I α χ) y)) =
        (∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramEuclid (I := I) g α k l y *
              (euclidPartial (E := E) k
                    (chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M)
                        g r s T α P.1 P.2)) y *
                  lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q y
                + covDerivLowerOrderTerm (I := I) (M := M)
                      g r s T α k P.1 P.2 y *
                    euclidPartial (E := E) l
                      (gramInvEntry (I := I) (M := M) g r s α Q P₀) y
                + covDerivLowerOrderTerm (I := I) (M := M)
                      g r s T α k P.1 P.2 y *
                    lowerOrderRotationLOCoeff (I := I) (M := M)
                      g r s α P₀ l Q y)) * chartPushedRaw I α χ y +
          ∑ l : Fin (Module.finrank ℝ E),
            (∑ k : Fin (Module.finrank ℝ E),
              chartInvGramEuclid (I := I) g α k l y *
                covDerivLowerOrderTerm (I := I) (M := M) g r s T α k P.1 P.2 y *
                covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀) *
              euclidPartial (E := E) l (chartPushedRaw I α χ) y := by
    intro P Q
    simp only [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.sum_mul]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => by
    rw [hsplit P Q, mul_add]))]
  simp only [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    rw [mul_assoc]
  · have hLHS :
        (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            ∑ l : Fin (Module.finrank ℝ E),
              (∑ k : Fin (Module.finrank ℝ E),
                chartInvGramEuclid (I := I) g α k l y *
                  covDerivLowerOrderTerm (I := I) (M := M)
                    g r s T α k P.1 P.2 y *
                  covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀) *
                euclidPartial (E := E) l (chartPushedRaw I α χ) y) =
          ∑ l : Fin (Module.finrank ℝ E), ∑ P : CompIdx E r s,
            ∑ Q : CompIdx E r s, ∑ k : Fin (Module.finrank ℝ E),
              covChartMetricGram (I := I) (M := M) g r s α P Q y *
                (chartInvGramEuclid (I := I) g α k l y *
                  covDerivLowerOrderTerm (I := I) (M := M)
                    g r s T α k P.1 P.2 y *
                  covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀) *
                euclidPartial (E := E) l (chartPushedRaw I α χ) y := by
      have h1 : ∀ P Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ∑ l : Fin (Module.finrank ℝ E),
                (∑ k : Fin (Module.finrank ℝ E),
                  chartInvGramEuclid (I := I) g α k l y *
                    covDerivLowerOrderTerm (I := I) (M := M)
                      g r s T α k P.1 P.2 y *
                    covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀) *
                  euclidPartial (E := E) l (chartPushedRaw I α χ) y =
            ∑ l : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
              covChartMetricGram (I := I) (M := M) g r s α P Q y *
                (chartInvGramEuclid (I := I) g α k l y *
                  covDerivLowerOrderTerm (I := I) (M := M)
                    g r s T α k P.1 P.2 y *
                  covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀) *
                euclidPartial (E := E) l (chartPushedRaw I α χ) y := by
        intro P Q
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [← mul_assoc, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl
        (fun Q _ => h1 P Q))]
      rw [Finset.sum_congr rfl (fun P (_ : P ∈ (Finset.univ : Finset (CompIdx E r s))) =>
        Finset.sum_comm (s := (Finset.univ : Finset (CompIdx E r s)))
          (t := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))))]
      rw [Finset.sum_comm]
    have hRHS :
        (∑ l : Fin (Module.finrank ℝ E),
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ∑ k : Fin (Module.finrank ℝ E),
                chartInvGramEuclid (I := I) g α k l y *
                  covDerivLowerOrderTerm (I := I) (M := M)
                    g r s T α k P.1 P.2 y *
                  covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀) *
            euclidPartial (E := E) l (chartPushedRaw I α χ) y) =
          ∑ l : Fin (Module.finrank ℝ E), ∑ P : CompIdx E r s,
            ∑ Q : CompIdx E r s, ∑ k : Fin (Module.finrank ℝ E),
              covChartMetricGram (I := I) (M := M) g r s α P Q y *
                (chartInvGramEuclid (I := I) g α k l y *
                  covDerivLowerOrderTerm (I := I) (M := M)
                    g r s T α k P.1 P.2 y *
                  covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀) *
                euclidPartial (E := E) l (chartPushedRaw I α χ) y := by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun P _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun Q _ => ?_)
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [hLHS, hRHS]

/-- The `l`-th chart-Euclidean partial derivative of a function `C^∞` on the
Euclidean chart target is again `C^∞` on the chart target. -/
lemma euclidPartial_contDiffOn_target
    (α : M) (l : Fin (Module.finrank ℝ E))
    {u : EuclN → ℝ}
    (hu : ContDiffOn ℝ ∞ u (chartTargetEuclid (I := I) (M := M) α)) :
    ContDiffOn ℝ ∞ (euclidPartial (E := E) l u)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hfderiv : ContDiffOn ℝ ∞ (fun z => fderiv ℝ u z)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have hsucc : ContDiffOn ℝ ((∞ : WithTop ℕ∞) + 1) u
        (chartTargetEuclid (I := I) (M := M) α) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl]; exact hu
    have hfw : ContDiffOn ℝ ∞ (fderivWithin ℝ u
        (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
      ((contDiffOn_succ_iff_fderivWithin hopen.uniqueDiffOn).mp hsucc).2.2
    refine hfw.congr (fun z hz => ?_)
    exact (fderivWithin_of_isOpen (f := u) (𝕜 := ℝ) hopen hz).symm
  have hcomp : ContDiffOn ℝ ∞
      ((fun L : EuclN →L[ℝ] ℝ => L (EuclideanSpace.single l 1)) ∘
        (fun z => fderiv ℝ u z))
      (chartTargetEuclid (I := I) (M := M) α) :=
    (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single l 1)).contDiff.comp_contDiffOn hfderiv
  refine hcomp.congr (fun z _ => ?_)
  rfl

/-- The collapsed Christoffel coefficient `lowerOrderRotationLOCoeff` is `C^∞`
on the Euclidean chart target. -/
lemma lowerOrderRotationLOCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    (l : Fin (Module.finrank ℝ E)) (Q : CompIdx E r s) :
    ContDiffOn ℝ ∞ (lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  refine ContDiffOn.sum (fun p _ => ?_)
  exact (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
      g r s α l Q.1 p.1 Q.2 p.2).mul
    (covChartMetricGramInv_entry_contDiffOn (I := I) (M := M) g r s α p P₀)

/-- The Christoffel correction `covDerivLowerOrderTerm g r s T α k Idx Jdx` is
`C^∞` on the Euclidean chart target — the raw-component-push-forward smoothness
hypothesis is discharged from `chartPushedRaw_tensorChartComponentRaw_contDiffOn`. -/
private lemma covDerivLowerOrderTerm_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (covDerivLowerOrderTerm (I := I) (M := M) g r s T α k Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
  covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M) g r s T α k Idx Jdx
    (fun Idx' Jdx' => chartPushedRaw_tensorChartComponentRaw_contDiffOn
      (I := I) (M := M) g r s T α Idx' Jdx')

/-- The lower-order gradient coefficient `covLowerOrderRotationGradCoeff` is
`C^∞` on the Euclidean chart target. -/
theorem covLowerOrderRotationGradCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    (l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold covLowerOrderRotationGradCoeff
  refine ContDiffOn.sum (fun P _ => ContDiffOn.sum (fun Q _ => ?_))
  refine (covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul ?_
  refine ContDiffOn.sum (fun k _ => ?_)
  exact ((chartInvGramEuclid_contDiffOn (I := I) g α k l).mul
      (covDerivLowerOrderTerm_contDiffOn (I := I) (M := M) g r s T α k P.1 P.2)).mul
    (covChartMetricGramInv_entry_contDiffOn (I := I) (M := M) g r s α Q P₀)

/-- The lower-order value coefficient `covLowerOrderRotationValueCoeff` is `C^∞`
on the Euclidean chart target. -/
theorem covLowerOrderRotationValueCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s) :
    ContDiffOn ℝ ∞
      (covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold covLowerOrderRotationValueCoeff
  refine ContDiffOn.sum (fun P _ => ContDiffOn.sum (fun Q _ => ?_))
  refine (covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul ?_
  refine ContDiffOn.sum (fun k _ => ContDiffOn.sum (fun l _ => ?_))
  refine (chartInvGramEuclid_contDiffOn (I := I) g α k l).mul ?_
  have hloT : ContDiffOn ℝ ∞
      (covDerivLowerOrderTerm (I := I) (M := M) g r s T α k P.1 P.2)
      (chartTargetEuclid (I := I) (M := M) α) :=
    covDerivLowerOrderTerm_contDiffOn (I := I) (M := M) g r s T α k P.1 P.2
  have hloVc : ContDiffOn ℝ ∞
      (lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q)
      (chartTargetEuclid (I := I) (M := M) α) :=
    lowerOrderRotationLOCoeff_contDiffOn (I := I) (M := M) g r s α P₀ l Q
  have hdkT : ContDiffOn ℝ ∞
      (euclidPartial (E := E) k
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T α P.1 P.2)))
      (chartTargetEuclid (I := I) (M := M) α) :=
    euclidPartial_chartPushedRaw_contDiffOn (I := I) (M := M) g r s T α k P.1 P.2
  have hdlGinv : ContDiffOn ℝ ∞
      (euclidPartial (E := E) l
        (gramInvEntry (I := I) (M := M) g r s α Q P₀))
      (chartTargetEuclid (I := I) (M := M) α) :=
    euclidPartial_contDiffOn_target (I := I) (M := M) α l
      (covChartMetricGramInv_entry_contDiffOn (I := I) (M := M) g r s α Q P₀)
  exact ((hdkT.mul hloVc).add (hloT.mul hdlGinv)).add (hloT.mul hloVc)

/-- **The test-bump-free coefficient of the principal rotation remainder.** The
first-order rotation remainder `covPrincipalRotationRemainder` divided by the
chart-pushed bump: the contributions in which the chart-Euclidean partial `∂_l`
falls on the inverse-Gram coefficient, with the chart-pushed bump factored out.

It is a plain function `EuclideanSpace ℝ (Fin n) → ℝ`, first-order in `T`, with
`C^∞` coefficients. -/
noncomputable def covPrincipalRotationCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s) : EuclN → ℝ :=
  fun y =>
    ∑ P : CompIdx E r s,
      ∑ Q : CompIdx E r s,
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramEuclid (I := I) g α k l y *
                  euclidPartial (E := E) k
                    (chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M)
                        g r s T α P.1 P.2)) y *
                euclidPartial (E := E) l
                  (gramInvEntry (I := I) (M := M) g r s α Q P₀) y

/-- Unfolding lemma for `covPrincipalRotationCoeff`. -/
lemma covPrincipalRotationCoeff_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s) (y : EuclN) :
    covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y =
      ∑ P : CompIdx E r s,
        ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramEuclid (I := I) g α k l y *
                    euclidPartial (E := E) k
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M)
                          g r s T α P.1 P.2)) y *
                  euclidPartial (E := E) l
                    (gramInvEntry (I := I) (M := M) g r s α Q P₀) y := rfl

/-- The first-order rotation remainder `covPrincipalRotationRemainder` factors as
the principal rotation coefficient `covPrincipalRotationCoeff` times the
chart-pushed bump: the bump is a literal factor of every summand. -/
lemma covPrincipalRotationRemainder_eq_coeff_mul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source) (y : EuclN) :
    covPrincipalRotationRemainder (I := I) (M := M) g r s T α P₀ χ hχs hχt y =
      covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y *
        chartPushedRaw I α χ y := by
  classical
  rw [covPrincipalRotationRemainder_def, covPrincipalRotationCoeff_def,
    Finset.sum_mul]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  have hinner :
      (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramEuclid (I := I) g α k l y *
              euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M)
                    g r s T α P.1 P.2)) y *
            (euclidPartial (E := E) l
                (gramInvEntry (I := I) (M := M) g r s α Q P₀) y *
              chartPushedRaw I α χ y)) =
        (∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramEuclid (I := I) g α k l y *
                euclidPartial (E := E) k
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M)
                      g r s T α P.1 P.2)) y *
              euclidPartial (E := E) l
                (gramInvEntry (I := I) (M := M) g r s α Q P₀) y) * chartPushedRaw I α χ y := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  rw [hinner, ← mul_assoc]

/-- The principal rotation coefficient `covPrincipalRotationCoeff` is `C^∞` on
the Euclidean chart target. -/
theorem covPrincipalRotationCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s) :
    ContDiffOn ℝ ∞ (covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold covPrincipalRotationCoeff
  refine ContDiffOn.sum (fun P _ => ContDiffOn.sum (fun Q _ => ?_))
  refine (covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul ?_
  refine ContDiffOn.sum (fun k _ => ContDiffOn.sum (fun l _ => ?_))
  refine ((chartInvGramEuclid_contDiffOn (I := I) g α k l).mul ?_).mul ?_
  · exact euclidPartial_chartPushedRaw_contDiffOn (I := I) (M := M)
      g r s T α k P.1 P.2
  · exact euclidPartial_contDiffOn_target (I := I) (M := M) α l
      (covChartMetricGramInv_entry_contDiffOn (I := I) (M := M) g r s α Q P₀)

/-- The chart-density-weighted lower-order gradient coefficient in chart direction
`l`: the coefficient whose chart-Euclidean divergence is the integration-by-parts
contribution of the lower-order gradient term. -/
noncomputable def weightedGradCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    (l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y => densityOnEuclid (I := I) g α y *
    covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y

/-- Unfolding lemma for `weightedGradCoeff`: it is the chart density times the
lower-order rotation gradient coefficient. -/
lemma weightedGradCoeff_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    (l : Fin (Module.finrank ℝ E)) :
    weightedGradCoeff (I := I) (M := M) g r s T α P₀ l =
      (fun y => densityOnEuclid (I := I) g α y *
        covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y) :=
  rfl

/-- The chart-density-weighted lower-order gradient coefficient `weightedGradCoeff`
is `C^∞` on the Euclidean chart target: it is the product of the `C^∞` chart
density `densityOnEuclid` and the `C^∞` lower-order rotation gradient
coefficient `covLowerOrderRotationGradCoeff`. -/
theorem weightedGradCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    (l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  rw [weightedGradCoeff_eq]
  exact (densityOnEuclid_contDiffOn (I := I) g α).mul
    (covLowerOrderRotationGradCoeff_contDiffOn (I := I) (M := M) g r s T α P₀ l)

/-- **The explicit test-function-independent right-hand side of the per-component
scalar weak equation.**

For smooth compactly-supported `(r, s)`-tensor sections `T` (the solution) and
`F` (the source), a chart center `α`, a compact `K ⊆ chartTargetEuclid α`, and a
component multi-index `P₀`, this is the Euclidean function

```
densityOnEuclid · sourcePairingCoeff
  − densityOnEuclid · covPrincipalRotationCoeff
  − densityOnEuclid · covLowerOrderRotationValueCoeff
  + ∑_l euclidPartial l (densityOnEuclid · covLowerOrderRotationGradCoeff l)
```

on the Euclidean chart target `chartTargetEuclid α`, and `0` off it. The first
term is the source contribution; the second is the principal rotation remainder;
the third and fourth collect the lower-order remainder, with the fourth being the
integration-by-parts divergence of the lower-order gradient coefficient.

It is a plain function `EuclideanSpace ℝ (Fin n) → ℝ`, independent of any test
function. -/
noncomputable def tensorComponentWeakRHS
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T F : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (_hK : IsCompact K)
    (_hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s) : EuclN → ℝ := by
  classical
  exact fun y =>
    if y ∈ chartTargetEuclid (I := I) (M := M) α then
      densityOnEuclid (I := I) g α y *
          sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y -
        densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y -
        densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y +
        ∑ l : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) l
            (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y
    else 0

/-- On the Euclidean chart target `tensorComponentWeakRHS` is the explicit
density-weighted combination of the source, principal-rotation and lower-order
coefficients. -/
lemma tensorComponentWeakRHS_apply_of_mem
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T F : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀ y =
      densityOnEuclid (I := I) g α y *
          sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y -
        densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y -
        densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y +
        ∑ l : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) l
            (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y := by
  unfold tensorComponentWeakRHS
  rw [if_pos hy]

/-- Off the Euclidean chart target `tensorComponentWeakRHS` vanishes. -/
lemma tensorComponentWeakRHS_apply_of_notMem
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T F : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s)
    {y : EuclN} (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀ y = 0 := by
  unfold tensorComponentWeakRHS
  rw [if_neg hy]

/-- A function that is `C^∞` on an open set `U` and vanishes off a closed set
`C ⊆ U` is globally `C^∞`. -/
private lemma contDiff_of_contDiffOn_zero_off_closed_local
    {P : EuclN → ℝ} {U C : Set EuclN}
    (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U)
    (hP : ContDiffOn ℝ ∞ P U) (hzero : ∀ y, y ∉ C → P y = 0) :
    ContDiff ℝ ∞ P := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ U
  · exact hP.contDiffAt (hU.mem_nhds hy)
  · have hyC : y ∉ C := fun hyC => hy (hCU hyC)
    have hy_nhds : Cᶜ ∈ 𝓝 y := hC.isOpen_compl.mem_nhds hyC
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hy_nhds] with z hz using hzero z hz

/-- The chart-Euclidean partial derivative of a function vanishing off a closed
set vanishes off that set: on the open complement the function is locally `0`. -/
private lemma euclidPartial_eq_zero_off_closed
    {u : EuclN → ℝ} {C : Set EuclN} (hC : IsClosed C)
    (hu : ∀ z, z ∉ C → u z = 0)
    (l : Fin (Module.finrank ℝ E)) {y : EuclN} (hy : y ∉ C) :
    euclidPartial (E := E) l u y = 0 := by
  classical
  have hy_nhds : Cᶜ ∈ 𝓝 y := hC.isOpen_compl.mem_nhds hy
  have hu_evt : u =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) :=
    Filter.eventually_of_mem hy_nhds (fun z hz => hu z hz)
  rw [euclidPartial_def, Filter.EventuallyEq.fderiv_eq hu_evt,
    fderiv_const_apply, ContinuousLinearMap.zero_apply]

/-- The chart-Euclidean partial derivative of a function vanishing on an open
neighbourhood of `y` vanishes at `y`. -/
private lemma euclidPartial_eq_zero_of_open_zero
    {u : EuclN → ℝ} {U : Set EuclN} (hU : IsOpen U) {y : EuclN} (hy : y ∈ U)
    (hu : ∀ z ∈ U, u z = 0) (l : Fin (Module.finrank ℝ E)) :
    euclidPartial (E := E) l u y = 0 := by
  classical
  have hu_evt : u =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) :=
    Filter.eventually_of_mem (hU.mem_nhds hy) (fun z hz => hu z hz)
  rw [euclidPartial_def, Filter.EventuallyEq.fderiv_eq hu_evt,
    fderiv_const_apply, ContinuousLinearMap.zero_apply]

/-- The Euclidean chart component `tensorComponentEuclid g r s S α P` vanishes off
the compact Euclidean image of the topological support of `S`. -/
private lemma tensorComponentEuclid_eq_zero_off_image
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P : CompIdx E r s)
    {y : EuclN}
    (hy : y ∉ toEuclidean '' ((extChartAt I α) '' tsupport S.toFun)) :
    tensorComponentEuclid (I := I) (M := M) g r s S α P y = 0 := by
  classical
  by_cases hyT : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [tensorComponentEuclid_def]
    refine chartPushedRaw_eq_zero_off_image_tsupport (I := I) (M := M)
      (u := tensorChartComponentRaw (I := I) (M := M) g r s S α P.1 P.2)
      α hyT (fun hmem => hy ?_)
    have hsub := tensorChartComponentRaw_tsupport_subset (I := I) (M := M)
      g r s S α P.1 P.2
    exact (Set.image_mono (Set.image_mono hsub)) hmem
  · exact tensorComponentEuclid_apply_of_notMem (I := I) (M := M) g r s S α P hyT

/-- The Euclidean image of the topological support of a smooth compactly-supported
section, under the chart, is compact (`S` supported inside the chart source). -/
private lemma image_tsupport_isCompact
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (hS_supp : tsupport S.toFun ⊆ (chartAt H α).source) :
    IsCompact (toEuclidean '' ((extChartAt I α) '' tsupport S.toFun)) := by
  have hcontOn : ContinuousOn (extChartAt I α) (tsupport S.toFun) := by
    refine (continuousOn_extChartAt (I := I) α).mono ?_
    intro x hx
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hS_supp hx
  have hTcompact : IsCompact (tsupport S.toFun) := S.hasCompactSupport
  have himg1 : IsCompact ((extChartAt I α) '' tsupport S.toFun) :=
    hTcompact.image_of_continuousOn hcontOn
  exact himg1.image (toEuclidean (E := E)).continuous

/-- The Euclidean image of the topological support of a chart-supported smooth
section lies inside the Euclidean chart target. -/
private lemma image_tsupport_subset_target
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (hS_supp : tsupport S.toFun ⊆ (chartAt H α).source) :
    toEuclidean '' ((extChartAt I α) '' tsupport S.toFun) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  rintro y ⟨w, ⟨x, hx, rfl⟩, rfl⟩
  refine ⟨(extChartAt I α) x, ?_, rfl⟩
  have hx_src : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hS_supp hx
  exact (extChartAt I α).map_source hx_src

/-- **The explicit right-hand side `tensorComponentWeakRHS` is globally `C^∞`.**
On the open Euclidean chart target every constituent is `C^∞`; off the compact
union of the Euclidean images of the topological supports of `T` and `F` the
right-hand side vanishes (each constituent carries a chart-component factor of
`T` or `F`). Extension by zero across the closed-off complement is therefore
globally `C^∞`. -/
theorem tensorComponentWeakRHS_contDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T F : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s)
    (hT_supp : tsupport T.toFun ⊆ (chartAt H α).source)
    (hF_supp : tsupport F.toFun ⊆ (chartAt H α).source) :
    ContDiff ℝ ∞
      (tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀) := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  set CT : Set EuclN := toEuclidean '' ((extChartAt I α) '' tsupport T.toFun)
    with hCT_def
  set CF : Set EuclN := toEuclidean '' ((extChartAt I α) '' tsupport F.toFun)
    with hCF_def
  have hCT_compact : IsCompact CT :=
    image_tsupport_isCompact (I := I) (M := M) g r s T α hT_supp
  have hCF_compact : IsCompact CF :=
    image_tsupport_isCompact (I := I) (M := M) g r s F α hF_supp
  have hCT_target : CT ⊆ chartTargetEuclid (I := I) (M := M) α :=
    image_tsupport_subset_target (I := I) (M := M) g r s T α hT_supp
  have hCF_target : CF ⊆ chartTargetEuclid (I := I) (M := M) α :=
    image_tsupport_subset_target (I := I) (M := M) g r s F α hF_supp
  have hK'_compact : IsCompact (CT ∪ CF) := hCT_compact.union hCF_compact
  have hK'_target : CT ∪ CF ⊆ chartTargetEuclid (I := I) (M := M) α :=
    Set.union_subset hCT_target hCF_target
  have hdensity : ContDiffOn ℝ ∞ (densityOnEuclid (I := I) g α)
      (chartTargetEuclid (I := I) (M := M) α) :=
    densityOnEuclid_contDiffOn (I := I) g α
  have hbody : ContDiffOn ℝ ∞
      (fun y : EuclN =>
        densityOnEuclid (I := I) g α y *
            sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y -
          densityOnEuclid (I := I) g α y *
            covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y -
          densityOnEuclid (I := I) g α y *
            covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y +
          ∑ l : Fin (Module.finrank ℝ E),
            euclidPartial (E := E) l
              (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have hgrad : ∀ l : Fin (Module.finrank ℝ E),
        ContDiffOn ℝ ∞
          (euclidPartial (E := E) l
            (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l))
          (chartTargetEuclid (I := I) (M := M) α) := by
      intro l
      refine euclidPartial_contDiffOn_target (I := I) (M := M) α l ?_
      exact hdensity.mul (covLowerOrderRotationGradCoeff_contDiffOn
        (I := I) (M := M) g r s T α P₀ l)
    refine (((hdensity.mul (sourcePairingCoeff_contDiffOn
      (I := I) (M := M) g r s F α P₀)).sub
      (hdensity.mul (covPrincipalRotationCoeff_contDiffOn
        (I := I) (M := M) g r s T α P₀))).sub
      (hdensity.mul (covLowerOrderRotationValueCoeff_contDiffOn
        (I := I) (M := M) g r s T α P₀))).add ?_
    exact ContDiffOn.sum (fun l _ => hgrad l)
  have hcontDiffOn : ContDiffOn ℝ ∞
      (tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine hbody.congr (fun y hy => ?_)
    exact (tensorComponentWeakRHS_apply_of_mem (I := I) (M := M)
      g r s T F α hK hK_target P₀ hy)
  have hzero : ∀ y, y ∉ CT ∪ CF →
      tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀ y = 0 := by
    intro y hy
    have hyCT : y ∉ CT := fun h => hy (Or.inl h)
    have hyCF : y ∉ CF := fun h => hy (Or.inr h)
    by_cases hyT : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [tensorComponentWeakRHS_apply_of_mem (I := I) (M := M)
        g r s T F α hK hK_target P₀ hyT]
      have hS0 : sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y = 0 := by
        rw [sourcePairingCoeff_def]
        refine Finset.sum_eq_zero (fun Q _ => ?_)
        refine mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun P _ => ?_))
        rw [tensorComponentEuclid_eq_zero_off_image (I := I) (M := M)
          g r s F α P (by rw [← hCF_def]; exact hyCF), mul_zero]
      have hpush_zero : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
          ∀ z, z ∉ CT →
            chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx) z = 0 := by
        intro Idx Jdx z hz
        by_cases hzT : z ∈ chartTargetEuclid (I := I) (M := M) α
        · refine chartPushedRaw_eq_zero_off_image_tsupport (I := I) (M := M)
            (u := tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx)
            α hzT (fun hmem => hz ?_)
          have hsub := tensorChartComponentRaw_tsupport_subset (I := I) (M := M)
            g r s T α Idx Jdx
          rw [hCT_def]
          exact (Set.image_mono (Set.image_mono hsub)) hmem
        · exact chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hzT
      have hClosedCT : IsClosed CT := hCT_compact.isClosed
      have hdkT_zero : ∀ (k : Fin (Module.finrank ℝ E))
          (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
          euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx)) y = 0 :=
        fun k Idx Jdx => euclidPartial_eq_zero_off_closed (E := E) hClosedCT
          (hpush_zero Idx Jdx) k hyCT
      have hloT_zero : ∀ (k : Fin (Module.finrank ℝ E))
          (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
          covDerivLowerOrderTerm (I := I) (M := M) g r s T α k Idx Jdx y = 0 := by
        intro k Idx Jdx
        rw [covDerivLowerOrderTerm_def]
        refine Finset.sum_eq_zero (fun p _ => ?_)
        have hraw0 : tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0 := by
          have := hpush_zero p.1 p.2 y hyCT
          by_cases hyT' : y ∈ chartTargetEuclid (I := I) (M := M) α
          · rwa [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hyT'] at this
          · exact absurd hyT hyT'
        rw [hraw0, mul_zero]
      have hP0 : covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y = 0 := by
        rw [covPrincipalRotationCoeff_def]
        refine Finset.sum_eq_zero (fun P _ => ?_)
        refine Finset.sum_eq_zero (fun Q _ => ?_)
        refine mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun k _ => ?_))
        refine Finset.sum_eq_zero (fun l _ => ?_)
        rw [hdkT_zero k P.1 P.2]; ring
      have hV0 : covLowerOrderRotationValueCoeff (I := I) (M := M)
          g r s T α P₀ y = 0 := by
        rw [covLowerOrderRotationValueCoeff_def]
        refine Finset.sum_eq_zero (fun P _ => ?_)
        refine Finset.sum_eq_zero (fun Q _ => ?_)
        refine mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun k _ => ?_))
        refine Finset.sum_eq_zero (fun l _ => ?_)
        rw [hdkT_zero k P.1 P.2, hloT_zero k P.1 P.2]; ring
      have hGrad0 : ∀ l : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) l
            (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y = 0 := by
        intro l
        have hUopen : IsOpen
            (chartTargetEuclid (I := I) (M := M) α \ CT) :=
          hopen.sdiff hClosedCT
        have hyU : y ∈ chartTargetEuclid (I := I) (M := M) α \ CT :=
          ⟨hyT, hyCT⟩
        refine euclidPartial_eq_zero_of_open_zero (E := E) hUopen hyU
          (fun z hz => ?_) l
        unfold weightedGradCoeff
        refine mul_eq_zero_of_right _ ?_
        rw [covLowerOrderRotationGradCoeff_def]
        refine Finset.sum_eq_zero (fun P _ => ?_)
        refine Finset.sum_eq_zero (fun Q _ => ?_)
        refine mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun k _ => ?_))
        have hloT_z : covDerivLowerOrderTerm (I := I) (M := M)
            g r s T α k P.1 P.2 z = 0 := by
          rw [covDerivLowerOrderTerm_def]
          refine Finset.sum_eq_zero (fun p _ => ?_)
          have hraw0 : tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) = 0 := by
            have hpz := hpush_zero p.1 p.2 z hz.2
            rwa [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hz.1] at hpz
          rw [hraw0, mul_zero]
        rw [hloT_z]; ring
      rw [hS0, hP0, hV0]
      simp only [mul_zero, sub_zero, zero_add]
      exact Finset.sum_eq_zero (fun l _ => hGrad0 l)
    · exact tensorComponentWeakRHS_apply_of_notMem (I := I) (M := M)
        g r s T F α hK hK_target P₀ hyT
  exact contDiff_of_contDiffOn_zero_off_closed_local (E := E) hopen
    hK'_compact.isClosed hK'_target hcontDiffOn hzero

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
