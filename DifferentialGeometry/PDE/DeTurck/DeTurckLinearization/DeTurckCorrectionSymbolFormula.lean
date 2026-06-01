import DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.DeTurckCorrectionSecondOrderSplit
import DifferentialGeometry.PDE.DeTurck.RicciLinearization.RicciSymbolFormula

/-!
# The principal symbol of the linearized DeTurck-correction operator in closed form

The pure `∂²h` part of the linearized DeTurck-correction operator,
`chartDeTurckCorrPrincipalSymbolExpr`, is the chart-coordinate expression
$$[D(\mathcal L_W g)]^{\sigma}_{ij}[h](y) =
    \sum_k g_{kj}(y)\,\sum_{a,b} G^{ab}(y)\,[\sigma]^k{}_{ab}[h](i)(y)
  + \sum_k g_{ik}(y)\,\sum_{a,b} G^{ab}(y)\,[\sigma]^k{}_{ab}[h](j)(y),$$
with the `∂²h` index block
$$[\sigma]^k{}_{ab}[h](d)(y) = \tfrac12\sum_l G^{kl}(y)\,
    \bigl(\partial_d\partial_a h_{lb} + \partial_d\partial_b h_{la}
        - \partial_d\partial_l h_{ab}\bigr)(y).$$

Its **principal symbol** is obtained by the formal substitution
`∂_a∂_b h_{cd} ↦ ξ_a ξ_b · t_{cd}`, where `ξ` is a covector with chart components
`ξ_a = (chartModelBasis E).repr ξ a` and `t` is the input symmetric bilinear form on the
fibre with components `t_{cd} = t (chartModelBasis E c) (chartModelBasis E d)`.  Carrying
out the substitution and contracting the chart Gram / inverse-Gram factors yields a
closed form.

The key contraction is that of the *outer* chart Gram factor against the *internal*
inverse-Gram factor of the `∂²h` index block: at the chart image of the base point
itself,
$$\sum_k g_{kj}\,G^{kl} = \delta^l_j,$$
because `chartInvGramMatrix g x x` is the matrix inverse of `chartGramMatrix g x x`.
This collapses the internal `l`-sum; the surviving inverse-Gram trace factor `G^{ab}`
then contracts each remaining term into a classical raised-index expression.  The block's
symmetric term pair `(ξ_a t_{jb}, ξ_b t_{ja})` produces **two equal** second-slot raised
contractions `∑_l ξ^l t_{jl}`, so the result is the textbook **gauge symbol** of the
linearized DeTurck-correction operator,
$$\sigma_{ij}(\xi)(t)
    = \xi_i \sum_l \xi^l\, t_{jl}
      + \xi_j \sum_l \xi^l\, t_{il}
      - \xi_i\xi_j\, \operatorname{tr}_g t,$$
with `ξ^l` the raised covector and `tr_g t` the metric trace of `t`.  The overall
constant factor is `1`: the `½` of the index block is doubled by the two equal
raised-contraction terms.

## Contents

* `chartGramOnE_extChartAt_self` — the chart-target Gram field at the chart image of the
  base point is the chart Gram matrix `chartGramMatrix g x x`.
* `sum_chartGram_mul_chartInvGram_self` — the `δ`-contraction
  `∑_k g_{kj} G^{kl} = δ^l_j` at the base point.
* `deTurckCorrSymbolComp` — the `(i, j)` component of the linearized-DeTurck-correction
  principal symbol, defined by the `∂_a∂_b ↦ ξ_aξ_b` substitution in
  `chartDeTurckCorrPrincipalSymbolExpr`.
* `deTurckCorrSymbolComp_eq_closedForm` — the closed-form gauge-symbol theorem.
* `deTurckCorrSymbolComp_add`, `deTurckCorrSymbolComp_smul`, `deTurckCorrSymbolComp_zero`
  — `ℝ`-linearity of the symbol component in the input bilinear form.
* `deTurckCorrSymbolComp_symm` — the `(i, j)`-symmetry of the symbol component on a
  symmetric input.
* `deTurckCorrSymbolComp_background_independent` — the symbol does not depend on the
  background metric `g'`.

The reusable fibre-form helpers `formComp`, `formMetricTrace`, `raisedFormContraction`,
`raisedFormContractionSnd` are taken from the linearized-Ricci symbol development.
-/

noncomputable section

open Set Function
open scoped Topology ContDiff Matrix Manifold

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace DeTurckLinearization

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

section GramBridge

/-- The chart-target Gram field of `g`, in the chart at `x`, evaluated at the chart image
of `x` itself, is the chart Gram matrix `chartGramMatrix g x x`.  This is
`chartGramOnE_def` followed by `(extChartAt I x).symm (extChartAt I x x) = x`. -/
lemma chartGramOnE_extChartAt_self (g : SmoothRiemannianMetric I M) (x : M)
    (k j : Fin (Module.finrank ℝ E)) :
    chartGramOnE (I := I) g x k j (extChartAt I x x) =
      chartGramMatrix (I := I) g x x k j := by
  rw [chartGramOnE_def, extChartAt_to_inv]

/-- The chart Gram matrix `chartGramMatrix g x x` contracted against the chart inverse
Gram matrix `chartInvGramMatrix g x x` over the shared upper index is the Kronecker
delta:
$$\sum_k g_{kj}\, G^{kl} = \delta^l_j.$$
Using the symmetry of the inverse Gram matrix, `∑_k g_{kj} G^{kl} = ∑_k G^{lk} g_{kj}`,
which is the `(l, j)` entry of `chartInvGramMatrix g x x * chartGramMatrix g x x = 1`,
valid because `x` lies in the base set of the trivialization at `x` itself. -/
lemma sum_chartGram_mul_chartInvGram_self (g : SmoothRiemannianMetric I M) (x : M)
    (j l : Fin (Module.finrank ℝ E)) :
    ∑ k : Fin (Module.finrank ℝ E),
        chartGramMatrix (I := I) g x x k j *
          chartInvGramMatrix (I := I) g x x k l =
      (if l = j then (1 : ℝ) else 0) := by
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact mem_chart_source H x
  have hmul := chartInvGramMatrix_mul_chartGramMatrix (I := I) g x hx
  have hentry : (chartInvGramMatrix (I := I) g x x *
      chartGramMatrix (I := I) g x x) l j = (1 : Matrix _ _ ℝ) l j := by
    rw [hmul]
  rw [Matrix.one_apply, Matrix.mul_apply] at hentry
  rw [← hentry]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [chartInvGramMatrix_self_symm (I := I) g x l k]
  ring

end GramBridge

section SymbolComponent

set_option linter.unusedVariables false in
/-- The `(i, j)` component of the **linearized-DeTurck-correction principal symbol**,
applied to the input bilinear form `t`.

It is obtained from `chartDeTurckCorrPrincipalSymbolExpr` (in the chart at `x` itself, at
the chart image `extChartAt I x x`) by the principal-symbol substitution
`∂_a∂_b h_{cd} ↦ ξ_a ξ_b · t_{cd}`.  Mirroring `chartDeTurckCorrPrincipalSymbolExpr`
term by term, the `∂²h` index block
`½∑_l G^{kl}·(∂_d∂_a h_{lb} + ∂_d∂_b h_{la} − ∂_d∂_l h_{ab})` becomes
`½∑_l G^{kl}·(ξ_dξ_a t_{lb} + ξ_dξ_b t_{la} − ξ_dξ_l t_{ab})`, so
$$\sigma_{ij}(\xi)(t) =
    \sum_k g_{kj}\,\sum_{a,b} G^{ab}\,
      \tfrac12\sum_l G^{kl}\bigl(
        \xi_i\xi_a\, t_{lb} + \xi_i\xi_b\, t_{la} - \xi_i\xi_l\, t_{ab}\bigr)
  + \sum_k g_{ik}\,\sum_{a,b} G^{ab}\,
      \tfrac12\sum_l G^{kl}\bigl(
        \xi_j\xi_a\, t_{lb} + \xi_j\xi_b\, t_{la} - \xi_j\xi_l\, t_{ab}\bigr),$$
with `g_{kj} = chartGramOnE g x k j (extChartAt I x x)`,
`G^{ab} = chartInvGramOnE g x a b (extChartAt I x x)`,
`G^{kl} = chartInvGramOnE g x k l (extChartAt I x x)`,
`ξ_a = (chartModelBasis E).repr ξ a`, and `t_{cd} = formComp x t c d`.

The background-metric parameter `g'` is retained for signature uniformity with
`chartDeTurckCorrPrincipalSymbolExpr`; it does not appear in the body, so the symbol is
independent of the background metric (`deTurckCorrSymbolComp_background_independent`). -/
def deTurckCorrSymbolComp (g g' : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i j : Fin (Module.finrank ℝ E)) : ℝ :=
  (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g x k j (extChartAt I x x) *
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g x a b (extChartAt I x x) *
            ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g x k l (extChartAt I x x) *
                ((chartModelBasis E).repr ξ i * (chartModelBasis E).repr ξ a *
                    formComp (I := I) x t l b +
                  (chartModelBasis E).repr ξ i * (chartModelBasis E).repr ξ b *
                    formComp (I := I) x t l a -
                  (chartModelBasis E).repr ξ i * (chartModelBasis E).repr ξ l *
                    formComp (I := I) x t a b))) +
  (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g x i k (extChartAt I x x) *
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g x a b (extChartAt I x x) *
            ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g x k l (extChartAt I x x) *
                ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ a *
                    formComp (I := I) x t l b +
                  (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ b *
                    formComp (I := I) x t l a -
                  (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
                    formComp (I := I) x t a b)))

@[simp] lemma deTurckCorrSymbolComp_def (g g' : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    deTurckCorrSymbolComp (I := I) g g' x ξ t i j =
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g x k j (extChartAt I x x) *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g x a b (extChartAt I x x) *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g x k l (extChartAt I x x) *
                    ((chartModelBasis E).repr ξ i * (chartModelBasis E).repr ξ a *
                        formComp (I := I) x t l b +
                      (chartModelBasis E).repr ξ i * (chartModelBasis E).repr ξ b *
                        formComp (I := I) x t l a -
                      (chartModelBasis E).repr ξ i * (chartModelBasis E).repr ξ l *
                        formComp (I := I) x t a b))) +
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g x i k (extChartAt I x x) *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g x a b (extChartAt I x x) *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g x k l (extChartAt I x x) *
                    ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ a *
                        formComp (I := I) x t l b +
                      (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ b *
                        formComp (I := I) x t l a -
                      (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
                        formComp (I := I) x t a b))) := rfl

end SymbolComponent

section ClosedForm

/-- **First raised contraction inside a block.**  Against the inverse-Gram trace factor
`G^{ab}`, the term `ξ_d ξ_a t_{mb}` of the contracted block contracts to
`ξ_d · ∑_l ξ^l t_{ml}`, the second-slot raised contraction of `t` at index `m`:
$$\sum_{a,b} G^{ab}\,\xi_d\xi_a\, t_{mb} = \xi_d\,(\xi\,t)_m.$$
Summing first over `a` recognises `∑_a G^{ab} ξ_a = ξ^b` (using symmetry of `G`). -/
private lemma block_term_a (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (d m : Fin (Module.finrank ℝ E)) :
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x a b *
          ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
            formComp (I := I) x t m b) =
      (chartModelBasis E).repr ξ d *
        raisedFormContractionSnd (I := I) g x ξ t m := by
  calc
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x a b *
            ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
              formComp (I := I) x t m b)
      = ∑ b : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr ξ d *
            (raisedCovectorComp (I := I) g x ξ b * formComp (I := I) x t m b) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [raisedCovectorComp_def, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [chartInvGramMatrix_self_symm (I := I) g x a b]
        ring
    _ = (chartModelBasis E).repr ξ d *
          raisedFormContractionSnd (I := I) g x ξ t m := by
        rw [raisedFormContractionSnd_def, Finset.mul_sum]

/-- **Second raised contraction inside a block.**  Against the inverse-Gram trace factor
`G^{ab}`, the term `ξ_d ξ_b t_{ma}` of the contracted block contracts to the *same*
second-slot raised contraction `ξ_d · ∑_l ξ^l t_{ml}`:
$$\sum_{a,b} G^{ab}\,\xi_d\xi_b\, t_{ma} = \xi_d\,(\xi\,t)_m.$$
Summing first over `b` recognises `∑_b G^{ab} ξ_b = ξ^a`.  This is the pair of
`block_term_a`; the two together give the doubled raised contraction. -/
private lemma block_term_b (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (d m : Fin (Module.finrank ℝ E)) :
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x a b *
          ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
            formComp (I := I) x t m a) =
      (chartModelBasis E).repr ξ d *
        raisedFormContractionSnd (I := I) g x ξ t m := by
  calc
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x a b *
            ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
              formComp (I := I) x t m a)
      = ∑ a : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr ξ d *
            (raisedCovectorComp (I := I) g x ξ a * formComp (I := I) x t m a) := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [raisedCovectorComp_def, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        ring
    _ = (chartModelBasis E).repr ξ d *
          raisedFormContractionSnd (I := I) g x ξ t m := by
        rw [raisedFormContractionSnd_def, Finset.mul_sum]

/-- **Trace contraction inside a block.**  Against the inverse-Gram trace factor
`G^{ab}`, the term `ξ_d ξ_m t_{ab}` of the contracted block contracts to
`ξ_d ξ_m · tr_g t`:
$$\sum_{a,b} G^{ab}\,\xi_d\xi_m\, t_{ab} = \xi_d\xi_m\,\operatorname{tr}_g t.$$ -/
private lemma block_term_trace (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (d m : Fin (Module.finrank ℝ E)) :
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x a b *
          ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ m *
            formComp (I := I) x t a b) =
      (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ m *
        formMetricTrace (I := I) g x t := by
  rw [formMetricTrace_def, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- **Per-block contraction.**  For a fixed lower index `d` (one of `i`, `j`) and a fixed
free upper index `m` (one of `j`, `i`), the `k`-summed block — chart Gram factor `g_{km}`
times the substituted `∂²h` index block — contracts to the gauge expression
$$\xi_d\,(\xi\,t)_m - \tfrac12\,\xi_d\xi_m\,\operatorname{tr}_g t.$$

The proof contracts the chart Gram factor `g_{km}` against the internal inverse-Gram
factor `G^{kl}` via `sum_chartGram_mul_chartInvGram_self` (collapsing the internal sum to
`l = m`), then the inverse-Gram trace factor `G^{ab}` against the surviving three terms
via `block_term_a`, `block_term_b`, `block_term_trace`.  The two raised contractions are
equal (both second-slot raises), so the index-block `½` survives only on the trace term:
the two `½·(ξ_d (ξ t)_m)` summands combine to the unit-coefficient raised term. -/
private lemma deTurckCorr_block_contraction (g : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (d m : Fin (Module.finrank ℝ E)) :
    ∑ k : Fin (Module.finrank ℝ E),
        chartGramMatrix (I := I) g x x k m *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x a b *
              ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g x x k l *
                  ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
                      formComp (I := I) x t l b +
                    (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
                      formComp (I := I) x t l a -
                    (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ l *
                      formComp (I := I) x t a b)) =
      (chartModelBasis E).repr ξ d *
            raisedFormContractionSnd (I := I) g x ξ t m -
        (1 / 2 : ℝ) * ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ m *
          formMetricTrace (I := I) g x t) := by
  have hstage1 : ∀ a b : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g x x k m *
            (chartInvGramMatrix (I := I) g x x a b *
              ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g x x k l *
                  ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
                      formComp (I := I) x t l b +
                    (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
                      formComp (I := I) x t l a -
                    (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ l *
                      formComp (I := I) x t a b))) =
        chartInvGramMatrix (I := I) g x x a b *
          ((1 / 2 : ℝ) *
            ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
                formComp (I := I) x t m b +
              (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
                formComp (I := I) x t m a -
              (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ m *
                formComp (I := I) x t a b)) := by
    intro a b
    set P : Fin (Module.finrank ℝ E) → ℝ := fun l =>
      (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
          formComp (I := I) x t l b +
        (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
          formComp (I := I) x t l a -
        (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ l *
          formComp (I := I) x t a b with hP
    calc
      ∑ k : Fin (Module.finrank ℝ E),
            chartGramMatrix (I := I) g x x k m *
              (chartInvGramMatrix (I := I) g x x a b *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramMatrix (I := I) g x x k l * P l))
        = ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            chartGramMatrix (I := I) g x x k m *
              (chartInvGramMatrix (I := I) g x x a b *
                ((1 / 2 : ℝ) * (chartInvGramMatrix (I := I) g x x k l * P l))) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      _ = ∑ l : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            chartGramMatrix (I := I) g x x k m *
              (chartInvGramMatrix (I := I) g x x a b *
                ((1 / 2 : ℝ) * (chartInvGramMatrix (I := I) g x x k l * P l))) :=
          Finset.sum_comm
      _ = ∑ l : Fin (Module.finrank ℝ E),
            (if l = m then (1 : ℝ) else 0) *
              (chartInvGramMatrix (I := I) g x x a b * ((1 / 2 : ℝ) * P l)) := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [← sum_chartGram_mul_chartInvGram_self (I := I) g x m l, Finset.sum_mul]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          ring
      _ = chartInvGramMatrix (I := I) g x x a b * ((1 / 2 : ℝ) * P m) := by
          rw [Finset.sum_eq_single m]
          · rw [if_pos rfl, one_mul]
          · intro l _ hl
            rw [if_neg hl, zero_mul]
          · intro hm
            exact absurd (Finset.mem_univ m) hm
  have reorder :
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g x x k m *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x a b *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramMatrix (I := I) g x x k l *
                    ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
                        formComp (I := I) x t l b +
                      (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
                        formComp (I := I) x t l a -
                      (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ l *
                        formComp (I := I) x t a b))) =
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            chartGramMatrix (I := I) g x x k m *
              (chartInvGramMatrix (I := I) g x x a b *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramMatrix (I := I) g x x k l *
                    ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
                        formComp (I := I) x t l b +
                      (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
                        formComp (I := I) x t l a -
                      (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ l *
                        formComp (I := I) x t a b))) := by
    have hrow : (∑ k : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g x x k m *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x a b *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramMatrix (I := I) g x x k l *
                    ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
                        formComp (I := I) x t l b +
                      (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
                        formComp (I := I) x t l a -
                      (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ l *
                        formComp (I := I) x t a b))) =
        ∑ k : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            chartGramMatrix (I := I) g x x k m *
              (chartInvGramMatrix (I := I) g x x a b *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramMatrix (I := I) g x x k l *
                    ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
                        formComp (I := I) x t l b +
                      (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
                        formComp (I := I) x t l a -
                      (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ l *
                        formComp (I := I) x t a b))) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.mul_sum]
    rw [hrow, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
  rw [reorder]
  rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g x x k m *
            (chartInvGramMatrix (I := I) g x x a b *
              ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g x x k l *
                  ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
                      formComp (I := I) x t l b +
                    (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
                      formComp (I := I) x t l a -
                    (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ l *
                      formComp (I := I) x t a b)))) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x a b *
          ((1 / 2 : ℝ) *
            ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
                formComp (I := I) x t m b +
              (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
                formComp (I := I) x t m a -
              (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ m *
                formComp (I := I) x t a b)) from by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    exact hstage1 a b]
  calc
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x a b *
            ((1 / 2 : ℝ) *
              ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
                  formComp (I := I) x t m b +
                (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
                  formComp (I := I) x t m a -
                (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ m *
                  formComp (I := I) x t a b))
      = (1 / 2 : ℝ) * ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x a b *
              ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
                  formComp (I := I) x t m b +
                (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
                  formComp (I := I) x t m a -
                (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ m *
                  formComp (I := I) x t a b) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        ring
    _ = (1 / 2 : ℝ) *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x a b *
                ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
                  formComp (I := I) x t m b)) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g x x a b *
                  ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
                    formComp (I := I) x t m a)) -
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g x x a b *
                  ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ m *
                    formComp (I := I) x t a b))) := by
        refine congrArg _ ?_
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        ring
    _ = (chartModelBasis E).repr ξ d *
            raisedFormContractionSnd (I := I) g x ξ t m -
          (1 / 2 : ℝ) * ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ m *
            formMetricTrace (I := I) g x t) := by
        rw [block_term_a (I := I) g x ξ t d m, block_term_b (I := I) g x ξ t d m,
          block_term_trace (I := I) g x ξ t d m]
        ring

/-- **The linearized-DeTurck-correction principal symbol in closed form.**

Carrying out the principal-symbol substitution `∂_a∂_b h_{cd} ↦ ξ_a ξ_b · t_{cd}` and
contracting the chart Gram and inverse-Gram factors turns the pure `∂²h` part of the
linearized DeTurck-correction operator into the textbook **gauge symbol**
$$\sigma_{ij}(\xi)(t)
    = \xi_i \sum_l \xi^l\, t_{jl}
      + \xi_j \sum_l \xi^l\, t_{il}
      - \xi_i\xi_j\, \operatorname{tr}_g t,$$
with `ξ_a = (chartModelBasis E).repr ξ a` the chart components of the covector, `ξ^l` the
raised covector `raisedCovectorComp`, `∑_l ξ^l t_{jl} = raisedFormContractionSnd g x ξ t j`
the second-slot raised contraction of `t`, and `tr_g t = formMetricTrace g x t` the metric
trace.

The overall coefficient is exactly `1`: each of the two `k`-sums of
`chartDeTurckCorrPrincipalSymbolExpr` contributes, after the Gram / inverse-Gram
contraction `∑_k g_{kj} G^{kl} = δ^l_j`, the doubled raised contraction
`2·(½)·ξ_d ∑_l ξ^l t_{m·}` (the `½` of the `∂²h` index block, the `2` from the symmetric
term pair `ξ_a t_{jb}, ξ_b t_{ja}`), giving the unit-coefficient raised-index terms.

This is the rigorous form of "the principal symbol of `D(𝓛_{W(g)}g)[h]`": the pure
`∂²h` expression `chartDeTurckCorrPrincipalSymbolExpr`, under the substitution
`∂_a∂_b ↦ ξ_aξ_b`, equals the classical gauge symbol of the linearized
DeTurck-correction operator. -/
theorem deTurckCorrSymbolComp_eq_closedForm (g g' : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    deTurckCorrSymbolComp (I := I) g g' x ξ t i j =
      (chartModelBasis E).repr ξ i *
          raisedFormContractionSnd (I := I) g x ξ t j +
        (chartModelBasis E).repr ξ j *
          raisedFormContractionSnd (I := I) g x ξ t i -
        (chartModelBasis E).repr ξ i * (chartModelBasis E).repr ξ j *
          formMetricTrace (I := I) g x t := by
  have hgram : ∀ k j' : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g x k j' (extChartAt I x x) =
        chartGramMatrix (I := I) g x x k j' :=
    fun k j' => chartGramOnE_extChartAt_self (I := I) g x k j'
  have hinv : ∀ a b : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g x a b (extChartAt I x x) =
        chartInvGramMatrix (I := I) g x x a b :=
    fun a b => chartInvGramOnE_extChartAt_self (I := I) g x a b
  have hksum : ∀ d m : Fin (Module.finrank ℝ E),
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g x k m (extChartAt I x x) *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g x a b (extChartAt I x x) *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g x k l (extChartAt I x x) *
                    ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ a *
                        formComp (I := I) x t l b +
                      (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ b *
                        formComp (I := I) x t l a -
                      (chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ l *
                        formComp (I := I) x t a b))) =
        (chartModelBasis E).repr ξ d *
              raisedFormContractionSnd (I := I) g x ξ t m -
          (1 / 2 : ℝ) * ((chartModelBasis E).repr ξ d * (chartModelBasis E).repr ξ m *
            formMetricTrace (I := I) g x t) := by
    intro d m
    rw [← deTurckCorr_block_contraction (I := I) g x ξ t d m]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hgram k m]
    refine congrArg _ ?_
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hinv a b]
    refine congrArg _ ?_
    refine congrArg _ ?_
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hinv k l]
  have hsecond :
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g x i k (extChartAt I x x) *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g x a b (extChartAt I x x) *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g x k l (extChartAt I x x) *
                    ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ a *
                        formComp (I := I) x t l b +
                      (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ b *
                        formComp (I := I) x t l a -
                      (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
                        formComp (I := I) x t a b))) =
        ∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g x k i (extChartAt I x x) *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g x a b (extChartAt I x x) *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g x k l (extChartAt I x x) *
                    ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ a *
                        formComp (I := I) x t l b +
                      (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ b *
                        formComp (I := I) x t l a -
                      (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
                        formComp (I := I) x t a b)) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [chartGramOnE_symm (I := I) g x i k]
  rw [deTurckCorrSymbolComp_def, hsecond, hksum i j, hksum j i]
  ring

end ClosedForm

section Linearity

/-- The symbol component is **additive** in the input bilinear form.

Through the closed form `deTurckCorrSymbolComp_eq_closedForm`, each classical term is
additive in `t` (`raisedFormContractionSnd_add`, `formMetricTrace_add`), so their
combination is. -/
theorem deTurckCorrSymbolComp_add (g g' : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t t' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    deTurckCorrSymbolComp (I := I) g g' x ξ (t + t') i j =
      deTurckCorrSymbolComp (I := I) g g' x ξ t i j +
        deTurckCorrSymbolComp (I := I) g g' x ξ t' i j := by
  rw [deTurckCorrSymbolComp_eq_closedForm (I := I) g g' x ξ (t + t') i j,
    deTurckCorrSymbolComp_eq_closedForm (I := I) g g' x ξ t i j,
    deTurckCorrSymbolComp_eq_closedForm (I := I) g g' x ξ t' i j,
    raisedFormContractionSnd_add, raisedFormContractionSnd_add, formMetricTrace_add]
  ring

/-- The symbol component is **homogeneous** in the input bilinear form.

Through the closed form `deTurckCorrSymbolComp_eq_closedForm`, each classical term is
homogeneous in `t` (`raisedFormContractionSnd_smul`, `formMetricTrace_smul`), so their
combination is. -/
theorem deTurckCorrSymbolComp_smul (g g' : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (a : ℝ) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    deTurckCorrSymbolComp (I := I) g g' x ξ (a • t) i j =
      a * deTurckCorrSymbolComp (I := I) g g' x ξ t i j := by
  rw [deTurckCorrSymbolComp_eq_closedForm (I := I) g g' x ξ (a • t) i j,
    deTurckCorrSymbolComp_eq_closedForm (I := I) g g' x ξ t i j,
    raisedFormContractionSnd_smul, raisedFormContractionSnd_smul, formMetricTrace_smul]
  ring

/-- The symbol component **vanishes** on the zero bilinear form.  This is the closed form
`deTurckCorrSymbolComp_eq_closedForm` with every `t`-contraction zero. -/
@[simp] theorem deTurckCorrSymbolComp_zero (g g' : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (i j : Fin (Module.finrank ℝ E)) :
    deTurckCorrSymbolComp (I := I) g g' x ξ
      (0 : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) i j = 0 := by
  rw [deTurckCorrSymbolComp_eq_closedForm, raisedFormContractionSnd_zero,
    raisedFormContractionSnd_zero, formMetricTrace_zero]
  ring

end Linearity

section Symmetry

/-- **The linearized-DeTurck-correction symbol component is `(i, j)`-symmetric.**

Through the closed form `deTurckCorrSymbolComp_eq_closedForm`, swapping `i ↔ j`
interchanges the two raised-contraction terms `ξ_i ∑_l ξ^l t_{jl}` and
`ξ_j ∑_l ξ^l t_{il}` and fixes the trace term `−ξ_iξ_j tr_g t`, so the gauge symbol is
invariant.  The symmetry holds for *any* input bilinear form; on a symmetric input it is
the symbol-level reflection of the symmetry of the DeTurck-correction tensor. -/
theorem deTurckCorrSymbolComp_symm (g g' : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    deTurckCorrSymbolComp (I := I) g g' x ξ t i j =
      deTurckCorrSymbolComp (I := I) g g' x ξ t j i := by
  rw [deTurckCorrSymbolComp_eq_closedForm (I := I) g g' x ξ t i j,
    deTurckCorrSymbolComp_eq_closedForm (I := I) g g' x ξ t j i]
  ring

end Symmetry

section BackgroundIndependence

/-- **The linearized-DeTurck-correction symbol does not depend on the background
metric.**  The parameter `g'` appears only for signature uniformity with
`chartDeTurckCorrPrincipalSymbolExpr`; the body of `deTurckCorrSymbolComp` involves only
the metric `g`, so the symbol component is the same for any two background metrics
`g'₁`, `g'₂`. -/
theorem deTurckCorrSymbolComp_background_independent
    (g g'₁ g'₂ : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    deTurckCorrSymbolComp (I := I) g g'₁ x ξ t i j =
      deTurckCorrSymbolComp (I := I) g g'₂ x ξ t i j := by
  rw [deTurckCorrSymbolComp_def, deTurckCorrSymbolComp_def]

end BackgroundIndependence

end DeTurckLinearization
end DeTurck
end PDE
end DifferentialGeometry
