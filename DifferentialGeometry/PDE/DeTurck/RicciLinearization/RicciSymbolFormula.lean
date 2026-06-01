import DifferentialGeometry.PDE.DeTurck.RicciLinearization.RicciPrincipalPart
import DifferentialGeometry.PDE.DeTurck.RicciLinearization.InvGramPerturbation
import DifferentialGeometry.PDE.DeTurck.Symbol

/-!
# The principal symbol of the linearized chart Ricci tensor in closed form

The four-term `∂²h` part of the linearized chart Ricci tensor,
`chartRicciSecondOrderPrincipalSymbol`, is
$$[D\operatorname{Rc}]^{\sigma}_{ik}[h](y) = \tfrac12 \sum_{j,l} G^{jl}(y)\,
    \bigl(\partial_j\partial_i h_{lk} + \partial_k\partial_l h_{ij}
        - \partial_j\partial_l h_{ik} - \partial_k\partial_i h_{lj}\bigr)(y).$$

Its **principal symbol** is obtained by the formal substitution
`∂_a∂_b h_{cd} ↦ ξ_a ξ_b · t_{cd}`, where `ξ` is a covector with chart components
`ξ_a = (chartModelBasis E).repr ξ a` and `t` is the input symmetric bilinear form on the
fibre with components `t_{cd} = t (chartModelBasis E c) (chartModelBasis E d)`.  Carrying
out the substitution turns the four-term combination into the algebraic expression
$$\sigma_{ik}(\xi)(t) = \tfrac12 \sum_{j,l} G^{jl}\bigl(
      \xi_j\xi_i\, t_{lk} + \xi_k\xi_l\, t_{ij}
    - \xi_j\xi_l\, t_{ik} - \xi_k\xi_i\, t_{lj}\bigr).$$

This file makes the substitution rigorous and contracts the inverse Gram matrix into the
**classical closed form** of the linearized-Ricci symbol.  The three contractions used
are
$$\sum_j G^{jl}\,\xi_j = \xi^l, \qquad
  \sum_{j,l} G^{jl}\,\xi_j\xi_l = |\xi|^2_g, \qquad
  \sum_{j,l} G^{jl}\,t_{lj} = \operatorname{tr}_g t,$$
the raised covector `raisedCovectorComp`, the squared norm `metricCovectorNormSq`, and the
metric trace of the bilinear form `formMetricTrace`.  The resulting closed form is
$$\sigma_{ik}(\xi)(t) = \tfrac12\,\xi_i \sum_l \xi^l\, t_{lk}
    + \tfrac12\,\xi_k \sum_j \xi^j\, t_{ij}
    - \tfrac12\,|\xi|^2_g\, t_{ik}
    - \tfrac12\,\xi_i\xi_k\, \operatorname{tr}_g t.$$

## Contents

* `formComp` — the `(c, d)` chart component `t_{cd}` of a fibre bilinear form `t`.
* `formMetricTrace` — the metric trace `tr_g t = ∑_{m,n} G^{mn} t_{mn}` of a fibre
  bilinear form, the bilinear-form analogue of `metricTrace` (which traces a
  `ChartMetricPerturbation`).
* `raisedFormContraction` — the raised contraction `∑_l ξ^l t_{lk}`, the result of
  raising the first index of `t` against `ξ`.
* `ricciSymbolComp` — the `(i, k)` component of the linearized-Ricci principal symbol,
  defined by the `∂_a∂_b ↦ ξ_aξ_b` substitution in
  `chartRicciSecondOrderPrincipalSymbol`.
* `ricciSymbolComp_eq_closedForm` — the classical closed-form theorem.
* `ricciSymbolComp_add`, `ricciSymbolComp_smul`, `ricciSymbolComp_zero` — `ℝ`-linearity
  of the symbol component in the input bilinear form.
* `ricciSymbolComp_symm` — the `(i, k)`-symmetry of the symbol component on a symmetric
  input.
-/

noncomputable section

open Set Function
open scoped Topology ContDiff Matrix Manifold

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace RicciLinearization

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

section InvGramBridge

/-- The chart-target inverse Gram field of `g`, in the chart at `x`, evaluated at the
chart image of `x` itself, is the chart inverse Gram matrix `chartInvGramMatrix g x x`.
This is `chartInvGramOnE_def` followed by `(extChartAt I x).symm (extChartAt I x x) = x`. -/
lemma chartInvGramOnE_extChartAt_self (g : SmoothRiemannianMetric I M) (x : M)
    (j l : Fin (Module.finrank ℝ E)) :
    chartInvGramOnE (I := I) g x j l (extChartAt I x x) =
      chartInvGramMatrix (I := I) g x x j l := by
  rw [chartInvGramOnE_def, extChartAt_to_inv]

/-- Symmetry of the chart inverse Gram matrix `chartInvGramMatrix g x x` in its two
indices.  It is the inverse of the Hermitian chart Gram matrix, hence Hermitian, hence
(over `ℝ`) symmetric. -/
lemma chartInvGramMatrix_self_symm (g : SmoothRiemannianMetric I M) (x : M)
    (j l : Fin (Module.finrank ℝ E)) :
    chartInvGramMatrix (I := I) g x x j l =
      chartInvGramMatrix (I := I) g x x l j := by
  have hHerm : (chartInvGramMatrix (I := I) g x x).IsHermitian := by
    unfold chartInvGramMatrix
    exact (chartGramMatrix_isHermitian (I := I) g x x).inv
  have hentry := hHerm.apply l j
  rwa [star_trivial] at hentry

end InvGramBridge

section FibreForm

/-- The `(c, d)` **chart component** of a fibre bilinear form `t` at `x`:
$$t_{cd} = t(e_c, e_d),$$
the evaluation of `t` on the model-basis vectors `e_c = chartModelBasis E c` (a covector
component convention matching `chartModelBasis E`'s use throughout the chart calculus).
The fibre `TangentSpace I x` is the model space `E`, so the model-basis vectors are
admissible arguments of `t`. -/
def formComp (x : M)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (c d : Fin (Module.finrank ℝ E)) : ℝ :=
  t ((chartModelBasis E) c) ((chartModelBasis E) d)

@[simp] lemma formComp_def (x : M)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (c d : Fin (Module.finrank ℝ E)) :
    formComp (I := I) x t c d =
      t ((chartModelBasis E) c) ((chartModelBasis E) d) := rfl

/-- The chart components of the zero bilinear form vanish. -/
@[simp] lemma formComp_zero (x : M) (c d : Fin (Module.finrank ℝ E)) :
    formComp (I := I) x
      (0 : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) c d = 0 := rfl

/-- The chart components are additive in the bilinear form. -/
lemma formComp_add (x : M)
    (t t' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (c d : Fin (Module.finrank ℝ E)) :
    formComp (I := I) x (t + t') c d =
      formComp (I := I) x t c d + formComp (I := I) x t' c d := by
  simp [formComp]

/-- The chart components are homogeneous in the bilinear form. -/
lemma formComp_smul (x : M) (a : ℝ)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (c d : Fin (Module.finrank ℝ E)) :
    formComp (I := I) x (a • t) c d = a * formComp (I := I) x t c d := by
  simp [formComp]

/-- For a **symmetric** bilinear form `t` the chart components are symmetric:
`t_{cd} = t_{dc}`. -/
lemma formComp_symm (x : M)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) (c d : Fin (Module.finrank ℝ E)) :
    formComp (I := I) x t c d = formComp (I := I) x t d c := by
  rw [formComp_def, formComp_def, ht]

/-- The **metric trace** of a fibre bilinear form `t` at `x`, in the chart at `x`:
$$\operatorname{tr}_g t = \sum_{m,n} g^{mn}(x)\, t_{mn},$$
the full contraction of the chart inverse Gram matrix `chartInvGramMatrix g x x` against
the chart components of `t`.  This is the bilinear-form analogue of `metricTrace`, which
traces a `ChartMetricPerturbation`. -/
def formMetricTrace (g : SmoothRiemannianMetric I M) (x : M)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) : ℝ :=
  ∑ m : Fin (Module.finrank ℝ E),
    ∑ n : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x m n * formComp (I := I) x t m n

@[simp] lemma formMetricTrace_def (g : SmoothRiemannianMetric I M) (x : M)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    formMetricTrace (I := I) g x t =
      ∑ m : Fin (Module.finrank ℝ E),
        ∑ n : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x m n * formComp (I := I) x t m n := rfl

/-- The metric trace of the zero bilinear form vanishes. -/
@[simp] lemma formMetricTrace_zero (g : SmoothRiemannianMetric I M) (x : M) :
    formMetricTrace (I := I) g x
      (0 : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) = 0 := by
  simp [formMetricTrace]

/-- The metric trace is additive in the bilinear form. -/
lemma formMetricTrace_add (g : SmoothRiemannianMetric I M) (x : M)
    (t t' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    formMetricTrace (I := I) g x (t + t') =
      formMetricTrace (I := I) g x t + formMetricTrace (I := I) g x t' := by
  rw [formMetricTrace_def, formMetricTrace_def, formMetricTrace_def,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [formComp_add]
  ring

/-- The metric trace is homogeneous in the bilinear form. -/
lemma formMetricTrace_smul (g : SmoothRiemannianMetric I M) (x : M) (a : ℝ)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    formMetricTrace (I := I) g x (a • t) = a * formMetricTrace (I := I) g x t := by
  rw [formMetricTrace_def, formMetricTrace_def, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [formComp_smul]
  ring

/-- The **index-raised contraction** of the first slot of a fibre bilinear form `t`
against a covector `ξ`, in the chart at `x`:
$$(\,t\,\xi\,)_k = \sum_l \xi^l\, t_{lk},$$
where `ξ^l = raisedCovectorComp g x ξ l` is the raised covector.  It is the `k`-th
component of the `(0,1)`-tensor obtained by raising `t`'s first index with `ξ`. -/
def raisedFormContraction (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (k : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ l : Fin (Module.finrank ℝ E),
    raisedCovectorComp (I := I) g x ξ l * formComp (I := I) x t l k

@[simp] lemma raisedFormContraction_def (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    raisedFormContraction (I := I) g x ξ t k =
      ∑ l : Fin (Module.finrank ℝ E),
        raisedCovectorComp (I := I) g x ξ l * formComp (I := I) x t l k := rfl

/-- The raised contraction of the zero bilinear form vanishes. -/
@[simp] lemma raisedFormContraction_zero (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (k : Fin (Module.finrank ℝ E)) :
    raisedFormContraction (I := I) g x ξ
      (0 : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) k = 0 := by
  simp [raisedFormContraction]

/-- The raised contraction is additive in the bilinear form. -/
lemma raisedFormContraction_add (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t t' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    raisedFormContraction (I := I) g x ξ (t + t') k =
      raisedFormContraction (I := I) g x ξ t k +
        raisedFormContraction (I := I) g x ξ t' k := by
  rw [raisedFormContraction_def, raisedFormContraction_def, raisedFormContraction_def,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [formComp_add]
  ring

/-- The raised contraction is homogeneous in the bilinear form. -/
lemma raisedFormContraction_smul (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) (a : ℝ)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    raisedFormContraction (I := I) g x ξ (a • t) k =
      a * raisedFormContraction (I := I) g x ξ t k := by
  rw [raisedFormContraction_def, raisedFormContraction_def, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [formComp_smul]
  ring

/-- The **index-raised contraction of the second slot** of a fibre bilinear form `t`
against a covector `ξ`, in the chart at `x`:
$$(\,\xi\,t\,)_i = \sum_j \xi^j\, t_{ij},$$
where `ξ^j = raisedCovectorComp g x ξ j` is the raised covector.  It is the `i`-th
component of the `(0,1)`-tensor obtained by raising `t`'s **second** index with `ξ`.

For a symmetric form this agrees with `raisedFormContraction`
(`raisedFormContractionSnd_eq_of_symm`); the linearized-Ricci symbol's two
raised-contraction terms use the two slots separately, so both are recorded. -/
def raisedFormContractionSnd (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E),
    raisedCovectorComp (I := I) g x ξ j * formComp (I := I) x t i j

@[simp] lemma raisedFormContractionSnd_def (g : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i : Fin (Module.finrank ℝ E)) :
    raisedFormContractionSnd (I := I) g x ξ t i =
      ∑ j : Fin (Module.finrank ℝ E),
        raisedCovectorComp (I := I) g x ξ j * formComp (I := I) x t i j := rfl

/-- The second-slot raised contraction of the zero bilinear form vanishes. -/
@[simp] lemma raisedFormContractionSnd_zero (g : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (i : Fin (Module.finrank ℝ E)) :
    raisedFormContractionSnd (I := I) g x ξ
      (0 : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) i = 0 := by
  simp [raisedFormContractionSnd]

/-- The second-slot raised contraction is additive in the bilinear form. -/
lemma raisedFormContractionSnd_add (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t t' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i : Fin (Module.finrank ℝ E)) :
    raisedFormContractionSnd (I := I) g x ξ (t + t') i =
      raisedFormContractionSnd (I := I) g x ξ t i +
        raisedFormContractionSnd (I := I) g x ξ t' i := by
  rw [raisedFormContractionSnd_def, raisedFormContractionSnd_def,
    raisedFormContractionSnd_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [formComp_add]
  ring

/-- The second-slot raised contraction is homogeneous in the bilinear form. -/
lemma raisedFormContractionSnd_smul (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (a : ℝ) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i : Fin (Module.finrank ℝ E)) :
    raisedFormContractionSnd (I := I) g x ξ (a • t) i =
      a * raisedFormContractionSnd (I := I) g x ξ t i := by
  rw [raisedFormContractionSnd_def, raisedFormContractionSnd_def, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [formComp_smul]
  ring

/-- For a **symmetric** bilinear form the two raised contractions agree:
`∑_j ξ^j t_{ij} = ∑_l ξ^l t_{li}`.  Indeed `t_{ij} = t_{ji}`, so raising the second slot
equals raising the first. -/
lemma raisedFormContractionSnd_eq_of_symm (g : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) (i : Fin (Module.finrank ℝ E)) :
    raisedFormContractionSnd (I := I) g x ξ t i =
      raisedFormContraction (I := I) g x ξ t i := by
  rw [raisedFormContractionSnd_def, raisedFormContraction_def]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [formComp_symm (I := I) x t ht i j]

end FibreForm

section SymbolComponent

/-- The `(i, k)` component of the **linearized-Ricci principal symbol**, applied to the
input bilinear form `t`.

It is obtained from `chartRicciSecondOrderPrincipalSymbol` (in the chart at `x` itself,
at the chart image `extChartAt I x x`) by the principal-symbol substitution
`∂_a∂_b h_{cd} ↦ ξ_a ξ_b · t_{cd}`:
$$\sigma_{ik}(\xi)(t) = \tfrac12 \sum_{j,l} G^{jl}\,\bigl(
    \xi_j\xi_i\, t_{lk} + \xi_k\xi_l\, t_{ij}
  - \xi_j\xi_l\, t_{ik} - \xi_k\xi_i\, t_{lj}\bigr),$$
with `G^{jl} = chartInvGramOnE g x j l (extChartAt I x x)`,
`ξ_a = (chartModelBasis E).repr ξ a`, and `t_{cd} = formComp x t c d`.

The four summands mirror, term by term, the four iterated derivatives of
`chartRicciSecondOrderPrincipalSymbol_def`:
`∂_j∂_i h_{lk} ↦ ξ_jξ_i t_{lk}`, `∂_k∂_l h_{ij} ↦ ξ_kξ_l t_{ij}`,
`∂_j∂_l h_{ik} ↦ ξ_jξ_l t_{ik}`, `∂_k∂_i h_{lj} ↦ ξ_kξ_i t_{lj}`. -/
def ricciSymbolComp (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) : ℝ :=
  (1 / 2 : ℝ) * ∑ j : Fin (Module.finrank ℝ E),
    ∑ l : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g x j l (extChartAt I x x) *
        ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ i *
            formComp (I := I) x t l k +
          (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ l *
            formComp (I := I) x t i j -
          (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
            formComp (I := I) x t i k -
          (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
            formComp (I := I) x t l j)

@[simp] lemma ricciSymbolComp_def (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    ricciSymbolComp (I := I) g x ξ t i k =
      (1 / 2 : ℝ) * ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g x j l (extChartAt I x x) *
            ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l k +
              (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ l *
                formComp (I := I) x t i j -
              (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
                formComp (I := I) x t i k -
              (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l j) := rfl

end SymbolComponent

section ClosedForm

/-- **First contraction.**  `∑_{j,l} G^{jl} ξ_j ξ_i t_{lk} = ξ_i · ∑_l ξ^l t_{lk}`.
Factoring `ξ_i` out and summing first over `j` recognises `∑_j G^{jl} ξ_j = ξ^l` after a
use of `chartInvGramMatrix`-symmetry. -/
private lemma sum_term_one (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x j l *
            ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ i *
              formComp (I := I) x t l k) =
      (chartModelBasis E).repr ξ i *
        raisedFormContraction (I := I) g x ξ t k := by
  calc
    ∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x j l *
              ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l k)
      = ∑ l : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x j l *
              ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l k) := Finset.sum_comm
    _ = ∑ l : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr ξ i *
            (raisedCovectorComp (I := I) g x ξ l * formComp (I := I) x t l k) := by
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [raisedCovectorComp_def, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [chartInvGramMatrix_self_symm (I := I) g x j l]
        ring
    _ = (chartModelBasis E).repr ξ i *
          raisedFormContraction (I := I) g x ξ t k := by
        rw [raisedFormContraction_def, Finset.mul_sum]

/-- **Second contraction.**  `∑_{j,l} G^{jl} ξ_k ξ_l t_{ij} = ξ_k · ∑_j ξ^j t_{ij}`.
Factoring `ξ_k` out and summing first over `l` recognises `∑_l G^{jl} ξ_l = ξ^j`
directly; the surviving `∑_j ξ^j t_{ij}` raises the **second** slot of `t`.  (Unlike the
first contraction this raises the second index of `t`, hence uses
`raisedFormContractionSnd`.) -/
private lemma sum_term_two (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x j l *
            ((chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ l *
              formComp (I := I) x t i j) =
      (chartModelBasis E).repr ξ k *
        raisedFormContractionSnd (I := I) g x ξ t i := by
  calc
    ∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x j l *
              ((chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ l *
                formComp (I := I) x t i j)
      = ∑ j : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr ξ k *
            (raisedCovectorComp (I := I) g x ξ j * formComp (I := I) x t i j) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [raisedCovectorComp_def, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        ring
    _ = (chartModelBasis E).repr ξ k *
          raisedFormContractionSnd (I := I) g x ξ t i := by
        rw [raisedFormContractionSnd_def, Finset.mul_sum]

/-- **Third contraction.**  `∑_{j,l} G^{jl} ξ_j ξ_l t_{ik} = |ξ|²_g · t_{ik}`.
Factoring `t_{ik}` out exposes `∑_{j,l} G^{jl} ξ_j ξ_l = metricCovectorNormSq`. -/
private lemma sum_term_three (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x j l *
            ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
              formComp (I := I) x t i k) =
      metricCovectorNormSq (I := I) g x ξ * formComp (I := I) x t i k := by
  rw [metricCovectorNormSq_def, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

/-- **Fourth contraction.**  `∑_{j,l} G^{jl} ξ_k ξ_i t_{lj} = ξ_k ξ_i · tr_g t`.
Factoring `ξ_k ξ_i` out leaves `∑_{j,l} G^{jl} t_{lj}`; swapping the summation indices and
using `chartInvGramMatrix`-symmetry identifies this with `formMetricTrace`. -/
private lemma sum_term_four (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x j l *
            ((chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
              formComp (I := I) x t l j) =
      (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
        formMetricTrace (I := I) g x t := by
  calc
    ∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x j l *
              ((chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l j)
      = ∑ m : Fin (Module.finrank ℝ E),
          ∑ n : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
              (chartInvGramMatrix (I := I) g x x m n *
                formComp (I := I) x t m n) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [chartInvGramMatrix_self_symm (I := I) g x n m]
        ring
    _ = (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
          formMetricTrace (I := I) g x t := by
        rw [formMetricTrace_def, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [Finset.mul_sum]

/-- The four-term bracket in `ricciSymbolComp`, summed over `j` and `l` against the chart
inverse Gram matrix, splits into the four contracted double sums.  This is the additive
decomposition of the double sum that the closed-form theorem feeds the contraction
lemmas. -/
private lemma ricciSymbol_doubleSum_split (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x j l *
            ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l k +
              (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ l *
                formComp (I := I) x t i j -
              (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
                formComp (I := I) x t i k -
              (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l j) =
      (∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x j l *
              ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l k)) +
      (∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x j l *
              ((chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ l *
                formComp (I := I) x t i j)) -
      (∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x j l *
              ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
                formComp (I := I) x t i k)) -
      (∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x j l *
              ((chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l j)) := by
  have hdist : ∀ j l : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x j l *
          ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ i *
              formComp (I := I) x t l k +
            (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ l *
              formComp (I := I) x t i j -
            (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
              formComp (I := I) x t i k -
            (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
              formComp (I := I) x t l j) =
        chartInvGramMatrix (I := I) g x x j l *
            ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ i *
              formComp (I := I) x t l k) +
          chartInvGramMatrix (I := I) g x x j l *
            ((chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ l *
              formComp (I := I) x t i j) -
          chartInvGramMatrix (I := I) g x x j l *
            ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
              formComp (I := I) x t i k) -
          chartInvGramMatrix (I := I) g x x j l *
            ((chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
              formComp (I := I) x t l j) := fun j l => by ring
  have hrow : ∀ j : Fin (Module.finrank ℝ E),
      (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x j l *
            ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l k +
              (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ l *
                formComp (I := I) x t i j -
              (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
                formComp (I := I) x t i k -
              (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l j)) =
        (∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x j l *
              ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l k)) +
          (∑ l : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x j l *
                ((chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ l *
                  formComp (I := I) x t i j)) -
          (∑ l : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x j l *
                ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
                  formComp (I := I) x t i k)) -
          (∑ l : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x j l *
                ((chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
                  formComp (I := I) x t l j)) := by
    intro j
    rw [Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) => hdist j l),
      Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hrow j),
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- **The linearized-Ricci principal symbol in classical closed form.**

Carrying out the principal-symbol substitution `∂_a∂_b h_{cd} ↦ ξ_a ξ_b · t_{cd}` and
contracting the chart inverse Gram matrix turns the four-term `∂²h` part of the linearized
chart Ricci tensor into the textbook closed form
$$\sigma_{ik}(\xi)(t) = \tfrac12\,\xi_i \sum_l \xi^l\, t_{lk}
    + \tfrac12\,\xi_k \sum_j \xi^j\, t_{ij}
    - \tfrac12\,|\xi|^2_g\, t_{ik}
    - \tfrac12\,\xi_i\xi_k\, \operatorname{tr}_g t,$$
with `ξ_a = (chartModelBasis E).repr ξ a` the chart components of the covector and `ξ^m`
the raised covector `raisedCovectorComp`.  The first raised-contraction term raises the
**first** index of `t` (`∑_l ξ^l t_{lk} = raisedFormContraction`), the second raises the
**second** index (`∑_j ξ^j t_{ij} = raisedFormContractionSnd`); they coincide on a
symmetric input.  Further, `|ξ|²_g = metricCovectorNormSq` and `tr_g t = formMetricTrace`.

This is the rigorous form of "the principal symbol of `D Rc[h]`": the four-term `∂²h`
expression `chartRicciSecondOrderPrincipalSymbol`, under `∂_a∂_b ↦ ξ_aξ_b`, equals the
classical contracted symbol of the linearized Ricci operator. -/
theorem ricciSymbolComp_eq_closedForm (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    ricciSymbolComp (I := I) g x ξ t i k =
      (1 / 2 : ℝ) * ((chartModelBasis E).repr ξ i *
          raisedFormContraction (I := I) g x ξ t k) +
        (1 / 2 : ℝ) * ((chartModelBasis E).repr ξ k *
          raisedFormContractionSnd (I := I) g x ξ t i) -
        (1 / 2 : ℝ) * (metricCovectorNormSq (I := I) g x ξ *
          formComp (I := I) x t i k) -
        (1 / 2 : ℝ) * ((chartModelBasis E).repr ξ i *
          (chartModelBasis E).repr ξ k * formMetricTrace (I := I) g x t) := by
  rw [ricciSymbolComp_def]
  have hgram : ∀ j l : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g x j l (extChartAt I x x) =
        chartInvGramMatrix (I := I) g x x j l :=
    fun j l => chartInvGramOnE_extChartAt_self (I := I) g x j l
  rw [show (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g x j l (extChartAt I x x) *
            ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l k +
              (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ l *
                formComp (I := I) x t i j -
              (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
                formComp (I := I) x t i k -
              (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l j)) =
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x j l *
            ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l k +
              (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ l *
                formComp (I := I) x t i j -
              (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
                formComp (I := I) x t i k -
              (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l j)) from by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hgram j l]]
  rw [ricciSymbol_doubleSum_split (I := I) g x ξ t i k,
    sum_term_one (I := I) g x ξ t i k, sum_term_two (I := I) g x ξ t i k,
    sum_term_three (I := I) g x ξ t i k, sum_term_four (I := I) g x ξ t i k]
  ring

end ClosedForm

section Linearity

/-- The symbol component is **additive** in the input bilinear form.

Through the closed form `ricciSymbolComp_eq_closedForm`, each of the four classical terms
is additive in `t` (`raisedFormContraction_add`, `raisedFormContractionSnd_add`,
`formComp_add`, `formMetricTrace_add`), so their `½`-weighted combination is. -/
theorem ricciSymbolComp_add (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t t' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    ricciSymbolComp (I := I) g x ξ (t + t') i k =
      ricciSymbolComp (I := I) g x ξ t i k +
        ricciSymbolComp (I := I) g x ξ t' i k := by
  rw [ricciSymbolComp_eq_closedForm (I := I) g x ξ (t + t') i k,
    ricciSymbolComp_eq_closedForm (I := I) g x ξ t i k,
    ricciSymbolComp_eq_closedForm (I := I) g x ξ t' i k,
    raisedFormContraction_add, raisedFormContractionSnd_add, formComp_add,
    formMetricTrace_add]
  ring

/-- The symbol component is **homogeneous** in the input bilinear form.

Through the closed form `ricciSymbolComp_eq_closedForm`, each of the four classical terms
is homogeneous in `t` (`raisedFormContraction_smul`, `raisedFormContractionSnd_smul`,
`formComp_smul`, `formMetricTrace_smul`), so their `½`-weighted combination is. -/
theorem ricciSymbolComp_smul (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) (a : ℝ)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    ricciSymbolComp (I := I) g x ξ (a • t) i k =
      a * ricciSymbolComp (I := I) g x ξ t i k := by
  rw [ricciSymbolComp_eq_closedForm (I := I) g x ξ (a • t) i k,
    ricciSymbolComp_eq_closedForm (I := I) g x ξ t i k,
    raisedFormContraction_smul, raisedFormContractionSnd_smul, formComp_smul,
    formMetricTrace_smul]
  ring

/-- The symbol component **vanishes** on the zero bilinear form.  This is the closed form
`ricciSymbolComp_eq_closedForm` with every `t`-contraction zero. -/
@[simp] theorem ricciSymbolComp_zero (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (i k : Fin (Module.finrank ℝ E)) :
    ricciSymbolComp (I := I) g x ξ
      (0 : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) i k = 0 := by
  rw [ricciSymbolComp_eq_closedForm, raisedFormContraction_zero,
    raisedFormContractionSnd_zero, formComp_zero, formMetricTrace_zero]
  ring

end Linearity

section Symmetry

/-- **The linearized-Ricci symbol component is symmetric on a symmetric input.**  For an
input bilinear form `t` with `t v w = t w v`, the symbol component is unchanged by
swapping its two indices:
$$\sigma_{ik}(\xi)(t) = \sigma_{ki}(\xi)(t).$$
Through the closed form `ricciSymbolComp_eq_closedForm`: on a symmetric input the
second-slot raised contraction equals the first-slot one
(`raisedFormContractionSnd_eq_of_symm`), so the `i ↔ k` swap interchanges the two
raised-contraction terms `½ ξ_i ∑ ξ^l t_{lk}` and `½ ξ_k ∑ ξ^l t_{li}`; the swap fixes the
`−½ |ξ|²_g t_{ik}` term once `t_{ik} = t_{ki}`, and fixes the trace term
`−½ ξ_iξ_k tr_g t`. -/
theorem ricciSymbolComp_symm (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) (i k : Fin (Module.finrank ℝ E)) :
    ricciSymbolComp (I := I) g x ξ t i k =
      ricciSymbolComp (I := I) g x ξ t k i := by
  rw [ricciSymbolComp_eq_closedForm (I := I) g x ξ t i k,
    ricciSymbolComp_eq_closedForm (I := I) g x ξ t k i]
  rw [raisedFormContractionSnd_eq_of_symm (I := I) g x ξ t ht i,
    raisedFormContractionSnd_eq_of_symm (I := I) g x ξ t ht k,
    formComp_symm (I := I) x t ht i k]
  ring

end Symmetry

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry
