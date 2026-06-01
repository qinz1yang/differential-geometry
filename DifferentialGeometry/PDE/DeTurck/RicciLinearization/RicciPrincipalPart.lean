import DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChristoffelLinearization

/-!
# The second-order part of the linearized chart Ricci tensor

The chart Ricci tensor of a Riemannian metric is, in chart coordinates, the algebraic
expression
$$\operatorname{Rc}_{ik}(\alpha)(y) = \sum_j \bigl(\partial_j \Gamma^j{}_{ik}
    - \partial_k \Gamma^j{}_{ij}\bigr)(y) + (\Gamma\cdot\Gamma\text{ terms})(y),$$
a function of the chart Christoffel symbols, their chart partial derivatives, and the
chart inverse Gram matrix.

Linearizing in a metric-perturbation direction `h` and collecting the terms that carry
**two** chart derivatives of `h` is the first step toward the principal symbol of the
linearized Ricci operator.  The `Γ·Γ` terms and the `D(G⁻¹)` part of the Christoffel
linearization each carry **at most one** chart derivative of `h`, so the second-order
part comes only from `∂` applied to the *principal* part
`chartLinearizedChristoffelPrincipal` of the linearized Christoffel symbol.  Thus the
second-order part of `D\operatorname{Rc}_{ik}[h]` is
$$\sum_j \bigl(\partial_j [D\Gamma_{\mathrm{principal}}]^j{}_{ik}
    - \partial_k [D\Gamma_{\mathrm{principal}}]^j{}_{ij}\bigr)(y).$$

## Contents

* `chartRicciSecondOrderPart` — the second-order-in-`h` part of `D\operatorname{Rc}_{ik}[h]`,
  defined as the chart-derivative combination `∑_j(∂_j[DΓ_principal]^j{}_{ik}
  − ∂_k[DΓ_principal]^j{}_{ij})` of the principal linearized Christoffel part, together
  with its unfolding lemma `chartRicciSecondOrderPart_def`.
* `chartRicciSecondOrderPrincipalSymbol` — the explicit four-term `∂²h` expression
  $$\tfrac12 \sum_{j,l} G^{jl}\bigl(\partial_j\partial_i h_{lk}
      + \partial_k\partial_l h_{ij} - \partial_j\partial_l h_{ik}
      - \partial_k\partial_i h_{lj}\bigr),$$
  obtained from `chartRicciSecondOrderPart` after a Leibniz expansion of the outer
  derivative and the Schwarz cancellation of the two `∂\partial h_{li}` terms.
* `chartRicciFirstOrderRemainder` — the complementary `(∂G⁻¹)\cdot(∂h)` terms, each
  carrying **exactly one** chart derivative of a component field of `h`.
* `chartRicciSecondOrderPart_eq_principalSymbol_add_remainder` — the rigorous split
  `chartRicciSecondOrderPart = chartRicciSecondOrderPrincipalSymbol
  + chartRicciFirstOrderRemainder`, valid at chart-interior points.
* `chartRicciFirstOrderRemainder_eq_first_order_sum` — the explicit exhibition of the
  remainder as a finite sum of terms of the syntactic shape
  `(coefficient)·partialDeriv _ (h _ _) _`, making precise that it carries at most one
  chart derivative of `h`.
* `h`-linearity (`_add`, `_smul`, `_zero`) of all three objects.

The `∂_a∂_b ↦ ξ_a\xi_b` substitution applied to `chartRicciSecondOrderPrincipalSymbol`
recovers the principal symbol of the linearized Ricci operator; the remainder, carrying
only first derivatives of `h`, is invisible to that second-order symbol.
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

section Differentiability

/-- The chart inverse Gram entry `G^{jl}` is differentiable at every point in the
interior of the chart target. -/
lemma chartInvGramOnE_differentiableAt_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (j l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartInvGramOnE (I := I) g α j l) y := by
  have hcd : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α j l)
      (extChartAt I α).target := chartInvGramOnE_contDiffOn (I := I) g α j l
  have hcd_int : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α j l)
      (interior (extChartAt I α).target) := hcd.mono interior_subset
  have hop : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hat : ContDiffAt ℝ ∞ (chartInvGramOnE (I := I) g α j l) y :=
    hcd_int.contDiffAt (hop.mem_nhds hy)
  exact hat.differentiableAt (by simp)

/-- Each `partialDeriv` of a globally `C^∞` real function on the model space is itself
globally `C^∞`. -/
lemma partialDeriv_contDiff_of_contDiff
    {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (i : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (partialDeriv (E := E) i u) := by
  have hfderiv : ContDiff ℝ ∞ (fderiv ℝ u) :=
    hu.fderiv_right (by rw [ENat.coe_top_add_one])
  unfold partialDeriv
  exact hfderiv.clm_apply contDiff_const

/-- Each `partialDeriv` of a perturbation component field is globally `C^∞`. -/
lemma partialDeriv_perturbation_contDiff
    (h : ChartMetricPerturbation E) (i a b : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (partialDeriv (E := E) i (h a b)) :=
  partialDeriv_contDiff_of_contDiff (h.smooth a b) i

/-- Each `partialDeriv` of a perturbation component field is differentiable at every
point of the model space. -/
lemma partialDeriv_perturbation_differentiableAt
    (h : ChartMetricPerturbation E) (i a b : Fin (Module.finrank ℝ E)) (y : E) :
    DifferentiableAt ℝ (partialDeriv (E := E) i (h a b)) y :=
  ((partialDeriv_perturbation_contDiff h i a b).differentiable (by simp)).differentiableAt

/-- The principal linearized Christoffel part is differentiable at every point in the
interior of the chart target (as a function of the chart-coordinate point). -/
lemma chartLinearizedChristoffelPrincipal_differentiableAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ
      (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h i j k y') y := by
  have hcd : ContDiffOn ℝ ∞
      (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h i j k y')
      (interior (extChartAt I α).target) :=
    (chartLinearizedChristoffelPrincipal_contDiffOn (I := I) g α h i j k).mono
      interior_subset
  have hat : ContDiffAt ℝ ∞
      (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h i j k y') y :=
    hcd.contDiffAt (isOpen_interior.mem_nhds hy)
  exact hat.differentiableAt (by simp)

/-- **Schwarz symmetry for a perturbation component field.**  The iterated chart partial
derivative of a perturbation component field `h_{ab}` is symmetric in the two
differentiation directions: `∂_p∂_q h_{ab} = ∂_q∂_p h_{ab}`.  This is Schwarz's theorem
applied to the globally `C^∞` component field `h a b`; no chart-interior hypothesis is
needed because `h a b` is smooth on all of the model space. -/
lemma partialDeriv_partialDeriv_perturbation_swap
    (h : ChartMetricPerturbation E) (a b p q : Fin (Module.finrank ℝ E)) (y : E) :
    partialDeriv (E := E) p (partialDeriv (E := E) q (h a b)) y =
      partialDeriv (E := E) q (partialDeriv (E := E) p (h a b)) y := by
  classical
  have hsmooth : ContDiff ℝ ∞ (h a b) := h.smooth a b
  have hcontDiffAt : ContDiffAt ℝ ∞ (h a b) y := hsmooth.contDiffAt
  have hsymm2 : IsSymmSndFDerivAt ℝ (h a b) y := by
    refine ContDiffAt.isSymmSndFDerivAt hcontDiffAt ?_
    rw [minSmoothness_of_isRCLikeNormedField]
    decide
  have hg_diff : DifferentiableAt ℝ (fderiv ℝ (h a b)) y := by
    have hfderiv : ContDiff ℝ ∞ (fderiv ℝ (h a b)) :=
      hsmooth.fderiv_right (by rw [ENat.coe_top_add_one])
    exact (hfderiv.differentiable (by simp)).differentiableAt
  have hkey : ∀ r s : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) r (partialDeriv (E := E) s (h a b)) y =
        (fderiv ℝ (fderiv ℝ (h a b)) y ((chartModelBasis E) r))
          ((chartModelBasis E) s) := by
    intro r s
    unfold partialDeriv
    set L : (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.apply ℝ ℝ ((chartModelBasis E) s)
    have hcomp_eq : (fun z : E => fderiv ℝ (h a b) z ((chartModelBasis E) s)) =
        L ∘ (fderiv ℝ (h a b)) := by
      funext z; rfl
    rw [hcomp_eq, fderiv_comp y L.differentiableAt hg_diff, L.fderiv]
    rfl
  rw [hkey p q, hkey q p]
  exact hsymm2 _ _

end Differentiability

/-- The **second-order-in-`h` part of the linearized chart Ricci tensor** in the chart
at `α`, in the perturbation direction `h`, evaluated at the chart-coordinate point
`y ∈ E`:
$$[D\operatorname{Rc}]^{(2)}_{ik}[h](y) = \sum_j \bigl(\partial_j
    [D\Gamma_{\mathrm{principal}}]^j{}_{ik} - \partial_k
    [D\Gamma_{\mathrm{principal}}]^j{}_{ij}\bigr)(y),$$
where `[DΓ_principal]^j{}_{ab} = chartLinearizedChristoffelPrincipal g α h a b j` is the
principal part of the linearized Christoffel symbol.  This is the term of the linearized
Ricci tensor carrying two chart derivatives of `h`; the `Γ·Γ` and `D(G⁻¹)` contributions
are lower order and do not appear here. -/
def chartRicciSecondOrderPart (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E),
    (partialDeriv (E := E) j
        (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h i k j y') y -
      partialDeriv (E := E) k
        (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h i j j y') y)

@[simp] lemma chartRicciSecondOrderPart_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciSecondOrderPart (I := I) g α h i k y =
      ∑ j : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j
            (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h i k j y') y -
          partialDeriv (E := E) k
            (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h i j j y') y) :=
  rfl

/-- The **explicit second-order symbol expression** of the linearized chart Ricci
tensor: the four-term `∂²h` combination
$$[D\operatorname{Rc}]^{\sigma}_{ik}[h](y) = \tfrac12 \sum_{j,l} G^{jl}(y)\,
    \bigl(\partial_j\partial_i h_{lk} + \partial_k\partial_l h_{ij}
        - \partial_j\partial_l h_{ik} - \partial_k\partial_i h_{lj}\bigr)(y),$$
where `∂_a∂_b h_{cd}` denotes the iterated chart partial derivative
`partialDeriv a (partialDeriv b (h c d))`.

This is the pure `∂²h` content of `chartRicciSecondOrderPart`: every term carries
exactly two chart derivatives of a component field of `h`, with the chart inverse Gram
matrix `G^{jl}` as a frozen coefficient.  Substituting `∂_a∂_b ↦ ξ_aξ_b` here gives the
principal symbol of the linearized Ricci operator. -/
def chartRicciSecondOrderPrincipalSymbol (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ j : Fin (Module.finrank ℝ E),
    ∑ l : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α j l y *
        (partialDeriv (E := E) j (partialDeriv (E := E) i (h l k)) y +
         partialDeriv (E := E) k (partialDeriv (E := E) l (h i j)) y -
         partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) y -
         partialDeriv (E := E) k (partialDeriv (E := E) i (h l j)) y)

@[simp] lemma chartRicciSecondOrderPrincipalSymbol_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciSecondOrderPrincipalSymbol (I := I) g α h i k y =
      (1 / 2 : ℝ) * ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) j (partialDeriv (E := E) i (h l k)) y +
             partialDeriv (E := E) k (partialDeriv (E := E) l (h i j)) y -
             partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) y -
             partialDeriv (E := E) k (partialDeriv (E := E) i (h l j)) y) :=
  rfl

/-- The **first-order remainder** of the linearized chart Ricci tensor second-order
part: the `(∂G⁻¹)·(∂h)` terms left over once the pure `∂²h` symbol is extracted.

Writing the principal linearized Christoffel part as
`[DΓ_principal]^j{}_{ab}(y) = ½∑_l G^{jl}(y)·(∂_a h_{lb} + ∂_b h_{la} − ∂_l h_{ab})(y)`
and applying the outer chart derivative `∂` by the Leibniz rule, the branch where `∂`
lands on the inverse-Gram factor `G^{jl}` produces
$$[D\operatorname{Rc}]^{\rho}_{ik}[h](y) = \tfrac12 \sum_{j,l}
    \bigl(\partial_j G^{jl}\bigr)(y)\,
      \bigl(\partial_i h_{lk} + \partial_k h_{li} - \partial_l h_{ik}\bigr)(y)
  - \tfrac12 \sum_{j,l} \bigl(\partial_k G^{jl}\bigr)(y)\,
      \bigl(\partial_i h_{lj} + \partial_j h_{li} - \partial_l h_{ij}\bigr)(y).$$

Each term carries **exactly one** chart derivative of a component field of `h`, with the
chart-derivative-of-inverse-Gram factor `∂G^{jl}` not involving `h` at all.  This is the
content of `chartRicciFirstOrderRemainder_eq_first_order_sum`, which justifies the
remainder being invisible to the second-order principal symbol. -/
def chartRicciFirstOrderRemainder (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ j : Fin (Module.finrank ℝ E),
    ∑ l : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) j (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i (h l k) y +
         partialDeriv (E := E) k (h l i) y -
         partialDeriv (E := E) l (h i k) y) -
  (1 / 2 : ℝ) * ∑ j : Fin (Module.finrank ℝ E),
    ∑ l : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i (h l j) y +
         partialDeriv (E := E) j (h l i) y -
         partialDeriv (E := E) l (h i j) y)

@[simp] lemma chartRicciFirstOrderRemainder_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciFirstOrderRemainder (I := I) g α h i k y =
      (1 / 2 : ℝ) * ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) j (chartInvGramOnE (I := I) g α j l) y *
            (partialDeriv (E := E) i (h l k) y +
             partialDeriv (E := E) k (h l i) y -
             partialDeriv (E := E) l (h i k) y) -
      (1 / 2 : ℝ) * ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
            (partialDeriv (E := E) i (h l j) y +
             partialDeriv (E := E) j (h l i) y -
             partialDeriv (E := E) l (h i j) y) :=
  rfl

/-- **Leibniz expansion of the outer chart derivative of the principal linearized
Christoffel part.**  Differentiating
`[DΓ_principal]^j{}_{ab}(y') = ½∑_l G^{jl}(y')·(∂_a h_{lb} + ∂_b h_{la} − ∂_l h_{ab})(y')`
in the direction `e_d` by the product rule splits each summand into the
`(∂_d G^{jl})·(∂h)` branch and the `G^{jl}·(∂_d∂h)` branch.  Valid at chart-interior
points, where `G^{jl}` is differentiable. -/
lemma partialDeriv_chartLinearizedChristoffelPrincipal
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (a b j d : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) d
        (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h a b j y') y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) d (chartInvGramOnE (I := I) g α j l) y *
            (partialDeriv (E := E) a (h l b) y +
             partialDeriv (E := E) b (h l a) y -
             partialDeriv (E := E) l (h a b) y) +
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) d (partialDeriv (E := E) a (h l b)) y +
             partialDeriv (E := E) d (partialDeriv (E := E) b (h l a)) y -
             partialDeriv (E := E) d (partialDeriv (E := E) l (h a b)) y)) := by
  classical
  set S : Fin (Module.finrank ℝ E) → E → ℝ := fun l y' =>
    partialDeriv (E := E) a (h l b) y' +
      partialDeriv (E := E) b (h l a) y' -
      partialDeriv (E := E) l (h a b) y' with hS
  have hS_diff : ∀ l : Fin (Module.finrank ℝ E), DifferentiableAt ℝ (S l) y := by
    intro l
    have h1 : DifferentiableAt ℝ (partialDeriv (E := E) a (h l b)) y :=
      partialDeriv_perturbation_differentiableAt h a l b y
    have h2 : DifferentiableAt ℝ (partialDeriv (E := E) b (h l a)) y :=
      partialDeriv_perturbation_differentiableAt h b l a y
    have h3 : DifferentiableAt ℝ (partialDeriv (E := E) l (h a b)) y :=
      partialDeriv_perturbation_differentiableAt h l a b y
    exact (h1.add h2).sub h3
  have hG_diff : ∀ l : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartInvGramOnE (I := I) g α j l) y :=
    fun l => chartInvGramOnE_differentiableAt_interior (I := I) g α j l hy
  have hsummand_diff : ∀ l : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun y' => chartInvGramOnE (I := I) g α j l y' * S l y') y :=
    fun l => (hG_diff l).mul (hS_diff l)
  have hrewrite : (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h a b j y') =
      fun y' => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α j l y' * S l y' := by
    funext y'
    rw [chartLinearizedChristoffelPrincipal_def]
  rw [hrewrite]
  rw [partialDeriv_const_mul (1 / 2 : ℝ)
        (fun y' => ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y' * S l y')
        (DifferentiableAt.fun_sum (fun l _ => hsummand_diff l))]
  congr 1
  rw [partialDeriv_sum Finset.univ
        (fun l y' => chartInvGramOnE (I := I) g α j l y' * S l y')
        (fun l _ => hsummand_diff l)]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [partialDeriv_mul (chartInvGramOnE (I := I) g α j l) (S l)
        (hG_diff l) (hS_diff l)]
  have hSderiv : partialDeriv (E := E) d (S l) y =
      partialDeriv (E := E) d (partialDeriv (E := E) a (h l b)) y +
        partialDeriv (E := E) d (partialDeriv (E := E) b (h l a)) y -
        partialDeriv (E := E) d (partialDeriv (E := E) l (h a b)) y := by
    have h1 : DifferentiableAt ℝ (partialDeriv (E := E) a (h l b)) y :=
      partialDeriv_perturbation_differentiableAt h a l b y
    have h2 : DifferentiableAt ℝ (partialDeriv (E := E) b (h l a)) y :=
      partialDeriv_perturbation_differentiableAt h b l a y
    have h3 : DifferentiableAt ℝ (partialDeriv (E := E) l (h a b)) y :=
      partialDeriv_perturbation_differentiableAt h l a b y
    rw [hS]
    rw [partialDeriv_sub (E := E)
          (fun y' => partialDeriv (E := E) a (h l b) y' +
            partialDeriv (E := E) b (h l a) y')
          (partialDeriv (E := E) l (h a b)) (h1.add h2) h3]
    rw [partialDeriv_add (E := E)
          (partialDeriv (E := E) a (h l b)) (partialDeriv (E := E) b (h l a)) h1 h2]
  rw [hSderiv, hS]

/-- **The expanded `∂²h` formula for the second-order part of the linearized chart Ricci
tensor.**  At chart-interior points, the literal chart-derivative combination
`chartRicciSecondOrderPart` splits as the explicit four-term `∂²h` symbol
`chartRicciSecondOrderPrincipalSymbol` plus the genuinely-first-order remainder
`chartRicciFirstOrderRemainder`.

The four-term symbol arises from the six raw `∂²h` terms after Schwarz cancellation of
the two `∂\partial h_{li}` terms; the remainder collects the inverse-Gram branches of
the Leibniz expansion.  Under `[I.Boundaryless]` the chart-interior hypothesis is
automatic for `y = extChartAt I α x` with `x` in the chart source — see
`chartRicciSecondOrderPart_eq_principalSymbol_add_remainder_of_mem_source`. -/
theorem chartRicciSecondOrderPart_eq_principalSymbol_add_remainder
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    chartRicciSecondOrderPart (I := I) g α h i k y =
      chartRicciSecondOrderPrincipalSymbol (I := I) g α h i k y +
        chartRicciFirstOrderRemainder (I := I) g α h i k y := by
  classical
  rw [chartRicciSecondOrderPart_def]
  have hexpand : ∀ j : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) j
          (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h i k j y') y -
        partialDeriv (E := E) k
          (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h i j j y') y =
      ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j (chartInvGramOnE (I := I) g α j l) y *
            (partialDeriv (E := E) i (h l k) y +
             partialDeriv (E := E) k (h l i) y -
             partialDeriv (E := E) l (h i k) y) +
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) j (partialDeriv (E := E) i (h l k)) y +
             partialDeriv (E := E) j (partialDeriv (E := E) k (h l i)) y -
             partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) y))) -
      ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
            (partialDeriv (E := E) i (h l j) y +
             partialDeriv (E := E) j (h l i) y -
             partialDeriv (E := E) l (h i j) y) +
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) k (partialDeriv (E := E) i (h l j)) y +
             partialDeriv (E := E) k (partialDeriv (E := E) j (h l i)) y -
             partialDeriv (E := E) k (partialDeriv (E := E) l (h i j)) y))) := by
    intro j
    rw [partialDeriv_chartLinearizedChristoffelPrincipal (I := I) g α h i k j j hy,
      partialDeriv_chartLinearizedChristoffelPrincipal (I := I) g α h i j j k hy]
  rw [Finset.sum_congr rfl (fun j _ => hexpand j)]
  have hsplit : ∀ j : Fin (Module.finrank ℝ E),
      ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j (chartInvGramOnE (I := I) g α j l) y *
            (partialDeriv (E := E) i (h l k) y +
             partialDeriv (E := E) k (h l i) y -
             partialDeriv (E := E) l (h i k) y) +
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) j (partialDeriv (E := E) i (h l k)) y +
             partialDeriv (E := E) j (partialDeriv (E := E) k (h l i)) y -
             partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) y))) -
      ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
            (partialDeriv (E := E) i (h l j) y +
             partialDeriv (E := E) j (h l i) y -
             partialDeriv (E := E) l (h i j) y) +
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) k (partialDeriv (E := E) i (h l j)) y +
             partialDeriv (E := E) k (partialDeriv (E := E) j (h l i)) y -
             partialDeriv (E := E) k (partialDeriv (E := E) l (h i j)) y))) =
      ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) j (partialDeriv (E := E) i (h l k)) y +
             partialDeriv (E := E) j (partialDeriv (E := E) k (h l i)) y -
             partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) y) -
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) k (partialDeriv (E := E) i (h l j)) y +
             partialDeriv (E := E) k (partialDeriv (E := E) j (h l i)) y -
             partialDeriv (E := E) k (partialDeriv (E := E) l (h i j)) y)) +
      ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) j (chartInvGramOnE (I := I) g α j l) y *
            (partialDeriv (E := E) i (h l k) y +
             partialDeriv (E := E) k (h l i) y -
             partialDeriv (E := E) l (h i k) y) -
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
            (partialDeriv (E := E) i (h l j) y +
             partialDeriv (E := E) j (h l i) y -
             partialDeriv (E := E) l (h i j) y)) := by
    intro j
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, mul_add, mul_add]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hsplit j)]
  rw [Finset.sum_add_distrib]
  have hrem : (∑ j : Fin (Module.finrank ℝ E),
      ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) j (chartInvGramOnE (I := I) g α j l) y *
            (partialDeriv (E := E) i (h l k) y +
             partialDeriv (E := E) k (h l i) y -
             partialDeriv (E := E) l (h i k) y) -
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
            (partialDeriv (E := E) i (h l j) y +
             partialDeriv (E := E) j (h l i) y -
             partialDeriv (E := E) l (h i j) y))) =
      chartRicciFirstOrderRemainder (I := I) g α h i k y := by
    rw [chartRicciFirstOrderRemainder_def]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hsymbol : (∑ j : Fin (Module.finrank ℝ E),
      ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) j (partialDeriv (E := E) i (h l k)) y +
             partialDeriv (E := E) j (partialDeriv (E := E) k (h l i)) y -
             partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) y) -
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) k (partialDeriv (E := E) i (h l j)) y +
             partialDeriv (E := E) k (partialDeriv (E := E) j (h l i)) y -
             partialDeriv (E := E) k (partialDeriv (E := E) l (h i j)) y))) =
      chartRicciSecondOrderPrincipalSymbol (I := I) g α h i k y := by
    rw [chartRicciSecondOrderPrincipalSymbol_def]
    have hcombine : ∀ j : Fin (Module.finrank ℝ E),
        ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j l y *
              (partialDeriv (E := E) j (partialDeriv (E := E) i (h l k)) y +
               partialDeriv (E := E) j (partialDeriv (E := E) k (h l i)) y -
               partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) y) -
          (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j l y *
              (partialDeriv (E := E) k (partialDeriv (E := E) i (h l j)) y +
               partialDeriv (E := E) k (partialDeriv (E := E) j (h l i)) y -
               partialDeriv (E := E) k (partialDeriv (E := E) l (h i j)) y)) =
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) j (partialDeriv (E := E) i (h l k)) y +
             partialDeriv (E := E) k (partialDeriv (E := E) l (h i j)) y -
             partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) y -
             partialDeriv (E := E) k (partialDeriv (E := E) i (h l j)) y) := by
      intro j
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [partialDeriv_partialDeriv_perturbation_swap h l i j k y]
      ring
    rw [Finset.sum_congr rfl (fun j _ => hcombine j), ← Finset.mul_sum]
  rw [hrem, hsymbol, add_comm]

/-- **The expanded `∂²h` formula on the chart source under `[I.Boundaryless]`.**  At
chart-image points `y = extChartAt I α x` with `x` in the chart source, the
chart-interior hypothesis of
`chartRicciSecondOrderPart_eq_principalSymbol_add_remainder` is automatic. -/
theorem chartRicciSecondOrderPart_eq_principalSymbol_add_remainder_of_mem_source
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E))
    {x : M} (hx : x ∈ (chartAt H α).source) :
    chartRicciSecondOrderPart (I := I) g α h i k (extChartAt I α x) =
      chartRicciSecondOrderPrincipalSymbol (I := I) g α h i k (extChartAt I α x) +
        chartRicciFirstOrderRemainder (I := I) g α h i k (extChartAt I α x) := by
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  have hx_target : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc
  have hx_int : extChartAt I α x ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α hx_target
  exact chartRicciSecondOrderPart_eq_principalSymbol_add_remainder (I := I) g α h i k hx_int

/-- **The first-order remainder, exhibited as a sum of first-order terms.**  The
remainder `chartRicciFirstOrderRemainder` is a finite double sum (over `j, l`) of terms,
each a product of a coefficient not involving `h` — namely `±(1/2)·∂G^{jl}` — with a
single `partialDeriv` of a component field of `h`.

Concretely, each `(j, l)` summand expands into six terms, each of the syntactic shape
`coeff · partialDeriv _ (h _ _) _`.  No term carries a second derivative of `h`; this is
the formal content of "the remainder carries at most one chart derivative of `h`". -/
theorem chartRicciFirstOrderRemainder_eq_first_order_sum
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciFirstOrderRemainder (I := I) g α h i k y =
      ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          (((1 / 2 : ℝ) * partialDeriv (E := E) j
                (chartInvGramOnE (I := I) g α j l) y) *
              partialDeriv (E := E) i (h l k) y +
            ((1 / 2 : ℝ) * partialDeriv (E := E) j
                (chartInvGramOnE (I := I) g α j l) y) *
              partialDeriv (E := E) k (h l i) y +
            (-(1 / 2 : ℝ) * partialDeriv (E := E) j
                (chartInvGramOnE (I := I) g α j l) y) *
              partialDeriv (E := E) l (h i k) y +
            (-(1 / 2 : ℝ) * partialDeriv (E := E) k
                (chartInvGramOnE (I := I) g α j l) y) *
              partialDeriv (E := E) i (h l j) y +
            (-(1 / 2 : ℝ) * partialDeriv (E := E) k
                (chartInvGramOnE (I := I) g α j l) y) *
              partialDeriv (E := E) j (h l i) y +
            ((1 / 2 : ℝ) * partialDeriv (E := E) k
                (chartInvGramOnE (I := I) g α j l) y) *
              partialDeriv (E := E) l (h i j) y) := by
  classical
  rw [chartRicciFirstOrderRemainder_def]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

/-- The second-order part of the linearized Ricci tensor vanishes on the zero
perturbation. -/
@[simp] lemma chartRicciSecondOrderPart_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciSecondOrderPart (I := I) g α
      (0 : ChartMetricPerturbation E) i k y = 0 := by
  classical
  rw [chartRicciSecondOrderPart_def]
  have hzero : ∀ j : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) j
          (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α
            (0 : ChartMetricPerturbation E) i k j y') y -
        partialDeriv (E := E) k
          (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α
            (0 : ChartMetricPerturbation E) i j j y') y = 0 := by
    intro j
    have hik : (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α
        (0 : ChartMetricPerturbation E) i k j y') = fun _ : E => (0 : ℝ) := by
      funext y'; rw [chartLinearizedChristoffelPrincipal_zero]
    have hij : (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α
        (0 : ChartMetricPerturbation E) i j j y') = fun _ : E => (0 : ℝ) := by
      funext y'; rw [chartLinearizedChristoffelPrincipal_zero]
    rw [hik, hij, partialDeriv_const, partialDeriv_const, sub_zero]
  rw [Finset.sum_congr rfl (fun j _ => hzero j), Finset.sum_const_zero]

/-- **Additivity** of the second-order part of the linearized Ricci tensor in the
perturbation direction. -/
theorem chartRicciSecondOrderPart_add
    (g : SmoothRiemannianMetric I M) (α : M)
    (h₁ h₂ : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    chartRicciSecondOrderPart (I := I) g α (h₁ + h₂) i k y =
      chartRicciSecondOrderPart (I := I) g α h₁ i k y +
        chartRicciSecondOrderPart (I := I) g α h₂ i k y := by
  classical
  rw [chartRicciSecondOrderPart_def, chartRicciSecondOrderPart_def,
    chartRicciSecondOrderPart_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hadd_ik : partialDeriv (E := E) j
        (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α (h₁ + h₂) i k j y')
        y =
      partialDeriv (E := E) j
        (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h₁ i k j y') y +
      partialDeriv (E := E) j
        (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h₂ i k j y') y := by
    have heq : (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α
          (h₁ + h₂) i k j y') =
        fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h₁ i k j y' +
          chartLinearizedChristoffelPrincipal (I := I) g α h₂ i k j y' := by
      funext y'; rw [chartLinearizedChristoffelPrincipal_add]
    rw [heq, partialDeriv_add (E := E)
          (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h₁ i k j y')
          (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h₂ i k j y')
          (chartLinearizedChristoffelPrincipal_differentiableAt (I := I) g α h₁ i k j hy)
          (chartLinearizedChristoffelPrincipal_differentiableAt (I := I) g α h₂ i k j hy)]
  have hadd_ij : partialDeriv (E := E) k
        (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α (h₁ + h₂) i j j y')
        y =
      partialDeriv (E := E) k
        (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h₁ i j j y') y +
      partialDeriv (E := E) k
        (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h₂ i j j y') y := by
    have heq : (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α
          (h₁ + h₂) i j j y') =
        fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h₁ i j j y' +
          chartLinearizedChristoffelPrincipal (I := I) g α h₂ i j j y' := by
      funext y'; rw [chartLinearizedChristoffelPrincipal_add]
    rw [heq, partialDeriv_add (E := E)
          (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h₁ i j j y')
          (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h₂ i j j y')
          (chartLinearizedChristoffelPrincipal_differentiableAt (I := I) g α h₁ i j j hy)
          (chartLinearizedChristoffelPrincipal_differentiableAt (I := I) g α h₂ i j j hy)]
  rw [hadd_ik, hadd_ij]
  ring

/-- **Scalar homogeneity** of the second-order part of the linearized Ricci tensor in
the perturbation direction. -/
theorem chartRicciSecondOrderPart_smul
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    chartRicciSecondOrderPart (I := I) g α (c • h) i k y =
      c • chartRicciSecondOrderPart (I := I) g α h i k y := by
  classical
  rw [chartRicciSecondOrderPart_def, chartRicciSecondOrderPart_def, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hsmul_ik : partialDeriv (E := E) j
        (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α (c • h) i k j y')
        y =
      c * partialDeriv (E := E) j
        (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h i k j y') y := by
    have heq : (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α
          (c • h) i k j y') =
        fun y' => c • chartLinearizedChristoffelPrincipal (I := I) g α h i k j y' := by
      funext y'; rw [chartLinearizedChristoffelPrincipal_smul]
    rw [heq, partialDeriv_const_smul (E := E) c
          (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h i k j y')
          (chartLinearizedChristoffelPrincipal_differentiableAt (I := I) g α h i k j hy),
      smul_eq_mul]
  have hsmul_ij : partialDeriv (E := E) k
        (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α (c • h) i j j y')
        y =
      c * partialDeriv (E := E) k
        (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h i j j y') y := by
    have heq : (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α
          (c • h) i j j y') =
        fun y' => c • chartLinearizedChristoffelPrincipal (I := I) g α h i j j y' := by
      funext y'; rw [chartLinearizedChristoffelPrincipal_smul]
    rw [heq, partialDeriv_const_smul (E := E) c
          (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h i j j y')
          (chartLinearizedChristoffelPrincipal_differentiableAt (I := I) g α h i j j hy),
      smul_eq_mul]
  rw [hsmul_ik, hsmul_ij]
  ring

/-- The explicit second-order symbol vanishes on the zero perturbation. -/
@[simp] lemma chartRicciSecondOrderPrincipalSymbol_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciSecondOrderPrincipalSymbol (I := I) g α
      (0 : ChartMetricPerturbation E) i k y = 0 := by
  classical
  rw [chartRicciSecondOrderPrincipalSymbol_def]
  have hiter : ∀ p q a b : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) p
          (partialDeriv (E := E) q ((0 : ChartMetricPerturbation E) a b)) y = 0 := by
    intro p q a b
    have hinner : partialDeriv (E := E) q ((0 : ChartMetricPerturbation E) a b) =
        fun _ : E => (0 : ℝ) := by
      funext y'
      have hconst : ((0 : ChartMetricPerturbation E) a b) = fun _ : E => (0 : ℝ) := rfl
      rw [hconst, partialDeriv_const]
    rw [hinner, partialDeriv_const]
  have hzero : ∀ j l : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α j l y *
        (partialDeriv (E := E) j (partialDeriv (E := E) i
            ((0 : ChartMetricPerturbation E) l k)) y +
         partialDeriv (E := E) k (partialDeriv (E := E) l
            ((0 : ChartMetricPerturbation E) i j)) y -
         partialDeriv (E := E) j (partialDeriv (E := E) l
            ((0 : ChartMetricPerturbation E) i k)) y -
         partialDeriv (E := E) k (partialDeriv (E := E) i
            ((0 : ChartMetricPerturbation E) l j)) y) = 0 := by
    intro j l
    rw [hiter j i l k, hiter k l i j, hiter j l i k, hiter k i l j]
    ring
  rw [Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun l _ => hzero j l))]
  rw [Finset.sum_const_zero, Finset.sum_const_zero, mul_zero]

/-- A perturbation component field of a pointwise sum splits the iterated partial
derivative additively. -/
private lemma partialDeriv_partialDeriv_add_apply
    (h₁ h₂ : ChartMetricPerturbation E) (p q a b : Fin (Module.finrank ℝ E)) (y : E) :
    partialDeriv (E := E) p (partialDeriv (E := E) q ((h₁ + h₂) a b)) y =
      partialDeriv (E := E) p (partialDeriv (E := E) q (h₁ a b)) y +
        partialDeriv (E := E) p (partialDeriv (E := E) q (h₂ a b)) y := by
  have hinner : partialDeriv (E := E) q ((h₁ + h₂) a b) =
      fun y' => partialDeriv (E := E) q (h₁ a b) y' +
        partialDeriv (E := E) q (h₂ a b) y' := by
    funext y'
    have heq : ((h₁ + h₂) a b) = fun y'' => h₁ a b y'' + h₂ a b y'' := rfl
    rw [heq, partialDeriv_add (E := E) (h₁ a b) (h₂ a b)
          (h₁.differentiableAt a b y') (h₂.differentiableAt a b y')]
  rw [hinner, partialDeriv_add (E := E)
        (partialDeriv (E := E) q (h₁ a b)) (partialDeriv (E := E) q (h₂ a b))
        (partialDeriv_perturbation_differentiableAt h₁ q a b y)
        (partialDeriv_perturbation_differentiableAt h₂ q a b y)]

/-- A perturbation component field of a scalar multiple scales the iterated partial
derivative. -/
private lemma partialDeriv_partialDeriv_smul_apply
    (c : ℝ) (h : ChartMetricPerturbation E) (p q a b : Fin (Module.finrank ℝ E)) (y : E) :
    partialDeriv (E := E) p (partialDeriv (E := E) q ((c • h) a b)) y =
      c * partialDeriv (E := E) p (partialDeriv (E := E) q (h a b)) y := by
  have hinner : partialDeriv (E := E) q ((c • h) a b) =
      fun y' => c • partialDeriv (E := E) q (h a b) y' := by
    funext y'
    have heq : ((c • h) a b) = fun y'' => c • h a b y'' := rfl
    rw [heq, partialDeriv_const_smul (E := E) c (h a b) (h.differentiableAt a b y')]
  rw [hinner, partialDeriv_const_smul (E := E) c
        (partialDeriv (E := E) q (h a b))
        (partialDeriv_perturbation_differentiableAt h q a b y), smul_eq_mul]

/-- **Additivity** of the explicit second-order symbol in the perturbation direction. -/
theorem chartRicciSecondOrderPrincipalSymbol_add
    (g : SmoothRiemannianMetric I M) (α : M)
    (h₁ h₂ : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciSecondOrderPrincipalSymbol (I := I) g α (h₁ + h₂) i k y =
      chartRicciSecondOrderPrincipalSymbol (I := I) g α h₁ i k y +
        chartRicciSecondOrderPrincipalSymbol (I := I) g α h₂ i k y := by
  classical
  rw [chartRicciSecondOrderPrincipalSymbol_def, chartRicciSecondOrderPrincipalSymbol_def,
    chartRicciSecondOrderPrincipalSymbol_def, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [partialDeriv_partialDeriv_add_apply h₁ h₂ j i l k y,
    partialDeriv_partialDeriv_add_apply h₁ h₂ k l i j y,
    partialDeriv_partialDeriv_add_apply h₁ h₂ j l i k y,
    partialDeriv_partialDeriv_add_apply h₁ h₂ k i l j y]
  ring

/-- **Scalar homogeneity** of the explicit second-order symbol in the perturbation
direction. -/
theorem chartRicciSecondOrderPrincipalSymbol_smul
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciSecondOrderPrincipalSymbol (I := I) g α (c • h) i k y =
      c • chartRicciSecondOrderPrincipalSymbol (I := I) g α h i k y := by
  classical
  rw [chartRicciSecondOrderPrincipalSymbol_def, chartRicciSecondOrderPrincipalSymbol_def,
    smul_eq_mul]
  have hsummand : ∀ j l : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α j l y *
        (partialDeriv (E := E) j (partialDeriv (E := E) i ((c • h) l k)) y +
         partialDeriv (E := E) k (partialDeriv (E := E) l ((c • h) i j)) y -
         partialDeriv (E := E) j (partialDeriv (E := E) l ((c • h) i k)) y -
         partialDeriv (E := E) k (partialDeriv (E := E) i ((c • h) l j)) y) =
      c * (chartInvGramOnE (I := I) g α j l y *
        (partialDeriv (E := E) j (partialDeriv (E := E) i (h l k)) y +
         partialDeriv (E := E) k (partialDeriv (E := E) l (h i j)) y -
         partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) y -
         partialDeriv (E := E) k (partialDeriv (E := E) i (h l j)) y)) := by
    intro j l
    rw [partialDeriv_partialDeriv_smul_apply c h j i l k y,
      partialDeriv_partialDeriv_smul_apply c h k l i j y,
      partialDeriv_partialDeriv_smul_apply c h j l i k y,
      partialDeriv_partialDeriv_smul_apply c h k i l j y]
    ring
  rw [Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun l _ => hsummand j l))]
  have hinner : ∀ j : Fin (Module.finrank ℝ E),
      (∑ l : Fin (Module.finrank ℝ E),
        c * (chartInvGramOnE (I := I) g α j l y *
          (partialDeriv (E := E) j (partialDeriv (E := E) i (h l k)) y +
           partialDeriv (E := E) k (partialDeriv (E := E) l (h i j)) y -
           partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) y -
           partialDeriv (E := E) k (partialDeriv (E := E) i (h l j)) y))) =
      c * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α j l y *
          (partialDeriv (E := E) j (partialDeriv (E := E) i (h l k)) y +
           partialDeriv (E := E) k (partialDeriv (E := E) l (h i j)) y -
           partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) y -
           partialDeriv (E := E) k (partialDeriv (E := E) i (h l j)) y) :=
    fun j => by rw [← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun j _ => hinner j), ← Finset.mul_sum]
  ring

/-- The first-order remainder vanishes on the zero perturbation. -/
@[simp] lemma chartRicciFirstOrderRemainder_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciFirstOrderRemainder (I := I) g α
      (0 : ChartMetricPerturbation E) i k y = 0 := by
  classical
  rw [chartRicciFirstOrderRemainder_def]
  have hzero1 : ∀ j l : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) j (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i ((0 : ChartMetricPerturbation E) l k) y +
         partialDeriv (E := E) k ((0 : ChartMetricPerturbation E) l i) y -
         partialDeriv (E := E) l ((0 : ChartMetricPerturbation E) i k) y) = 0 := by
    intro j l
    have e1 : ((0 : ChartMetricPerturbation E) l k) = fun _ : E => (0 : ℝ) := rfl
    have e2 : ((0 : ChartMetricPerturbation E) l i) = fun _ : E => (0 : ℝ) := rfl
    have e3 : ((0 : ChartMetricPerturbation E) i k) = fun _ : E => (0 : ℝ) := rfl
    rw [e1, e2, e3]
    simp only [partialDeriv_const]
    ring
  have hzero2 : ∀ j l : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i ((0 : ChartMetricPerturbation E) l j) y +
         partialDeriv (E := E) j ((0 : ChartMetricPerturbation E) l i) y -
         partialDeriv (E := E) l ((0 : ChartMetricPerturbation E) i j) y) = 0 := by
    intro j l
    have e1 : ((0 : ChartMetricPerturbation E) l j) = fun _ : E => (0 : ℝ) := rfl
    have e2 : ((0 : ChartMetricPerturbation E) l i) = fun _ : E => (0 : ℝ) := rfl
    have e3 : ((0 : ChartMetricPerturbation E) i j) = fun _ : E => (0 : ℝ) := rfl
    rw [e1, e2, e3]
    simp only [partialDeriv_const]
    ring
  rw [Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun l _ => hzero1 j l))]
  rw [Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun l _ => hzero2 j l))]
  simp

/-- **Additivity** of the first-order remainder in the perturbation direction. -/
theorem chartRicciFirstOrderRemainder_add
    (g : SmoothRiemannianMetric I M) (α : M)
    (h₁ h₂ : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciFirstOrderRemainder (I := I) g α (h₁ + h₂) i k y =
      chartRicciFirstOrderRemainder (I := I) g α h₁ i k y +
        chartRicciFirstOrderRemainder (I := I) g α h₂ i k y := by
  classical
  rw [chartRicciFirstOrderRemainder_def, chartRicciFirstOrderRemainder_def,
    chartRicciFirstOrderRemainder_def]
  have hsummand1 : ∀ j l : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) j (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i ((h₁ + h₂) l k) y +
         partialDeriv (E := E) k ((h₁ + h₂) l i) y -
         partialDeriv (E := E) l ((h₁ + h₂) i k) y) =
      partialDeriv (E := E) j (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i (h₁ l k) y +
         partialDeriv (E := E) k (h₁ l i) y -
         partialDeriv (E := E) l (h₁ i k) y) +
      partialDeriv (E := E) j (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i (h₂ l k) y +
         partialDeriv (E := E) k (h₂ l i) y -
         partialDeriv (E := E) l (h₂ i k) y) := by
    intro j l
    have ea : partialDeriv (E := E) i ((h₁ + h₂) l k) y =
        partialDeriv (E := E) i (h₁ l k) y + partialDeriv (E := E) i (h₂ l k) y := by
      have heq : ((h₁ + h₂) l k) = fun y'' => h₁ l k y'' + h₂ l k y'' := rfl
      rw [heq, partialDeriv_add (E := E) (h₁ l k) (h₂ l k)
            (h₁.differentiableAt l k y) (h₂.differentiableAt l k y)]
    have eb : partialDeriv (E := E) k ((h₁ + h₂) l i) y =
        partialDeriv (E := E) k (h₁ l i) y + partialDeriv (E := E) k (h₂ l i) y := by
      have heq : ((h₁ + h₂) l i) = fun y'' => h₁ l i y'' + h₂ l i y'' := rfl
      rw [heq, partialDeriv_add (E := E) (h₁ l i) (h₂ l i)
            (h₁.differentiableAt l i y) (h₂.differentiableAt l i y)]
    have ec : partialDeriv (E := E) l ((h₁ + h₂) i k) y =
        partialDeriv (E := E) l (h₁ i k) y + partialDeriv (E := E) l (h₂ i k) y := by
      have heq : ((h₁ + h₂) i k) = fun y'' => h₁ i k y'' + h₂ i k y'' := rfl
      rw [heq, partialDeriv_add (E := E) (h₁ i k) (h₂ i k)
            (h₁.differentiableAt i k y) (h₂.differentiableAt i k y)]
    rw [ea, eb, ec]
    ring
  have hsummand2 : ∀ j l : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i ((h₁ + h₂) l j) y +
         partialDeriv (E := E) j ((h₁ + h₂) l i) y -
         partialDeriv (E := E) l ((h₁ + h₂) i j) y) =
      partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i (h₁ l j) y +
         partialDeriv (E := E) j (h₁ l i) y -
         partialDeriv (E := E) l (h₁ i j) y) +
      partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i (h₂ l j) y +
         partialDeriv (E := E) j (h₂ l i) y -
         partialDeriv (E := E) l (h₂ i j) y) := by
    intro j l
    have ea : partialDeriv (E := E) i ((h₁ + h₂) l j) y =
        partialDeriv (E := E) i (h₁ l j) y + partialDeriv (E := E) i (h₂ l j) y := by
      have heq : ((h₁ + h₂) l j) = fun y'' => h₁ l j y'' + h₂ l j y'' := rfl
      rw [heq, partialDeriv_add (E := E) (h₁ l j) (h₂ l j)
            (h₁.differentiableAt l j y) (h₂.differentiableAt l j y)]
    have eb : partialDeriv (E := E) j ((h₁ + h₂) l i) y =
        partialDeriv (E := E) j (h₁ l i) y + partialDeriv (E := E) j (h₂ l i) y := by
      have heq : ((h₁ + h₂) l i) = fun y'' => h₁ l i y'' + h₂ l i y'' := rfl
      rw [heq, partialDeriv_add (E := E) (h₁ l i) (h₂ l i)
            (h₁.differentiableAt l i y) (h₂.differentiableAt l i y)]
    have ec : partialDeriv (E := E) l ((h₁ + h₂) i j) y =
        partialDeriv (E := E) l (h₁ i j) y + partialDeriv (E := E) l (h₂ i j) y := by
      have heq : ((h₁ + h₂) i j) = fun y'' => h₁ i j y'' + h₂ i j y'' := rfl
      rw [heq, partialDeriv_add (E := E) (h₁ i j) (h₂ i j)
            (h₁.differentiableAt i j y) (h₂.differentiableAt i j y)]
    rw [ea, eb, ec]
    ring
  rw [Finset.sum_congr rfl (fun j _ =>
        Finset.sum_congr rfl (fun l _ => hsummand1 j l)),
    Finset.sum_congr rfl (fun j _ =>
        Finset.sum_congr rfl (fun l _ => hsummand2 j l))]
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_add_distrib),
    Finset.sum_congr rfl (fun j _ => Finset.sum_add_distrib),
    Finset.sum_add_distrib, Finset.sum_add_distrib, mul_add, mul_add]
  ring

/-- **Scalar homogeneity** of the first-order remainder in the perturbation
direction. -/
theorem chartRicciFirstOrderRemainder_smul
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciFirstOrderRemainder (I := I) g α (c • h) i k y =
      c • chartRicciFirstOrderRemainder (I := I) g α h i k y := by
  classical
  rw [chartRicciFirstOrderRemainder_def, chartRicciFirstOrderRemainder_def, smul_eq_mul]
  have hsummand1 : ∀ j l : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) j (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i ((c • h) l k) y +
         partialDeriv (E := E) k ((c • h) l i) y -
         partialDeriv (E := E) l ((c • h) i k) y) =
      c * (partialDeriv (E := E) j (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i (h l k) y +
         partialDeriv (E := E) k (h l i) y -
         partialDeriv (E := E) l (h i k) y)) := by
    intro j l
    have ea : partialDeriv (E := E) i ((c • h) l k) y =
        c * partialDeriv (E := E) i (h l k) y := by
      have heq : ((c • h) l k) = fun y'' => c • h l k y'' := rfl
      rw [heq, partialDeriv_const_smul (E := E) c (h l k) (h.differentiableAt l k y),
        smul_eq_mul]
    have eb : partialDeriv (E := E) k ((c • h) l i) y =
        c * partialDeriv (E := E) k (h l i) y := by
      have heq : ((c • h) l i) = fun y'' => c • h l i y'' := rfl
      rw [heq, partialDeriv_const_smul (E := E) c (h l i) (h.differentiableAt l i y),
        smul_eq_mul]
    have ec : partialDeriv (E := E) l ((c • h) i k) y =
        c * partialDeriv (E := E) l (h i k) y := by
      have heq : ((c • h) i k) = fun y'' => c • h i k y'' := rfl
      rw [heq, partialDeriv_const_smul (E := E) c (h i k) (h.differentiableAt i k y),
        smul_eq_mul]
    rw [ea, eb, ec]
    ring
  have hsummand2 : ∀ j l : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i ((c • h) l j) y +
         partialDeriv (E := E) j ((c • h) l i) y -
         partialDeriv (E := E) l ((c • h) i j) y) =
      c * (partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i (h l j) y +
         partialDeriv (E := E) j (h l i) y -
         partialDeriv (E := E) l (h i j) y)) := by
    intro j l
    have ea : partialDeriv (E := E) i ((c • h) l j) y =
        c * partialDeriv (E := E) i (h l j) y := by
      have heq : ((c • h) l j) = fun y'' => c • h l j y'' := rfl
      rw [heq, partialDeriv_const_smul (E := E) c (h l j) (h.differentiableAt l j y),
        smul_eq_mul]
    have eb : partialDeriv (E := E) j ((c • h) l i) y =
        c * partialDeriv (E := E) j (h l i) y := by
      have heq : ((c • h) l i) = fun y'' => c • h l i y'' := rfl
      rw [heq, partialDeriv_const_smul (E := E) c (h l i) (h.differentiableAt l i y),
        smul_eq_mul]
    have ec : partialDeriv (E := E) l ((c • h) i j) y =
        c * partialDeriv (E := E) l (h i j) y := by
      have heq : ((c • h) i j) = fun y'' => c • h i j y'' := rfl
      rw [heq, partialDeriv_const_smul (E := E) c (h i j) (h.differentiableAt i j y),
        smul_eq_mul]
    rw [ea, eb, ec]
    ring
  rw [Finset.sum_congr rfl (fun j _ =>
        Finset.sum_congr rfl (fun l _ => hsummand1 j l)),
    Finset.sum_congr rfl (fun j _ =>
        Finset.sum_congr rfl (fun l _ => hsummand2 j l))]
  rw [Finset.sum_congr rfl (fun j _ => (Finset.mul_sum _ _ c).symm),
    Finset.sum_congr rfl (fun j _ => (Finset.mul_sum _ _ c).symm),
    ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- **Symmetry of the explicit second-order symbol** in the index pair `(i, k)`.  The
four-term `∂²h` formula is invariant under `i ↔ k`: each of the four terms of the
`(k, i)`-symbol matches a term of the `(i, k)`-symbol after the dummy-index swap
`j ↔ l` (with `G^{jl} = G^{lj}`), the perturbation symmetry `h_{ab} = h_{ba}`, and
Schwarz symmetry `∂_a∂_b h = ∂_b∂_a h` of the smooth mixed partials. -/
theorem chartRicciSecondOrderPrincipalSymbol_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciSecondOrderPrincipalSymbol (I := I) g α h i k y =
      chartRicciSecondOrderPrincipalSymbol (I := I) g α h k i y := by
  classical
  rw [chartRicciSecondOrderPrincipalSymbol_def, chartRicciSecondOrderPrincipalSymbol_def]
  congr 1
  have hsplit : ∀ p q : Fin (Module.finrank ℝ E),
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) j (partialDeriv (E := E) p (h l q)) y +
             partialDeriv (E := E) q (partialDeriv (E := E) l (h p j)) y -
             partialDeriv (E := E) j (partialDeriv (E := E) l (h p q)) y -
             partialDeriv (E := E) q (partialDeriv (E := E) p (h l j)) y)) =
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) j (partialDeriv (E := E) p (h l q)) y) +
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) q (partialDeriv (E := E) l (h p j)) y) -
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) j (partialDeriv (E := E) l (h p q)) y) -
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) q (partialDeriv (E := E) p (h l j)) y) := by
    intro p q
    have hinner : ∀ j : Fin (Module.finrank ℝ E),
        (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) j (partialDeriv (E := E) p (h l q)) y +
             partialDeriv (E := E) q (partialDeriv (E := E) l (h p j)) y -
             partialDeriv (E := E) j (partialDeriv (E := E) l (h p q)) y -
             partialDeriv (E := E) q (partialDeriv (E := E) p (h l j)) y)) =
        (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) j (partialDeriv (E := E) p (h l q)) y) +
        (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) q (partialDeriv (E := E) l (h p j)) y) -
        (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) j (partialDeriv (E := E) l (h p q)) y) -
        (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) q (partialDeriv (E := E) p (h l j)) y) := by
      intro j
      rw [show (∑ l : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α j l y *
                (partialDeriv (E := E) j (partialDeriv (E := E) p (h l q)) y +
                 partialDeriv (E := E) q (partialDeriv (E := E) l (h p j)) y -
                 partialDeriv (E := E) j (partialDeriv (E := E) l (h p q)) y -
                 partialDeriv (E := E) q (partialDeriv (E := E) p (h l j)) y)) =
            (∑ l : Fin (Module.finrank ℝ E),
              (chartInvGramOnE (I := I) g α j l y *
                  partialDeriv (E := E) j (partialDeriv (E := E) p (h l q)) y +
                chartInvGramOnE (I := I) g α j l y *
                  partialDeriv (E := E) q (partialDeriv (E := E) l (h p j)) y -
                chartInvGramOnE (I := I) g α j l y *
                  partialDeriv (E := E) j (partialDeriv (E := E) l (h p q)) y -
                chartInvGramOnE (I := I) g α j l y *
                  partialDeriv (E := E) q (partialDeriv (E := E) p (h l j)) y)) from
        Finset.sum_congr rfl (fun l _ => by ring)]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun j _ => hinner j)]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hsplit i k, hsplit k i]
  have hA : (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) j (partialDeriv (E := E) k (h l i)) y) =
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) k (partialDeriv (E := E) l (h i j)) y) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [chartInvGramOnE_symm (I := I) g α l j y, h.symm_fun j i,
      partialDeriv_partialDeriv_perturbation_swap h i j l k y]
  have hB : (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) i (partialDeriv (E := E) l (h k j)) y) =
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) j (partialDeriv (E := E) i (h l k)) y) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [chartInvGramOnE_symm (I := I) g α l j y, h.symm_fun k l,
      partialDeriv_partialDeriv_perturbation_swap h l k i j y]
  have hC : (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) j (partialDeriv (E := E) l (h k i)) y) =
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) y) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [h.symm_fun k i]
  have hD : (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) i (partialDeriv (E := E) k (h l j)) y) =
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) k (partialDeriv (E := E) i (h l j)) y) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [partialDeriv_partialDeriv_perturbation_swap h l j i k y]
  rw [hA, hB, hC, hD]
  ring

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry
