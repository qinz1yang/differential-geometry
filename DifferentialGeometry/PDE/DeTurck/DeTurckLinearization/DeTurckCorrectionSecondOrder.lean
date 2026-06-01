import DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.LinearizedVectorField

/-!
# The second-order part of the linearized DeTurck-correction operator

In the chart at a base point `α : M`, the DeTurck-correction term of an evolving
metric `g` against a fixed background metric `g'` is the metric Lie derivative
`𝓛_W g` of `g` along the DeTurck vector field `W = W(g, g')`, with chart-coordinate
components
$$(\mathcal L_W g)_{ij}
    = \sum_k W^k\,\partial_k g_{ij}
        + \sum_k g_{kj}\,\partial_i W^k
        + \sum_k g_{ik}\,\partial_j W^k.$$

Linearizing `g ↦ 𝓛_{W(g, g')} g` in a metric-perturbation direction `h` and
collecting the terms that carry **two** chart derivatives of `h` is the first step
toward the principal symbol of the linearized DeTurck-correction operator.  The
convective term `∑_k W^k\,\partial_k g_{ij}` and the metric factors `g_{kj}`,
`g_{ik}` of the two deformation terms each carry **at most one** chart derivative of
`h`, so the only `∂²h` terms come from the deformation terms `∑_k g_{kj}\,\partial_i
W^k + ∑_k g_{ik}\,\partial_j W^k` once the linearized vector field `DW^k` is
inserted: the only summand of `DW^k` carrying a chart derivative of `h` is the
principal part `chartLinearizedDeTurckVFPrincipal`, and applying the outer chart
derivative `∂_i` to that principal part produces the `∂²h` content.

Thus the second-order-in-`h` part of `D(\mathcal L_W g)_{ij}[h]` is
$$\sum_k g_{kj}\,\partial_i \bigl[(DW)^k_{\mathrm{principal}}[h]\bigr]
    + \sum_k g_{ik}\,\partial_j \bigl[(DW)^k_{\mathrm{principal}}[h]\bigr],$$
where `(DW)^k_{\mathrm{principal}}[h] = chartLinearizedDeTurckVFPrincipal g g' α h k`.

## Contents

* `chartDeTurckCorrSecondOrderPart` — the second-order-in-`h` part of
  `D(\mathcal L_W g)_{ij}[h]`, defined as the chart-derivative combination
  `∑_k g_{kj}\,\partial_i[(DW)^k_{\mathrm{principal}}] + ∑_k g_{ik}\,\partial_j
  [(DW)^k_{\mathrm{principal}}]` of the metric Gram entries against the principal
  part of the linearized DeTurck vector field, together with its unfolding lemma
  `chartDeTurckCorrSecondOrderPart_def`.
* `partialDeriv_chartLinearizedDeTurckVFPrincipal` — the Leibniz expansion of the
  outer chart derivative `∂_d[(DW)^k_{\mathrm{principal}}]`, the single technical
  lemma the principal-symbol / remainder split consumes.  It separates, summand by
  summand, the `(∂G)·(DΓ_{\mathrm{principal}})` branch (which carries `h`
  through a single chart derivative) from the `G·∂(DΓ_{\mathrm{principal}})` branch
  (which carries the second chart derivative of `h`).
* `chartLinearizedDeTurckVFPrincipal_differentiableAt` — differentiability of the
  principal part of the linearized DeTurck vector field at chart-interior points,
  the form the Leibniz expansion consumes.
* `h`-linearity (`_add`, `_smul`, `_zero`) of `chartDeTurckCorrSecondOrderPart`.

The principal-symbol / remainder split itself — extracting the pure `∂²h`
expression and the genuinely-first-order remainder from
`chartDeTurckCorrSecondOrderPart` — is carried out in
`DeTurckCorrectionSecondOrderSplit.lean`, which builds on the Leibniz expansion
recorded here.
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

section Differentiability

/-- The chart Gram entry `g_{ij}` is differentiable at every point in the interior of
the chart target. -/
lemma chartGramOnE_differentiableAt_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) y := by
  have hcd : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j)
      (extChartAt I α).target := chartGramOnE_contDiffOn (I := I) g α i j
  have hcd_int : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j)
      (interior (extChartAt I α).target) := hcd.mono interior_subset
  have hat : ContDiffAt ℝ ∞ (chartGramOnE (I := I) g α i j) y :=
    hcd_int.contDiffAt (isOpen_interior.mem_nhds hy)
  exact hat.differentiableAt (by simp)

/-- The chart inverse Gram entry `G^{ab}` is differentiable at every point in the
interior of the chart target. -/
lemma chartInvGramOnE_differentiableAt_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (a b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartInvGramOnE (I := I) g α a b) y := by
  have hcd : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α a b)
      (extChartAt I α).target := chartInvGramOnE_contDiffOn (I := I) g α a b
  have hcd_int : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α a b)
      (interior (extChartAt I α).target) := hcd.mono interior_subset
  have hat : ContDiffAt ℝ ∞ (chartInvGramOnE (I := I) g α a b) y :=
    hcd_int.contDiffAt (isOpen_interior.mem_nhds hy)
  exact hat.differentiableAt (by simp)

/-- The principal part of the linearized DeTurck vector field is differentiable at
every point in the interior of the chart target (as a function of the chart-coordinate
point). -/
lemma chartLinearizedDeTurckVFPrincipal_differentiableAt
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ
      (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y := by
  have hcd : ContDiffOn ℝ ∞
      (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y')
      (interior (extChartAt I α).target) :=
    chartLinearizedDeTurckVFPrincipal_contDiffOn_interior (I := I) g g' α h k
  have hat : ContDiffAt ℝ ∞
      (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y :=
    hcd.contDiffAt (isOpen_interior.mem_nhds hy)
  exact hat.differentiableAt (by simp)

/-- The principal linearized Christoffel part is differentiable at every point in the
interior of the chart target (as a function of the chart-coordinate point). -/
lemma chartLinearizedChristoffelPrincipal_differentiableAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (a b k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ
      (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h a b k y') y := by
  have hcd : ContDiffOn ℝ ∞
      (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h a b k y')
      (interior (extChartAt I α).target) :=
    (chartLinearizedChristoffelPrincipal_contDiffOn (I := I) g α h a b k).mono
      interior_subset
  have hat : ContDiffAt ℝ ∞
      (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h a b k y') y :=
    hcd.contDiffAt (isOpen_interior.mem_nhds hy)
  exact hat.differentiableAt (by simp)

end Differentiability

/-- The **second-order-in-`h` part of the linearized DeTurck-correction operator**
`D(\mathcal L_{W(g, g')} g)_{ij}[h]` in the chart at `α`, in the perturbation
direction `h`, evaluated at the chart-coordinate point `y ∈ E`:
$$[D(\mathcal L_W g)]^{(2)}_{ij}[h](y) =
    \sum_k g_{kj}(y)\,\partial_i\bigl[(DW)^k_{\mathrm{principal}}[h]\bigr](y)
      + \sum_k g_{ik}(y)\,\partial_j\bigl[(DW)^k_{\mathrm{principal}}[h]\bigr](y),$$
where `(DW)^k_{\mathrm{principal}}[h] = chartLinearizedDeTurckVFPrincipal g g' α h k`
is the principal part of the linearized DeTurck vector field, `g_{kj} = chartGramOnE
g α k j`, and `∂_i F` denotes the Fréchet partial derivative `partialDeriv i F`.

This is the term of the linearized DeTurck-correction operator carrying two chart
derivatives of `h`: the outer chart derivative `∂_i` falls on the `∂h`-order principal
part `(DW)^k_{\mathrm{principal}}[h]`.  The convective contribution and the
inverse-Gram contribution of the linearized vector field are lower order and do not
appear here. -/
def chartDeTurckCorrSecondOrderPart (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α k j y *
        partialDeriv (E := E) i
          (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y) +
  (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α i k y *
        partialDeriv (E := E) j
          (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y)

@[simp] lemma chartDeTurckCorrSecondOrderPart_def
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrSecondOrderPart (I := I) g g' α h i j y =
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α k j y *
            partialDeriv (E := E) i
              (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y) +
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α i k y *
            partialDeriv (E := E) j
              (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y) :=
  rfl

/-- **Leibniz expansion of the outer chart derivative of the principal part of the
linearized DeTurck vector field.**  Differentiating
`(DW)^k_{\mathrm{principal}}[h](y') = ∑_{a,b} G^{ab}(y')·(DΓ)^k{}_{ab}[h](y')` in the
direction `e_d` by the product rule splits each `(a, b)` summand into the
`(∂_d G^{ab})·(DΓ)^k{}_{ab}[h]` branch and the `G^{ab}·∂_d[(DΓ)^k{}_{ab}[h]]` branch.
Valid at chart-interior points, where the inverse-Gram entries `G^{ab}` and the
principal linearized Christoffel parts are differentiable. -/
lemma partialDeriv_chartLinearizedDeTurckVFPrincipal
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (k d : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) d
        (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
            chartLinearizedChristoffelPrincipal (I := I) g α h a b k y +
          chartInvGramOnE (I := I) g α a b y *
            partialDeriv (E := E) d
              (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h a b k y')
              y) := by
  classical
  set Γ : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ :=
    fun a b y' => chartLinearizedChristoffelPrincipal (I := I) g α h a b k y' with hΓ
  have hΓ_diff : ∀ a b : Fin (Module.finrank ℝ E), DifferentiableAt ℝ (Γ a b) y :=
    fun a b => chartLinearizedChristoffelPrincipal_differentiableAt (I := I) g α h a b k hy
  have hG_diff : ∀ a b : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartInvGramOnE (I := I) g α a b) y :=
    fun a b => chartInvGramOnE_differentiableAt_interior (I := I) g α a b hy
  have hsummand_diff : ∀ a b : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun y' => chartInvGramOnE (I := I) g α a b y' * Γ a b y') y :=
    fun a b => (hG_diff a b).mul (hΓ_diff a b)
  have hrewrite :
      (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') =
        fun y' => ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y' * Γ a b y' := by
    funext y'
    rw [chartLinearizedDeTurckVFPrincipal_def]
  rw [hrewrite]
  rw [partialDeriv_sum Finset.univ
        (fun a y' => ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y' * Γ a b y')
        (fun a _ => DifferentiableAt.fun_sum (fun b _ => hsummand_diff a b))]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [partialDeriv_sum Finset.univ
        (fun b y' => chartInvGramOnE (I := I) g α a b y' * Γ a b y')
        (fun b _ => hsummand_diff a b)]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [partialDeriv_mul (chartInvGramOnE (I := I) g α a b) (Γ a b)
        (hG_diff a b) (hΓ_diff a b)]

/-- The second-order part of the linearized DeTurck-correction operator vanishes on
the zero perturbation: every principal-part outer derivative is the derivative of the
zero function. -/
@[simp] theorem chartDeTurckCorrSecondOrderPart_zero
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrSecondOrderPart (I := I) g g' α
      (0 : ChartMetricPerturbation E) i j y = 0 := by
  classical
  rw [chartDeTurckCorrSecondOrderPart_def]
  have hpd : ∀ (d k : Fin (Module.finrank ℝ E)),
      partialDeriv (E := E) d
        (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α
          (0 : ChartMetricPerturbation E) k y') y = 0 := by
    intro d k
    have heq : (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α
        (0 : ChartMetricPerturbation E) k y') = fun _ : E => (0 : ℝ) := by
      funext y'; rw [chartLinearizedDeTurckVFPrincipal_zero]
    rw [heq, partialDeriv_const]
  have hsum1 : (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α k j y *
        partialDeriv (E := E) i
          (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α
            (0 : ChartMetricPerturbation E) k y') y) = 0 := by
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [hpd i k, mul_zero]
  have hsum2 : (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α i k y *
        partialDeriv (E := E) j
          (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α
            (0 : ChartMetricPerturbation E) k y') y) = 0 := by
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [hpd j k, mul_zero]
  rw [hsum1, hsum2, add_zero]

/-- **Additivity** of the second-order part of the linearized DeTurck-correction
operator in the perturbation direction. -/
theorem chartDeTurckCorrSecondOrderPart_add
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h₁ h₂ : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    chartDeTurckCorrSecondOrderPart (I := I) g g' α (h₁ + h₂) i j y =
      chartDeTurckCorrSecondOrderPart (I := I) g g' α h₁ i j y +
        chartDeTurckCorrSecondOrderPart (I := I) g g' α h₂ i j y := by
  classical
  rw [chartDeTurckCorrSecondOrderPart_def, chartDeTurckCorrSecondOrderPart_def,
    chartDeTurckCorrSecondOrderPart_def]
  have hadd : ∀ (d k : Fin (Module.finrank ℝ E)),
      partialDeriv (E := E) d
          (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α (h₁ + h₂) k y')
          y =
        partialDeriv (E := E) d
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h₁ k y') y +
          partialDeriv (E := E) d
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h₂ k y') y := by
    intro d k
    have heq : (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α
          (h₁ + h₂) k y') =
        fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h₁ k y' +
          chartLinearizedDeTurckVFPrincipal (I := I) g g' α h₂ k y' := by
      funext y'; rw [chartLinearizedDeTurckVFPrincipal_add]
    rw [heq, partialDeriv_add (E := E)
          (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h₁ k y')
          (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h₂ k y')
          (chartLinearizedDeTurckVFPrincipal_differentiableAt (I := I) g g' α h₁ k hy)
          (chartLinearizedDeTurckVFPrincipal_differentiableAt (I := I) g g' α h₂ k hy)]
  have hsum1 : (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          partialDeriv (E := E) i
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α (h₁ + h₂) k y')
            y) =
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          partialDeriv (E := E) i
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h₁ k y') y) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          partialDeriv (E := E) i
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h₂ k y') y) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hadd i k]; ring
  have hsum2 : (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          partialDeriv (E := E) j
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α (h₁ + h₂) k y')
            y) =
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          partialDeriv (E := E) j
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h₁ k y') y) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          partialDeriv (E := E) j
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h₂ k y') y) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hadd j k]; ring
  rw [hsum1, hsum2]
  ring

/-- **Scalar homogeneity** of the second-order part of the linearized DeTurck-correction
operator in the perturbation direction. -/
theorem chartDeTurckCorrSecondOrderPart_smul
    (g g' : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    chartDeTurckCorrSecondOrderPart (I := I) g g' α (c • h) i j y =
      c • chartDeTurckCorrSecondOrderPart (I := I) g g' α h i j y := by
  classical
  rw [chartDeTurckCorrSecondOrderPart_def, chartDeTurckCorrSecondOrderPart_def,
    smul_eq_mul]
  have hsmul : ∀ (d k : Fin (Module.finrank ℝ E)),
      partialDeriv (E := E) d
          (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α (c • h) k y') y =
        c * partialDeriv (E := E) d
          (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y := by
    intro d k
    have heq : (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α
          (c • h) k y') =
        fun y' => c • chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y' := by
      funext y'; rw [chartLinearizedDeTurckVFPrincipal_smul]
    rw [heq, partialDeriv_const_smul (E := E) c
          (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y')
          (chartLinearizedDeTurckVFPrincipal_differentiableAt (I := I) g g' α h k hy),
      smul_eq_mul]
  have hsum1 : (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          partialDeriv (E := E) i
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α (c • h) k y')
            y) =
      c * ∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          partialDeriv (E := E) i
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hsmul i k]; ring
  have hsum2 : (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          partialDeriv (E := E) j
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α (c • h) k y')
            y) =
      c * ∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          partialDeriv (E := E) j
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hsmul j k]; ring
  rw [hsum1, hsum2]
  ring

end DeTurckLinearization
end DeTurck
end PDE
end DifferentialGeometry
