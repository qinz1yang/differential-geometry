import DifferentialGeometry.PDE.DeTurck.RicciLinearization.InvGramPerturbation

/-!
# The principal part of the linearized Christoffel symbol

The chart Christoffel symbol of the second kind is the algebraic expression
$$\Gamma^k{}_{ij}(g, \alpha)(y) = \tfrac12 \sum_l G^{kl}(y)\,
    \bigl(\partial_i G_{lj} + \partial_j G_{li} - \partial_l G_{ij}\bigr)(y),$$
a function of the chart Gram matrix `G`, its first partial derivatives, and the chart
inverse Gram matrix `G⁻¹`.

Linearizing in a metric-perturbation direction `h` (with chart components `h_{ab}(y)`)
splits into two pieces:

* the **principal part**, which carries a *derivative* of `h`,
  $$(D\Gamma)^k{}_{ij}[h](y) = \tfrac12 \sum_l G^{kl}(y)\,
      \bigl(\partial_i h_{lj} + \partial_j h_{li} - \partial_l h_{ij}\bigr)(y);$$
* the lower-order part `D(G^{kl})[h] \cdot (\partial G\ldots)`, which carries `h`
  undifferentiated — this is the `invGramPerturbation` contribution and is treated
  elsewhere.

This file builds **only** the principal part.  It is the term that survives into the
second-order symbol of the linearized Ricci tensor.

## Contents

* `chartLinearizedChristoffelPrincipal` — the closed-form principal part, together with
  its unfolding lemma `chartLinearizedChristoffelPrincipal_def`.  The index convention
  matches `chartChristoffel`: the two lower indices `i, j` come first, then the upper
  index `k`, then the chart-coordinate point `y ∈ E`.
* `chartLinearizedChristoffelPrincipal_symm` — symmetry in the lower index pair.
* algebraic instances `Add`, `SMul ℝ` on `ChartMetricPerturbation E`, plus
  `chartLinearizedChristoffelPrincipal_add`, `chartLinearizedChristoffelPrincipal_smul`,
  `chartLinearizedChristoffelPrincipal_zero` — linearity of the principal part in the
  perturbation direction.
* `chartLinearizedChristoffelPrincipal_contDiffOn` — smoothness on the chart target
  `(extChartAt I α).target`, the form the second-order symbol step consumes.
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

namespace ChartMetricPerturbation

/-- Pointwise sum of two perturbations: `(h₁ + h₂) i j y = h₁ i j y + h₂ i j y`. -/
instance : Add (ChartMetricPerturbation E) :=
  ⟨fun h₁ h₂ =>
    { toFun := fun i j y => h₁ i j y + h₂ i j y
      symm' := fun i j y => by
        simp only [ChartMetricPerturbation.symm h₁ i j y, ChartMetricPerturbation.symm h₂ i j y]
      smooth' := fun i j => (h₁.smooth i j).add (h₂.smooth i j) }⟩

@[simp] lemma add_apply (h₁ h₂ : ChartMetricPerturbation E)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    (h₁ + h₂) i j y = h₁ i j y + h₂ i j y := rfl

/-- Pointwise real-scalar multiple of a perturbation: `(c • h) i j y = c • (h i j y)`. -/
instance : SMul ℝ (ChartMetricPerturbation E) :=
  ⟨fun c h =>
    { toFun := fun i j y => c • h i j y
      symm' := fun i j y => by
        simp only [ChartMetricPerturbation.symm h i j y]
      smooth' := fun i j => (h.smooth i j).const_smul c }⟩

@[simp] lemma smul_apply (c : ℝ) (h : ChartMetricPerturbation E)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    (c • h) i j y = c • h i j y := rfl

end ChartMetricPerturbation

/-- The **principal part of the linearized Christoffel symbol** in the chart at `α`, in
the perturbation direction `h`, evaluated at the chart-coordinate point `y ∈ E`:
$$(D\Gamma)^k{}_{ij}[h](y) = \tfrac12 \sum_l G^{kl}(y)\,
    \bigl(\partial_i h_{lj} + \partial_j h_{li} - \partial_l h_{ij}\bigr)(y),$$
where `G^{kl} = chartInvGramOnE g α k l` is the chart inverse Gram matrix pulled back to
the chart target and `h_{ab} = h a b` are the chart components of the perturbation.

The index convention matches `chartChristoffel`: the two lower indices `i, j` come
first, then the upper index `k`.  This is the term of the Christoffel linearization that
carries a derivative of `h`; the complementary `D(G^{kl})[h]` term carries `h`
undifferentiated and is the `invGramPerturbation` contribution handled separately. -/
def chartLinearizedChristoffelPrincipal (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
    chartInvGramOnE (I := I) g α k l y *
      (partialDeriv (E := E) i (h l j) y +
       partialDeriv (E := E) j (h l i) y -
       partialDeriv (E := E) l (h i j) y)

@[simp] lemma chartLinearizedChristoffelPrincipal_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedChristoffelPrincipal (I := I) g α h i j k y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l y *
          (partialDeriv (E := E) i (h l j) y +
           partialDeriv (E := E) j (h l i) y -
           partialDeriv (E := E) l (h i j) y) := rfl

/-- **Symmetry of the principal linearized Christoffel part** in the lower indices. -/
theorem chartLinearizedChristoffelPrincipal_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedChristoffelPrincipal (I := I) g α h i j k y =
      chartLinearizedChristoffelPrincipal (I := I) g α h j i k y := by
  classical
  rw [chartLinearizedChristoffelPrincipal_def, chartLinearizedChristoffelPrincipal_def]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  congr 1
  rw [show partialDeriv (E := E) l (h i j) y =
        partialDeriv (E := E) l (h j i) y from by rw [h.symm_fun i j]]
  ring

/-- The principal linearized Christoffel part vanishes on the zero perturbation. -/
@[simp] lemma chartLinearizedChristoffelPrincipal_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedChristoffelPrincipal (I := I) g α
      (0 : ChartMetricPerturbation E) i j k y = 0 := by
  classical
  rw [chartLinearizedChristoffelPrincipal_def]
  have hzero : ∀ l : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α k l y *
        (partialDeriv (E := E) i ((0 : ChartMetricPerturbation E) l j) y +
         partialDeriv (E := E) j ((0 : ChartMetricPerturbation E) l i) y -
         partialDeriv (E := E) l ((0 : ChartMetricPerturbation E) i j) y) = 0 := by
    intro l
    have hlj : ((0 : ChartMetricPerturbation E) l j) = fun _ : E => (0 : ℝ) := rfl
    have hli : ((0 : ChartMetricPerturbation E) l i) = fun _ : E => (0 : ℝ) := rfl
    have hij : ((0 : ChartMetricPerturbation E) i j) = fun _ : E => (0 : ℝ) := rfl
    rw [hlj, hli, hij, partialDeriv_const, partialDeriv_const, partialDeriv_const]
    ring
  rw [Finset.sum_congr rfl (fun l _ => hzero l), Finset.sum_const_zero, mul_zero]

/-- **Additivity** of the principal linearized Christoffel part in the perturbation
direction: `(DΓ)[h₁ + h₂] = (DΓ)[h₁] + (DΓ)[h₂]`. -/
theorem chartLinearizedChristoffelPrincipal_add
    (g : SmoothRiemannianMetric I M) (α : M)
    (h₁ h₂ : ChartMetricPerturbation E) (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedChristoffelPrincipal (I := I) g α (h₁ + h₂) i j k y =
      chartLinearizedChristoffelPrincipal (I := I) g α h₁ i j k y +
        chartLinearizedChristoffelPrincipal (I := I) g α h₂ i j k y := by
  classical
  rw [chartLinearizedChristoffelPrincipal_def, chartLinearizedChristoffelPrincipal_def,
    chartLinearizedChristoffelPrincipal_def]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have hi : partialDeriv (E := E) i ((h₁ + h₂) l j) y =
      partialDeriv (E := E) i (h₁ l j) y + partialDeriv (E := E) i (h₂ l j) y := by
    have heq : ((h₁ + h₂) l j) = fun y => h₁ l j y + h₂ l j y := rfl
    rw [heq, partialDeriv_add _ _ (h₁.differentiableAt l j y) (h₂.differentiableAt l j y)]
  have hj : partialDeriv (E := E) j ((h₁ + h₂) l i) y =
      partialDeriv (E := E) j (h₁ l i) y + partialDeriv (E := E) j (h₂ l i) y := by
    have heq : ((h₁ + h₂) l i) = fun y => h₁ l i y + h₂ l i y := rfl
    rw [heq, partialDeriv_add _ _ (h₁.differentiableAt l i y) (h₂.differentiableAt l i y)]
  have hl : partialDeriv (E := E) l ((h₁ + h₂) i j) y =
      partialDeriv (E := E) l (h₁ i j) y + partialDeriv (E := E) l (h₂ i j) y := by
    have heq : ((h₁ + h₂) i j) = fun y => h₁ i j y + h₂ i j y := rfl
    rw [heq, partialDeriv_add _ _ (h₁.differentiableAt i j y) (h₂.differentiableAt i j y)]
  rw [hi, hj, hl]
  ring

/-- **Scalar homogeneity** of the principal linearized Christoffel part in the
perturbation direction: `(DΓ)[c • h] = c • (DΓ)[h]`. -/
theorem chartLinearizedChristoffelPrincipal_smul
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (h : ChartMetricPerturbation E) (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedChristoffelPrincipal (I := I) g α (c • h) i j k y =
      c • chartLinearizedChristoffelPrincipal (I := I) g α h i j k y := by
  classical
  rw [chartLinearizedChristoffelPrincipal_def, chartLinearizedChristoffelPrincipal_def,
    smul_eq_mul]
  have hsummand : ∀ l : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α k l y *
        (partialDeriv (E := E) i ((c • h) l j) y +
         partialDeriv (E := E) j ((c • h) l i) y -
         partialDeriv (E := E) l ((c • h) i j) y) =
      c * (chartInvGramOnE (I := I) g α k l y *
        (partialDeriv (E := E) i (h l j) y +
         partialDeriv (E := E) j (h l i) y -
         partialDeriv (E := E) l (h i j) y)) := by
    intro l
    have hi : partialDeriv (E := E) i ((c • h) l j) y =
        c * partialDeriv (E := E) i (h l j) y := by
      have heq : ((c • h) l j) = fun y => c • h l j y := rfl
      rw [heq, partialDeriv_const_smul c _ (h.differentiableAt l j y), smul_eq_mul]
    have hj : partialDeriv (E := E) j ((c • h) l i) y =
        c * partialDeriv (E := E) j (h l i) y := by
      have heq : ((c • h) l i) = fun y => c • h l i y := rfl
      rw [heq, partialDeriv_const_smul c _ (h.differentiableAt l i y), smul_eq_mul]
    have hl : partialDeriv (E := E) l ((c • h) i j) y =
        c * partialDeriv (E := E) l (h i j) y := by
      have heq : ((c • h) i j) = fun y => c • h i j y := rfl
      rw [heq, partialDeriv_const_smul c _ (h.differentiableAt i j y), smul_eq_mul]
    rw [hi, hj, hl]
    ring
  rw [Finset.sum_congr rfl (fun l _ => hsummand l), ← Finset.mul_sum]
  ring

/-- Each `partialDeriv` of a globally `C^∞` real function on the model space is itself
globally `C^∞`. -/
private lemma partialDeriv_contDiff_of_contDiff
    {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (i : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (partialDeriv (E := E) i u) := by
  have hfderiv : ContDiff ℝ ∞ (fderiv ℝ u) :=
    hu.fderiv_right (by rw [ENat.coe_top_add_one])
  unfold partialDeriv
  exact hfderiv.clm_apply contDiff_const

/-- Each `partialDeriv` of a perturbation component field is globally `C^∞`. -/
private lemma partialDeriv_perturbation_contDiff
    (h : ChartMetricPerturbation E) (i a b : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (partialDeriv (E := E) i (h a b)) :=
  partialDeriv_contDiff_of_contDiff (h.smooth a b) i

/-- **Smoothness of the principal linearized Christoffel part.**  As a function of the
chart-coordinate point `y`, `(DΓ)^k{}_{ij}[h]` is `C^∞` on the chart target
`(extChartAt I α).target`. -/
theorem chartLinearizedChristoffelPrincipal_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y => chartLinearizedChristoffelPrincipal (I := I) g α h i j k y)
      (extChartAt I α).target := by
  classical
  have hsummand : ∀ l : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (fun y => chartInvGramOnE (I := I) g α k l y *
          (partialDeriv (E := E) i (h l j) y +
           partialDeriv (E := E) j (h l i) y -
           partialDeriv (E := E) l (h i j) y))
        (extChartAt I α).target := by
    intro l
    have hG : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α k l)
        (extChartAt I α).target :=
      chartInvGramOnE_contDiffOn (I := I) g α k l
    have hdi : ContDiffOn ℝ ∞ (partialDeriv (E := E) i (h l j))
        (extChartAt I α).target :=
      (partialDeriv_perturbation_contDiff h i l j).contDiffOn
    have hdj : ContDiffOn ℝ ∞ (partialDeriv (E := E) j (h l i))
        (extChartAt I α).target :=
      (partialDeriv_perturbation_contDiff h j l i).contDiffOn
    have hdl : ContDiffOn ℝ ∞ (partialDeriv (E := E) l (h i j))
        (extChartAt I α).target :=
      (partialDeriv_perturbation_contDiff h l i j).contDiffOn
    exact hG.mul ((hdi.add hdj).sub hdl)
  have hsum : ContDiffOn ℝ ∞
      (fun y => ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l y *
          (partialDeriv (E := E) i (h l j) y +
           partialDeriv (E := E) j (h l i) y -
           partialDeriv (E := E) l (h i j) y))
      (extChartAt I α).target :=
    ContDiffOn.sum (fun l _ => hsummand l)
  have hresult : ContDiffOn ℝ ∞
      (fun y => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l y *
          (partialDeriv (E := E) i (h l j) y +
           partialDeriv (E := E) j (h l i) y -
           partialDeriv (E := E) l (h i j) y))
      (extChartAt I α).target :=
    contDiffOn_const.mul hsum
  refine hresult.congr (fun y _ => ?_)
  rw [chartLinearizedChristoffelPrincipal_def]

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry
