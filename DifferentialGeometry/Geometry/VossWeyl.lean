import DifferentialGeometry.Geometry.Laplacian
import DifferentialGeometry.Integral.DivergenceTheorem.ChartInvariance

/-!
# The chart Voss-Weyl formula for the Laplace-Beltrami operator

For a smooth Riemannian metric `g` on a smooth boundaryless manifold `M`,
a smooth scalar function `f : M → ℝ`, and a chart based at `α : M`, this file
establishes the chart-coordinate Voss-Weyl formula:
$$
(\Delta_g f)(x) = \frac{1}{\sqrt{\det g_\alpha(x)}}
  \sum_i \partial_i \Bigl(\sqrt{\det g_\alpha}\,
    \sum_j g^{ij}_\alpha\, \partial_j \tilde f\Bigr)(\varphi_\alpha(x)),
$$
where `\tilde f := f \circ \varphi_\alpha^{-1}` is the chart pullback of `f`,
`g^{ij}_\alpha` is the inverse of the chart Gram matrix
`(g_\alpha)_{ij} = g.inner (e_i, e_j)` of the chart-basis frame, and
`\sqrt{\det g_\alpha}` is the chart density.

The proof combines:

* the Voss-Weyl chart formula for the divergence
  (`voss_weyl_divergence_formula`), which computes
  `divergence_g g X x` as `localDivergence g α X x` for `x` in the chart source;
* the chart-coordinate decomposition of the gradient
  (`gradChartLocal_eq_gradFun`), which writes
  `gradFun g f x = ∑_i \mathrm{gradChartCoeff}_i\, e_i(x)`;
* the identification of the divergence chart-coefficient
  `chartCoeff α (grad_g g hf) i x` with `gradChartCoeff g α f i x`, by
  uniqueness of basis decomposition.

## Main definitions

* `chartVossWeylLaplacian g α f x` : the chart Voss-Weyl right-hand side, as a
  scalar function of `x : M`.

## Main results

* `chartCoeff_grad_g_eq_gradChartCoeff` : on the chart base set, the Voss-Weyl
  chart coefficient of `grad_g g hf` agrees with `gradChartCoeff g α f`.
* `localDivergence_grad_g_eq_chartVossWeylLaplacian` : the chart-local
  Voss-Weyl divergence of `grad_g g hf` rewrites as the chart Voss-Weyl
  Laplacian.
* `voss_weyl_laplacian_formula_of_closed` : the headline identity
  `Δ_g g hf x = chartVossWeylLaplacian g α f x` on the chart source.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

/-- The pulled-back inverse Gram matrix entry on the chart target
`(extChartAt I α).target ⊆ E`. -/
def chartInvGramOnE (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) i j

@[simp] lemma chartInvGramOnE_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartInvGramOnE (I := I) g α i j y =
      chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) i j := rfl

/-- The chart-pulled-back chart-local gradient component, viewed as a function
on the chart target. -/
def gradChartCoeffOnE (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ)
    (i : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y =>
    ∑ j : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α i j y *
        partialDeriv (E := E) j (scalarOnE (I := I) α f) y

@[simp] lemma gradChartCoeffOnE_def
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ)
    (i : Fin (Module.finrank ℝ E)) (y : E) :
    gradChartCoeffOnE (I := I) g α f i y =
      ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α i j y *
          partialDeriv (E := E) j (scalarOnE (I := I) α f) y := rfl

/-- The integrand of the chart Voss-Weyl Laplacian: in chart coordinates,
the `i`-th term reads `gradChartCoeffOnE g α f i · chartDensityOnE g α`. -/
def chartVossWeylIntegrand (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ)
    (i : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y =>
    gradChartCoeffOnE (I := I) g α f i y * chartDensityOnE (I := I) g α y

@[simp] lemma chartVossWeylIntegrand_def
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ)
    (i : Fin (Module.finrank ℝ E)) (y : E) :
    chartVossWeylIntegrand (I := I) g α f i y =
      gradChartCoeffOnE (I := I) g α f i y *
        chartDensityOnE (I := I) g α y := rfl

/-- The chart Voss-Weyl right-hand side for the Laplace-Beltrami operator. -/
def chartVossWeylLaplacian (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ)
    (x : M) : ℝ :=
  (∑ i : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) i
        (chartVossWeylIntegrand (I := I) g α f i)
        (extChartAt I α x))
    / chartDensity (I := I) g α x

@[simp] lemma chartVossWeylLaplacian_def
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ) (x : M) :
    chartVossWeylLaplacian (I := I) g α f x =
      (∑ i : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i
            (chartVossWeylIntegrand (I := I) g α f i)
            (extChartAt I α x))
        / chartDensity (I := I) g α x := rfl

/-- On the chart base set with `extChartAt` value in the interior of the chart
target, the Voss-Weyl chart coefficient of `grad_g g hf` agrees with the
gradient chart coefficient `gradChartCoeff g α f`. -/
lemma chartCoeff_grad_g_eq_gradChartCoeff [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {x : M} (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target)
    (i : Fin (Module.finrank ℝ E)) :
    chartCoeff (I := I) α (grad_g (I := I) g hf) i x =
      gradChartCoeff (I := I) g α f i x := by
  classical
  set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) α
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E
  have hxchart : x ∈ (chartAt H α).source := by
    rw [trivializationAt_baseSet_eq_chartAt_source] at hx; exact hx
  have hf_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) f x :=
    hf.mdifferentiable (by simp) x
  have hgrad_eq :
      gradFun (I := I) g f x =
        ∑ k : Fin (Module.finrank ℝ E),
          gradChartCoeff (I := I) g α f k x •
            chartBasisVecFiber (I := I) α k x :=
    (gradChartLocal_eq_gradFun (I := I) g α hf_mdiff hx hx_int).symm
  set L : TangentSpace I x ≃L[ℝ] E := T.continuousLinearEquivAt ℝ x hx with hL_def
  have hL_apply : ∀ v : TangentSpace I x, L v = (T ⟨x, v⟩).2 := fun _ => rfl
  have hL_basis : ∀ k : Fin (Module.finrank ℝ E),
      L (chartBasisVecFiber (I := I) α k x) = b k := by
    intro k
    rw [hL_apply]
    exact trivializationAt_chartBasisVec_snd (I := I) α k hx
  have hLgrad : L (gradFun (I := I) g f x) =
      ∑ k : Fin (Module.finrank ℝ E),
        gradChartCoeff (I := I) g α f k x • b k := by
    rw [hgrad_eq]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [map_smul]
    rw [hL_basis k]
  have hrepr_basis_combo :
      b.repr (∑ k : Fin (Module.finrank ℝ E),
            gradChartCoeff (I := I) g α f k x • b k) i =
        gradChartCoeff (I := I) g α f i x := by
    rw [map_sum]
    rw [Finsupp.coe_finset_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single i]
    · rw [map_smul, Module.Basis.repr_self]
      simp
    · intro k _ hki
      rw [map_smul, Module.Basis.repr_self]
      simp [Ne.symm hki]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hgrad_g_x : ((grad_g (I := I) g hf :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) = gradFun (I := I) g f x :=
    grad_g_apply (I := I) g hf x
  unfold chartCoeff
  rw [show ((grad_g (I := I) g hf :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) = gradFun (I := I) g f x
      from hgrad_g_x]
  rw [show (T ⟨x, gradFun (I := I) g f x⟩).2 = L (gradFun (I := I) g f x)
      from (hL_apply (gradFun (I := I) g f x)).symm]
  rw [hLgrad]
  exact hrepr_basis_combo

/-- Pointwise rewriting on the chart target: the chart-local divergence
coefficient `chartCoeffOnE α (grad_g g hf) i` for `grad_g g hf` matches the
chart Voss-Weyl gradient coefficient `gradChartCoeffOnE g α f i`, at any point
of the chart target. -/
private lemma chartCoeffOnE_grad_g_eq_gradChartCoeffOnE [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ (extChartAt I α).target) :
    chartCoeffOnE (I := I) α (grad_g (I := I) g hf) i y =
      gradChartCoeffOnE (I := I) g α f i y := by
  classical
  set z : M := (extChartAt I α).symm y with hz_def
  have hz_src : z ∈ (extChartAt I α).source := (extChartAt I α).map_target hy
  have hz_chart : z ∈ (chartAt H α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hz_src; exact hz_src
  have hz_base : z ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hz_chart
  have htarget_eq_int :
      (extChartAt I α).target = interior (extChartAt I α).target :=
    (isOpen_extChartAt_target (I := I) α).interior_eq.symm
  have hz_image_int : extChartAt I α z ∈ interior (extChartAt I α).target := by
    have h1 : extChartAt I α z = y := (extChartAt I α).right_inv hy
    rw [h1]
    rw [← htarget_eq_int]
    exact hy
  have hpw :=
    chartCoeff_grad_g_eq_gradChartCoeff (I := I) g α hf hz_base hz_image_int i
  have hext_z : extChartAt I α z = y := (extChartAt I α).right_inv hy
  unfold chartCoeffOnE gradChartCoeffOnE
  rw [hpw]
  unfold gradChartCoeff
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [hext_z]
  rw [chartInvGramOnE_def]

/-- On the chart source, the chart-local Voss-Weyl divergence of
`grad_g g hf` agrees with the chart Voss-Weyl Laplacian. -/
lemma localDivergence_grad_g_eq_chartVossWeylLaplacian [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    localDivergence (I := I) g α (grad_g (I := I) g hf) x =
      chartVossWeylLaplacian (I := I) g α f x := by
  classical
  rw [localDivergence_def, chartVossWeylLaplacian_def]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  set y₀ : E := extChartAt I α x with hy₀_def
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  have hy₀_target : y₀ ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc
  have htarget_open : IsOpen (extChartAt I α).target :=
    isOpen_extChartAt_target (I := I) α
  have htarget_nhd : (extChartAt I α).target ∈ 𝓝 y₀ :=
    htarget_open.mem_nhds hy₀_target
  have hev : (fun y : E =>
        chartCoeffOnE (I := I) α (grad_g (I := I) g hf) i y *
          chartDensityOnE (I := I) g α y) =ᶠ[𝓝 y₀]
      chartVossWeylIntegrand (I := I) g α f i := by
    filter_upwards [htarget_nhd] with y hy
    rw [chartVossWeylIntegrand_def,
        chartCoeffOnE_grad_g_eq_gradChartCoeffOnE (I := I) g α hf i hy]
  unfold partialDeriv
  rw [hev.fderiv_eq]

/-- **Chart Voss-Weyl formula for the Laplace-Beltrami operator.** For a smooth
scalar `f`, a chart `α`, and `x` in the source of the chart at `α`, the
Laplacian `Δ_g g hf x` equals the chart Voss-Weyl right-hand side
`chartVossWeylLaplacian g α f x`. Stated here on a closed manifold: `M` is
boundaryless, `T2`, `σ`-compact, and compact. (The compactness hypothesis is
not actually needed for the chart-local conclusion; see
`voss_weyl_laplacian_formula_pointwise` for the σ-compact-only variant.) -/
theorem voss_weyl_laplacian_formula_of_closed
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    Δ_g (I := I) g hf x = chartVossWeylLaplacian (I := I) g α f x := by
  rw [Δ_g_def]
  rw [voss_weyl_divergence_formula (I := I) g α (grad_g (I := I) g hf) hx]
  exact localDivergence_grad_g_eq_chartVossWeylLaplacian (I := I) g α hf hx

/-- A `σ`-compact (not necessarily compact) variant: same conclusion, with
compactness dropped. -/
theorem laplacian_eq_chartVossWeyl_of_sigmaCompact
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    Δ_g (I := I) g hf x = chartVossWeylLaplacian (I := I) g α f x := by
  rw [Δ_g_def]
  rw [voss_weyl_divergence_formula (I := I) g α (grad_g (I := I) g hf) hx]
  exact localDivergence_grad_g_eq_chartVossWeylLaplacian (I := I) g α hf hx

/-- **Pointwise chart Voss-Weyl formula.** Same conclusion as
`voss_weyl_laplacian_formula_of_closed` — `Δ_g g hf x = chartVossWeylLaplacian g α f x` for
`x` in the source of the chart at `α` — but on a manifold that is only
boundaryless, `T2`, and `σ`-compact, dropping `[CompactSpace M]`. The chart
Voss-Weyl identity is chart-source-pointwise, so global compactness plays no
role in the derivation. This is the variant consumed by downstream theorems
(e.g. the chart Hessian-trace identity) that do not assume global
compactness. -/
theorem voss_weyl_laplacian_formula_pointwise
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    Δ_g (I := I) g hf x = chartVossWeylLaplacian (I := I) g α f x :=
  laplacian_eq_chartVossWeyl_of_sigmaCompact (I := I) g α hf hx

end DivergenceTheorem
end Integral
end DifferentialGeometry
