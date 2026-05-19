import RicciFlower.Analysis.DivergenceTheorem.Closed
import RicciFlower.Analysis.DivergenceTheorem.Proper
import RicciFlower.Analysis.DivergenceTheorem.IntegrationByParts
import RicciFlower.Analysis.DivergenceTheorem.Green
import RicciFlower.Analysis.DivergenceTheorem.Gradient
import RicciFlower.Analysis.DivergenceTheorem.Laplacian
import RicciFlower.Analysis.Volume.Family

/-!
# Time-parameterised wrappers around the divergence theorem and the volume-variation formula

For a smoothly time-parameterised Riemannian metric family
`g_fam : ℝ → SmoothRiemannianMetric I M`, this file packages the existing
fixed-metric divergence theorem and integration-by-parts identities pointwise
in the time parameter `t`, and re-exports the time-dependence of the integral
of a regular scalar integrand against the family of Riemannian volume
measures.

Each pointwise-in-`t` wrapper is a one-line consequence of its fixed-metric
counterpart with the metric chosen as `g_fam t`. They introduce no new
time-regularity assumptions on `g_fam`: each statement holds at a fixed time
and uses only the standard typeclass and topological hypotheses (Hausdorff
boundaryless σ-compact manifold, possibly compact, and possibly compact
support of the section).

The volume-variation formula is re-exported under a name in this directory,
without modifying its hypotheses, for navigation convenience downstream.

## Main results

* `integral_divergence_eq_zero_of_compact_family`: at each `t`,
  `∫_M divergence_g (g_fam t) X dμ_{g_fam t} = 0` on a closed manifold.
* `integral_divergence_eq_zero_of_hasCompactSupport_family`: at each `t`, the
  same identity for a compactly-supported section on a σ-compact boundaryless
  manifold.
* `integral_tangentSectionAction_eq_neg_integral_smul_divergence_family`:
  at each `t`, the basic integration-by-parts identity in the family setting.
* `integral_tangentSectionAction_mul_add_eq_neg_family`: at each `t`, the
  symmetric integration-by-parts identity in the family setting.
* `integral_inner_grad_eq_neg_integral_smul_laplacian_family`: at each `t`,
  Green's first identity in the family setting.
* `integral_smul_laplacian_sub_eq_zero_family`: at each `t`, Green's second
  identity in the family setting.
* `volumeVariation_hasDerivAt`: re-export of the volume-variation formula
  for `t ↦ ∫ f t d(vol_t)` along a regular family `g_fam` and a regular
  integrand `f`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix ENNReal

namespace RicciFlower
namespace Analysis
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open RicciFlower.Analysis.Volume

/-! ## File-local Borel-space instances

Match the convention in the surrounding files: `E` and `M` carry their canonical
Borel σ-algebras. Declared `local` to avoid leaking into callers. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Pointwise-in-`t` divergence theorem on a closed manifold -/

/-- **Family form of the divergence theorem on a closed manifold.** For a
smoothly time-parameterised Riemannian metric family `g_fam` on a closed
(compact and boundaryless) smooth manifold `M`, a smooth tangent section `X`,
and any time `t`, the integral of `divergence_g (g_fam t) X` against the
family-volume measure at `t` vanishes:
$$\int_M \operatorname{div}_{g(t)}(X)\,d\mu_{g(t)} = 0.$$ -/
theorem integral_divergence_eq_zero_of_compact_family
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (t : ℝ) :
    ∫ x, divergence_g (I := I) (g_fam t) X x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) = 0 := by
  rw [riemannianMeasureFamily_def]
  exact integral_divergence_eq_zero_of_compact (I := I) (g_fam t) X

/-- **Family form of the divergence theorem for compactly-supported sections.**
For a smoothly time-parameterised Riemannian metric family `g_fam` on a
σ-compact Hausdorff boundaryless smooth manifold `M`, a smooth tangent section
`X` with compact support, and any time `t`, the integral of
`divergence_g (g_fam t) X` against the family-volume measure at `t` vanishes:
$$\int_M \operatorname{div}_{g(t)}(X)\,d\mu_{g(t)} = 0.$$ -/
theorem integral_divergence_eq_zero_of_hasCompactSupport_family
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport X) (t : ℝ) :
    ∫ x, divergence_g (I := I) (g_fam t) X x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) = 0 := by
  rw [riemannianMeasureFamily_def]
  exact integral_divergence_eq_zero_of_hasCompactSupport (I := I) (g_fam t) X hX

/-! ## Pointwise-in-`t` integration by parts -/

/-- **Family form of integration by parts (basic).** For a smoothly
time-parameterised Riemannian metric family `g_fam` on a σ-compact Hausdorff
boundaryless smooth manifold `M`, a smooth scalar `f : M → ℝ`, a smooth tangent
section `X` with compact support, and any time `t`,
$$\int_M X(f)\,d\mu_{g(t)} =
    -\int_M f \cdot \operatorname{div}_{g(t)}(X)\,d\mu_{g(t)}.$$ -/
theorem integral_tangentSectionAction_eq_neg_integral_smul_divergence_family
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport X) (t : ℝ) :
    ∫ x, tangentSectionAction (I := I) X f x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) =
      -∫ x, f x * divergence_g (I := I) (g_fam t) X x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) := by
  rw [riemannianMeasureFamily_def]
  exact integral_tangentSectionAction_eq_neg_integral_smul_divergence
    (I := I) (g_fam t) hf X hX

/-- **Family form of integration by parts (symmetric).** For a smoothly
time-parameterised Riemannian metric family `g_fam` on a σ-compact Hausdorff
boundaryless smooth manifold `M`, smooth scalars `f, h : M → ℝ`, a smooth
tangent section `X` with compact support, and any time `t`,
$$\int_M \bigl(X(f)\,h + f\,X(h)\bigr)\,d\mu_{g(t)}
       = -\int_M f\,h \cdot \operatorname{div}_{g(t)}(X)\,d\mu_{g(t)}.$$ -/
theorem integral_tangentSectionAction_mul_add_eq_neg_family
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ) ∞ h)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport X) (t : ℝ) :
    ∫ x, (tangentSectionAction (I := I) X f x * h x +
            f x * tangentSectionAction (I := I) X h x)
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) =
      -∫ x, f x * h x * divergence_g (I := I) (g_fam t) X x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) := by
  rw [riemannianMeasureFamily_def]
  exact integral_tangentSectionAction_mul_add_eq_neg
    (I := I) (g_fam t) hf hh X hX

/-! ## Pointwise-in-`t` Green's identities -/

/-- **Family form of Green's first identity.** For a smoothly time-parameterised
Riemannian metric family `g_fam` on a σ-compact Hausdorff boundaryless smooth
manifold `M`, smooth scalars `f, h : M → ℝ` with `h` having compact support,
and any time `t`,
$$\int_M g_t(\nabla_{g(t)} f, \nabla_{g(t)} h)\,d\mu_{g(t)}
    = -\int_M f \cdot \Delta_{g(t)} h\,d\mu_{g(t)}.$$ -/
theorem integral_inner_grad_eq_neg_integral_smul_laplacian_family
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_supp : HasCompactSupport h) (t : ℝ) :
    ∫ x, (g_fam t).inner x
            ((grad_g (I := I) (g_fam t) hf :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) (g_fam t) hh :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) =
      -∫ x, f x * Δ_g (I := I) (g_fam t) hh x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) := by
  rw [riemannianMeasureFamily_def]
  exact integral_inner_grad_eq_neg_integral_smul_laplacian
    (I := I) (g_fam t) hf hh hh_supp

/-- **Family form of Green's second identity.** For a smoothly time-parameterised
Riemannian metric family `g_fam` on a closed (compact and boundaryless) smooth
manifold `M`, smooth scalars `f, h : M → ℝ`, and any time `t`,
$$\int_M (f \cdot \Delta_{g(t)} h - h \cdot \Delta_{g(t)} f)\,d\mu_{g(t)} = 0.$$ -/
theorem integral_smul_laplacian_sub_eq_zero_family
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (t : ℝ) :
    ∫ x, (f x * Δ_g (I := I) (g_fam t) hh x -
            h x * Δ_g (I := I) (g_fam t) hf x)
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) = 0 := by
  rw [riemannianMeasureFamily_def]
  exact integral_smul_laplacian_sub_eq_zero (I := I) (g_fam t) hf hh

/-! ## Volume-variation formula re-export

The clean volume-variation formula is established in
`RicciFlower.Analysis.Volume.Family.volume_variation_formula_clean`.
We re-export it here under a name belonging to this directory for navigation
convenience downstream. The hypotheses, namespaces, and statement are
unchanged. -/

/-- **Volume-variation formula.** Re-export of the volume-variation formula:
for a regular family of Riemannian metrics `g_fam` and a regular integrand
`f : ℝ → M → ℝ`, on a closed manifold `M`, the function
`s ↦ ∫_M f(s, ·) d(vol_{g_fam s})` is differentiable at `t₀` with derivative
$$\int_M \bigl(\partial_t f\bigr|_{t_0}
     + \tfrac{1}{2}\,\operatorname{tr}_{g(t_0)}(\partial_t g)\cdot f(t_0, \cdot)\bigr)
     \,d\mu_{g(t_0)}.$$ -/
theorem volumeVariation_hasDerivAt
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g_fam : ℝ → SmoothRiemannianMetric I M}
    {f : ℝ → M → ℝ} {t₀ : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g_fam t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : ℝ => ∫ x, f s x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam s))
      (∫ x, (deriv (fun s : ℝ => f s x) t₀
              + (1/2) * traceTimeDerivMetric (I := I) g_fam t₀ x * f t₀ x)
          ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t₀))
      t₀ :=
  volume_variation_formula_clean (I := I) (M := M) (g_fam := g_fam)
    (f := f) (t₀ := t₀) hg hf

end DivergenceTheorem
end Analysis
end RicciFlower
