import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.InteriorCompactSupport
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.IntegrationByParts
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Green
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Stokes
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.GreenWithBoundary
import DifferentialGeometry.Integral.DivergenceTheorem.Family
import DifferentialGeometry.Integral.Measure.Family

/-!
# Time-parameterised wrappers for the with-boundary divergence theorems

For a smoothly time-parameterised Riemannian metric family
`g_fam : ℝ → SmoothRiemannianMetric I M` on a smooth manifold `M` whose model
`I : ModelWithCorners ℝ E H` may carry a non-trivial boundary, this file
packages the previously established with-boundary divergence theorems,
integration-by-parts identities, Green's identities, and the global Stokes
theorem pointwise in the time parameter `t`.

Each pointwise-in-`t` wrapper is a one-line consequence of its fixed-metric
counterpart at `g := g_fam t`. They introduce no new time-regularity
assumptions on `g_fam`: each statement holds at a fixed time and uses only
the standard typeclass and topological hypotheses (Hausdorff σ-compact
manifold, possibly compact, with model `I` carrying or not carrying a
boundary).

The volume-variation formula is re-exported in this directory under a
navigationally-convenient name, without modifying its hypotheses. The
underlying `first_variation_of_volume` does not require
`[I.Boundaryless]`, so the same formula applies in the with-boundary
setting unchanged.

## Main results

### Interior-supported divergence theorem and integration by parts

* `integral_divergence_with_boundary_eq_zero_of_compact_of_interior_support_family`
  — at each time `t`, the with-boundary divergence theorem on a closed
  manifold for sections supported in the interior.
* `integral_divergence_with_boundary_eq_zero_of_hasCompactSupport_of_interior_support_family`
  — at each time `t`, the with-boundary divergence theorem for compactly-
  and interior-supported sections on a σ-compact Hausdorff manifold.
* `integral_tangentSectionAction_eq_neg_integral_smul_divergence_with_boundary_family`
  — at each time `t`, the basic with-boundary integration-by-parts identity
  for interior-supported test scalars and sections.
* `integral_tangentSectionAction_mul_add_eq_neg_with_boundary_family`
  — at each time `t`, the symmetric form of the with-boundary integration-
  by-parts identity.
* `integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary_family`
  — at each time `t`, the with-boundary Green's first identity for
  interior-supported test scalars.
* `integral_smul_laplacian_sub_eq_zero_with_boundary_family`
  — at each time `t`, the with-boundary Green's second identity on a closed
  manifold for interior-supported test scalars.

### Global Stokes theorem and Green's identities with boundary terms

* `stokes_compact_via_pou_family` — at each time `t`, the global Stokes
  theorem on a compact manifold-with-boundary, expressed through the
  chart-atlas boundary face sum.
* `green_first_with_boundary_family` — at each time `t`, Green's first
  identity with boundary contribution.
* `green_second_with_boundary_family` — at each time `t`, Green's second
  identity with boundary contribution.

### Volume variation re-export

* `volumeVariation_hasDerivAt_with_boundary` — re-export of the volume-
  variation formula. The clean formula does not require `[I.Boundaryless]`,
  so it applies unchanged in the with-boundary setting.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix ENNReal

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **Family form of the with-boundary divergence theorem on a closed
manifold.** For a smoothly time-parameterised Riemannian metric family
`g_fam` on a compact σ-compact Hausdorff smooth manifold `M` whose model
`I` may carry a boundary, a smooth tangent section `X` whose topological
support sits inside the manifold interior `I.interior M`, and any time
`t`,
$$\int_M \operatorname{div}_{g(t)}^{(\partial)}(X)\,d\mu_{g(t)} = 0.$$ -/
theorem integral_divergence_with_boundary_eq_zero_of_compact_of_interior_support_family
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX_int : tsupport X ⊆ I.interior M) (t : ℝ) :
    ∫ x, divergence_g_with_boundary (I := I) (g_fam t) X x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) = 0 := by
  rw [riemannianMeasureFamily_def]
  exact integral_divergence_with_boundary_eq_zero_of_compact_of_interior_support
    (I := I) (g_fam t) X hX_int

/-- **Family form of the with-boundary divergence theorem for compactly-
supported, interior-supported sections.** For a smoothly time-parameterised
Riemannian metric family `g_fam` on a σ-compact Hausdorff smooth manifold
`M` whose model `I` may carry a boundary, a smooth tangent section `X`
with compact support whose topological support sits inside the manifold
interior `I.interior M`, and any time `t`,
$$\int_M \operatorname{div}_{g(t)}^{(\partial)}(X)\,d\mu_{g(t)} = 0.$$ -/
theorem integral_divergence_with_boundary_eq_zero_of_hasCompactSupport_of_interior_support_family
    [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport X)
    (hX_int : tsupport X ⊆ I.interior M) (t : ℝ) :
    ∫ x, divergence_g_with_boundary (I := I) (g_fam t) X x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) = 0 := by
  rw [riemannianMeasureFamily_def]
  exact integral_divergence_with_boundary_eq_zero_of_hasCompactSupport_of_interior_support
    (I := I) (g_fam t) X hX hX_int

/-- **Family form of with-boundary integration by parts (basic).** For a
smoothly time-parameterised Riemannian metric family `g_fam` on a
σ-compact Hausdorff smooth manifold `M` whose model `I` may carry a
boundary, a smooth scalar `f : M → ℝ` whose topological support sits
inside the manifold interior, a smooth tangent section `X` with compact
support whose topological support also sits inside the manifold interior,
and any time `t`,
$$\int_M X(f)\,d\mu_{g(t)}
    = -\int_M f \cdot \operatorname{div}_{g(t)}^{(\partial)}(X)\,d\mu_{g(t)}.$$ -/
theorem integral_tangentSectionAction_eq_neg_integral_smul_divergence_with_boundary_family
    [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport X)
    (hX_int : tsupport X ⊆ I.interior M) (t : ℝ) :
    ∫ x, tangentSectionAction (I := I) X f x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) =
      -∫ x, f x * divergence_g_with_boundary (I := I) (g_fam t) X x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) := by
  rw [riemannianMeasureFamily_def]
  exact integral_tangentSectionAction_eq_neg_integral_smul_divergence_with_boundary
    (I := I) (g_fam t) hf hf_int X hX hX_int

/-- **Family form of with-boundary integration by parts (symmetric).** For
a smoothly time-parameterised Riemannian metric family `g_fam` on a
σ-compact Hausdorff smooth manifold `M` whose model `I` may carry a
boundary, smooth scalars `f, h : M → ℝ` whose topological supports sit
inside the manifold interior, a smooth tangent section `X` with compact
support whose topological support also sits inside the manifold interior,
and any time `t`,
$$\int_M \bigl(X(f)\,h + f\,X(h)\bigr)\,d\mu_{g(t)}
    = -\int_M f\,h \cdot \operatorname{div}_{g(t)}^{(\partial)}(X)\,d\mu_{g(t)}.$$ -/
theorem integral_tangentSectionAction_mul_add_eq_neg_with_boundary_family
    [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ) ∞ h)
    (hf_int : tsupport f ⊆ I.interior M) (hh_int : tsupport h ⊆ I.interior M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport X)
    (hX_int : tsupport X ⊆ I.interior M) (t : ℝ) :
    ∫ x, (tangentSectionAction (I := I) X f x * h x +
            f x * tangentSectionAction (I := I) X h x)
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) =
      -∫ x, f x * h x * divergence_g_with_boundary (I := I) (g_fam t) X x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) := by
  rw [riemannianMeasureFamily_def]
  exact integral_tangentSectionAction_mul_add_eq_neg_with_boundary
    (I := I) (g_fam t) hf hh hf_int hh_int X hX hX_int

/-- **Family form of Green's first identity, with boundary.** For a
smoothly time-parameterised Riemannian metric family `g_fam` on a
σ-compact Hausdorff smooth manifold `M` whose model `I` may carry a
boundary, smooth scalars `f, h : M → ℝ` whose topological supports sit
inside the manifold interior, with `h` having compact support, and any
time `t`,
$$\int_M g_t(\nabla_{g(t)} f, \nabla_{g(t)} h)\,d\mu_{g(t)}
    = -\int_M f \cdot \Delta_{g(t)}^{(\partial)} h\,d\mu_{g(t)}.$$ -/
theorem integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary_family
    [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hf_int : tsupport f ⊆ I.interior M) (hh_int : tsupport h ⊆ I.interior M)
    (hh_supp : HasCompactSupport h) (t : ℝ) :
    ∫ x, (g_fam t).inner x (gradFun (I := I) (g_fam t) f x)
            (gradFun (I := I) (g_fam t) h x)
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) =
      -∫ x, f x * Δ_g_with_boundary (I := I) (g_fam t) hh hh_int x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) := by
  rw [riemannianMeasureFamily_def]
  exact integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary
    (I := I) (g_fam t) hf hh hf_int hh_int hh_supp

/-- **Family form of Green's second identity on a closed manifold, with
boundary.** For a smoothly time-parameterised Riemannian metric family
`g_fam` on a compact σ-compact Hausdorff smooth manifold `M` whose model
`I` may carry a boundary, smooth scalars `f, h : M → ℝ` whose topological
supports sit inside the manifold interior, and any time `t`,
$$\int_M (f \cdot \Delta_{g(t)}^{(\partial)} h
    - h \cdot \Delta_{g(t)}^{(\partial)} f)\,d\mu_{g(t)} = 0.$$ -/
theorem integral_smul_laplacian_sub_eq_zero_with_boundary_family
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hf_int : tsupport f ⊆ I.interior M) (hh_int : tsupport h ⊆ I.interior M)
    (t : ℝ) :
    ∫ x, (f x * Δ_g_with_boundary (I := I) (g_fam t) hh hh_int x -
            h x * Δ_g_with_boundary (I := I) (g_fam t) hf hf_int x)
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) = 0 := by
  rw [riemannianMeasureFamily_def]
  exact integral_smul_laplacian_sub_eq_zero_with_boundary
    (I := I) (g_fam t) hf hh hf_int hh_int

section StokesGlobal

variable [hI : HasSmoothBoundary E H I]

/-- **Family form of the global Stokes theorem on a compact manifold-with-
boundary.** For a smoothly time-parameterised Riemannian metric family
`g_fam` on a compact σ-compact Hausdorff smooth manifold `M` whose model
`I` admits a smooth boundary, a smooth tangent section `X`, and any time
`t`,
$$\int_M \operatorname{div}_{g(t)}^{(\partial)}(X)\,d\mu_{g(t)}
    = \sum_\alpha \chartBoundaryFaceIntegral{g(t), \alpha, X, \rho_\alpha},$$
where the sum runs over the chart-atlas POU support set and
`ρ := chartAtlasPOU I M`. -/
theorem stokes_compact_via_pou_family
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (t : ℝ) :
    ∫ x, divergence_g_with_boundary (I := I) (g_fam t) X x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        chartBoundaryFaceIntegral (I := I) (g_fam t) α X
          ((chartAtlasPOU I M) α) := by
  rw [riemannianMeasureFamily_def]
  exact stokes_compact_via_pou (I := I) (g_fam t) X

/-- **Family form of the global Stokes theorem rephrased through
`boundaryFaceSum`.** For a smoothly time-parameterised Riemannian metric
family `g_fam` on a compact σ-compact Hausdorff smooth manifold `M` whose
model `I` admits a smooth boundary, a smooth tangent section `X`, and any
time `t`,
$$\int_M \operatorname{div}_{g(t)}^{(\partial)}(X)\,d\mu_{g(t)}
    = \boundaryFaceSum{g(t), X}.$$ -/
theorem integral_divergence_with_boundary_eq_boundaryFaceSum_family
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (t : ℝ) :
    ∫ x, divergence_g_with_boundary (I := I) (g_fam t) X x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) =
      boundaryFaceSum (I := I) (g_fam t) X := by
  rw [riemannianMeasureFamily_def]
  exact integral_divergence_with_boundary_eq_boundaryFaceSum (I := I) (g_fam t) X

/-- **Family form of Green's first identity, with boundary contribution
(closed manifold).** For a smoothly time-parameterised Riemannian metric
family `g_fam` on a compact σ-compact Hausdorff smooth manifold `M` whose
model `I` admits a smooth boundary, smooth scalars `f, h : M → ℝ` with
`tsupport h ⊆ I.interior M`, and any time `t`,
$$\int_M \langle \nabla_{g(t)} f, \nabla_{g(t)} h\rangle_{g(t)}\,d\mu_{g(t)}
   + \int_M f \cdot \Delta_{g(t)}^{(\partial)} h\,d\mu_{g(t)}
   = \boundaryFaceSum{g(t), f \cdot \nabla_{g(t)} h}.$$ -/
theorem green_first_with_boundary_family
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_int : tsupport h ⊆ I.interior M) (t : ℝ) :
    ∫ x, (g_fam t).inner x (gradFun (I := I) (g_fam t) f x)
            (gradFun (I := I) (g_fam t) h x)
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) +
      ∫ x, f x * Δ_g_with_boundary (I := I) (g_fam t) hh hh_int x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) =
      boundaryFaceSum (I := I) (g_fam t)
        (smoothSmul (I := I) f hf
          (grad_g_with_boundary_section (I := I) (g_fam t) hh hh_int)) := by
  simp only [riemannianMeasureFamily_def]
  exact green_first_with_boundary (I := I) (g_fam t) hf hh hh_int

/-- **Family form of Green's second identity, with boundary contribution
(closed manifold).** For a smoothly time-parameterised Riemannian metric
family `g_fam` on a compact σ-compact Hausdorff smooth manifold `M` whose
model `I` admits a smooth boundary, smooth scalars `f, h : M → ℝ` with
`tsupport f, tsupport h ⊆ I.interior M`, and any time `t`,
$$\int_M \bigl(f \cdot \Delta_{g(t)}^{(\partial)} h
    - h \cdot \Delta_{g(t)}^{(\partial)} f\bigr)\,d\mu_{g(t)}
  = \boundaryFaceSum{g(t), f \cdot \nabla_{g(t)} h}
    - \boundaryFaceSum{g(t), h \cdot \nabla_{g(t)} f}.$$ -/
theorem green_second_with_boundary_family
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hf_int : tsupport f ⊆ I.interior M) (hh_int : tsupport h ⊆ I.interior M)
    (t : ℝ) :
    ∫ x, (f x * Δ_g_with_boundary (I := I) (g_fam t) hh hh_int x -
            h x * Δ_g_with_boundary (I := I) (g_fam t) hf hf_int x)
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) =
      boundaryFaceSum (I := I) (g_fam t)
        (smoothSmul (I := I) f hf
          (grad_g_with_boundary_section (I := I) (g_fam t) hh hh_int)) -
      boundaryFaceSum (I := I) (g_fam t)
        (smoothSmul (I := I) h hh
          (grad_g_with_boundary_section (I := I) (g_fam t) hf hf_int)) := by
  rw [riemannianMeasureFamily_def]
  exact green_second_with_boundary (I := I) (g_fam t) hf hh hf_int hh_int

end StokesGlobal

/-- **Volume-variation formula (with-boundary re-export).** For a regular
family of Riemannian metrics `g_fam` and a regular integrand
`f : ℝ → M → ℝ` on a closed manifold `M`, the function
`s ↦ ∫_M f(s, ·) d(vol_{g_fam s})` is differentiable at `t₀` with
derivative
$$\int_M \bigl(\partial_t f\bigr|_{t_0}
    + \tfrac{1}{2}\,\operatorname{tr}_{g(t_0)}(\partial_t g)\cdot
      f(t_0, \cdot)\bigr)\,d\mu_{g(t_0)}.$$

This is `DifferentialGeometry.Integral.DivergenceTheorem.volumeVariation_hasDerivAt`
with the underlying `first_variation_of_volume` requiring no
`[I.Boundaryless]` assumption — the same formula applies in the
with-boundary setting unchanged. -/
theorem volumeVariation_hasDerivAt_with_boundary
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
  first_variation_of_volume (I := I) (M := M) (g_fam := g_fam)
    (f := f) (t₀ := t₀) hg hf

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
