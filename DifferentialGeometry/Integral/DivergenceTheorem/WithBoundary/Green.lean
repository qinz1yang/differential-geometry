import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Laplacian
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.IntegrationByParts
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Gradient
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Global
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.InteriorCompactSupport
import DifferentialGeometry.Integral.DivergenceTheorem.TangentAction
import DifferentialGeometry.Integral.Measure.Properties
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Green's identities on a Riemannian manifold (with boundary)

For a smooth Riemannian metric `g` on a smooth manifold `M` whose local model
`I : ModelWithCorners ℝ E H` may carry a non-trivial boundary, this file
establishes Green's first and second identities for smooth scalar functions
whose topological supports are contained in the manifold interior
`I.interior M`.

The interior-support hypothesis is the natural with-boundary analogue of the
boundaryless `HasCompactSupport` requirement: the with-boundary divergence
theorem itself requires the test section to be supported in the interior, so
the gradient sections involved in Green's identities must inherit interior
support from their underlying scalar functions.

## Strategy

The proofs mirror the boundaryless variants in
`DifferentialGeometry/Integral/DivergenceTheorem/Green.lean`. The key
differences are:

* the gradient is packaged as a smooth tangent section via
  `grad_g_with_boundary_section` (defined in `Laplacian.lean`), which
  inherits compact support and interior support from the underlying scalar
  function;
* the integration-by-parts identity is the with-boundary variant
  `integral_tangentSectionAction_eq_neg_integral_smul_divergence_with_boundary`
  from `IntegrationByParts.lean`, which carries explicit interior-support
  hypotheses on both the test scalar and the test section.

## Main results

* `integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary`
  (**Green's first identity, with boundary**): for smooth `f, h : M → ℝ` with
  `tsupport f, tsupport h ⊆ I.interior M` and `h` compactly supported,
  $$\int_M g(\nabla_g f, \nabla_g h)\,d\mu_g
       = -\int_M f \cdot \Delta_g^{(\partial)} h\,d\mu_g.$$

* `integral_smul_laplacian_sub_eq_zero_with_boundary`
  (**Green's second identity, closed manifold with boundary**): on a closed
  manifold (compact + boundary allowed), for any smooth `f, h : M → ℝ` with
  `tsupport f, tsupport h ⊆ I.interior M`,
  $$\int_M (f \cdot \Delta_g^{(\partial)} h - h \cdot \Delta_g^{(\partial)} f)
       \,d\mu_g = 0.$$
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

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

/-- **Green's first identity on a Riemannian manifold with boundary.** For
smooth `f, h : M → ℝ` with `tsupport f, tsupport h ⊆ I.interior M` and `h`
having compact support on a σ-compact Hausdorff smooth Riemannian manifold
`(M, g)` whose model `I` may carry a boundary,
$$\int_M g(\nabla_g f, \nabla_g h)\,d\mu_g
     = -\int_M f \cdot \Delta_g^{(\partial)} h\,d\mu_g.$$ -/
theorem integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hf_int : tsupport f ⊆ I.interior M) (hh_int : tsupport h ⊆ I.interior M)
    (hh_supp : HasCompactSupport h) :
    ∫ x, g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, f x * Δ_g_with_boundary (I := I) g hh hh_int x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    grad_g_with_boundary_section (I := I) g hh hh_int with hX_def
  have hX_cs : HasCompactSupport X :=
    hasCompactSupport_grad_g_with_boundary_section (I := I) g hh hh_int hh_supp
  have hX_int : tsupport (X : ∀ x, TangentSpace I x) ⊆ I.interior M :=
    tsupport_grad_g_with_boundary_section_subset_interior (I := I) g hh hh_int
  have h_ibp :=
    integral_tangentSectionAction_eq_neg_integral_smul_divergence_with_boundary
      (I := I) g hf hf_int X hX_cs hX_int
  have hLHS_eq : ∀ x : M,
      tangentSectionAction (I := I) X f x =
        g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x) := by
    intro x
    rw [tangentSectionAction_grad_g_with_boundary_eq_inner (I := I) g hf X x]
    change g.inner x (gradFun (I := I) g h x) (gradFun (I := I) g f x) =
      g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x)
    exact g.symm x _ _
  have hRHS_eq : ∀ x : M,
      f x * divergence_g_with_boundary (I := I) g X x =
        f x * Δ_g_with_boundary (I := I) g hh hh_int x := by
    intro x; rfl
  have hLHS_int : ∫ x, tangentSectionAction (I := I) X f x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hLHS_eq)
  have hRHS_int : ∫ x, f x * divergence_g_with_boundary (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, f x * Δ_g_with_boundary (I := I) g hh hh_int x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hRHS_eq)
  rw [← hLHS_int, h_ibp, hRHS_int]

/-- A symmetric variant of Green's first identity, with the integration-by-parts
test section built from `f` instead of `h`. The compactness of `tsupport f` is
recorded via `hf_supp`. -/
private theorem integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary'
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hf_int : tsupport f ⊆ I.interior M) (hh_int : tsupport h ⊆ I.interior M)
    (hf_supp : HasCompactSupport f) :
    ∫ x, g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, h x * Δ_g_with_boundary (I := I) g hf hf_int x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    grad_g_with_boundary_section (I := I) g hf hf_int with hX_def
  have hX_cs : HasCompactSupport X :=
    hasCompactSupport_grad_g_with_boundary_section (I := I) g hf hf_int hf_supp
  have hX_int : tsupport (X : ∀ x, TangentSpace I x) ⊆ I.interior M :=
    tsupport_grad_g_with_boundary_section_subset_interior (I := I) g hf hf_int
  have h_ibp :=
    integral_tangentSectionAction_eq_neg_integral_smul_divergence_with_boundary
      (I := I) g hh hh_int X hX_cs hX_int
  have hLHS_eq : ∀ x : M,
      tangentSectionAction (I := I) X h x =
        g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x) := by
    intro x
    rw [tangentSectionAction_grad_g_with_boundary_eq_inner (I := I) g hh X x]
    rfl
  have hRHS_eq : ∀ x : M,
      h x * divergence_g_with_boundary (I := I) g X x =
        h x * Δ_g_with_boundary (I := I) g hf hf_int x := by
    intro x; rfl
  have hLHS_int : ∫ x, tangentSectionAction (I := I) X h x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hLHS_eq)
  have hRHS_int : ∫ x, h x * divergence_g_with_boundary (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, h x * Δ_g_with_boundary (I := I) g hf hf_int x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hRHS_eq)
  rw [← hLHS_int, h_ibp, hRHS_int]

/-- **Green's second identity on a closed Riemannian manifold with boundary.**
For smooth `f, h : M → ℝ` with `tsupport f, tsupport h ⊆ I.interior M` on a
compact σ-compact Hausdorff smooth Riemannian manifold `(M, g)` whose model
`I` may carry a boundary,
$$\int_M (f \cdot \Delta_g^{(\partial)} h - h \cdot \Delta_g^{(\partial)} f)
     \,d\mu_g = 0.$$ -/
theorem integral_smul_laplacian_sub_eq_zero_with_boundary
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hf_int : tsupport f ⊆ I.interior M) (hh_int : tsupport h ⊆ I.interior M) :
    ∫ x, (f x * Δ_g_with_boundary (I := I) g hh hh_int x -
            h x * Δ_g_with_boundary (I := I) g hf hf_int x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  classical
  have hf_cs : HasCompactSupport f := HasCompactSupport.of_compactSpace _
  have hh_cs : HasCompactSupport h := HasCompactSupport.of_compactSpace _
  have h1 := integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary
    (I := I) g hf hh hf_int hh_int hh_cs
  have h2 := integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary'
    (I := I) g hf hh hf_int hh_int hf_cs
  have h_eq : ∫ x, f x * Δ_g_with_boundary (I := I) g hh hh_int x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, h x * Δ_g_with_boundary (I := I) g hf hf_int x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    have : -∫ x, f x * Δ_g_with_boundary (I := I) g hh hh_int x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
          -∫ x, h x * Δ_g_with_boundary (I := I) g hf hf_int x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      rw [← h1, h2]
    linarith
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hΔh_cont : Continuous (Δ_g_with_boundary (I := I) g hh hh_int) :=
    Δ_g_with_boundary_continuous (I := I) g hh hh_int
  have hΔf_cont : Continuous (Δ_g_with_boundary (I := I) g hf hf_int) :=
    Δ_g_with_boundary_continuous (I := I) g hf hf_int
  have hf_cont : Continuous f := hf.continuous
  have hh_cont : Continuous h := hh.continuous
  have h_int_fΔh : Integrable (fun x : M => f x * Δ_g_with_boundary (I := I) g hh hh_int x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hcont : Continuous (fun x : M => f x * Δ_g_with_boundary (I := I) g hh hh_int x) :=
      hf_cont.mul hΔh_cont
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h_int_hΔf : Integrable (fun x : M => h x * Δ_g_with_boundary (I := I) g hf hf_int x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hcont : Continuous (fun x : M => h x * Δ_g_with_boundary (I := I) g hf hf_int x) :=
      hh_cont.mul hΔf_cont
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_sub h_int_fΔh h_int_hΔf]
  rw [h_eq, sub_self]

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
