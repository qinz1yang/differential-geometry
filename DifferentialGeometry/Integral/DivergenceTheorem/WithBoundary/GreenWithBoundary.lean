import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Stokes
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Laplacian
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Gradient
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.IntegrationByParts
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.POUReduction
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Green
import DifferentialGeometry.Integral.DivergenceTheorem.POUReduction
import DifferentialGeometry.Integral.DivergenceTheorem.TangentAction
import DifferentialGeometry.Integral.Measure.Family
import DifferentialGeometry.Integral.Measure.Properties
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Green's identities with boundary contribution
(chart-by-chart formulation)

For a smooth Riemannian metric `g` on a compact smooth manifold `M` whose
local model `I : ModelWithCorners ℝ E H` admits a smooth boundary stratum
(`[hI : HasSmoothBoundary E H I]`), this file establishes Green's first and
second identities with explicit boundary contribution terms.

Because a global smooth outward unit normal vector field on the boundary is,
in the present infrastructure, available only pointwise (not as a smooth
bundle section), the boundary contribution is naturally expressed in
chart-by-chart form: as the finite sum, over the chart-atlas partition of
unity, of `chartBoundaryFaceIntegral` quantities. This mirrors the
formulation in `Stokes.lean`.

## Strategy

The proof of Green's first identity with boundary applies the global Stokes
theorem `stokes_compact_via_pou` to the smooth tangent section
`Y := smoothSmul f hf (grad_g_with_boundary_section g hh hh_int)` (i.e.
`f · ∇_g h`). By the divergence Leibniz rule
`divergence_g_with_boundary_smoothSmul`,
`div_g^{(\partial)}(f · ∇h) = f · Δh + ⟨∇f, ∇h⟩`, where `Δh` is the
with-boundary Laplacian and `⟨·,·⟩` is the metric inner product. Integrating
both sides against the canonical Riemannian volume measure and using the
global Stokes theorem to evaluate the integral of the divergence as the
chart-α boundary face sum yields Green's first identity.

Green's second identity follows by symmetrising in `f` and `h` and
subtracting; the `⟨∇f, ∇h⟩` and `⟨∇h, ∇f⟩` terms cancel by symmetry of the
metric.

## Sanity check

When the test scalar `f` is also interior-supported (in addition to `h`), the
boundary face sum vanishes — the section `f · ∇h` then has compact support
contained in `I.interior M`, and its with-boundary divergence integrates to
zero by `integral_divergence_with_boundary_eq_zero_of_hasCompactSupport_of_interior_support`.
This recovers the interior-supported Green's first identity from
`Green.lean` (i.e.
`integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary`), and is
recorded as `green_first_with_boundary_face_sum_eq_zero_of_interior_support`.

## Main definitions and results

* `boundaryFaceSum g X` — the chart-α boundary face integral summed over the
  chart-atlas POU support, with weights `(chartAtlasPOU I M) α`. A single
  named definition encapsulating the boundary contribution to the with-
  boundary divergence theorem.

* `green_first_with_boundary` — Green's first identity with boundary terms.

* `green_second_with_boundary` — Green's second identity with boundary terms.

* `green_first_with_boundary_face_sum_eq_zero_of_interior_support` — sanity
  check: when the test scalar is interior-supported, the boundary face sum
  vanishes and the boundaryless-style identity from `Green.lean` is
  recovered.
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

/-- **Boundary face sum.** The boundary contribution to the with-boundary
divergence theorem, expressed as a finite sum over the chart-atlas
partition of unity. By definition, the chart-α boundary face integral of
`X` against the chart-α POU weight, summed over the POU support set.

This is the chart-by-chart presentation of the boundary integral: when a
single intrinsic surface integral over `I.boundary M` against an outward
unit normal vector field is available, the boundary face sum coincides
with that intrinsic surface integral; this identification is not
established in the present file. -/
noncomputable def boundaryFaceSum
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : ℝ :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    chartBoundaryFaceIntegral (I := I) g α X
      ((chartAtlasPOU I M) α : M → ℝ)

@[simp] lemma boundaryFaceSum_def
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    boundaryFaceSum (I := I) g X =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        chartBoundaryFaceIntegral (I := I) g α X
          ((chartAtlasPOU I M) α : M → ℝ) := rfl

section StokesGlobal

variable [hI : HasSmoothBoundary E H I]

/-- For any smooth tangent section `X` on a compact smooth Riemannian
manifold `(M, g)`, the integral of `divergence_g_with_boundary g X` against
the canonical Riemannian volume measure equals `boundaryFaceSum g X`.

This is a restatement of `stokes_compact_via_pou` through the packaged
`boundaryFaceSum`. Both sides are volume integrals: `boundaryFaceSum g X` is
by definition the partition-of-unity sum of the chart-local
`chartBoundaryFaceIntegral` quantities, each of which is itself the
chart-local volume integral of `localDivergenceWithin g α X`. So this is a
tautological POU decomposition of the left-hand volume integral, not a
reduction to a surface integral over `I.boundary M`; no `d(∂M)` surface
integral appears here. The identification of `boundaryFaceSum` with an
intrinsic boundary surface integral is not established in this file. -/
theorem integral_divergence_with_boundary_eq_boundaryFaceSum
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∫ x, divergence_g_with_boundary (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      boundaryFaceSum (I := I) g X := by
  rw [boundaryFaceSum_def]
  exact stokes_compact_via_pou (I := I) g X

/-- A continuity helper: the inner product `⟨∇f, ∇h⟩` is continuous on the
manifold interior. The pointwise formula `g.inner x (gradFun g f x) (gradFun
g h x)` is continuous on `I.interior M` because both gradients are smooth
sections on the interior and `g.inner` is a smooth bundle map.

Combined with vanishing on the open complement of `tsupport h ⊆ I.interior
M`, this gives global continuity. -/
private lemma inner_grad_grad_continuous_of_interior_support
    [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_int : tsupport h ⊆ I.interior M) :
    Continuous
      (fun x : M => g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x)) := by
  classical
  set Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    grad_g_with_boundary_section (I := I) g hh hh_int with hY_def
  have hY_int : tsupport (Y : ∀ x, TangentSpace I x) ⊆ I.interior M :=
    tsupport_grad_g_with_boundary_section_subset_interior (I := I) g hh hh_int
  have h_eq : ∀ x : M,
      g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x) =
        tangentSectionAction (I := I) Y f x := by
    intro x
    rw [tangentSectionAction_grad_g_with_boundary_eq_inner (I := I) g hf Y x]
    change g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x) =
      g.inner x (gradFun (I := I) g h x) (gradFun (I := I) g f x)
    exact g.symm x _ _
  have hY_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (Y x)) := Y.contMDiff
  have h_act_cont : Continuous (tangentSectionAction (I := I) Y f) := by
    classical
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx_supp : x ∈ tsupport (Y : ∀ x, TangentSpace I x)
    · have hx_int : x ∈ I.interior M := hY_int hx_supp
      have hx_chart : x ∈ (chartAt H x).source := mem_chart_source H x
      have hx_target_int : extChartAt I x x ∈ interior (extChartAt I x).target :=
        extChartAt_mem_interior_target_of_isInteriorPoint
          (I := I) (M := M) x hx_chart hx_int
      have hsmooth : ContMDiffOn I 𝓘(ℝ) ∞ (tangentSectionAction (I := I) Y f)
          ((extChartAt I x).source ∩
            (extChartAt I x : M → E) ⁻¹' interior (extChartAt I x).target) :=
        tangentSectionAction_contMDiffOn (I := I) x Y hf
      have hxsrc : x ∈ (extChartAt I x).source := by
        rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx_chart
      have hxU : x ∈ (extChartAt I x).source ∩
          (extChartAt I x : M → E) ⁻¹' interior (extChartAt I x).target :=
        ⟨hxsrc, hx_target_int⟩
      have hUopen : IsOpen ((extChartAt I x).source ∩
          (extChartAt I x : M → E) ⁻¹' interior (extChartAt I x).target) := by
        have hcontOn := continuousOn_extChartAt (I := I) x
        exact hcontOn.isOpen_inter_preimage (isOpen_extChartAt_source (I := I) x)
          isOpen_interior
      exact ((hsmooth x hxU).continuousWithinAt.continuousAt) (hUopen.mem_nhds hxU)
    · have h_open : IsOpen (tsupport (Y : ∀ x, TangentSpace I x))ᶜ :=
        (isClosed_tsupport _).isOpen_compl
      have hev_zero : tangentSectionAction (I := I) Y f =ᶠ[𝓝 x]
          (fun _ => (0 : ℝ)) := by
        filter_upwards [h_open.mem_nhds hx_supp] with y hy
        have hY_zero : (Y : ∀ z, TangentSpace I z) y = 0 := by
          by_contra hne
          exact hy (subset_tsupport _ hne)
        change mfderiv I 𝓘(ℝ) f y ((Y : ∀ z, TangentSpace I z) y) = 0
        rw [hY_zero]
        exact (mfderiv I 𝓘(ℝ, ℝ) f y).map_zero
      exact (continuous_const.continuousAt.congr hev_zero.symm)
  refine h_act_cont.congr ?_
  intro x
  exact (h_eq x).symm

/-- The product `f · Δh` is continuous on `M`. -/
private lemma f_mul_Δ_continuous
    [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_int : tsupport h ⊆ I.interior M) :
    Continuous (fun x : M =>
      f x * Δ_g_with_boundary (I := I) g hh hh_int x) :=
  hf.continuous.mul (Δ_g_with_boundary_continuous (I := I) g hh hh_int)

set_option linter.unusedVariables false in
/-- The product `f · Δh` has compact support inherited from `Δh`. -/
private lemma f_mul_Δ_hasCompactSupport
    [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_int : tsupport h ⊆ I.interior M) :
    HasCompactSupport (fun x : M =>
      f x * Δ_g_with_boundary (I := I) g hh hh_int x) :=
  HasCompactSupport.of_compactSpace _

/-- Both integrands `f · Δh` and `⟨∇f, ∇h⟩` are integrable against the
canonical Riemannian volume measure on a closed manifold. -/
private lemma f_mul_Δ_integrable
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_int : tsupport h ⊆ I.interior M) :
    Integrable
      (fun x : M => f x * Δ_g_with_boundary (I := I) g hh hh_int x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  exact (f_mul_Δ_continuous (I := I) g hf hh hh_int).integrable_of_hasCompactSupport
    (f_mul_Δ_hasCompactSupport (I := I) g hf hh hh_int)

private lemma inner_grad_grad_integrable
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_int : tsupport h ⊆ I.interior M) :
    Integrable
      (fun x : M => g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  exact (inner_grad_grad_continuous_of_interior_support
    (I := I) g hf hh hh_int).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- **Green's first identity (closed manifold-with-boundary, chart-local
boundary term).** For smooth `f, h : M → ℝ` with `tsupport h ⊆ I.interior M`
on a compact σ-compact Hausdorff smooth Riemannian manifold `(M, g)` whose
model `I` admits a smooth boundary,
$$\int_M \langle \nabla_g f, \nabla_g h\rangle_g\,d\mu_g
   + \int_M f \cdot \Delta_g^{(\partial)} h\,d\mu_g
   = \text{boundaryFaceSum}\,g\,(f\,\nabla_g h).$$

The right-hand `boundaryFaceSum g (f · ∇_g h)` is the partition-of-unity sum
of the chart-local `chartBoundaryFaceIntegral` quantities for the test
section `f · ∇_g h`. As such it is a sum of chart-local VOLUME integrals of
`localDivergenceWithin`, not a surface integral over `I.boundary M`: the
identity is the with-boundary divergence theorem applied to `f · ∇_g h`, with
the boundary contribution left in chart-local form. The reduction of this
chart-local sum to a genuine `d(∂M)` surface integral against an outward unit
normal is not performed here (it is achieved, conditionally, in
`green_first_eq_boundary_surface_integral`).

The proof applies the divergence Leibniz rule
`divergence_g_with_boundary_smoothSmul`,
`div_g^{(∂)}(f · ∇h) = f · Δ_g^{(∂)} h + ⟨∇f, ∇h⟩`, integrates against the
volume measure, and evaluates the integral of the divergence via
`integral_divergence_with_boundary_eq_boundaryFaceSum`. -/
theorem green_first_with_boundary
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_int : tsupport h ⊆ I.interior M) :
    ∫ x, g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) +
      ∫ x, f x * Δ_g_with_boundary (I := I) g hh hh_int x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      boundaryFaceSum (I := I) g
        (smoothSmul (I := I) f hf
          (grad_g_with_boundary_section (I := I) g hh hh_int)) := by
  classical
  set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    grad_g_with_boundary_section (I := I) g hh hh_int with hX_def
  set Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    smoothSmul (I := I) f hf X with hY_def
  have hStokes :=
    integral_divergence_with_boundary_eq_boundaryFaceSum (I := I) g Y
  have h_leibniz : ∀ x : M,
      divergence_g_with_boundary (I := I) g Y x =
        f x * divergence_g_with_boundary (I := I) g X x +
          tangentSectionAction (I := I) X f x :=
    divergence_g_with_boundary_smoothSmul (I := I) g f hf X
  have h1 : ∀ x : M,
      f x * divergence_g_with_boundary (I := I) g X x =
        f x * Δ_g_with_boundary (I := I) g hh hh_int x := by
    intro x; rfl
  have h2 : ∀ x : M,
      tangentSectionAction (I := I) X f x =
        g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x) := by
    intro x
    rw [tangentSectionAction_grad_g_with_boundary_eq_inner (I := I) g hf X x]
    change g.inner x (gradFun (I := I) g h x) (gradFun (I := I) g f x) =
      g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x)
    exact g.symm x _ _
  have h_combined : ∀ x : M,
      divergence_g_with_boundary (I := I) g Y x =
        f x * Δ_g_with_boundary (I := I) g hh hh_int x +
          g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x) := by
    intro x
    rw [h_leibniz x, h1 x, h2 x]
  have h_int_eq :
      ∫ x, divergence_g_with_boundary (I := I) g Y x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, (f x * Δ_g_with_boundary (I := I) g hh hh_int x +
                g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact h_combined x
  have h_int_fΔh : Integrable
      (fun x : M => f x * Δ_g_with_boundary (I := I) g hh hh_int x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    f_mul_Δ_integrable (I := I) g hf hh hh_int
  have h_int_inner : Integrable
      (fun x : M =>
        g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    inner_grad_grad_integrable (I := I) g hf hh hh_int
  rw [h_int_eq] at hStokes
  rw [integral_add h_int_fΔh h_int_inner] at hStokes
  linarith

set_option linter.unusedVariables false in
/-- **Sanity check — vanishing of the boundary face sum on
interior-supported test scalars.** When the test scalar `f` is also
interior-supported, the section `f · ∇h` (used in Green's first identity
above) has compact support and interior support inherited from the
gradient section, and the boundary face sum vanishes.

The hypothesis `hf_int` is recorded in the signature for symmetry with
`hh_int` and to make the call site self-documenting; the proof routes
through the gradient section's own interior support
(`tsupport_grad_g_with_boundary_section_subset_interior`), which is
inherited from `hh_int` and already suffices. -/
theorem green_first_with_boundary_face_sum_eq_zero_of_interior_support
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hf_int : tsupport f ⊆ I.interior M)
    (hh_int : tsupport h ⊆ I.interior M) :
    boundaryFaceSum (I := I) g
        (smoothSmul (I := I) f hf
          (grad_g_with_boundary_section (I := I) g hh hh_int)) = 0 := by
  classical
  set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    grad_g_with_boundary_section (I := I) g hh hh_int with hX_def
  set Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    smoothSmul (I := I) f hf X with hY_def
  have hY_cs : HasCompactSupport Y := HasCompactSupport.of_compactSpace _
  have hX_int : tsupport (X : ∀ x, TangentSpace I x) ⊆ I.interior M :=
    tsupport_grad_g_with_boundary_section_subset_interior (I := I) g hh hh_int
  have hY_int : tsupport (Y : ∀ x, TangentSpace I x) ⊆ I.interior M :=
    tsupport_smoothSmul_subset_interior (I := I) hf X hX_int
  have h_div_Y_zero :
      ∫ x, divergence_g_with_boundary (I := I) g Y x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 :=
    integral_divergence_with_boundary_eq_zero_of_hasCompactSupport_of_interior_support
      (I := I) g Y hY_cs hY_int
  have h_stokes :=
    integral_divergence_with_boundary_eq_boundaryFaceSum (I := I) g Y
  rw [h_div_Y_zero] at h_stokes
  exact h_stokes.symm

/-- A symmetric variant of Green's first identity (with boundary): with
the integration-by-parts test section built from `f` instead of `h`. The
boundary face sum is built from the section `h · ∇f`. -/
private theorem green_first_with_boundary_swap
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hf_int : tsupport f ⊆ I.interior M) :
    ∫ x, g.inner x (gradFun (I := I) g h x) (gradFun (I := I) g f x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) +
      ∫ x, h x * Δ_g_with_boundary (I := I) g hf hf_int x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      boundaryFaceSum (I := I) g
        (smoothSmul (I := I) h hh
          (grad_g_with_boundary_section (I := I) g hf hf_int)) :=
  green_first_with_boundary (I := I) g hh hf hf_int

/-- **Green's second identity (closed manifold-with-boundary, chart-local
boundary terms).** For smooth `f, h : M → ℝ` with `tsupport f, tsupport h ⊆
I.interior M` on a compact σ-compact Hausdorff smooth Riemannian manifold
`(M, g)` whose model `I` admits a smooth boundary,
$$\int_M \bigl(f \cdot \Delta_g^{(\partial)} h
     - h \cdot \Delta_g^{(\partial)} f\bigr)\,d\mu_g
   = \text{boundaryFaceSum}\,g\,(f\,\nabla_g h)
     - \text{boundaryFaceSum}\,g\,(h\,\nabla_g f).$$

As in `green_first_with_boundary`, each `boundaryFaceSum` is the
partition-of-unity sum of the chart-local `chartBoundaryFaceIntegral`
volume-integral proxies, not a surface integral over `I.boundary M`; the
reduction to a genuine `d(∂M)` term is not performed here.

The proof subtracts `green_first_with_boundary` applied to `(f, h)` from the
swapped variant `green_first_with_boundary_swap`; the `⟨∇f, ∇h⟩` and
`⟨∇h, ∇f⟩` integrals cancel by symmetry of the metric. -/
theorem green_second_with_boundary
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hf_int : tsupport f ⊆ I.interior M)
    (hh_int : tsupport h ⊆ I.interior M) :
    ∫ x, (f x * Δ_g_with_boundary (I := I) g hh hh_int x -
            h x * Δ_g_with_boundary (I := I) g hf hf_int x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      boundaryFaceSum (I := I) g
        (smoothSmul (I := I) f hf
          (grad_g_with_boundary_section (I := I) g hh hh_int)) -
      boundaryFaceSum (I := I) g
        (smoothSmul (I := I) h hh
          (grad_g_with_boundary_section (I := I) g hf hf_int)) := by
  classical
  have h_main := green_first_with_boundary (I := I) g hf hh hh_int
  have h_swap := green_first_with_boundary_swap (I := I) g hf hh hf_int
  have h_inner_symm : ∀ x : M,
      g.inner x (gradFun (I := I) g h x) (gradFun (I := I) g f x) =
        g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x) := by
    intro x; exact g.symm x _ _
  have h_inner_int_eq :
      ∫ x, g.inner x (gradFun (I := I) g h x) (gradFun (I := I) g f x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall h_inner_symm)
  rw [h_inner_int_eq] at h_swap
  have h_int_fΔh : Integrable
      (fun x : M => f x * Δ_g_with_boundary (I := I) g hh hh_int x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    f_mul_Δ_integrable (I := I) g hf hh hh_int
  have h_int_hΔf : Integrable
      (fun x : M => h x * Δ_g_with_boundary (I := I) g hf hf_int x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    f_mul_Δ_integrable (I := I) g hh hf hf_int
  rw [integral_sub h_int_fΔh h_int_hΔf]
  linarith [h_main, h_swap]

end StokesGlobal

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
