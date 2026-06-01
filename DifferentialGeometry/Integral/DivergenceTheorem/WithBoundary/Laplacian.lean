import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Gradient
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Global
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.InteriorCompactSupport
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.IntegrationByParts
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Topology.Algebra.Support

/-!
# Laplace–Beltrami operator on a Riemannian manifold (with boundary)

For a smooth Riemannian metric `g` on a smooth manifold `M` whose local model
`I : ModelWithCorners ℝ E H` may carry a non-trivial boundary, this file
constructs the Laplace–Beltrami operator on smooth scalar functions `f : M → ℝ`
whose topological supports are contained in the manifold interior
`I.interior M`.

The construction proceeds in two stages:

1. The intrinsic gradient `gradFun g f` is packaged as a globally smooth tangent
   section `Cₛ^∞⟮I; E, TangentSpace I⟯`. Although `gradFun g f` is only smooth
   on `I.interior M` in general, the interior-support hypothesis on `f` ensures
   that `gradFun g f` vanishes on a neighbourhood of every boundary point —
   namely the open complement of `tsupport f`, which contains the entire
   manifold boundary because `tsupport f ⊆ I.interior M`. The smoothness of
   the section is then established by combining the chart-local smoothness on
   `I.interior M` with the trivial smoothness of the zero section on
   `(tsupport f)ᶜ`, via `contMDiff_of_contMDiffOn_union_of_isOpen`.

2. The Laplacian `Δ_g_with_boundary g hf hf_int` is defined as the with-boundary
   divergence of this packaged gradient section.

## Sign convention

The geometer convention `Δ = div ∘ grad` is used throughout, mirroring the
boundaryless Laplacian. With this convention the Laplacian is non-positive on a
closed manifold, and the spectrum of `-Δ` lies in `[0, ∞)`.

## Main definitions

* `grad_g_with_boundary_section g hf hf_int` : the gradient of an
  interior-supported smooth function as a globally smooth tangent section.
* `Δ_g_with_boundary g hf hf_int` : the Laplace–Beltrami operator on an
  interior-supported smooth function, defined as the with-boundary divergence
  of the packaged gradient section.

## Main results

* `Δ_g_with_boundary_contMDiffOn_interior` : the Laplacian is `C^∞` on the
  manifold interior.
* `Δ_g_with_boundary_continuous` : the Laplacian is continuous on `M`.
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

/-- `I.interior M` is open in `M`. -/
private lemma isOpen_interior_M : IsOpen (I.interior M) :=
  I.isOpen_interior (M := M) (n := ∞)
    (by exact (by decide : (∞ : WithTop ℕ∞) ≠ 0))

/-- The pointwise gradient `gradFun g f` vanishes outside the topological
support of `f`. Restated from the boundary-agnostic
`gradFun_eq_zero_of_eventuallyEq_zero` for the convenience of the smoothness
argument below. -/
private lemma gradFun_eq_zero_on_compl_tsupport
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    {x : M} (hx : x ∈ (tsupport f)ᶜ) :
    gradFun (I := I) g f x = (0 : TangentSpace I x) := by
  have h_open : IsOpen (tsupport f)ᶜ := (isClosed_tsupport _).isOpen_compl
  have hev : f =ᶠ[𝓝 x] (fun _ : M => (0 : ℝ)) := by
    filter_upwards [h_open.mem_nhds hx] with y hy
    by_contra hne
    exact hy (subset_tsupport _ hne)
  exact gradFun_eq_zero_of_eventuallyEq_zero (I := I) g hev

/-- On the open complement of the topological support of `f`, the lifted
gradient `fun x => TotalSpace.mk' E x (gradFun g f x)` agrees with the zero
section. -/
private lemma gradFun_total_eq_zeroSection_on_compl_tsupport
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    {y : M} (hy : y ∈ (tsupport f)ᶜ) :
    TotalSpace.mk' E y (gradFun (I := I) g f y) =
      (Bundle.zeroSection E (TangentSpace I : M → Type _) y) := by
  have hzero : gradFun (I := I) g f y = (0 : TangentSpace I y) :=
    gradFun_eq_zero_on_compl_tsupport (I := I) g hy
  rw [hzero]
  rfl

/-- The lifted gradient is `C^∞` on the open complement of the topological
support of `f`: it agrees there with the zero section, which is globally
smooth. -/
private lemma gradFun_total_contMDiffOn_compl_tsupport
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradFun (I := I) g f x))
      (tsupport f)ᶜ := by
  have hzero : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (Bundle.zeroSection E (TangentSpace I : M → Type _)) :=
    contMDiff_zeroSection ℝ (TangentSpace I : M → Type _)
  refine (hzero.contMDiffOn).congr ?_
  intro y hy
  exact gradFun_total_eq_zeroSection_on_compl_tsupport (I := I) g hy

/-- Cover of `M` by the open sets `I.interior M` and `(tsupport f)ᶜ`, valid
when `tsupport f ⊆ I.interior M`. Every point lies in one of the two:
interior points trivially in `I.interior M`, boundary points (which lie outside
`I.interior M` and hence outside `tsupport f`) in `(tsupport f)ᶜ`. -/
private lemma interior_union_compl_tsupport_eq_univ
    {f : M → ℝ} (hf_int : tsupport f ⊆ I.interior M) :
    I.interior M ∪ (tsupport f)ᶜ = (Set.univ : Set M) := by
  refine Set.eq_univ_of_forall ?_
  intro x
  by_cases hx : x ∈ I.interior M
  · exact Or.inl hx
  · refine Or.inr ?_
    intro hx_supp
    exact hx (hf_int hx_supp)

/-- **Block A — Smooth tangent section packaging of the gradient.** For a
smooth function `f : M → ℝ` with `tsupport f ⊆ I.interior M`, the intrinsic
pointwise gradient `gradFun g f` packages as a globally smooth `C^∞` tangent
section. The smoothness argument combines:

* `C^∞` on `I.interior M` via `gradFun_contMDiffOn_interior`;
* `C^∞` on `(tsupport f)ᶜ` because the gradient vanishes there (it agrees with
  the zero section, which is globally smooth);
* the open cover `I.interior M ∪ (tsupport f)ᶜ = M` (since
  `tsupport f ⊆ I.interior M`).
-/
def grad_g_with_boundary_section [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨fun x : M => gradFun (I := I) g f x, by
    have hs_open : IsOpen (I.interior M) := isOpen_interior_M
    have ht_open : IsOpen ((tsupport f)ᶜ) := (isClosed_tsupport _).isOpen_compl
    have hs : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E x (gradFun (I := I) g f x))
        (I.interior M) :=
      gradFun_contMDiffOn_interior (I := I) g hf
    have ht : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E x (gradFun (I := I) g f x))
        ((tsupport f)ᶜ) :=
      gradFun_total_contMDiffOn_compl_tsupport (I := I) g f
    have hcover : I.interior M ∪ (tsupport f)ᶜ = (Set.univ : Set M) :=
      interior_union_compl_tsupport_eq_univ (I := I) (M := M) hf_int
    exact contMDiff_of_contMDiffOn_union_of_isOpen hs ht hcover hs_open ht_open⟩

@[simp] lemma grad_g_with_boundary_section_apply [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) (x : M) :
    (grad_g_with_boundary_section (I := I) g hf hf_int :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      gradFun (I := I) g f x := rfl

/-- The packaged gradient section coincides with the underlying intrinsic
gradient `grad_g_with_boundary g f` as a fiber-valued function on `M`. -/
@[simp] lemma grad_g_with_boundary_section_coe [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) (x : M) :
    (grad_g_with_boundary_section (I := I) g hf hf_int :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      grad_g_with_boundary (I := I) g f x := rfl

/-- The support of the packaged gradient section is contained in the
topological support of `f`. -/
lemma support_grad_g_with_boundary_section_subset [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) :
    Function.support
        ((grad_g_with_boundary_section (I := I) g hf hf_int :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
          ∀ x, TangentSpace I x) ⊆ tsupport f :=
  support_grad_g_with_boundary_subset (I := I) g f

/-- The topological support of the packaged gradient section is contained in
the topological support of `f`. -/
lemma tsupport_grad_g_with_boundary_section_subset [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) :
    tsupport ((grad_g_with_boundary_section (I := I) g hf hf_int :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
      ∀ x, TangentSpace I x) ⊆ tsupport f :=
  closure_minimal
    (support_grad_g_with_boundary_section_subset (I := I) g hf hf_int)
    (isClosed_tsupport _)

/-- The topological support of the packaged gradient section is contained in
`I.interior M`. -/
lemma tsupport_grad_g_with_boundary_section_subset_interior [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) :
    tsupport ((grad_g_with_boundary_section (I := I) g hf hf_int :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
      ∀ x, TangentSpace I x) ⊆ I.interior M :=
  (tsupport_grad_g_with_boundary_section_subset (I := I) g hf hf_int).trans hf_int

/-- If the underlying function has compact support, so does the packaged
gradient section. -/
lemma hasCompactSupport_grad_g_with_boundary_section [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M)
    (hf_cs : HasCompactSupport f) :
    HasCompactSupport
      ((grad_g_with_boundary_section (I := I) g hf hf_int :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)) := by
  refine HasCompactSupport.of_support_subset_isCompact (hf_cs : IsCompact (tsupport f)) ?_
  intro x hx
  exact support_grad_g_with_boundary_section_subset (I := I) g hf hf_int hx

/-- **The Laplace–Beltrami operator on an interior-supported smooth function.**
Defined as the with-boundary divergence of the packaged gradient section. The
sign convention is the geometer's: `Δ = div ∘ grad`, so the Laplacian is
non-positive on a closed manifold. -/
def Δ_g_with_boundary [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) : M → ℝ :=
  divergence_g_with_boundary (I := I) g
    (grad_g_with_boundary_section (I := I) g hf hf_int)

@[simp] lemma Δ_g_with_boundary_def [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) (x : M) :
    Δ_g_with_boundary (I := I) g hf hf_int x =
      divergence_g_with_boundary (I := I) g
        (grad_g_with_boundary_section (I := I) g hf hf_int) x := rfl

/-- The Laplacian is `C^∞` on `I.interior M`. -/
theorem Δ_g_with_boundary_contMDiffOn_interior [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (Δ_g_with_boundary (I := I) g hf hf_int)
      (I.interior M) :=
  divergence_g_with_boundary_contMDiffOn_interior (I := I) g
    (grad_g_with_boundary_section (I := I) g hf hf_int)

/-- The topological support of the Laplacian is contained in the topological
support of the underlying function `f`. -/
lemma tsupport_Δ_g_with_boundary_subset [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) :
    tsupport (Δ_g_with_boundary (I := I) g hf hf_int) ⊆ tsupport f := by
  have hsec_supp : tsupport ((grad_g_with_boundary_section (I := I) g hf hf_int :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : ∀ x, TangentSpace I x) ⊆
        I.interior M :=
    tsupport_grad_g_with_boundary_section_subset_interior (I := I) g hf hf_int
  have h1 : tsupport (Δ_g_with_boundary (I := I) g hf hf_int) ⊆
      tsupport ((grad_g_with_boundary_section (I := I) g hf hf_int :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : ∀ x, TangentSpace I x) :=
    tsupport_divergence_g_with_boundary_subset_of_interior_support
      (I := I) g (grad_g_with_boundary_section (I := I) g hf hf_int) hsec_supp
  exact h1.trans (tsupport_grad_g_with_boundary_section_subset (I := I) g hf hf_int)

/-- The Laplacian is continuous on `M`. The proof glues the smoothness on the
manifold interior with the local vanishing on the open complement of the
topological support of `f`. -/
theorem Δ_g_with_boundary_continuous [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) :
    Continuous (Δ_g_with_boundary (I := I) g hf hf_int) := by
  classical
  have hΔ_supp_int : tsupport (Δ_g_with_boundary (I := I) g hf hf_int) ⊆
      I.interior M :=
    (tsupport_Δ_g_with_boundary_subset (I := I) g hf hf_int).trans hf_int
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx_supp : x ∈ tsupport (Δ_g_with_boundary (I := I) g hf hf_int)
  · have hx_int : x ∈ I.interior M := hΔ_supp_int hx_supp
    have hcont_int : ContinuousOn (Δ_g_with_boundary (I := I) g hf hf_int)
        (I.interior M) :=
      (Δ_g_with_boundary_contMDiffOn_interior (I := I) g hf hf_int).continuousOn
    exact (hcont_int x hx_int).continuousAt (isOpen_interior_M.mem_nhds hx_int)
  · have h_open : IsOpen (tsupport (Δ_g_with_boundary (I := I) g hf hf_int))ᶜ :=
      (isClosed_tsupport _).isOpen_compl
    have hev_zero : (Δ_g_with_boundary (I := I) g hf hf_int) =ᶠ[𝓝 x]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [h_open.mem_nhds hx_supp] with y hy
      by_contra hne
      exact hy (subset_tsupport _ hne)
    exact (continuous_const.continuousAt.congr hev_zero.symm)

/-- The Laplacian has compact support whenever the underlying function does
(in addition to interior support). -/
lemma hasCompactSupport_Δ_g_with_boundary [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M)
    (hf_cs : HasCompactSupport f) :
    HasCompactSupport (Δ_g_with_boundary (I := I) g hf hf_int) := by
  refine HasCompactSupport.of_support_subset_isCompact (hf_cs : IsCompact (tsupport f)) ?_
  intro x hx
  have h1 : x ∈ tsupport (Δ_g_with_boundary (I := I) g hf hf_int) :=
    subset_tsupport _ hx
  exact tsupport_Δ_g_with_boundary_subset (I := I) g hf hf_int h1

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
