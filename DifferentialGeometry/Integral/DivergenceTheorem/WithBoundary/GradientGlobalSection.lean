import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Gradient
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.PartialDerivWithin
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.EuclideanHalfSpaceInstance
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Global smooth tangent-bundle section for the metric gradient on a
manifold-with-boundary modelled on the Euclidean half-space

Given a smooth Riemannian metric `g` on a smooth manifold-with-boundary `M`
modelled on the canonical Euclidean half-space `EuclideanHalfSpace n`, and a
smooth scalar function `f : M → ℝ`, the pointwise metric gradient
`gradFun g f` packages as a globally smooth tangent-bundle section, **with no
interior-support hypothesis on `f`**. In particular, smoothness extends to the
boundary points of `M`.

The key technical fact is that the within-partial derivative
`partialDerivWithin (extChartAt I α).target j (scalarOnE α f)` is `C^∞` on the
**entire chart target** `(extChartAt I α).target`, not just on its interior.
This holds because the chart target satisfies
`UniqueDiffOn ℝ (extChartAt I α).target` (Mathlib's
`uniqueDiffOn_extChartAt_target`), and the smoothness of the within-partial of a
`ContDiffOn ℝ ∞` function on a unique-diff set is itself `ContDiffOn ℝ ∞` on
that set (`partialDerivWithin_contDiffOn_top_of_uniqueDiffOn`).

Composing with the chart map `extChartAt I α : M → E` (smooth on the chart
source mapping into the chart target), the chart-coefficient
`gradChartCoeffWithin g α f i` is smooth on the **entire chart source**, not
just the manifold-interior intersection. The chart-local representation
`gradChartLocalWithin g α f` is therefore globally smooth as a tangent-bundle
section on the chart source. Combined with the agreement
`gradChartLocalWithin = gradFun` on the chart source
(`gradChartLocalWithin_eq_gradFun`), this yields global smoothness of
`gradFun g f` on all of `M`.

## Main results

* `gradChartCoeffWithin_contMDiffOn_full` — chart-coefficient smoothness on
  the entire chart source.
* `gradChartLocalWithin_contMDiffOn_total_full` — total-space smoothness of
  the chart-local representation on the entire chart source.
* `gradFun_contMDiffOn_chart_source_full` — the intrinsic gradient
  `gradFun g f` is smooth on every chart source.
* `gradFun_contMDiff_total_full` — the intrinsic gradient is `C^∞` as a
  tangent-bundle section on all of `M` (specialised to the half-space model).
* `grad_g_smooth_section_full` — the headline theorem: for any smooth
  `f : M → ℝ` on a half-space-modelled compact manifold-with-boundary `(M, g)`,
  the pointwise gradient `gradFun g f` packages as a smooth tangent-bundle
  section.
* `grad_g_full_section` — equivalently, `gradFun g f` packaged as
  `Cₛ^∞⟮I; E, TangentSpace I⟯`.

## Comparison to interior-support packaging

The previously available smooth-section packaging
`grad_g_with_boundary_section` (in `WithBoundary/Laplacian.lean`) requires the
hypothesis `tsupport f ⊆ I.interior M`. That hypothesis is essential for the
gluing argument used there (which combines the boundary-shy interior-only
smoothness with the trivial smoothness of the zero section away from
`tsupport f`). The construction here is genuinely stronger: it shows that the
within-formula gradient itself is smooth at boundary points, no support
hypothesis required.

The two packagings agree pointwise on smooth interior-supported `f`; the new
one is the canonical extension.
-/

noncomputable section

open Bundle Manifold Set
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

/-- The within-partial of the chart pullback, viewed as a manifold-smooth
function `E → ℝ` on the chart target — including boundary points. -/
private lemma partialDerivWithin_scalarOnE_contMDiffOn_target
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (partialDerivWithin (E := E) (extChartAt I α).target j
        (scalarOnE (I := I) α f))
      (extChartAt I α).target := by
  have hUD : UniqueDiffOn ℝ (extChartAt I α).target :=
    uniqueDiffOn_extChartAt_target (I := I) α
  have hbase : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
      (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hf
  have hpartial : ContDiffOn ℝ ∞
      (partialDerivWithin (E := E) (extChartAt I α).target j
        (scalarOnE (I := I) α f))
      (extChartAt I α).target :=
    partialDerivWithin_contDiffOn_top_of_uniqueDiffOn (i := j) hbase hUD
  exact hpartial.contMDiffOn

/-- The chart map `extChartAt I α : M → E` is `C^∞` as a manifold map on the
entire chart source. Thin wrapper around `contMDiffOn_extChartAt`. -/
private lemma extChartAt_contMDiffOn_chart_source (α : M) :
    ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E) (chartAt H α).source :=
  contMDiffOn_extChartAt

/-- The chart map sends the entire chart source into the chart target. -/
private lemma chart_source_subset_preimage_target (α : M) :
    (chartAt H α).source ⊆
      (extChartAt I α : M → E) ⁻¹' (extChartAt I α).target := by
  intro x hx
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  exact (extChartAt I α).map_source hxsrc

/-- Each chart-coefficient `gradChartCoeffWithin g α f i` is `C^∞` on the
**entire** chart source `(chartAt H α).source` — including boundary points.
This is the with-boundary version's central technical advance over the
interior-only smoothness available in `Gradient.lean`. -/
lemma gradChartCoeffWithin_contMDiffOn_full
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞ (gradChartCoeffWithin (I := I) g α f i)
      (chartAt H α).source := by
  classical
  refine contMDiffOn_finset_sum (fun j _ => ?_)
  refine ContMDiffOn.mul ?_ ?_
  · have h1 : ContMDiffOn I 𝓘(ℝ) ∞
        (fun x => chartInvGramMatrix (I := I) g α x i j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j
    refine h1.mono ?_
    intro x hx
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hx
  · have hpartialM : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
        (partialDerivWithin (E := E) (extChartAt I α).target j
          (scalarOnE (I := I) α f))
        (extChartAt I α).target :=
      partialDerivWithin_scalarOnE_contMDiffOn_target (I := I) α hf j
    have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
        (chartAt H α).source :=
      extChartAt_contMDiffOn_chart_source (I := I) α
    have hsubset : (chartAt H α).source ⊆
        (extChartAt I α : M → E) ⁻¹' (extChartAt I α).target :=
      chart_source_subset_preimage_target (I := I) α
    exact hpartialM.comp hchart hsubset

/-- The chart-local within-representation `gradChartLocalWithin g α f`, viewed
as a tangent-bundle total-space section, is `C^∞` on the **entire** chart
source. -/
lemma gradChartLocalWithin_contMDiffOn_total_full
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradChartLocalWithin (I := I) g α f x))
      (chartAt H α).source := by
  classical
  have hcoeff : ∀ i, ContMDiffOn I 𝓘(ℝ) ∞
      (gradChartCoeffWithin (I := I) g α f i)
      (chartAt H α).source :=
    fun i => gradChartCoeffWithin_contMDiffOn_full (I := I) g α hf i
  have hbasis : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (chartBasisVecFiber (I := I) α i x))
      (chartAt H α).source := by
    intro i
    refine (chartBasisVec_contMDiffOn (I := I) α i).mono ?_
    intro x hx
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hx
  have hsmul : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x
        (gradChartCoeffWithin (I := I) g α f i x •
          chartBasisVecFiber (I := I) α i x))
      (chartAt H α).source := by
    intro i
    exact (hcoeff i).smul_section (hbasis i)
  exact ContMDiffOn.sum_section (fun i _ => hsmul i)

/-- On the chart source `(chartAt H α).source`, the intrinsic gradient
`gradFun g f` agrees pointwise with the chart-local within-formula
`gradChartLocalWithin g α f`. Restated from `gradChartLocalWithin_eq_gradFun`
in the form needed for the smoothness transfer below (no interior precondition
required). -/
private lemma gradFun_eq_gradChartLocalWithin_on_chart_source
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ∀ y ∈ (chartAt H α).source,
      gradFun (I := I) g f y = gradChartLocalWithin (I := I) g α f y := by
  intro y hy
  exact (gradChartLocalWithin_eq_gradFun (I := I) g α hf hy).symm

/-- The intrinsic gradient `gradFun g f`, viewed as a tangent-bundle
total-space section, is `C^∞` on every chart source `(chartAt H α).source` —
including boundary points. This is the local-to-global ingredient for the
global smoothness statement. -/
lemma gradFun_contMDiffOn_chart_source_full
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradFun (I := I) g f x))
      (chartAt H α).source := by
  have hsmooth :=
    gradChartLocalWithin_contMDiffOn_total_full (I := I) g α hf
  have hcongr := gradFun_eq_gradChartLocalWithin_on_chart_source
    (I := I) g α hf
  refine hsmooth.congr ?_
  intro y hy
  have h := hcongr y hy
  change TotalSpace.mk' E y (gradFun (I := I) g f y) =
    TotalSpace.mk' E y (gradChartLocalWithin (I := I) g α f y)
  rw [h]

/-- The intrinsic gradient `gradFun g f`, viewed as a tangent-bundle
total-space section, is `C^∞` on **all of `M`** — including boundary points.
The proof is local-to-global via `contMDiffOn_of_locally_contMDiffOn` applied
to the chart sources, each of which is open and centered at the point. -/
theorem gradFun_contMDiff_total_full
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradFun (I := I) g f x)) := by
  rw [← contMDiffOn_univ]
  refine contMDiffOn_of_locally_contMDiffOn ?_
  intro x _
  refine ⟨(chartAt H x).source, (chartAt H x).open_source,
    mem_chart_source H x, ?_⟩
  have hsm := gradFun_contMDiffOn_chart_source_full
    (I := I) g x hf
  have hset_eq : univ ∩ (chartAt H x).source = (chartAt H x).source :=
    Set.univ_inter _
  rw [hset_eq]
  exact hsm

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

open DifferentialGeometry.Integral.Measure

/-- **Smooth tangent-bundle section packaging of the gradient (half-space
model, no interior-support hypothesis).**

For any smooth Riemannian metric `g` on a smooth manifold-with-boundary `M`
modelled on the canonical Euclidean half-space `EuclideanHalfSpace n`, and any
smooth scalar function `f : M → ℝ`, the pointwise metric gradient `gradFun g f`
is `C^∞` as a tangent-bundle section on **all of `M`** — including boundary
points.

This is the with-boundary parallel of `gradFun_contMDiff_total` from the
boundaryless theory. No `tsupport f ⊆ I.interior M` hypothesis is required;
smoothness extends to boundary points because the chart-local representation
of the gradient via `partialDerivWithin (extChartAt I α).target` is smooth
already on the entire chart target (`partialDerivWithin_contDiffOn_top_of_uniqueDiffOn`).
-/
theorem grad_g_smooth_section_full
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {f : M → ℝ} (hf : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff (modelWithCornersEuclideanHalfSpace n)
      (modelWithCornersEuclideanHalfSpace n).tangent ∞
      (fun x : M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) x
        (gradFun (I := modelWithCornersEuclideanHalfSpace n) g f x)) :=
  gradFun_contMDiff_total_full
    (I := modelWithCornersEuclideanHalfSpace n) (M := M) g hf

/-- **The metric gradient as a globally smooth tangent-bundle section
(half-space model, no interior-support hypothesis).**

Equivalent packaging of `grad_g_smooth_section_full` as a
`ContMDiffSection`. The pointwise value `(grad_g_full_section g hf) x`
coincides with `gradFun g f x` for every `x : M`, including boundary points.
-/
def grad_g_full_section
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {f : M → ℝ} (hf : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ f) :
    Cₛ^∞⟮(modelWithCornersEuclideanHalfSpace n);
      EuclideanSpace ℝ (Fin n),
      (TangentSpace (modelWithCornersEuclideanHalfSpace n) : M → Type _)⟯ :=
  ⟨fun x : M => gradFun (I := modelWithCornersEuclideanHalfSpace n) g f x,
    grad_g_smooth_section_full (M := M) (n := n) g hf⟩

@[simp] lemma grad_g_full_section_apply
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {f : M → ℝ} (hf : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ f)
    (x : M) :
    (grad_g_full_section (M := M) (n := n) g hf :
      Cₛ^∞⟮(modelWithCornersEuclideanHalfSpace n);
        EuclideanSpace ℝ (Fin n),
        (TangentSpace (modelWithCornersEuclideanHalfSpace n) : M → Type _)⟯) x =
      gradFun (I := modelWithCornersEuclideanHalfSpace n) g f x := rfl

/-- The full smooth gradient section coincides with the underlying intrinsic
gradient `grad_g_with_boundary g f` as a fiber-valued function on `M`. -/
@[simp] lemma grad_g_full_section_coe
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {f : M → ℝ} (hf : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ f)
    (x : M) :
    (grad_g_full_section (M := M) (n := n) g hf :
      Cₛ^∞⟮(modelWithCornersEuclideanHalfSpace n);
        EuclideanSpace ℝ (Fin n),
        (TangentSpace (modelWithCornersEuclideanHalfSpace n) : M → Type _)⟯) x =
      grad_g_with_boundary (I := modelWithCornersEuclideanHalfSpace n) g f x := rfl

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry

end
