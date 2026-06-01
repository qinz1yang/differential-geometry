import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.InducedMetric
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.SurfaceMeasure
import DifferentialGeometry.Geometry.Laplacian

/-!
# The boundary Laplacian on a Riemannian manifold-with-boundary

Given a smooth manifold `M` modelled on `(E, H, I)` with
`[hI : HasSmoothBoundary E H I]`, and a smooth Riemannian metric `g` on the
tangent bundle of `M`, this file defines the *boundary Laplacian*
`Δ^∂_g f` of a smooth scalar function `f : BoundaryManifold I M → ℝ`.

The boundary submanifold inherits:

* a `T2Space` structure (when `M` is `T2`);
* a `SigmaCompactSpace` structure (when `M` is σ-compact);
* the boundary model `hI.boundaryI` is automatically *boundaryless*;
* the induced (pull-back) Riemannian metric `inducedMetric g`.

The boundary Laplacian is then defined as the ambient Laplace–Beltrami operator
`Δ_g` of the induced metric on the boundary submanifold:

$$\Delta^\partial_g f := \Delta_{g_\partial} f.$$

## Main definitions

* `boundaryLaplacian g hf` — the boundary Laplacian of a smooth scalar
  function `f` on the boundary submanifold, with smoothness witness `hf`.

## Main results

* `boundaryLaplacian_def` — unfolding lemma identifying the boundary
  Laplacian with `Δ_g` of the induced metric.
* `boundaryLaplacian_contMDiff` — smoothness of the boundary Laplacian.
* `boundaryLaplacian_add` — `ℝ`-linearity (sum rule) of the boundary
  Laplacian.
* `boundaryLaplacian_const` — the boundary Laplacian of a constant vanishes.
* `boundaryLaplacian_eq_zero_of_isEmpty_boundaryH` — when the ambient model
  is itself boundaryless, the boundary submanifold is empty and the boundary
  Laplacian is identically zero.

## Sign convention

The geometer convention `Δ = div ∘ grad` is inherited from `Δ_g`. With this
convention the boundary Laplacian is a non-positive operator on a closed
boundary, so its spectrum lies in `(-∞, 0]`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

open DifferentialGeometry.Integral.Measure

/-- The boundary Laplacian `Δ^∂_g f` of a smooth scalar function
`f : BoundaryManifold I M → ℝ` (with smoothness witness `hf`), defined as the
ambient Laplace–Beltrami operator `Δ_g` of the induced metric on the boundary
submanifold. -/
def boundaryLaplacian
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : BoundaryManifold I M → ℝ}
    (hf : ContMDiff hI.boundaryI 𝓘(ℝ, ℝ) ∞ f) :
    BoundaryManifold I M → ℝ :=
  Δ_g (I := hI.boundaryI) (inducedMetric (I := I) (M := M) g) hf

/-- Unfolding lemma: the boundary Laplacian is the ambient Laplacian of the
induced metric. -/
@[simp] lemma boundaryLaplacian_def
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : BoundaryManifold I M → ℝ}
    (hf : ContMDiff hI.boundaryI 𝓘(ℝ, ℝ) ∞ f)
    (x : BoundaryManifold I M) :
    boundaryLaplacian (I := I) (M := M) g hf x =
      Δ_g (I := hI.boundaryI) (inducedMetric (I := I) (M := M) g) hf x := rfl

/-- The boundary Laplacian of a smooth function is `C^∞`. -/
theorem boundaryLaplacian_contMDiff
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : BoundaryManifold I M → ℝ}
    (hf : ContMDiff hI.boundaryI 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff hI.boundaryI 𝓘(ℝ, ℝ) ∞
      (boundaryLaplacian (I := I) (M := M) g hf) :=
  Δ_g_contMDiff (I := hI.boundaryI) (inducedMetric (I := I) (M := M) g) hf

/-- The boundary Laplacian of a sum of smooth functions equals the sum of the
boundary Laplacians. -/
theorem boundaryLaplacian_add
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f h : BoundaryManifold I M → ℝ}
    (hf : ContMDiff hI.boundaryI 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff hI.boundaryI 𝓘(ℝ, ℝ) ∞ h)
    (x : BoundaryManifold I M) :
    boundaryLaplacian (I := I) (M := M) g (hf.add hh) x =
      boundaryLaplacian (I := I) (M := M) g hf x +
        boundaryLaplacian (I := I) (M := M) g hh x :=
  Δ_g_add (I := hI.boundaryI) (inducedMetric (I := I) (M := M) g) hf hh x

/-- The boundary Laplacian of a constant function vanishes. -/
@[simp] theorem boundaryLaplacian_const
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (c : ℝ)
    (x : BoundaryManifold I M) :
    boundaryLaplacian (I := I) (M := M) g
      (contMDiff_const : ContMDiff hI.boundaryI 𝓘(ℝ, ℝ) ∞
        (fun _ : BoundaryManifold I M => c)) x = 0 :=
  Δ_g_const (I := hI.boundaryI) (inducedMetric (I := I) (M := M) g) c x

/-- When the ambient model `I` is boundaryless, the boundary topological model
`hI.boundaryH` is empty (by `HasSmoothBoundary.boundaryH_isEmpty_of_boundaryless`)
and so is the boundary submanifold `BoundaryManifold I M` (by
`BoundaryManifold.isEmpty_of_isEmpty_boundaryH`). The boundary Laplacian is
therefore identically zero on the empty type. -/
theorem boundaryLaplacian_eq_zero_of_boundaryless
    [I.Boundaryless] [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : BoundaryManifold I M → ℝ}
    (hf : ContMDiff hI.boundaryI 𝓘(ℝ, ℝ) ∞ f) :
    boundaryLaplacian (I := I) (M := M) g hf = 0 := by
  haveI : IsEmpty hI.boundaryH :=
    HasSmoothBoundary.boundaryH_isEmpty_of_boundaryless I
  haveI : IsEmpty (BoundaryManifold I M) :=
    BoundaryManifold.isEmpty_of_isEmpty_boundaryH (I := I)
  funext x
  exact (IsEmpty.false x).elim

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
