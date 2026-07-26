import DifferentialGeometry.Geometry.Boundary.OutwardNormal

/-!
# Orientation-preservation of chart transitions on a manifold-with-boundary

For a smooth manifold-with-boundary `M` modelled on `(E, H, I)` with
`[HasSmoothBoundary E H I]`, this file introduces the `HasOrientableBoundary M`
typeclass, which records the structural fact that the chart transitions of `M`,
read against the chart-coordinate "inward direction" `inwardCoordE` from the
`HasSmoothBoundary` typeclass, agree on the inward side of the boundary up to
boundary-tangent corrections with strictly positive scalings.

Concretely, for any two boundary points `α₀, α₁ : M` whose chart sources both
contain a boundary point `y : BoundaryManifold I M`, the typeclass asserts that

  `inwardCoordAt α₀ y - c • inwardCoordAt α₁ y ∈ Set.range (dincl y).toLinearMap`

for some `c > 0`. Geometrically: the chart-α₀ inward-direction representative
at `y` differs from a positive multiple of the chart-α₁ inward-direction
representative by a vector tangent to the boundary submanifold.

This is the abstract analog of the standard fact that, for a smooth
manifold-with-boundary modelled on a Euclidean half-space, chart transitions
have positive Jacobian determinant on the boundary stratum. The canonical
instance `instHasOrientableBoundary_self_EuclideanHalfSpace` in
`EuclideanHalfSpaceInstance.lean` verifies orientability for the self-charted
model space `EuclideanHalfSpace n`; the general case for arbitrary `M`
modelled on `EuclideanHalfSpace n` reduces to the standard "positive Jacobian
of half-space chart transitions" theorem and is documented as a gap there.
The typeclass abstracts away the concrete `e_0`-component reasoning and
exposes only what's needed by downstream chart-invariance arguments for the
outward unit normal vector field.

## Main definitions

* `HasOrientableBoundary M` — the orientation typeclass.

## Main results

* `inwardCoord_chart_consistent` — convenience accessor that retrieves the
  orientation property from the typeclass.
* `inwardCoord_chart_consistent_self` — degenerate case `α₀ = α₁` (with
  `c = 1`).

## Scope

The typeclass is parameterised by `M` because chart transitions are defined on
overlapping pairs of charts, and the property depends on the entire chart
atlas, not just the model `(E, H, I)`. This matches the parameterisation of
`IsManifold I ∞ M` and `ChartedSpace H M`.

For models with no boundary (i.e., `[I.Boundaryless]`), `BoundaryManifold I M`
is empty, the universal quantifier becomes vacuous, and every `M` trivially
satisfies the typeclass; downstream code may install the trivial instance via
`Boundaryless` arguments without further work.
-/

noncomputable section

open Set Function Topology Bundle Manifold MeasureTheory
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

/-- Chart-transition orientation preservation.

For a smooth manifold-with-boundary `M` modelled on `(E, H, I)` with
`[HasSmoothBoundary E H I]`, this typeclass asserts that any two chart
trivialisations at the manifold base points map the model-side inward
direction `inwardCoordE` to vectors in the ambient tangent space at any
boundary point that lie on the **same side** of the boundary tangent space
`Set.range (dincl y)`. Equivalently: the two chart-α inward-direction
representatives at `y` differ by a strictly positive scalar modulo a
boundary-tangent vector at `y`.

This is the abstract analog of "chart transitions on a manifold-with-boundary
have positive Jacobian determinant on the boundary stratum" (a standard fact
for smooth manifolds-with-boundary modelled on Euclidean half-spaces, verified
in `EuclideanHalfSpaceInstance.lean`).

Use sites supplying this typeclass instance enable chart-invariance derivations
for the outward unit normal vector field constructed in `OutwardNormal.lean`.
The "modulo boundary-tangent" formulation is the most usable for the
chart-invariance proof of the outward unit normal: in the orthogonal
decomposition `T_y M = range (dincl y) ⊕ normalSubspace g y`, the
`normalSubspace`-component of `inwardCoordAt α₀ y` is a positive multiple of
the `normalSubspace`-component of `inwardCoordAt α₁ y`.
-/
class HasOrientableBoundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] : Prop
where

  inwardCoord_chart_consistent :
    ∀ (α₀ α₁ : BoundaryManifold I M) (y : BoundaryManifold I M),
      (y : M) ∈ (chartAt H (α₀ : M)).source →
      (y : M) ∈ (chartAt H (α₁ : M)).source →
      ∃ c : ℝ, 0 < c ∧
        inwardCoordAt (M := M) α₀ y - c • inwardCoordAt (M := M) α₁ y ∈
          Set.range (dincl (M := M) y).toLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

/-- Convenience accessor for the orientation property packaged in the
`HasOrientableBoundary` typeclass. -/
theorem inwardCoord_chart_consistent
    [HasOrientableBoundary (E := E) (H := H) (I := I) M]
    (α₀ α₁ : BoundaryManifold I M) (y : BoundaryManifold I M)
    (hα₀ : (y : M) ∈ (chartAt H (α₀ : M)).source)
    (hα₁ : (y : M) ∈ (chartAt H (α₁ : M)).source) :
    ∃ c : ℝ, 0 < c ∧
      inwardCoordAt (M := M) α₀ y - c • inwardCoordAt (M := M) α₁ y ∈
        Set.range (dincl (M := M) y).toLinearMap :=
  HasOrientableBoundary.inwardCoord_chart_consistent α₀ α₁ y hα₀ hα₁

/-- Self-coincidence: when `α₀ = α₁`, the inward-direction representatives at
`y` agree, so `c = 1` and the difference is `0 ∈ range (dincl y)`. This holds
without any orientation hypothesis. -/
theorem inwardCoord_chart_consistent_self (α : BoundaryManifold I M)
    (y : BoundaryManifold I M) :
    ∃ c : ℝ, 0 < c ∧
      inwardCoordAt (M := M) α y - c • inwardCoordAt (M := M) α y ∈
        Set.range (dincl (M := M) y).toLinearMap := by
  refine ⟨1, by norm_num, ?_⟩
  simp only [one_smul, sub_self]
  exact ⟨0, map_zero _⟩

/-- **Chart-invariance of the parameterised outward unit normal.** Under the
orientation typeclass, the parameterised outward unit normal at a boundary
point is independent of which chart base point is used to read the inward
direction. -/
theorem outwardNormalAt_chart_invariance
    [HasOrientableBoundary (E := E) (H := H) (I := I) M]
    (g : Measure.SmoothRiemannianMetric I M) (α₀ α₁ : BoundaryManifold I M)
    {y : BoundaryManifold I M}
    (hy_α₀ : (y : M) ∈ (chartAt H (α₀ : M)).source)
    (hy_α₁ : (y : M) ∈ (chartAt H (α₁ : M)).source) :
    outwardNormalAt (M := M) g α₀ y = outwardNormalAt (M := M) g α₁ y := by
  obtain ⟨c, hc, h_w⟩ := inwardCoord_chart_consistent (M := M) α₀ α₁ y hy_α₀ hy_α₁
  exact outwardNormalAt_chart_invariance_of_orientation
    (M := M) g α₀ α₁ y hc h_w

/-- **Coincidence of the parameterised and the global outward unit normal on a
chart neighbourhood.** Under the orientation typeclass, whenever `y : BoundaryManifold I M`
satisfies `(y : M) ∈ (chartAt H (α₀ : M)).source`, the parameterised outward
unit normal `outwardNormalAt α₀ g y` coincides with the global outward unit
normal `outwardNormal g y`.

This is the bridge between the chart-α₀-local smoothness statement
(parameterised by a fixed reference base point `α₀`) and the global section
`y ↦ outwardNormal g y`: on a neighbourhood of every chosen base point `α₀`,
the two functions agree, so chart-α₀-local smoothness transfers to the
global section. -/
theorem outwardNormalAt_eq_outwardNormal_on_chart
    [HasOrientableBoundary (E := E) (H := H) (I := I) M]
    (g : Measure.SmoothRiemannianMetric I M) (α₀ : BoundaryManifold I M)
    {y : BoundaryManifold I M}
    (hy : (y : M) ∈ (chartAt H (α₀ : M)).source) :
    outwardNormalAt (M := M) g α₀ y = outwardNormal (M := M) g y := by
  have hy_self : (y : M) ∈ (chartAt H (y : M)).source := mem_chart_source H (y : M)
  have h_chart_inv :
      outwardNormalAt (M := M) g α₀ y = outwardNormalAt (M := M) g y y :=
    outwardNormalAt_chart_invariance (M := M) g α₀ y hy hy_self
  rw [h_chart_inv, outwardNormalAt_self]

/-- **Smoothness of the global outward unit normal as a bundle section.** The
section `y ↦ TotalSpace.mk' E (boundaryInclusion I M y) (outwardNormal g y)`
of the pulled-back ambient tangent bundle along the boundary inclusion is
`C^∞`. -/
theorem outwardNormal_contMDiff
    [HasOrientableBoundary (E := E) (H := H) (I := I) M]
    (g : Measure.SmoothRiemannianMetric I M) :
    ContMDiff hI.boundaryI (I.prod 𝓘(ℝ, E)) ∞
      (fun x : BoundaryManifold I M =>
        TotalSpace.mk' E (boundaryInclusion I M x)
          (outwardNormal (M := M) g x)) := by
  intro x₀
  have h_smooth_at : ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' E (b : M) (outwardNormalAt (M := M) g x₀ b)) x₀ :=
    outwardNormalAt_section_contMDiffAt (M := M) g x₀
  set U : Set (BoundaryManifold I M) :=
    Subtype.val ⁻¹' (chartAt H (x₀ : M)).source with hU_def
  have hU_open : IsOpen U :=
    (chartAt H (x₀ : M)).open_source.preimage continuous_subtype_val
  have hU_mem : x₀ ∈ U := by
    change (x₀ : M) ∈ (chartAt H (x₀ : M)).source
    exact mem_chart_source H (x₀ : M)
  have hU_nhds : U ∈ 𝓝 x₀ := hU_open.mem_nhds hU_mem
  have h_eventually :
      (fun b : BoundaryManifold I M =>
          TotalSpace.mk' E (boundaryInclusion I M b)
            (outwardNormal (M := M) g b)) =ᶠ[𝓝 x₀]
        (fun b : BoundaryManifold I M =>
          TotalSpace.mk' E (b : M) (outwardNormalAt (M := M) g x₀ b)) := by
    refine Filter.eventually_of_mem hU_nhds ?_
    intro b hb_mem
    have h_eq : outwardNormalAt (M := M) g x₀ b = outwardNormal (M := M) g b :=
      outwardNormalAt_eq_outwardNormal_on_chart (M := M) g x₀ hb_mem
    change TotalSpace.mk' E (boundaryInclusion I M b) (outwardNormal (M := M) g b) =
        TotalSpace.mk' E (b : M) (outwardNormalAt (M := M) g x₀ b)
    simp only [boundaryInclusion_apply, h_eq]
  exact h_smooth_at.congr_of_eventuallyEq h_eventually

/-- **Continuity of the global outward unit normal as a bundle section.** The
section `y ↦ TotalSpace.mk' E (boundaryInclusion I M y) (outwardNormal g y)`
of the pulled-back ambient tangent bundle along the boundary inclusion is
continuous. -/
theorem outwardNormal_continuous
    [HasOrientableBoundary (E := E) (H := H) (I := I) M]
    (g : Measure.SmoothRiemannianMetric I M) :
    Continuous (fun x : BoundaryManifold I M =>
      TotalSpace.mk' E (boundaryInclusion I M x) (outwardNormal (M := M) g x)) :=
  (outwardNormal_contMDiff (M := M) g).continuous

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
