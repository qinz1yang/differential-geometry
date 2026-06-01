import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.LocalFormula
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.ChartInvariance
import DifferentialGeometry.Integral.DivergenceTheorem.LocalFormula
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Global divergence on a smooth Riemannian manifold with boundary

For a smooth Riemannian metric `g` on the tangent bundle of a smooth manifold
`M` whose model `I` may carry a non-trivial boundary, this file builds the
global with-boundary divergence operator
`divergence_g_with_boundary g X : M → ℝ` and proves its core properties.

The construction parallels the boundaryless `divergence_g` from
`DivergenceTheorem/LocalFormula.lean`, using the chart-local with-boundary
formula `localDivergenceWithin g (chartAt H x) X` from
`WithBoundary/LocalFormula.lean`. The chart is taken at `x` itself, so the
chart-local formula is well-defined at `x` for every `x : M`.

## Main definition

* `divergence_g_with_boundary g X x` — the global with-boundary divergence
  evaluated at `x`, defined as `localDivergenceWithin g x X x`.

## Main results

* `voss_weyl_divergence_with_boundary_formula` — Voss–Weyl identity in any
  chart at any **interior** point of the chart base set: the global
  with-boundary divergence equals the chart-local within-divergence in that
  chart.
* `divergence_g_with_boundary_eq_divergence_g_of_isInteriorPoint` — agreement
  with the boundaryless `divergence_g` at every manifold-interior point.
* `divergence_g_with_boundary_contMDiffOn_interior` — `C^∞` smoothness of the
  global with-boundary divergence on the manifold interior `I.interior M`.
* `divergence_g_with_boundary_continuousOn_interior` — continuity corollary on
  the manifold interior.

## Architectural notes

* On a boundary point the global definition still produces a real number — the
  chart-local within-divergence at the chart at that point is well-posed
  thanks to `uniqueDiffOn_extChartAt_target` — but the divergence theorem
  introduces a boundary integral term, so the value at boundary points should
  be interpreted with care. The smoothness theorem here is therefore stated
  on `I.interior M`.

* Chart invariance of `localDivergenceWithin` is only proved on the
  manifold-interior overlap of two chart sources (see
  `WithBoundary/ChartInvariance.lean`). The Voss–Weyl identity below
  consequently restricts to interior points.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

/-- Global divergence operator on a smooth Riemannian manifold (possibly with
boundary). At each point `x`, evaluated using the chart-local within-divergence
in the chart at `x`. On manifold-interior points, this agrees with the
boundaryless `divergence_g`; on boundary points, it is well-defined (the chart
target is locally a half-space, and `partialDerivWithin` is well-defined there)
but should be treated with care — the with-boundary divergence theorem
introduces a boundary integral term. -/
def divergence_g_with_boundary
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : M → ℝ :=
  fun x => localDivergenceWithin (I := I) g x X x

@[simp] lemma divergence_g_with_boundary_def
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergence_g_with_boundary (I := I) g X x =
      localDivergenceWithin (I := I) g x X x := rfl

/-- Voss–Weyl-type identity: in any chart at `α`, the global with-boundary
divergence equals the chart-α local within-divergence at any **interior** point
`x` in the chart source. This is the manifold-interior chart-invariance
re-expressed via the global definition. -/
theorem voss_weyl_divergence_with_boundary_formula [T2Space M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {x : M} (hx_α : x ∈ (chartAt H α).source) (hx_int : x ∈ I.interior M) :
    divergence_g_with_boundary (I := I) g X x =
      localDivergenceWithin (I := I) g α X x := by
  unfold divergence_g_with_boundary
  exact localDivergenceWithin_chart_invariance
    (I := I) g x α X (mem_chart_source H x) hx_α hx_int

/-- On `I.interior M`, the with-boundary divergence agrees with the
boundaryless `divergence_g`. This is automatic at every interior point because
both `localDivergenceWithin g x X` and `localDivergence g x X` agree there
(by `localDivergenceWithin_eq_localDivergence_of_isInteriorPoint`), with the
convenient global-divergence packaging on both sides. -/
theorem divergence_g_with_boundary_eq_divergence_g_of_isInteriorPoint
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {x : M} (hx_int : x ∈ I.interior M) :
    divergence_g_with_boundary (I := I) g X x = divergence_g (I := I) g X x := by
  unfold divergence_g_with_boundary
  rw [divergence_g_def]
  exact localDivergenceWithin_eq_localDivergence_of_isInteriorPoint
    (I := I) g x X (mem_chart_source H x) hx_int

/-- The interior of the manifold is open. Direct application of
`ModelWithCorners.isOpen_interior` at `n = ∞` (which satisfies `n ≠ 0`). -/
private lemma isOpen_interior_M : IsOpen (I.interior M) :=
  I.isOpen_interior (M := M) (n := ∞)
    (by exact (by decide : (∞ : WithTop ℕ∞) ≠ 0))

/-- For any `x ∈ I.interior M`, the open neighborhood
`(chartAt H x).source ∩ I.interior M` is contained in the chart source at `x`,
contains `x`, and consists of interior points. -/
private lemma chart_source_inter_interior_open_nhd (x : M) (hx_int : x ∈ I.interior M) :
    IsOpen ((chartAt H x).source ∩ I.interior M) ∧
      x ∈ (chartAt H x).source ∩ I.interior M := by
  refine ⟨?_, ?_, ?_⟩
  · exact (chartAt H x).open_source.inter isOpen_interior_M
  · exact mem_chart_source H x
  · exact hx_int

/-- On the open set `(chartAt H x).source ∩ I.interior M`, the global
with-boundary divergence agrees pointwise with the chart-`x` local
within-divergence `localDivergenceWithin g x X`. This is the key local
agreement underlying the smoothness proof. -/
private lemma divergence_g_with_boundary_eq_localDivergenceWithin_on_chart
    [T2Space M] (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    ∀ y ∈ (chartAt H x).source ∩ I.interior M,
      divergence_g_with_boundary (I := I) g X y =
        localDivergenceWithin (I := I) g x X y := by
  intro y hy
  exact voss_weyl_divergence_with_boundary_formula
    (I := I) g x X hy.1 hy.2

/-- The chart-`x` local within-divergence is `C^∞` on
`(chartAt H x).source ∩ I.interior M`. Direct restriction from
`localDivergenceWithin_contMDiffOn`. -/
private lemma localDivergenceWithin_contMDiffOn_chart_inter_interior
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    ContMDiffOn I 𝓘(ℝ) ∞ (localDivergenceWithin (I := I) g x X)
      ((chartAt H x).source ∩ I.interior M) :=
  (localDivergenceWithin_contMDiffOn (I := I) g x X).mono Set.inter_subset_left

/-- The global with-boundary divergence is `C^∞` on
`(chartAt H x).source ∩ I.interior M` for every `x ∈ I.interior M`. Combines
the agreement with the chart-`x` local within-divergence and the smoothness of
the latter. -/
private lemma divergence_g_with_boundary_contMDiffOn_chart_inter_interior
    [T2Space M] (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    ContMDiffOn I 𝓘(ℝ) ∞ (divergence_g_with_boundary (I := I) g X)
      ((chartAt H x).source ∩ I.interior M) := by
  have hsmooth :=
    localDivergenceWithin_contMDiffOn_chart_inter_interior (I := I) g X x
  have hcongr := divergence_g_with_boundary_eq_localDivergenceWithin_on_chart
    (I := I) g X x
  exact hsmooth.congr hcongr

/-- The with-boundary divergence is `C^∞` on `I.interior M`. The proof is
local-to-global via the Voss–Weyl identity in the chart at each interior
point. -/
theorem divergence_g_with_boundary_contMDiffOn_interior [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiffOn I 𝓘(ℝ) ∞ (divergence_g_with_boundary (I := I) g X)
      (I.interior M) := by
  refine contMDiffOn_of_locally_contMDiffOn ?_
  intro x hx_int
  refine ⟨(chartAt H x).source, ?_, ?_, ?_⟩
  · exact (chartAt H x).open_source
  · exact mem_chart_source H x
  · have hsm := divergence_g_with_boundary_contMDiffOn_chart_inter_interior
      (I := I) g X x
    have hset_eq : I.interior M ∩ (chartAt H x).source =
        (chartAt H x).source ∩ I.interior M := by
      rw [Set.inter_comm]
    rw [hset_eq]
    exact hsm

/-- The with-boundary divergence is continuous on `I.interior M`. Direct
corollary of `divergence_g_with_boundary_contMDiffOn_interior`. -/
theorem divergence_g_with_boundary_continuousOn_interior [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContinuousOn (divergence_g_with_boundary (I := I) g X) (I.interior M) :=
  (divergence_g_with_boundary_contMDiffOn_interior (I := I) g X).continuousOn

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
