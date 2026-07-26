import DifferentialGeometry.Geometry.Operator.MetricSharpSmooth
import DifferentialGeometry.Tensor.RSTensor.CotangentRiemannian

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Smoothness bridge: `metricSharp` ↔ `cotangentSharp_gen`

The metric musical sharp appears in the codebase under two interfaces with
*different* domains:

* `metricSharp g x : Module.Dual ℝ (TangentSpace I x) → TangentSpace I x`
  (`Geometry/Operator/Operators.lean`), whose bundled smoothness over a smooth
  covector field is proved in `metricSharp_contMDiff_total`
  (`Geometry/Operator/MetricSharpSmooth.lean`);
* `cotangentSharp_gen g x : Tensor0SSpace 1 I x → TangentSpace I x`
  (`Tensor/RSTensor/CotangentRiemannian.lean`), which raises a realized `(0,1)`
  tensor and is the form consumed by the `T₂`/curvature-action contraction
  expansion `curvatureAction0SAt_orthoBasis_eq_sum`
  (`Evolution/NablaRiemannT2Bound.lean`) and by the sharp-parallelism hypothesis
  of `cotangentSharp_cov_eq_sharp_curry_of_mdiffAt`
  (`Tensor/RSTensor/Tensor0SRiemannian/Smooth.lean`).

Both are the Riesz raising map of `g`: they satisfy the *same* defining identity
`g(♯α, w) = α(w)`, with `α` interpreted either as a dual vector or (via
`cotangentToDual_gen`) as the dual of a realized one-form.  Hence they agree
through `cotangentToDual_gen`:

```
cotangentSharp_gen g x β = metricSharp g x (cotangentToDual_gen β).
```

Because `Module.Dual ℝ V` is reducibly `V →ₗ[ℝ] ℝ`, the field
`b ↦ cotangentToDual_gen (β b)` has exactly the type `Π b, TangentSpace I b →ₗ[ℝ] ℝ`
that `metricSharp_contMDiff_total` consumes.  This file packages that observation
into a smoothness statement for the `cotangentSharp_gen` field, in the `MDiffAt
(T% …)` shape required to discharge the `hSharp` hypothesis of the
sharp-parallelism.

## Main results

* `cotangentSharp_gen_eq_metricSharp` : the pointwise map identity
  `cotangentSharp_gen g x β = metricSharp g x (cotangentToDual_gen β)`.
* `cotangentSharp_gen_contMDiff_total` : on a boundaryless model, the bundled
  raised field `b ↦ TotalSpace.mk' E b (cotangentSharp_gen g b (β b))` is `C^∞`,
  given chart-basis smoothness of `b ↦ β b (fun _ => chartBasisVecFiber α j b)`.
* `cotangentSharp_gen_mdiffAt` : the `MDiffAt (T% …)` corollary, the exact
  predicate `cotangentSharp_cov_eq_sharp_curry_of_mdiffAt` needs.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The map identity.**  The two musical-sharp interfaces agree through
`cotangentToDual_gen`: raising a realized `(0,1)` tensor `β` with
`cotangentSharp_gen` equals applying the dual-vector sharp `metricSharp` to the
dual vector `cotangentToDual_gen β`.

Both sides are the Riesz representative of the same functional: `metricSharp`
satisfies `g(metricSharp g x α, w) = α w` (`inner_metricSharp`) and
`cotangentSharp_gen` satisfies `g(cotangentSharp_gen g x β, w) =
cotangentToDual_gen β w` (`cotangentSharp_inner_gen`).  With
`α = cotangentToDual_gen β` these coincide, so the representatives are equal by
injectivity of the flat map. -/
theorem cotangentSharp_gen_eq_metricSharp
    (g : SmoothRiemannianMetric I M) (x : M)
    (β : Tensor0SSpace 1 I x) :
    cotangentSharp_gen (I := I) g x β =
      metricSharp (I := I) g x (cotangentToDual_gen (I := I) β) := by
  apply metricFlatLinear_injective (I := I) g x
  ext w
  change g.inner x (cotangentSharp_gen (I := I) g x β) w =
    g.inner x (metricSharp (I := I) g x (cotangentToDual_gen (I := I) β)) w
  rw [cotangentSharp_inner_gen (I := I) g x β w,
    inner_metricSharp (I := I) g x (cotangentToDual_gen (I := I) β) w]

/-- The chart-basis component of the dual field `b ↦ cotangentToDual_gen (β b)`
is the one-form's evaluation on the chart-basis frame vector. -/
theorem cotangentToDual_gen_chartBasis_eval
    (α : M) (j : Fin (Module.finrank ℝ E))
    (β : Π b : M, Tensor0SSpace 1 I b) (b : M) :
    cotangentToDual_gen (I := I) (β b) (chartBasisVecFiber (I := I) α j b) =
      β b (fun _ : Fin 1 => chartBasisVecFiber (I := I) α j b) :=
  cotangentToDual_apply_gen (I := I) (β b) (chartBasisVecFiber (I := I) α j b)

/-- **Smoothness of the `cotangentSharp_gen` field.**  On a boundaryless model, if
the chart-basis evaluations `b ↦ β b (fun _ => chartBasisVecFiber α j b)` of a
realized one-form field `β` are `C^∞` on each chart source, then the raised
tangent field `b ↦ cotangentSharp_gen g b (β b)` is a smooth tangent-bundle
section.

This is `metricSharp_contMDiff_total` applied to the dual covector field
`cv b := cotangentToDual_gen (β b)` (which has type `Π b, TangentSpace I b →ₗ[ℝ] ℝ`
because `Module.Dual ℝ V` is reducibly `V →ₗ[ℝ] ℝ`), transported through the map
identity `cotangentSharp_gen_eq_metricSharp`. -/
theorem cotangentSharp_gen_contMDiff_total [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {β : Π b : M, Tensor0SSpace 1 I b}
    (hβ : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => β b (fun _ : Fin 1 => chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M =>
        TotalSpace.mk' E b (cotangentSharp_gen (I := I) g b (β b))) := by
  -- The dual covector field; `Module.Dual ℝ (TangentSpace I b) = TangentSpace I b →ₗ[ℝ] ℝ`.
  set cv : Π b : M, TangentSpace I b →ₗ[ℝ] ℝ :=
    fun b => cotangentToDual_gen (I := I) (β b) with hcv
  -- The chart-basis components of `cv` are the one-form evaluations, hence smooth.
  have hcv_smooth : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => cv b (chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source := by
    intro α j
    have heq :
        (fun b : M => cv b (chartBasisVecFiber (I := I) α j b)) =
          fun b : M => β b (fun _ : Fin 1 => chartBasisVecFiber (I := I) α j b) := by
      funext b
      exact cotangentToDual_gen_chartBasis_eval (I := I) α j β b
    rw [heq]
    exact hβ α j
  -- Smoothness of the bundled `metricSharp` field of `cv`.
  have hmetric :=
    metricSharp_contMDiff_total (I := I) g (cv := cv) hcv_smooth
  -- Transport through the map identity `cotangentSharp_gen = metricSharp ∘ cotangentToDual_gen`.
  have hsection_eq :
      (fun b : M =>
          TotalSpace.mk' E b (cotangentSharp_gen (I := I) g b (β b))) =
        fun b : M =>
          TotalSpace.mk' E b (metricSharp (I := I) g b (cv b)) := by
    funext b
    change TotalSpace.mk' E b (cotangentSharp_gen (I := I) g b (β b)) =
      TotalSpace.mk' E b (metricSharp (I := I) g b (cotangentToDual_gen (I := I) (β b)))
    rw [cotangentSharp_gen_eq_metricSharp (I := I) g b (β b)]
  rw [hsection_eq]
  exact hmetric

/-- **The `MDiffAt (T% …)` corollary.**  The exact differentiability predicate the
sharp-parallelism `cotangentSharp_cov_eq_sharp_curry_of_mdiffAt`
(`Tensor/RSTensor/Tensor0SRiemannian/Smooth.lean`) needs for its `hSharp`
hypothesis: the raised field is `MDifferentiableAt` (in the total-space embedding)
at every point, from chart-basis smoothness of the one-form field. -/
theorem cotangentSharp_gen_mdiffAt [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {β : Π b : M, Tensor0SSpace 1 I b}
    (hβ : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => β b (fun _ : Fin 1 => chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source)
    (x : M) :
    MDiffAt (T% (fun y : M => cotangentSharp_gen (I := I) g y (β y))) x :=
  (cotangentSharp_gen_contMDiff_total (I := I) g hβ).contMDiffAt.mdifferentiableAt
    (by simp)

end DivergenceTheorem
end Integral
end DifferentialGeometry
