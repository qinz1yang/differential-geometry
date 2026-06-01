import DifferentialGeometry.Metric.Basic
import DifferentialGeometry.Integral.Connection.Ricci
import DifferentialGeometry.PDE.DeTurck.VectorField
import DifferentialGeometry.PDE.DeTurck.LieDerivativeMetric

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-! ## Smoothness-index bridge

Both `DifferentialGeometry.SmoothRiemannianMetric I M` (from
`Metric/Basic.lean`) and `Integral.Measure.SmoothRiemannianMetric I M`
(from `Integral/Measure/ChartDensity.lean`) are now aliased to
`Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I)`; the bridge
is a definitional identity. -/

/-- Identify a smooth Riemannian metric across the two project aliases
(`DifferentialGeometry.SmoothRiemannianMetric` and
`Integral.Measure.SmoothRiemannianMetric`), both of which now reduce to
`Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I)`. -/
noncomputable def smoothRiemannianMetricToInfty
    (g : SmoothRiemannianMetric I M) :
    Integral.Measure.SmoothRiemannianMetric I M := g

/-- Auxiliary linear map: `v ↦ (lieDerivMetric g W x v).toContinuousLinearMap`,
viewed as a `LinearMap` from `T_x M` to the continuous-functional space
`T_x M →L[ℝ] ℝ`. -/
private noncomputable def lieDerivMetricClmAux
    (g : Integral.Measure.SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    TangentSpace I x →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  { toFun := fun v =>
      LinearMap.toContinuousLinearMap (lieDerivMetric (I := I) g W x v)
    map_add' := fun v v' => by
      ext w
      have := (lieDerivMetric (I := I) g W x).map_add v v'
      have happ := congrArg
        (fun (φ : TangentSpace I x →ₗ[ℝ] ℝ) => φ w) this
      set_option linter.unnecessarySimpa false in
      simpa [LinearMap.add_apply, ContinuousLinearMap.add_apply,
             LinearMap.coe_toContinuousLinearMap'] using happ
    map_smul' := fun c v => by
      ext w
      have := (lieDerivMetric (I := I) g W x).map_smul c v
      have happ := congrArg
        (fun (φ : TangentSpace I x →ₗ[ℝ] ℝ) => φ w) this
      set_option linter.unnecessarySimpa false in
      simpa [LinearMap.smul_apply, ContinuousLinearMap.smul_apply,
             LinearMap.coe_toContinuousLinearMap', smul_eq_mul] using happ }

@[simp] private lemma lieDerivMetricClmAux_apply
    (g : Integral.Measure.SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M)
    (v w : TangentSpace I x) :
    lieDerivMetricClmAux (I := I) g W x v w =
      lieDerivMetric (I := I) g W x v w := rfl

/-- Continuous-linear upgrade of the pointwise Lie-derivative metric.

Given a smooth Riemannian metric `g` (in the `⊤`-aliased
`DifferentialGeometry.SmoothRiemannianMetric` form) and a smooth tangent
vector field `W`, this is the continuous bilinear form
`T_x M →L[ℝ] T_x M →L[ℝ] ℝ` obtained from
`lieDerivMetric g W x : T_x M →ₗ[ℝ] T_x M →ₗ[ℝ] ℝ` by
`LinearMap.toContinuousLinearMap` in each slot.  Internally, `g` is
downgraded to the `∞`-aliased form expected by `lieDerivMetric`. -/
noncomputable def lieDerivMetricClm
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    (lieDerivMetricClmAux (I := I) (smoothRiemannianMetricToInfty (I := I) g) W x)

/-- The CLM upgrade agrees with the underlying linear-map evaluation. -/
theorem lieDerivMetricClm_apply
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) (v w : TangentSpace I x) :
    lieDerivMetricClm (I := I) g W x v w
      = lieDerivMetric (I := I) (smoothRiemannianMetricToInfty (I := I) g) W x v w := rfl

/-- The right-hand side of the Ricci–DeTurck flow:
`-2 · Ric(g) + 𝓛_{W(g, g_bg)} g`, as a continuous bilinear form on `T_x M`.

Here `W(g, g_bg) = deTurckVF g g_bg` is the DeTurck vector field — the metric
`g`-trace of the connection difference `∇^{LC}(g) − ∇^{LC}(g_bg)` — and
`𝓛_{W(g, g_bg)} g` is the corresponding Lie-derivative deformation of `g`.

The two metric arguments are presented in the `⊤`-aliased
`DifferentialGeometry.SmoothRiemannianMetric` form; internally they are
downgraded to the `∞`-aliased form expected by `ricciTensor`, `deTurckVF`,
and `lieDerivMetric`. -/
noncomputable def deTurckRicciRHS
    (g_bg g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (-2 : ℝ) • ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x +
    lieDerivMetricClm (I := I) g
      (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g)
        (smoothRiemannianMetricToInfty (I := I) g_bg)) x

end RicciFlow
end PDE
end DifferentialGeometry
