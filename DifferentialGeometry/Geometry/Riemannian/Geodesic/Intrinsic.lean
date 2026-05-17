import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Existence
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Uniqueness
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Velocity
import DifferentialGeometry.Geometry.Riemannian.Geodesic.VelocityChart
import DifferentialGeometry.Geometry.Riemannian.Curve.CovDerivAlong
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

set_option linter.unusedSectionVars false

/-!
# Smoothness packaging for the velocity lift along a `C²` curve

For a curve `γ : ℝ → M` with `ContMDiff 𝓘(ℝ, ℝ) I 2 γ`, the intrinsic
velocity lift `t ↦ ⟨γ t, velocity γ t⟩ : TangentBundle I M` is `C¹` as
a manifold map. This is the smoothness hypothesis required by the
chart-local covariant-derivative operator
`covDerivAlong` (see `Geometry/Riemannian/Curve/CovDerivAlong.lean`) on
the velocity vector field along `γ`.

The identification `velocityLift γ t = tangentMap 𝓘(ℝ, ℝ) I γ ⟨t, 1⟩`
expresses the lift as the bundled derivative of `γ` evaluated on the
canonical "unit-tangent" section `t ↦ ⟨t, 1⟩` of
`TangentBundle 𝓘(ℝ, ℝ) ℝ`. Mathlib's `ContMDiff.contMDiff_tangentMap`
gives `C¹` smoothness of `tangentMap γ` when `γ` is `C²`; the canonical
section is `C^∞` because the tangent bundle of `(ℝ, 𝓘(ℝ, ℝ))` is
trivially `ℝ × ℝ` with all chart transitions equal to the identity.

We provide:

* `velocityLift_contMDiff_of_contMDiff_two` — the `C¹` smoothness of
  the velocity lift along a `C²` curve.
* `velocityLift_smoothness` — convenient alias for use as the second
  smoothness hypothesis of `covDerivAlong`.

## Intrinsic bridge to the covariant-derivative equation

For a `C²` curve `γ` on a boundaryless smooth manifold modelled on a
complete inner-product space, the geodesic predicate
`IsGeodesicAt g γ t₀` (from
`Geometry/Riemannian/Geodesic/Equation.lean`) should be equivalent to
the vanishing of the covariant derivative of `velocity γ` along `γ` at
`t₀`. Establishing this equivalence requires two ingredients:

* **Reverse direction** (`covDerivAlong = 0 ⇒ IsGeodesicAt`): the
  chart-`γ t₀` coordinate computation must be promoted to a manifold
  `HasMFDerivAt` claim for the velocity lift, with the chart-fixed
  geodesic vector field at basepoint `γ t₀` as the right-hand side.
  The promotion is a chart-fibre computation against the
  trivialisation at `⟨γ t₀, 0⟩ : TangentBundle I M`.

* **Forward direction** (`IsGeodesicAt ⇒ covDerivAlong = 0`): the
  `IsGeodesicAt` predicate provides a witness basepoint `α : M` not
  necessarily equal to `γ t₀`, while `covDerivAlong` uses the chart at
  `γ t₀`. Bridging the two chart pictures requires the chart-overlap
  law for the chart-coordinate Christoffel symbols (or, equivalently,
  Picard-Lindelöf uniqueness for integral curves of distinct chart-fixed
  geodesic vector fields with matching base projections). Neither is
  currently recorded in `Integral/Connection/` or
  `Geometry/Riemannian/Geodesic/`; both are independently
  substantial pieces of infrastructure.

The smoothness packaging here is the first deliverable; the
covariant-derivative bridge proper is downstream of the chart-overlap
infrastructure.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Curve

/-! ## Canonical unit-tangent section of `TangentBundle 𝓘(ℝ, ℝ) ℝ` -/

/-- The canonical "unit-tangent" section `t ↦ ⟨t, 1⟩` of
`TangentBundle 𝓘(ℝ, ℝ) ℝ`. Composed with `tangentMap γ` this expresses
the velocity lift of `γ`. -/
def realUnitTangentSection : ℝ → TangentBundle 𝓘(ℝ, ℝ) ℝ :=
  fun t => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)

@[simp] lemma realUnitTangentSection_proj (t : ℝ) :
    (realUnitTangentSection t).proj = t := rfl

@[simp] lemma realUnitTangentSection_snd (t : ℝ) :
    (realUnitTangentSection t).2 = (1 : ℝ) := rfl

/-- On `ℝ`, every chart's `extChartAt` is the identity. Pure
unwrapping of the trivial chart structure. -/
private lemma extChartAt_real_apply (p z : ℝ) :
    extChartAt 𝓘(ℝ, ℝ) p z = z := rfl

private lemma extChartAt_real_symm_apply (p z : ℝ) :
    (extChartAt 𝓘(ℝ, ℝ) p).symm z = z := by
  have h : extChartAt 𝓘(ℝ, ℝ) p = PartialEquiv.refl ℝ :=
    extChartAt_model_space_eq_id ℝ p
  rw [h]
  rfl

/-- On `ℝ`, the tangent-bundle coordinate change between any two charts
at any point is the identity (acting on the fibre `ℝ`). -/
private lemma tangentCoordChange_real (x y z : ℝ) (v : ℝ) :
    tangentCoordChange 𝓘(ℝ, ℝ) x y z v = v := by
  classical
  -- `tangentCoordChange x y z = fderivWithin (extChartAt y ∘ (extChartAt x).symm)
  --   (range 𝓘(ℝ, ℝ)) (extChartAt x z)`. On `ℝ` the inner function is
  -- the identity, and `range 𝓘(ℝ, ℝ) = univ`.
  rw [tangentCoordChange_def]
  have hcomp_id : (extChartAt 𝓘(ℝ, ℝ) y ∘ (extChartAt 𝓘(ℝ, ℝ) x).symm) =
      (fun z : ℝ => z) := by
    funext w
    rw [Function.comp_apply, extChartAt_real_symm_apply, extChartAt_real_apply]
  rw [hcomp_id]
  have hrange : range (𝓘(ℝ, ℝ) : ModelWithCorners ℝ ℝ ℝ) = Set.univ := by
    rw [ModelWithCorners.range_eq_univ]
  rw [hrange, fderivWithin_univ]
  rw [fderiv_id']
  rfl

/-- The canonical "unit-tangent" section `t ↦ ⟨t, 1⟩` of
`TangentBundle 𝓘(ℝ, ℝ) ℝ` is `C^∞`. -/
theorem realUnitTangentSection_contMDiff :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞ realUnitTangentSection := by
  classical
  -- Apply `Trivialization.contMDiff_iff` at the basepoint `α := 0`.
  set α : ℝ := 0
  set e := trivializationAt ℝ (TangentSpace 𝓘(ℝ, ℝ)) α with he_def
  -- Source membership for the trivialisation: every base point is on `ℝ`'s chart.
  have hsrc : ∀ t : ℝ, realUnitTangentSection t ∈ e.source := by
    intro t
    rw [Trivialization.mem_source, he_def, TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source ℝ t
  refine (e.contMDiff_iff (IM := 𝓘(ℝ, ℝ)) (IB := 𝓘(ℝ, ℝ))
    (n := (∞ : WithTop ℕ∞)) hsrc).mpr ⟨?_, ?_⟩
  · -- Base smoothness: `(realUnitTangentSection t).proj = t`, smooth as `id`.
    change ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun t : ℝ => (realUnitTangentSection t).proj)
    have hid : (fun t : ℝ => (realUnitTangentSection t).proj) = (fun t : ℝ => t) := rfl
    rw [hid]
    exact contMDiff_id
  · -- Fibre smoothness: the fibre coord under the trivialisation at `α = 0`
    -- is constant (= 1) along the section.
    change ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun t : ℝ => (e (realUnitTangentSection t)).2)
    have hfibre_const : (fun t : ℝ => (e (realUnitTangentSection t)).2) =
        (fun _ : ℝ => (1 : ℝ)) := by
      funext t
      -- `e ⟨t, 1⟩ .2 = tangentCoordChange t α t 1 = 1` by `tangentCoordChange_real`.
      have h : (e (realUnitTangentSection t)).2 =
          tangentCoordChange 𝓘(ℝ, ℝ) t α t (1 : ℝ) := rfl
      rw [h, tangentCoordChange_real]
    rw [hfibre_const]
    exact contMDiff_const

/-! ## Velocity lift via `tangentMap` -/

/-- The intrinsic velocity lift `t ↦ ⟨γ t, velocity γ t⟩` is exactly the
composition of `tangentMap 𝓘(ℝ, ℝ) I γ` with the canonical unit-tangent
section `t ↦ ⟨t, 1⟩`. -/
lemma velocityLift_eq_tangentMap_comp (γ : ℝ → M) :
    (fun t : ℝ => (⟨γ t, velocity (I := I) γ t⟩ : TangentBundle I M)) =
      (tangentMap 𝓘(ℝ, ℝ) I γ) ∘ realUnitTangentSection := by
  funext t
  rfl

/-- **The velocity lift is `C¹`.** If `γ : ℝ → M` is `C²`, the
total-space velocity lift `t ↦ ⟨γ t, velocity γ t⟩` is `C¹` as a
manifold map `ℝ → TangentBundle I M`.

This is precisely the smoothness hypothesis required by
`covDerivAlong g γ (velocity γ) …`. -/
theorem velocityLift_contMDiff_of_contMDiff_two
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 2 γ) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
      (fun t => (⟨γ t, velocity (I := I) γ t⟩ : TangentBundle I M)) := by
  classical
  rw [velocityLift_eq_tangentMap_comp (I := I) γ]
  -- `tangentMap γ` is `C¹` because `γ` is `C²`.
  have htm : ContMDiff 𝓘(ℝ, ℝ).tangent I.tangent 1
      (tangentMap 𝓘(ℝ, ℝ) I γ) := by
    have hle : (1 : WithTop ℕ∞) + 1 ≤ 2 := by
      exact_mod_cast (by decide : (1 : ℕ∞) + 1 ≤ 2)
    exact hγ.contMDiff_tangentMap hle
  -- The canonical section is `C^∞`, downgrade to `C¹`.
  have hsec : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent 1 realUnitTangentSection :=
    realUnitTangentSection_contMDiff.of_le
      (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  exact htm.comp hsec

/-- Convenient alias: the velocity-lift `C¹` smoothness from a `C²` curve. -/
def velocityLift_smoothness {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 2 γ) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
      (fun t => (⟨γ t, velocity (I := I) γ t⟩ : TangentBundle I M)) :=
  velocityLift_contMDiff_of_contMDiff_two (I := I) hγ

/-- The `C¹` smoothness of `γ` derived from `C²` smoothness, packaged as
the first smoothness hypothesis of `covDerivAlong`. -/
lemma contMDiff_one_of_contMDiff_two {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 2 γ) :
    ContMDiff 𝓘(ℝ, ℝ) I 1 γ :=
  hγ.of_le (by exact_mod_cast (by decide : (1 : ℕ∞) ≤ 2))

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
