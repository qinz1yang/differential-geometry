import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

set_option linter.unusedSectionVars false

/-!
# Intrinsic velocity of a curve

For a smooth manifold `M` modelled on `E` and a curve `γ : ℝ → M`, the
*velocity* `velocity γ t` is the manifold derivative `mfderiv 𝓘(ℝ, ℝ) I γ t`
applied to `1 : ℝ ≃ TangentSpace 𝓘(ℝ, ℝ) t`. It is an intrinsic element of
the tangent space `TangentSpace I (γ t)`, independent of any chart.

The companion lift `velocityLift γ t : TangentBundle I M` is the
total-space packaging `⟨γ t, velocity γ t⟩`, ready to be compared with the
lift of `γ` provided by the integral-curve formulation of `IsGeodesicAt`
(`DifferentialGeometry/Geometry/Riemannian/Geodesic/Equation.lean`).

## Bridge to the integral-curve lift

The geodesic-equation predicate `IsGeodesicAt g γ t₀` is formulated via a
basepoint `α : M` and a lifted curve `f : ℝ → TangentBundle I M`, with
`(f s).proj = γ s` and `f` an integral curve of the chart-fixed geodesic
vector field `geodesicVectorFieldChart g α` at `t₀`. The fibre part
`(f t).snd ∈ TangentSpace I (γ t)` is the "velocity at time `t`" in
chart-`α`-relative coordinates.

This file establishes the intrinsic bridge identity: whenever `f` is a
local integral curve of any vector field `V` and projects to `γ`,

```
velocity γ t = (mfderiv I.tangent I (TotalSpace.proj : TM → M) (f t)) (V (f t))
```

in `TangentSpace I (γ t)`. Specialised to `V = geodesicVectorFieldChart g α`,
this is the rosetta stone that lets later development treat
`velocity γ t` and the chart-relative fibre data of `f t` as different
presentations of the same intrinsic vector.

A standard chart computation further identifies
`(mfderiv proj (f t)) (geodesicVectorFieldChart g α (f t))` with the
intrinsic second component `(f t).2`; the present file ships the
projection-mfderiv form, which is the form Mathlib's
`MDifferentiableAt.comp` provides for free.
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

/-! ## Intrinsic velocity -/

/-- The intrinsic velocity vector of a curve `γ : ℝ → M` at time `t`:
the manifold derivative `mfderiv 𝓘(ℝ, ℝ) I γ t` applied to `1 : ℝ`. -/
def velocity (γ : ℝ → M) (t : ℝ) : TangentSpace I (γ t) :=
  mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)

@[simp] lemma velocity_def (γ : ℝ → M) (t : ℝ) :
    velocity (I := I) γ t = mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) := rfl

/-- The intrinsic velocity lift of a curve at time `t`: the point of the
tangent bundle whose foot is `γ t` and whose fibre is the velocity. -/
def velocityLift (γ : ℝ → M) (t : ℝ) : TangentBundle I M :=
  ⟨γ t, velocity (I := I) γ t⟩

@[simp] lemma velocityLift_proj (γ : ℝ → M) (t : ℝ) :
    (velocityLift (I := I) γ t).proj = γ t := rfl

@[simp] lemma velocityLift_snd (γ : ℝ → M) (t : ℝ) :
    (velocityLift (I := I) γ t).2 = velocity (I := I) γ t := rfl

@[simp] lemma velocityLift_mk (γ : ℝ → M) (t : ℝ) :
    velocityLift (I := I) γ t = ⟨γ t, velocity (I := I) γ t⟩ := rfl

/-- The velocity of a curve is zero when the curve is not
manifold-differentiable at the given time, by the convention of `mfderiv`. -/
lemma velocity_eq_zero_of_not_mdifferentiable
    {γ : ℝ → M} {t : ℝ} (h : ¬ MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    velocity (I := I) γ t = 0 := by
  classical
  simp [velocity, mfderiv, h]

/-! ## Velocity from a `HasMFDerivAt` hypothesis -/

/-- If `γ` has manifold derivative `L` at `t`, then the intrinsic velocity at
`t` is `L 1`. -/
theorem velocity_eq_of_hasMFDerivAt
    {γ : ℝ → M} {t : ℝ} {L : ℝ →L[ℝ] TangentSpace I (γ t)}
    (h : HasMFDerivAt 𝓘(ℝ, ℝ) I γ t L) :
    velocity (I := I) γ t = L (1 : ℝ) := by
  unfold velocity
  rw [h.mfderiv]
  rfl

/-- The intrinsic velocity lift, expressed from a `HasMFDerivAt`-hypothesis on
`γ`. -/
theorem velocityLift_eq_of_hasMFDerivAt
    {γ : ℝ → M} {t : ℝ} {L : ℝ →L[ℝ] TangentSpace I (γ t)}
    (h : HasMFDerivAt 𝓘(ℝ, ℝ) I γ t L) :
    velocityLift (I := I) γ t = ⟨γ t, L (1 : ℝ)⟩ := by
  unfold velocityLift
  rw [velocity_eq_of_hasMFDerivAt (I := I) h]

/-! ## Rosetta-stone bridge to integral-curve lifts

If `f : ℝ → TM` is a local integral curve of a vector field `V` at `t`,
projecting to `γ`, then the intrinsic velocity of `γ` at `t` is the image
of `V (f t)` under the manifold derivative of the bundle projection
`TotalSpace.proj : TM → M` at `f t`. -/

section IntegralCurveBridge

/-- The bundle projection `Bundle.TotalSpace.proj : TM → M` viewed as a
shorthand. -/
abbrev tangentBundleProj : TangentBundle I M → M := Bundle.TotalSpace.proj

/-- Manifold-differentiability of the tangent-bundle projection at any
point, restated for convenience. -/
lemma mdifferentiableAt_tangentBundleProj {p : TangentBundle I M} :
    MDifferentiableAt I.tangent I
      (tangentBundleProj (I := I) (M := M)) p :=
  Bundle.mdifferentiableAt_proj _

/-- The intrinsic velocity equals the image of the integrand vector field
value under `mfderiv` of the bundle projection: rosetta-stone bridge in
projection form.

Suppose `f : ℝ → TM` is a local integral curve of the vector field `V` in
a neighbourhood of `t`, and that the lift projects to `γ`, i.e.
`(f s).proj = γ s` for all `s`. Then

```
velocity γ t = (mfderiv I.tangent I (TotalSpace.proj) (f t)) (V (f t)).
```
-/
theorem velocity_eq_mfderiv_proj_of_isMIntegralCurveAt
    {γ : ℝ → M} {V : (p : TangentBundle I M) → TangentSpace I.tangent p}
    {f : ℝ → TangentBundle I M} {t : ℝ}
    (hproj : ∀ s, (f s).proj = γ s)
    (hf : IsMIntegralCurveAt f V t) :
    velocity (I := I) γ t =
      (mfderiv I.tangent I (tangentBundleProj (I := I) (M := M)) (f t))
        (V (f t)) := by
  classical
  -- From `IsMIntegralCurveAt`, extract the manifold-derivative formula at `t`.
  have h_f_mf : HasMFDerivAt 𝓘(ℝ, ℝ) I.tangent f t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (f t))) := hf.hasMFDerivAt
  -- Composition with the bundle projection.
  have h_proj :
      MDifferentiableAt I.tangent I
        (tangentBundleProj (I := I) (M := M)) (f t) :=
    mdifferentiableAt_tangentBundleProj
  have h_comp :
      HasMFDerivAt 𝓘(ℝ, ℝ) I
        (tangentBundleProj (I := I) (M := M) ∘ f) t
        ((mfderiv I.tangent I
            (tangentBundleProj (I := I) (M := M)) (f t)).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight (V (f t)))) :=
    h_proj.hasMFDerivAt.comp t h_f_mf
  -- Rewrite the function `tangentBundleProj ∘ f` as `γ` via `hproj`.
  have h_fun_eq :
      tangentBundleProj (I := I) (M := M) ∘ f = γ := by
    funext s
    exact hproj s
  rw [h_fun_eq] at h_comp
  -- Convert the `HasMFDerivAt`-formula into a `mfderiv = …` equation and apply at `1`.
  have h_mfderiv : mfderiv 𝓘(ℝ, ℝ) I γ t =
      (mfderiv I.tangent I
        (tangentBundleProj (I := I) (M := M)) (f t)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V (f t))) :=
    h_comp.mfderiv
  unfold velocity
  rw [h_mfderiv]
  -- Apply the composed CLM to `1 : ℝ`.
  -- `(K.comp ((1 : ℝ →L[ℝ] ℝ).smulRight (V (f t)))) 1 = K (((1).smulRight (V (f t))) 1) = K (V (f t))`.
  change ((mfderiv I.tangent I
        (tangentBundleProj (I := I) (M := M)) (f t)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V (f t)))) (1 : ℝ) =
      (mfderiv I.tangent I
        (tangentBundleProj (I := I) (M := M)) (f t)) (V (f t))
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, one_smul]

/-- **Rosetta-stone bridge for `IsGeodesicAt`.** Combining the
projection-form bridge with the geodesic vector-field setup: if `γ` is a
local geodesic at `t₀` in the `IsGeodesicAt` sense, then there exist a
basepoint `α : M`, a lifted curve `f : ℝ → TM`, and a relation between
the intrinsic velocity at `t₀` and the chart-fixed geodesic vector field
applied to `f t₀`. -/
theorem IsGeodesicAt.exists_velocity_eq_mfderiv_proj
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {t₀ : ℝ}
    (hγ : IsGeodesicAt (I := I) g γ t₀) :
    ∃ (α : M) (f : ℝ → TangentBundle I M),
      (∀ s, (f s).proj = γ s) ∧
      IsMIntegralCurveAt f
        (geodesicVectorFieldChart (I := I) g α) t₀ ∧
      velocity (I := I) γ t₀ =
        (mfderiv I.tangent I
          (tangentBundleProj (I := I) (M := M)) (f t₀))
          (geodesicVectorFieldChart (I := I) g α (f t₀)) := by
  obtain ⟨α, f, hproj, hf⟩ := hγ
  refine ⟨α, f, hproj, hf, ?_⟩
  exact velocity_eq_mfderiv_proj_of_isMIntegralCurveAt (I := I)
    (V := geodesicVectorFieldChart (I := I) g α) hproj hf

/-- **Global form of the rosetta-stone bridge for `IsGeodesic`.** If `γ`
is a global geodesic, there are a basepoint `α` and a global lift `f`
projecting to `γ` such that the intrinsic velocity at every time `t`
equals the image of `geodesicVectorFieldChart g α (f t)` under the
projection mfderiv. -/
theorem IsGeodesic.exists_velocity_eq_mfderiv_proj
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsGeodesic (I := I) g γ) :
    ∃ (α : M) (f : ℝ → TangentBundle I M),
      (∀ s, (f s).proj = γ s) ∧
      IsMIntegralCurve f
        (geodesicVectorFieldChart (I := I) g α) ∧
      ∀ t, velocity (I := I) γ t =
        (mfderiv I.tangent I
          (tangentBundleProj (I := I) (M := M)) (f t))
          (geodesicVectorFieldChart (I := I) g α (f t)) := by
  obtain ⟨α, f, hproj, hf⟩ := hγ
  refine ⟨α, f, hproj, hf, ?_⟩
  intro t
  exact velocity_eq_mfderiv_proj_of_isMIntegralCurveAt (I := I)
    (V := geodesicVectorFieldChart (I := I) g α) hproj
    (hf.isMIntegralCurveAt t)

end IntegralCurveBridge

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
