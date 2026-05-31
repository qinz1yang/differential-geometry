/-
# The round metric on S³ and its constant sectional curvature

Tier 3 of the spherical-space-form construction. We build the induced ("round")
Riemannian metric on the unit 3-sphere `RoundSphere3 = ↥(Metric.sphere (0:E4) 1)`
in `E4 = EuclideanSpace ℝ (Fin 4)`, modeled on `𝓡 3`, as the pullback of the
ambient Euclidean inner product along the inclusion, and (later) prove it has
constant positive sectional curvature `1`.

The metric definition mirrors `RicciFlower.Diffeomorph.pullbackInner`
(`RicciFlower/Metric/Pullback.lean`): the inclusion differential `dι` plays the
role of `mfderiv Φ`, and the constant `innerSL ℝ` on `E4` plays the role of
`g.inner`.
-/
import RicciFlower.Metric.Basic
import RicciFlower.VectorBundle.ClmSectionSmooth
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.InnerProductSpace.Basic

set_option autoImplicit false

noncomputable section

namespace RicciFlower
namespace RoundSphere

open Bundle Metric
open scoped Manifold ContDiff RealInnerProductSpace

/-- The ambient Euclidean space `ℝ⁴`. -/
abbrev E4 : Type := EuclideanSpace ℝ (Fin 4)

instance : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

/-- The unit 3-sphere in `ℝ⁴`, as a type, modeled on `𝓡 3`. -/
abbrev RoundSphere3 : Type := ↥(Metric.sphere (0 : E4) 1)

/-- The inclusion `S³ ↪ ℝ⁴`. -/
abbrev incl : RoundSphere3 → E4 := ((↑) : RoundSphere3 → E4)

/-- `S³` is a `C^∞` manifold (downgraded from Mathlib's analytic structure). -/
instance : IsManifold (𝓡 3) (∞ : WithTop ℕ∞) RoundSphere3 :=
  IsManifold.of_le le_top

/-- The differential of the inclusion at `p`, `dι_p : T_p S³ →L ℝ⁴`. -/
abbrev dincl (p : RoundSphere3) : TangentSpace (𝓡 3) p →L[ℝ] E4 :=
  mfderiv (𝓡 3) 𝓘(ℝ, E4) incl p

theorem dincl_injective (p : RoundSphere3) : Function.Injective (dincl p) :=
  mfderiv_coe_sphere_injective p

/-- The round metric on `S³`: pullback of the ambient inner product along `incl`. -/
noncomputable def roundMetricS3 : SmoothRiemannianMetric (𝓡 3) RoundSphere3 where
  inner p :=
    (ContinuousLinearMap.precomp ℝ (dincl p)).comp ((innerSL ℝ).comp (dincl p))
  symm p v w := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply,
      innerSL_apply_apply]
    exact real_inner_comm _ _
  pos p v hv := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply,
      innerSL_apply_apply]
    have hv' : dincl p v ≠ 0 := fun h => hv (dincl_injective p (by simpa using h))
    exact real_inner_self_pos.mpr hv'
  isVonNBounded p := by
    -- WIP (T3.1). Mathematically: `{v | ‖dincl p v‖² < 1}` is bounded since `dincl p` is an
    -- injective continuous-linear embedding of the finite-dim `T_p` into `E4`.
    -- BLOCKER (infrastructure): `TangentSpace (𝓡 3) p` carries ONLY the bundle TVS structure
    -- (no `NormedAddCommGroup`/`UniformSpace`/`CompleteSpace`/normed-module instances — the
    -- manifold tangent bundle is a topological VB by design). So norm-based routes
    -- (`NormedSpace.isVonNBounded_iff'`, `(Linear|ContinuousLinear)Map…antilipschitz…`,
    -- `closed_of_finiteDimensional`) do not apply on `T_p`. Need a TVS-level argument:
    -- `dincl p` injective continuous-linear from a finite-dim TVS is a closed embedding, so
    -- the preimage of the (vonN-bounded) ambient ball `{w : E4 | ⟪w,w⟫ < 1}` is vonN-bounded;
    -- or transport the norm onto `T_p` via the model identification. Investigate how the
    -- project's base metrics obtain `isVonNBounded` on the tangent bundle.
    sorry
  contMDiff := by
    sorry

@[simp] theorem roundMetricS3_inner (p : RoundSphere3) (v w : TangentSpace (𝓡 3) p) :
    roundMetricS3.inner p v w = inner ℝ (dincl p v) (dincl p w) := by
  simp only [roundMetricS3, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.precomp_apply, innerSL_apply_apply]

end RoundSphere
end RicciFlower
