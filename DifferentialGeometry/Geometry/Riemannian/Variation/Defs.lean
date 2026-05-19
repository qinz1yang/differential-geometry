import DifferentialGeometry.Geometry.Riemannian.Geodesic.Velocity

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A **smooth one-parameter variation** of a curve `γ : ℝ → M` is a
jointly-`C¹` map `α : ℝ × ℝ → M` (in the parameter `s` and the time `t`)
satisfying `α(0, t) = γ(t)` for every `t : ℝ`.

The first slot is the *variation parameter* `s`; the second slot is the
*time* `t`. At `s = 0`, the curve coincides with `γ`. The structure is
the foundational data carrier for the first and second variation
formulas of length and energy. -/
structure SmoothVariation (γ : ℝ → M) where
  /-- The 1-parameter family of curves, indexed by `s` then `t`. -/
  α : ℝ → ℝ → M
  /-- Joint `C¹` smoothness of `α` as a map `ℝ × ℝ → M`. -/
  smooth : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I 1
              (fun p : ℝ × ℝ => α p.1 p.2)
  /-- At `s = 0`, the family reduces to the original curve `γ`. -/
  fixes_curve : ∀ t : ℝ, α 0 t = γ t

namespace SmoothVariation

/-- **The variation field at time `t`.** For a smooth variation `V` of
`γ`, the variation field at `t` is the tangent vector at `γ t = V.α 0 t`
given by the partial derivative of `α` in `s` at `s = 0`:
$$
  \partial_s V.\alpha(0, t) \in T_{\gamma(t)} M.
$$
Because `mfderiv` of `s ↦ V.α s t` at `s = 0` returns a vector in
`T_{V.α 0 t} M`, and `V.α 0 t = γ t`, a trivial transport via
`V.fixes_curve t` lands the result in `T_{γ t} M`. -/
def field {γ : ℝ → M} (V : SmoothVariation (I := I) γ) (t : ℝ) :
    TangentSpace I (γ t) := by
  -- Take the s-partial derivative at s = 0, then transport.
  refine V.fixes_curve t ▸ ?_
  exact mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => V.α s t) 0 (1 : ℝ)

/-! ## The constant variation -/

/-- The **constant variation** of a `C¹` curve `γ`: `α s t = γ t` for
every `(s, t)`. This is a smooth variation whose variation field is
identically zero. -/
def const {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) :
    SmoothVariation (I := I) γ where
  α := fun _ t => γ t
  smooth := by
    -- The map (s, t) ↦ γ t is the composition `γ ∘ Prod.snd`.
    have hsnd : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × ℝ => p.2) := contMDiff_snd
    -- γ ∘ Prod.snd at smoothness 1
    have hγ' : ContMDiff 𝓘(ℝ, ℝ) I 1 γ := hγ
    exact hγ'.comp (hsnd.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)))
  fixes_curve := fun _ => rfl

end SmoothVariation

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

end
