import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Topology.Manifold.SubmersionFiber
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The rounded height `(x, t) ↦ f x + t²` (SF6, step 2)

For `f` smooth on an open set `W` of a manifold, the function `G (x, t) = f x + t²` on `W × ℝ` is
smooth, with differential `(v, τ) ↦ df(v) + 2 t τ`.  At a point of a level `G = c` it is a submersion
as soon as `t ≠ 0` or `df ≠ 0`: so if `c` is a regular value of `f`, the level `{G = c}` (the "rounded
double" of the sublevel `{f ≤ c}`) is a smooth closed hypersurface of `W × ℝ`.
-/

set_option autoImplicit false

open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Surface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace H Z]

/-- The rounded height `(x, t) ↦ f x + t²` on `W × ℝ`. -/
def roundedHeight (W : TopologicalSpace.Opens Z) (f : Z → ℝ) (p : W × ℝ) : ℝ :=
  f p.1 + p.2 ^ 2

theorem contMDiff_roundedHeight {W : TopologicalSpace.Opens Z} {f : Z → ℝ}
    (hfW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f W) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (roundedHeight W f) := by
  have h1 : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : W => f x) :=
    hfW.comp_contMDiff contMDiff_subtype_val fun x => x.2
  have h2 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => t ^ 2) := (contDiff_id.pow 2).contMDiff
  exact (h1.comp contMDiff_fst).add (h2.comp contMDiff_snd)

/-- The differential of the rounded height: `(v, τ) ↦ df(v) + 2 t τ`. -/
theorem exists_hasMFDerivAt_roundedHeight {W : TopologicalSpace.Opens Z} {f : Z → ℝ}
    (hfW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f W) (p : W × ℝ) :
    ∃ L : E × ℝ →L[ℝ] ℝ, HasMFDerivAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (roundedHeight W f) p L ∧
      ∀ v : E × ℝ, L v = mvfderiv (I := I) f p.1 v.1 + 2 * p.2 * v.2 := by
  have hfx : MDifferentiableAt I 𝓘(ℝ, ℝ) f p.1 :=
    ((hfW (p.1 : Z) p.1.2).contMDiffAt (W.isOpen.mem_nhds p.1.2)).mdifferentiableAt (by simp)
  have h1 : HasMFDerivAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun q : W × ℝ => f q.1) p
      ((mfderiv I 𝓘(ℝ, ℝ) f p.1).comp
        ((ContinuousLinearMap.id ℝ E).comp (ContinuousLinearMap.fst ℝ E ℝ))) :=
    hfx.hasMFDerivAt.comp p
      ((DifferentialGeometry.hasMFDerivAt_subtype_val (I := I) W p.1).comp p (hasMFDerivAt_fst p))
  have hsq : HasFDerivAt (fun t : ℝ => t ^ 2)
      ((1 : ℝ →L[ℝ] ℝ).smulRight ((2 : ℕ) * p.2 ^ (2 - 1))) p.2 :=
    (hasDerivAt_pow 2 p.2).hasFDerivAt
  have h2 : HasMFDerivAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun q : W × ℝ => q.2 ^ 2) p
      (((1 : ℝ →L[ℝ] ℝ).smulRight ((2 : ℕ) * p.2 ^ (2 - 1))).comp
        (ContinuousLinearMap.snd ℝ E ℝ)) :=
    hsq.hasMFDerivAt.comp p (hasMFDerivAt_snd p)
  refine ⟨_, h1.add h2, fun v => ?_⟩
  change mvfderiv (I := I) f p.1 v.1 + v.2 * (((2 : ℕ) : ℝ) * p.2 ^ (2 - 1)) =
    mvfderiv (I := I) f p.1 v.1 + 2 * p.2 * v.2
  push_cast
  ring

/-- The rounded height is a submersion at `p` as soon as `t ≠ 0` or `df ≠ 0` at `p`. -/
theorem surjective_mfderiv_roundedHeight {W : TopologicalSpace.Opens Z} {f : Z → ℝ}
    (hfW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f W) (p : W × ℝ)
    (hp : p.2 ≠ 0 ∨ ∃ v, mvfderiv (I := I) f p.1 v ≠ 0) :
    Surjective (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (roundedHeight W f) p) := by
  obtain ⟨L, hL, hLv⟩ := exists_hasMFDerivAt_roundedHeight hfW p
  rw [hL.mfderiv]
  have hne : ∃ w : E × ℝ, L w ≠ 0 := by
    rcases hp with hp | ⟨v, hv⟩
    · refine ⟨(0, 1), ?_⟩
      rw [hLv]
      have h0 : mvfderiv (I := I) f p.1 ((0, 1) : E × ℝ).1 = 0 :=
        (mvfderiv (I := I) f p.1).map_zero
      rw [h0, zero_add]
      simpa using hp
    · refine ⟨(v, 0), ?_⟩
      rw [hLv]
      simpa using hv
  obtain ⟨w, hw⟩ := hne
  change Surjective (L : E × ℝ → ℝ)
  intro y
  refine ⟨(y / L w) • w, ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ y hw]

end DifferentialGeometry.Topology.Surface
