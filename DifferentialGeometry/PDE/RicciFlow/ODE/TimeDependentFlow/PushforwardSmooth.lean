import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ManifoldIntegralFlow
import DifferentialGeometry.PDE.RicciFlow.Pullback.PushforwardVF
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
## Regularity of the time-dependent integral flow map and its pushforward

The genuine manifold integral flow of a time-dependent vector field `X`
(`time_dependent_vf_manifold_integral_flow_family`) packages the flow into a
single time-indexed family of diffeomorphisms `Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)`
carrying the bare flow equation `∂_s (Φ_fam s x) = X s (Φ_fam s x)`. Downstream
the Hamilton–DeTurck pull-back assembly consumes *separate* regularity facts
about this family:

* **spatial smoothness at a fixed time** — each `Φ_fam s` is a smooth self-map
  of `M`, and the *pushforward* of a smooth vector field `Y` along `Φ_fam s` is a
  smooth section of `TM` (this is the exact `hPush_smooth`-shaped hypothesis taken
  by `lie_derivative_metric_pullback_natural_under_diffeomorphism_pointwise` / `assemble_lie_deriv_naturality`);
* **time regularity at a fixed point** — the bare flow's pointwise
  `HasMFDerivWithinAt` in `s`, with velocity `X s (Φ_fam s x)`, together with the
  continuity `s ↦ Φ_fam s x` it implies;
* **existence of the moving differential** — `mfderiv I I (Φ_fam s) x` is defined
  at every `(s, x)`, the object whose `s`-variation feeds the Cartan-cancellation
  chain.

This file derives exactly those pieces from the flow construction. Each
fixed-time spatial fact is free from the `Diffeomorph` structure of `Φ_fam s`;
the pushforward smoothness is the manifold pullback of `Y` by the inverse
diffeomorphism, smooth by Mathlib's `ContMDiff.mpullback_vectorField`; the time
facts are re-exports of the bare flow equation carried by the family.

### The regularity the autonomous-flow theory does *not* supply

Mathlib's manifold integral-curve API
(`exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless` and the
`IsPicardLindelof` flow it is built on) provides existence, uniqueness, the
pointwise time-derivative, and *Lipschitz* (hence continuous) dependence of the
flow on the initial condition — but **no** smoothness of the flow in the initial
condition, and in particular **no** derivative of the moving differential
`s ↦ mfderiv I I (Φ_fam s) x`. The latter (the "variational"/"smooth-in-IC"
content `∂_s (dΦ_s) = -∇ X ∘ dΦ_s`) is a strictly stronger fact than anything the
`C¹`-field autonomous flow yields; it is left as an explicit, separable
hypothesis at the Cartan-cancellation call sites and is **not** produced here.
No joint-`C∞`-on-`ℝ × M` hypothesis is taken anywhere in this file.

No `HasLocallyConstantChartAt`-style or finite-atlas hypothesis is used.
-/

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff

section SpatialAtFixedTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M]

/-- **Spatial smoothness of the flow at a fixed time.** For every fixed time `s`,
the flow map `Φ_fam s : M → M` of a time-indexed diffeomorphism family is a smooth
(`C^∞`) self-map of `M`. This is the per-time spatial regularity consumed
downstream; it is immediate from `Φ_fam s` being a `Diffeomorph`, and carries no
joint smoothness in `(s, x)`. -/
theorem flowFamily_contMDiff_fixed_time
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (s : ℝ) :
    ContMDiff I I ∞ (Φ_fam s : M → M) :=
  (Φ_fam s).contMDiff

/-- **Existence of the moving differential.** At every time `s` and point `x`, the
flow map `Φ_fam s` is manifold-differentiable, so its differential
`mfderiv I I (Φ_fam s) x : T_x M →L T_{Φ_fam s x} M` is defined. This is the object
whose `s`-variation (the "moving pushforward") appears in the Cartan-cancellation
chain; here we only record that it exists pointwise. -/
theorem flowFamily_mdifferentiableAt_fixed_time
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (s : ℝ) (x : M) :
    MDifferentiableAt I I (Φ_fam s : M → M) x := by
  have hinfty : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  exact (Φ_fam s).mdifferentiable hinfty x

end SpatialAtFixedTime

section Pushforward

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.PDE.RicciFlow.Pullback

private lemma pushforward_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by decide

/-- The pushforward of a vector field `Y` along a diffeomorphism `Φ` equals,
as a function, the manifold pullback of `Y` by the inverse diffeomorphism
`Φ.symm`. This is the identity that converts pushforward smoothness into a
statement about Mathlib's `mpullback`. -/
private lemma flowFamily_pushforward_eq_mpullback_symm
    (Φ : M ≃ₘ⟮I, I⟯ M) (Y : ∀ x : M, TangentSpace I x) :
    (Diffeomorph.pushforward Φ Y : ∀ x : M, TangentSpace I x)
      = (VectorField.mpullback I I (⇑Φ.symm) Y : ∀ x : M, TangentSpace I x) := by
  funext z
  have hinv : (mfderiv I I (⇑Φ.symm) z).inverse = mfderiv I I (⇑Φ) (Φ.symm z) := by
    apply ContinuousLinearMap.inverse_eq
    · have hΦ : MDifferentiableAt I I (⇑Φ) (Φ.symm z) :=
        Φ.mdifferentiable pushforward_infty_ne_zero _
      have hΦsymm : MDifferentiableAt I I (⇑Φ.symm) (Φ (Φ.symm z)) := by
        have hap : Φ (Φ.symm z) = z := Φ.apply_symm_apply z
        rw [hap]; exact Φ.symm.mdifferentiable pushforward_infty_ne_zero z
      have hcomp : (⇑Φ.symm) ∘ (⇑Φ) = (id : M → M) := by
        funext w; exact Φ.symm_apply_apply w
      have hchain := mfderiv_comp (Φ.symm z) hΦsymm hΦ
      rw [hcomp, mfderiv_id] at hchain
      have hap : Φ (Φ.symm z) = z := Φ.apply_symm_apply z
      rw [hap] at hchain
      exact hchain.symm
    · have hΦsymm : MDifferentiableAt I I (⇑Φ.symm) z :=
        Φ.symm.mdifferentiable pushforward_infty_ne_zero z
      have hΦ : MDifferentiableAt I I (⇑Φ) (Φ.symm z) :=
        Φ.mdifferentiable pushforward_infty_ne_zero _
      have hcomp : (⇑Φ) ∘ (⇑Φ.symm) = (id : M → M) := by
        funext w; exact Φ.apply_symm_apply w
      have hchain := mfderiv_comp z hΦ hΦsymm
      rw [hcomp, mfderiv_id] at hchain
      exact hchain.symm
  change (Φ.apply_symm_apply z) ▸
      (mfderiv I I (⇑Φ) (Φ.symm z)) (Y (Φ.symm z))
    = (mfderiv I I (⇑Φ.symm) z).inverse (Y (Φ.symm z))
  rw [hinv]
  refine eq_of_heq ?_
  exact eqRec_heq (φ := fun w => TangentSpace I w) (Φ.apply_symm_apply z)
    ((mfderiv I I (⇑Φ) (Φ.symm z)) (Y (Φ.symm z)))

/-- **Pushforward smoothness at a fixed time — the `hPush_smooth` shape.**

For a time-indexed diffeomorphism family `Φ_fam`, a fixed time `s`, and a smooth
tangent vector field `Y` on `M`, the pushforward `Diffeomorph.pushforward (Φ_fam s) Y`
is a smooth section of the tangent bundle. This is *exactly* the hypothesis
`hPush_smooth` taken (rather than proved) by `lie_derivative_metric_pullback_natural_under_diffeomorphism_pointwise`
and `assemble_lie_deriv_naturality` in the pull-back layer, here produced from the
flow family for the specialisation `Φ := Φ_fam s`.

The proof rewrites the pushforward as the manifold pullback of `Y` by the inverse
diffeomorphism `(Φ_fam s).symm` (a smooth map with everywhere-invertible
differential) and applies Mathlib's `ContMDiff.mpullback_vectorField`. No joint
`(s, x)` regularity is involved: `s` is fixed and the statement is purely spatial. -/
theorem flowFamily_pushforward_contMDiff
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (s : ℝ)
    {Y : ∀ x : M, TangentSpace I x}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (Y x))) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x
        (Diffeomorph.pushforward (Φ_fam s) Y x)) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  set Φ := Φ_fam s with hΦ
  have hfun_eq := flowFamily_pushforward_eq_mpullback_symm (I := I) Φ Y
  have hfun_total :
      (fun z : M => (TotalSpace.mk' E z (Diffeomorph.pushforward Φ Y z) : TangentBundle I M))
        = (fun z : M => (TotalSpace.mk' E z (VectorField.mpullback I I (⇑Φ.symm) Y z) :
            TangentBundle I M)) := by
    funext z; congr 1
    exact congrFun hfun_eq z
  rw [hfun_total]
  have hΦsymm_smooth : ContMDiff I I (∞ : WithTop ℕ∞) (⇑Φ.symm) := Φ.symm.contMDiff
  have hinv : ∀ x, (mfderiv I I (⇑Φ.symm) x).IsInvertible := by
    intro x
    refine ⟨(Diffeomorph.mfderivToContinuousLinearEquiv Φ.symm pushforward_infty_ne_zero x), ?_⟩
    exact Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := Φ.symm) (x := x)
      pushforward_infty_ne_zero
  exact ContMDiff.mpullback_vectorField (I := I) (I' := I) (V := Y)
    (f := ⇑Φ.symm) (m := (∞ : WithTop ℕ∞)) (n := (∞ : WithTop ℕ∞))
    hY hΦsymm_smooth hinv (by simp)

end Pushforward

section TimeRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M] [CompactSpace M] [SigmaCompactSpace M]

/-- **Time regularity of the flow at a fixed point (bare-flow re-export).**

Given the genuine manifold integral flow family `Φ_fam` produced by
`time_dependent_vf_manifold_integral_flow_family` — with its bare flow equation
`hbare s _ _ x : HasMFDerivWithinAt 𝓘(ℝ,ℝ) I (u ↦ Φ_fam u x) (Ici 0) s (𝟙.smulRight (X s (Φ_fam s x)))`
— the time-curve `s ↦ Φ_fam s x` has, at every interior time `s ∈ (0, T)` and
every point `x`, the manifold derivative with velocity the geometric `X s (Φ_fam s x)`.

This packages the time-derivative side of the flow's regularity in the exact form
used downstream: the velocity is the bare integral-flow velocity, never a chart
pull-back. It is a re-statement (the hypothesis is itself the bare flow), recorded
here as the time-regularity component of the regularity package. -/
theorem flowFamily_hasMFDerivWithinAt_time
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hbare : ∀ s : ℝ, 0 < s → s < T → ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ_fam u x) (Ici 0) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ_fam s x))))
    (s : ℝ) (hs : 0 < s) (hsT : s < T) (x : M) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ_fam u x) (Ici 0) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ_fam s x))) :=
  hbare s hs hsT x

/-- **Continuity of the flow in time at a fixed point.** From the bare flow's
pointwise `HasMFDerivWithinAt` in `s`, the time-curve `s ↦ Φ_fam s x` is
continuous within `Ici 0` at every interior time `s ∈ (0, T)` and every point `x`.
This is the (one-sided) time-continuity component of the flow regularity, derived
purely from the existence of the manifold time-derivative. -/
theorem flowFamily_continuousWithinAt_time
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hbare : ∀ s : ℝ, 0 < s → s < T → ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ_fam u x) (Ici 0) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ_fam s x))))
    (s : ℝ) (hs : 0 < s) (hsT : s < T) (x : M) :
    ContinuousWithinAt (fun u : ℝ => Φ_fam u x) (Ici 0) s :=
  (hbare s hs hsT x).continuousWithinAt

end TimeRegularity

section RegularityPackage

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [CompactSpace M]

open DifferentialGeometry.PDE.RicciFlow.Pullback

/-- **Regularity package of the time-dependent integral flow map.**

The honest, separable regularity of the flow family `Φ_fam` carrying the genuine
bare flow `hbare`, bundled into one statement, in the form usable downstream:

* `(1)` per-fixed-time **spatial smoothness**: each `Φ_fam s` is a `C^∞` self-map
  of `M`;
* `(2)` per-fixed-time **pushforward smoothness** (the downstream `hPush_smooth`
  shape): for any smooth vector field `Y`, the pushforward
  `Diffeomorph.pushforward (Φ_fam s) Y` is a smooth section;
* `(3)` existence of the **moving differential** `mfderiv I I (Φ_fam s) x` at every
  `(s, x)`;
* `(4)` per-point **time regularity**: the bare flow's `HasMFDerivWithinAt` in `s`
  with velocity `X s (Φ_fam s x)` on `(0, T)`;
* `(5)` per-point **time continuity** `s ↦ Φ_fam s x` on `Ici 0` over `(0, T)`.

These are precisely the regularity facts the Hamilton–DeTurck pull-back assembly
needs and currently *takes* as hypotheses. No joint-`C∞`-on-`ℝ × M` hypothesis is
introduced; the time and space regularities are exposed separately. The remaining
"smooth-in-initial-condition" content — a derivative for the moving differential
`s ↦ mfderiv I I (Φ_fam s) x` — is *not* part of this package: it is not supplied by
the `C¹`-field autonomous-flow theory (see the file header) and remains a separable
hypothesis at its call sites. -/
theorem flowFamily_regularity_package
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hbare : ∀ s : ℝ, 0 < s → s < T → ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ_fam u x) (Ici 0) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ_fam s x)))) :
    (∀ s : ℝ, ContMDiff I I ∞ (Φ_fam s : M → M)) ∧
    (∀ (s : ℝ) (Y : ∀ x : M, TangentSpace I x),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (Y x)) →
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x
          (Diffeomorph.pushforward (Φ_fam s) Y x))) ∧
    (∀ (s : ℝ) (x : M), MDifferentiableAt I I (Φ_fam s : M → M) x) ∧
    (∀ s : ℝ, 0 < s → s < T → ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ_fam u x) (Ici 0) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ_fam s x)))) ∧
    (∀ s : ℝ, 0 < s → s < T → ∀ x : M,
      ContinuousWithinAt (fun u : ℝ => Φ_fam u x) (Ici 0) s) :=
  ⟨fun s => flowFamily_contMDiff_fixed_time Φ_fam s,
   fun s _Y hY => flowFamily_pushforward_contMDiff Φ_fam s hY,
   fun s x => flowFamily_mdifferentiableAt_fixed_time Φ_fam s x,
   hbare,
   fun s hs hsT x => (hbare s hs hsT x).continuousWithinAt⟩

end RegularityPackage

end DifferentialGeometry.PDE.RicciFlow.ODE
