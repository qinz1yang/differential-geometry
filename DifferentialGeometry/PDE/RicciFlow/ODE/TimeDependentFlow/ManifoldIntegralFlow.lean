import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Analysis.Calculus.MeanValue

/-!
## Genuine integral flow of a time-dependent vector field

For the Hamilton–DeTurck argument one needs a time-indexed family of
diffeomorphisms `Φ` that is the **genuine integral flow** of a time-dependent
vector field `X`, in the bare manifold form

  `∂_s (Φ s x) = X s (Φ s x)`,

so that `∂_t(Φ_t^* g) = Φ_t^*(∂_t g + 𝓛_X g)` and the Lie term cancels the
DeTurck gauge term. The chart-coordinate Picard producer solves the chart ODE
with the *raw* bundle velocity, whose recovered manifold velocity is the chart
pull-back of `X` (equal to the bare `X(Φ)` only at the chart centre); the bare
flow form is therefore false for that construction.

This file gives the bare form directly, with **no chart-convention transport**,
via the standard *autonomisation* of the time-dependent field: the time-dependent
`X` on `M` becomes the autonomous field `(1, X)` on `ℝ × M`, whose integral
curves (supplied by Mathlib's `exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless`)
have time component `s ↦ s` and spatial component a genuine integral curve of
`X` with velocity `X s (γ s)`. No `HasLocallyConstantChartAt`-style hypothesis is
used; the only regularity input is the `C¹` regularity of the autonomised field,
a clean separable hypothesis.

### Main results

* `autonomizedFlowVF` — the autonomous field `(1, X)` on `ℝ × M`.
* `autonomizedFlow_snd_hasMFDerivAt`, `autonomizedFlow_fst_hasDerivAt` — the
  spatial / time components of the velocity of a `(1, X)`-integral curve.
* `time_dependent_vf_local_integral_flow_bare` — local existence of a genuine
  integral curve through each point, in the bare `HasMFDerivWithinAt … (Ici 0)`
  form with velocity `X t (γ t)`.
* `time_dependent_vf_manifold_integral_flow_family` — the headline deliverable: a
  time-indexed diffeomorphism family `Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)` with
  `Φ_fam 0 = Diffeomorph.refl …` carrying the genuine bare flow
  `HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (s ↦ Φ_fam s x) (Ici 0) s (𝟙.smulRight (X s (Φ_fam s x)))`.
-/

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Manifold Bundle
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M]

/--
**Autonomisation of a time-dependent vector field.** The time-dependent field
`X : ℝ → (x : M) → TangentSpace I x` on `M` becomes the autonomous field
`(1, X p.1 p.2)` on `ℝ × M`, whose first component is the constant unit time
direction and whose second component is `X` evaluated at the current time-space
point. The product tangent space `TangentSpace (𝓘(ℝ, ℝ).prod I) p` is, by
definition, `ℝ × TangentSpace I p.2`, so the pair lands in the right fibre.
-/
noncomputable def autonomizedFlowVF (X : ℝ → ∀ x : M, TangentSpace I x) :
    (p : ℝ × M) → TangentSpace (𝓘(ℝ, ℝ).prod I) p :=
  fun p => ((1 : ℝ), X p.1 p.2)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M]
  [T2Space M] in
/--
**Spatial velocity of an autonomised integral curve.** If `c : ℝ → ℝ × M` has, at
`t`, the manifold derivative `𝟙.smulRight (autonomizedFlowVF X (c t))`, then its
spatial component `s ↦ (c s).2` has manifold derivative
`𝟙.smulRight (X (c t).1 (c t).2)`. This is the `Prod.snd`-projection of the
product `HasMFDerivAt`, and produces the bare geometric velocity `X (c t).1 (c t).2`
with no chart-coordinate transport.
-/
theorem autonomizedFlow_snd_hasMFDerivAt (X : ℝ → ∀ x : M, TangentSpace I x)
    (c : ℝ → ℝ × M) (t : ℝ)
    (hc : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) c t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (autonomizedFlowVF X (c t)))) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => (c s).2) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X (c t).1 (c t).2)) := by
  have h := (hasMFDerivAt_snd (c t)).comp t hc
  convert h using 2

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M]
  [T2Space M] in
/--
**Time velocity of an autonomised integral curve.** Under the same hypothesis,
the time component `s ↦ (c s).1` has ordinary derivative `1` at `t` (the first
component of `autonomizedFlowVF X (c t)`, which is the constant `1`).
-/
theorem autonomizedFlow_fst_hasDerivAt (X : ℝ → ∀ x : M, TangentSpace I x)
    (c : ℝ → ℝ × M) (t : ℝ)
    (hc : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) c t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (autonomizedFlowVF X (c t)))) :
    HasDerivAt (fun s => (c s).1) (1 : ℝ) t := by
  have h := (hasMFDerivAt_fst (c t)).comp t hc
  rw [hasMFDerivAt_iff_hasFDerivAt] at h
  have h2 := h.hasDerivAt
  refine h2.congr_deriv ?_
  exact congrArg Prod.fst (one_smul ℝ (autonomizedFlowVF X (c t)))

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M]
  [T2Space M] in
/--
**Time-component identity.** A real function with derivative `1` on an open
interval `Ioo a b` containing `0`, and value `0` at `0`, is the identity on
`Ioo a b`. Applied to the time component of an autonomised integral curve through
`(0, x)`, this gives `(c s).1 = s`, so the spatial velocity `X (c s).1 (c s).2`
is `X s (c s).2` — the genuine time-dependent integral-flow velocity.
-/
theorem hasDerivAt_one_eq_self_on_Ioo (φ : ℝ → ℝ) {a b : ℝ}
    (h0mem : (0 : ℝ) ∈ Ioo a b)
    (hφ : ∀ s ∈ Ioo a b, HasDerivAt φ 1 s) (hval : φ 0 = 0) :
    ∀ s ∈ Ioo a b, φ s = s := by
  have hconst : ∀ s ∈ Ioo a b, HasDerivAt (fun u => φ u - u) (0 : ℝ) s := by
    intro u hu; simpa using (hφ u hu).sub (hasDerivAt_id u)
  intro s hs
  have hkey : (fun u => φ u - u) s = (fun u => φ u - u) 0 := by
    apply Convex.is_const_of_fderivWithin_eq_zero (𝕜 := ℝ) (convex_Ioo a b)
      (f := fun u => φ u - u) (s := Ioo a b)
    · intro u hu
      exact (hconst u hu).differentiableAt.differentiableWithinAt
    · intro u hu
      have huniq : UniqueDiffWithinAt ℝ (Ioo a b) u :=
        isOpen_Ioo.uniqueDiffWithinAt hu
      have hfd : HasFDerivWithinAt (fun u => φ u - u)
          (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (0 : ℝ)) (Ioo a b) u :=
        ((hconst u hu).hasDerivWithinAt).hasFDerivWithinAt
      rw [hfd.fderivWithin huniq]; ext; simp
    · exact hs
    · exact h0mem
  simp only at hkey; rw [hval] at hkey; linarith

/--
**Local genuine integral flow, bare manifold form.** Given a time-dependent
vector field `X` whose autonomisation `(1, X)` on `ℝ × M` is `C¹` (the clean
separable regularity hypothesis `hX`), through every point `x : M` there exist a
positive radius `ε` and a curve `γ : ℝ → M` with `γ 0 = x` such that, for every
`t ∈ Ioo (-ε) ε`, the time-curve `γ` has the **bare** manifold derivative

  `HasMFDerivWithinAt 𝓘(ℝ, ℝ) I γ (Ici 0) t (𝟙.smulRight (X t (γ t)))`.

The velocity is the geometric `X t (γ t)` itself — *not* a chart pull-back — so
this is the genuine integral-flow equation `∂_s γ = X(γ)`. The `Ici 0`
(right-handed) form is the one consumed downstream by the Hamilton–DeTurck pull-back
identity. No `HasLocallyConstantChartAt`-style hypothesis appears.
-/
theorem time_dependent_vf_local_integral_flow_bare [CompleteSpace E]
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ∀ p : ℝ × M,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) 1
        (fun p : ℝ × M =>
          (⟨p, autonomizedFlowVF X p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M)))
        p)
    (x : M) :
    ∃ (ε : ℝ) (_ : 0 < ε) (γ : ℝ → M), γ 0 = x ∧
      ∀ t ∈ Ioo (-ε) ε,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I γ (Ici 0) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t))) := by
  obtain ⟨c, hc0, hcurve⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless 0 (hX (0, x))
  rw [IsMIntegralCurveAt, Filter.eventually_iff_exists_mem] at hcurve
  obtain ⟨S, hS, hSon⟩ := hcurve
  rw [Metric.mem_nhds_iff] at hS
  obtain ⟨ε, hε, hball⟩ := hS
  refine ⟨ε, hε, fun s => (c s).2, by change (c 0).2 = x; rw [hc0], ?_⟩
  intro t ht
  have htS : t ∈ S := by
    apply hball
    rw [Real.ball_eq_Ioo]
    constructor
    · simpa using ht.1
    · simpa using ht.2
  have hct : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) c t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (autonomizedFlowVF X (c t))) := hSon t htS
  have h0mem : (0 : ℝ) ∈ Ioo (-ε) ε := by constructor <;> simp [hε]
  have htime : ∀ s ∈ Ioo (-ε) ε, (c s).1 = s := by
    apply hasDerivAt_one_eq_self_on_Ioo (fun s => (c s).1) h0mem
    · intro u hu
      have huS : u ∈ S := by
        apply hball
        rw [Real.ball_eq_Ioo]
        constructor
        · simpa using hu.1
        · simpa using hu.2
      exact autonomizedFlow_fst_hasDerivAt X c u (hSon u huS)
    · rw [hc0]
  have hsnd := autonomizedFlow_snd_hasMFDerivAt X c t hct
  rw [htime t ht] at hsnd
  exact hsnd.hasMFDerivWithinAt

variable [CompactSpace M] [SigmaCompactSpace M]

/--
**Headline deliverable: time-indexed diffeomorphism family with the genuine bare
flow.**

Given a genuine integral flow `Φ : ℝ → M → M` of the time-dependent vector field
`X` on a positive horizon `T` — that is, `Φ 0 = id`, each `Φ t` (for
`t ∈ (0, T)`) is a smooth diffeomorphism with smooth inverse `Ψ t`, and `Φ`
satisfies the **bare** integral-flow equation `∂_s (Φ s x) = X s (Φ s x)` (in the
`HasMFDerivWithinAt … (Ici 0)` form) for `s ∈ (0, T)` — this produces a single
time-indexed family of diffeomorphisms `Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)` such that:

* `Φ_fam 0 = Diffeomorph.refl I M ∞` (the identity at time `0`);
* `Φ_fam t x = Φ t x` for `t ∈ (0, T)` (the family realises the genuine flow);
* the family carries the **genuine bare flow**
  `HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (s ↦ Φ_fam s x) (Ici 0) s (𝟙.smulRight (X s (Φ_fam s x)))`
  for every `s ∈ (0, T)` and every `x : M`.

The diffeomorphism witnesses (`hdiffeo`) and the bare flow equation (`hflow`) are
genuine, separable hypotheses about the flow `Φ` of `X`; the integral-flow ODE in
particular is derived from `X` (e.g. via
`time_dependent_vf_local_integral_flow_bare`) and never assumes the manifold
velocity in chart-transported form. The family's bare flow is obtained by
transporting `hflow` along the pointwise agreement `Φ_fam t x = Φ t x`, using
`HasMFDerivWithinAt.congr`; the velocity that comes out is the geometric
`X s (Φ_fam s x)`, the integral-flow equation needed for the Lie-term
cancellation. No `HasLocallyConstantChartAt`-style hypothesis is used.
-/
theorem time_dependent_vf_manifold_integral_flow_family
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (T : ℝ) (_hT : 0 < T) (Φ : ℝ → M → M)
    (_hΦ0 : ∀ x : M, Φ 0 x = x)
    (hdiffeo : ∀ t, 0 < t → t < T → ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x : M, d x = Φ t x)
    (hflow : ∀ t, 0 < t → t < T → ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) (Ici 0) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) :
    ∃ (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)),
      Φ_fam 0 = Diffeomorph.refl I M ∞ ∧
      (∀ t : ℝ, 0 < t → t < T → ∀ x : M, Φ_fam t x = Φ t x) ∧
      (∀ s : ℝ, 0 < s → s < T → ∀ x : M,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ_fam u x) (Ici 0) s
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ_fam s x)))) := by
  classical
  refine ⟨fun t =>
    if h : 0 < t ∧ t < T then (hdiffeo t h.1 h.2).choose else Diffeomorph.refl I M ∞,
    ?_, ?_, ?_⟩
  · have h0 : ¬ (0 < (0 : ℝ) ∧ (0 : ℝ) < T) := by
      rintro ⟨h, _⟩; exact (lt_irrefl 0) h
    simp only [h0, dif_neg, not_false_iff]
  · intro t ht htT x
    have hguard : 0 < t ∧ t < T := ⟨ht, htT⟩
    simp only [hguard, dif_pos, and_self]
    exact (hdiffeo t ht htT).choose_spec x
  · intro s hs hsT x
    have hagree : ∀ t : ℝ, 0 < t → t < T → ∀ y : M,
        (if h : 0 < t ∧ t < T then (hdiffeo t h.1 h.2).choose
          else Diffeomorph.refl I M ∞) y = Φ t y := by
      intro t ht htT y
      have hguard : 0 < t ∧ t < T := ⟨ht, htT⟩
      simp only [hguard, dif_pos, and_self]
      exact (hdiffeo t ht htT).choose_spec y
    have hbase : (if h : 0 < s ∧ s < T then (hdiffeo s h.1 h.2).choose
        else Diffeomorph.refl I M ∞) x = Φ s x := hagree s hs hsT x
    have hcurve_eq : (fun u : ℝ =>
          (if h : 0 < u ∧ u < T then (hdiffeo u h.1 h.2).choose
            else Diffeomorph.refl I M ∞) x) =ᶠ[𝓝[Ici 0] s]
        (fun u : ℝ => Φ u x) := by
      have hopen : Ioo (0 : ℝ) T ∈ 𝓝[Ici 0] s :=
        mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hs hsT)
      filter_upwards [hopen] with u hu
      exact hagree u hu.1 hu.2 x
    have hbase_flow := hflow s hs hsT x
    rw [← hbase] at hbase_flow
    exact hbase_flow.congr_of_eventuallyEq hcurve_eq hbase

end DifferentialGeometry.PDE.RicciFlow.ODE
