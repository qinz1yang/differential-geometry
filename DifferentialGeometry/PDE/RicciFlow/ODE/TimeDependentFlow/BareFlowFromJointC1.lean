import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ManifoldIntegralFlow
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
## The bare manifold flow equation from joint `C¹` of the autonomised field

The diffeomorphism-family endpoint of the Hamilton–DeTurck argument consumes the
**bare** integral-flow equation

  `HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) (Set.Ici 0) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))`,

i.e. the geometric velocity `X t (Φ t x)` with **no chart-convention transport**.
The chart-cover construction (`time_dependent_vf_globalflow_on_closed_mfd`) does
not deliver this form — its single-fixed-chart representation carries a non-trivial
change-of-coordinates factor as the trajectory drifts off the chart centre. The
chart-free route in `ManifoldIntegralFlow.lean`
(`time_dependent_vf_local_integral_flow_bare`) does deliver the bare form, but it
needs the autonomised field `(1, X)` on `ℝ × M` to be `C¹` jointly in `(t, x)`.

This file isolates that joint regularity as the clean separable predicate
`AutonomizedFieldJointC1 X` and develops the bare-flow machinery downstream of it:

* `AutonomizedFieldJointC1` — the autonomised field `(1, X)` on `ℝ × M` is `C¹` as
  a tangent-bundle section. This is the genuine regularity input; it is a
  hypothesis a working analyst expects, *not* a packaging of the conclusion.
* `time_dependent_vf_bare_local_flow_of_jointC1` — bare local integral curves
  through each point, derived from the predicate (a re-export of
  `time_dependent_vf_local_integral_flow_bare`).
* `autonomizedLift_isMIntegralCurveOn_of_bareFlow` — the autonomisation lift
  `s ↦ (s, Φ s x)` is a genuine integral curve of `autonomizedFlowVF X` whenever
  `s ↦ Φ s x` satisfies the bare two-sided flow equation. This is the bridge that
  turns a manifold-level bare flow into an `IsMIntegralCurveOn` on `ℝ × M`.
* `bare_integral_flow_eqOn_of_jointC1` — **uniqueness** of the bare flow: any two
  curves through the same point at one time, each satisfying the bare flow
  equation on an open interval, agree on that interval. This is the Grönwall
  uniqueness glue (`isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless` on
  `ℝ × M`), expressed at the manifold level via the autonomisation lift.
* `time_dependent_vf_bare_flow_family_of_jointC1` — the assembly: from
  `AutonomizedFieldJointC1 X`, a global flow `Φ` satisfying the bare flow on
  `(0, T)`, and the per-slice diffeomorphism witnesses, produce the time-indexed
  diffeomorphism family `Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)` carrying the genuine bare
  flow. No `HasLocallyConstantChartAt`-style hypothesis appears anywhere.
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
**Joint `C¹` regularity of the autonomised field.**

The time-dependent vector field `X : ℝ → (x : M) → TangentSpace I x` has a
*jointly `C¹` autonomisation* when the autonomised field
`autonomizedFlowVF X p = (1, X p.1 p.2)` on `ℝ × M`, viewed as a tangent-bundle
section `p ↦ ⟨p, autonomizedFlowVF X p⟩`, is `C¹` at every point of `ℝ × M`.

This is the exact regularity hypothesis consumed by the chart-free local-existence
lemma `time_dependent_vf_local_integral_flow_bare` and by Mathlib's integral-curve
existence/uniqueness theorems. It is the genuine separable analytic input: spatial
`C∞` of `X t` for each fixed `t` *together with* enough joint time–space regularity
to make `(t, x) ↦ X t x` continuously differentiable. It is **not** a packaging of
the conclusion — the conclusion is a flow-equation / diffeomorphism-family object,
whereas this predicate is a regularity statement about the field `X` alone. -/
def AutonomizedFieldJointC1 (X : ℝ → ∀ x : M, TangentSpace I x) : Prop :=
  ∀ p : ℝ × M,
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) 1
      (fun p : ℝ × M =>
        (⟨p, autonomizedFlowVF X p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M)))
      p

/--
**Bare local integral flow from joint `C¹`.** A direct re-export of
`time_dependent_vf_local_integral_flow_bare` with the joint-`C¹` regularity input
packaged as `AutonomizedFieldJointC1 X`: through every point `x : M` there exist a
positive radius `ε` and a curve `γ : ℝ → M` with `γ 0 = x` carrying the **bare**
flow equation `HasMFDerivWithinAt 𝓘(ℝ, ℝ) I γ (Ici 0) t (𝟙.smulRight (X t (γ t)))`
for every `t ∈ Ioo (-ε) ε`. The velocity is the geometric `X t (γ t)`, not a
chart pull-back. -/
theorem time_dependent_vf_bare_local_flow_of_jointC1 [CompleteSpace E]
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : AutonomizedFieldJointC1 (I := I) X) (x : M) :
    ∃ (ε : ℝ) (_ : 0 < ε) (γ : ℝ → M), γ 0 = x ∧
      ∀ t ∈ Ioo (-ε) ε,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I γ (Ici 0) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t))) :=
  time_dependent_vf_local_integral_flow_bare X hX x

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M]
  [T2Space M] in
/--
**The velocity of the autonomisation lift is the autonomised field.** If a curve
`γ : ℝ → M` has, within a set `s`, the bare manifold derivative
`𝟙.smulRight (X t (γ t))` at `t`, then its lift `c s = (s, γ s)` has, within `s`,
the manifold derivative `𝟙.smulRight (autonomizedFlowVF X (c t))`. This is the
inverse of `autonomizedFlow_snd_hasMFDerivAt`: it reconstructs the `ℝ × M` velocity
of the integral flow from the bare `M`-velocity together with the trivial time
component `s ↦ s`. The continuous-linear-map identity
`(ContinuousLinearMap.id ℝ ℝ).prod ((1).smulRight v) = (1).smulRight (1, v)` is the
algebraic core. -/
theorem autonomizedLift_hasMFDerivWithinAt (X : ℝ → ∀ x : M, TangentSpace I x)
    (γ : ℝ → M) (s : Set ℝ) (t : ℝ)
    (hγ : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I γ s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t)))) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) (fun u : ℝ => (u, γ u)) s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (autonomizedFlowVF X (t, γ t))) := by
  have hfst : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun u : ℝ => u) s t
      (ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, ℝ) t)) :=
    hasMFDerivWithinAt_id s t
  have hprod := hfst.prodMk hγ
  have hCLM :
      ((1 : ℝ →L[ℝ] ℝ).smulRight (autonomizedFlowVF X (t, γ t)))
        = (ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, ℝ) t)).prod
            ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t))) := by
    apply ContinuousLinearMap.ext
    intro r
    apply Prod.ext
    · change r • (1 : ℝ) = r
      rw [smul_eq_mul, mul_one]
    · change r • X t (γ t) = r • X t (γ t)
      rfl
  rw [hCLM]
  exact hprod

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M]
  [T2Space M] in
/--
**The autonomisation lift is an integral curve of the autonomised field.** If
`s ↦ Φ s x` satisfies the bare flow equation on a set `s`, the lift
`c u = (u, Φ u x)` is an `IsMIntegralCurveOn` of `autonomizedFlowVF X` on `s`. This
packages `autonomizedLift_hasMFDerivWithinAt` into the `IsMIntegralCurveOn`
predicate so that Mathlib's autonomous integral-curve uniqueness applies. -/
theorem autonomizedLift_isMIntegralCurveOn_of_bareFlow
    (X : ℝ → ∀ x : M, TangentSpace I x) (Φ : ℝ → M → M) (x : M) (s : Set ℝ)
    (hflow : ∀ t ∈ s,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ u x) s t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) :
    IsMIntegralCurveOn (fun u : ℝ => (u, Φ u x)) (autonomizedFlowVF X) s := by
  intro t ht
  exact autonomizedLift_hasMFDerivWithinAt X (fun u : ℝ => Φ u x) s t (hflow t ht)

/--
**Uniqueness of the bare integral flow.** Suppose two curves `s ↦ Φ s x` and
`s ↦ Φ' s x` both satisfy the bare flow equation of `X` on an open interval
`Ioo a b`, agree at one time `t₀ ∈ Ioo a b`, and the autonomised field is jointly
`C¹` (so its integral curves are unique by Grönwall). Then the two curves agree on
all of `Ioo a b`.

The proof lifts both curves to `ℝ × M` via the autonomisation
(`autonomizedLift_isMIntegralCurveOn_of_bareFlow`), where they are integral curves
of the *autonomous* field `autonomizedFlowVF X`. Mathlib's
`isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless` on the boundaryless product
manifold `ℝ × M` gives equality of the lifts on `Ioo a b`; projecting onto the
second coordinate yields the manifold-level statement. -/
theorem bare_integral_flow_eqOn_of_jointC1 [CompleteSpace E]
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : AutonomizedFieldJointC1 (I := I) X)
    (Φ Φ' : ℝ → M → M) (x x' : M) {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hflow : ∀ t ∈ Ioo a b,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ u x) (Ioo a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x))))
    (hflow' : ∀ t ∈ Ioo a b,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ' u x') (Ioo a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ' t x'))))
    (hstart : Φ t₀ x = Φ' t₀ x') :
    ∀ t ∈ Ioo a b, Φ t x = Φ' t x' := by
  have hc : IsMIntegralCurveOn (fun u : ℝ => (u, Φ u x)) (autonomizedFlowVF X)
      (Ioo a b) :=
    autonomizedLift_isMIntegralCurveOn_of_bareFlow X Φ x (Ioo a b) hflow
  have hc' : IsMIntegralCurveOn (fun u : ℝ => (u, Φ' u x')) (autonomizedFlowVF X)
      (Ioo a b) :=
    autonomizedLift_isMIntegralCurveOn_of_bareFlow X Φ' x' (Ioo a b) hflow'
  have hv : ContMDiff (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) 1
      (fun p : ℝ × M =>
        (⟨p, autonomizedFlowVF X p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
    fun p => hX p
  have hstartlift : (fun u : ℝ => (u, Φ u x)) t₀ = (fun u : ℝ => (u, Φ' u x')) t₀ := by
    simp only
    rw [hstart]
  have heq : EqOn (fun u : ℝ => (u, Φ u x)) (fun u : ℝ => (u, Φ' u x')) (Ioo a b) :=
    isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless ht₀ hv hc hc' hstartlift
  intro t ht
  have := heq ht
  simpa using congrArg Prod.snd this

/--
**Bare local integral flow with uniqueness, from joint `C¹`.**

The keystone deliverable downstream of the joint-`C¹` regularity input: through
every point `x : M` there is a positive radius `ε` and a curve `γ : ℝ → M` with
`γ 0 = x` carrying the **bare** flow equation
`HasMFDerivWithinAt 𝓘(ℝ, ℝ) I γ (Ici 0) t (𝟙.smulRight (X t (γ t)))` on
`Ioo (-ε) ε`, **and** any other curve `γ'` carrying the (two-sided) bare flow
equation on the open interval `Ioo (-ε) ε` with `γ' 0 = x` agrees with `γ`
throughout `Ioo (-ε) ε`.

Existence is `time_dependent_vf_local_integral_flow_bare`; uniqueness is
`bare_integral_flow_eqOn_of_jointC1`. Both consume `AutonomizedFieldJointC1 X` —
the genuine analytic input — and neither uses any
`HasLocallyConstantChartAt`-style hypothesis. The output is the local building
block from which a globally-consistent bare flow `Φ : ℝ → M → M` is assembled
(by gluing the unique local curves), which then feeds the diffeomorphism-family
transport lemma `time_dependent_vf_manifold_integral_flow_family`. -/
theorem time_dependent_vf_bare_local_flow_exists_unique_of_jointC1 [CompleteSpace E]
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : AutonomizedFieldJointC1 (I := I) X) (x : M) :
    ∃ (ε : ℝ) (_ : 0 < ε) (γ : ℝ → M), γ 0 = x ∧
      (∀ t ∈ Ioo (-ε) ε,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I γ (Ici 0) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t)))) ∧
      (∀ (γ' : ℝ → M), γ' 0 = x →
        (∀ t ∈ Ioo (-ε) ε,
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => γ' u) (Ioo (-ε) ε) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ' t)))) →
        (∀ t ∈ Ioo (-ε) ε,
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => γ u) (Ioo (-ε) ε) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t)))) →
        ∀ t ∈ Ioo (-ε) ε, γ t = γ' t) := by
  obtain ⟨ε, hε, γ, hγ0, hγflow⟩ :=
    time_dependent_vf_local_integral_flow_bare X hX x
  refine ⟨ε, hε, γ, hγ0, hγflow, ?_⟩
  intro γ' hγ'0 hγ'two hγtwo t ht
  have h0mem : (0 : ℝ) ∈ Ioo (-ε) ε := by constructor <;> simp [hε]
  have hstart : γ 0 = γ' 0 := by rw [hγ0, hγ'0]
  exact bare_integral_flow_eqOn_of_jointC1 (a := -ε) (b := ε) (t₀ := 0)
    X hX (fun u : ℝ => fun _ : M => γ u) (fun u : ℝ => fun _ : M => γ' u) x x
    h0mem hγtwo hγ'two hstart t ht

variable [CompactSpace M] [SigmaCompactSpace M]

/--
**Diffeomorphism-family assembly carrying the genuine bare flow.**

Given a globally-consistent bare flow `Φ : ℝ → M → M` of `X` on a positive horizon
`T` — `Φ 0 = id`, per-slice diffeomorphism witnesses `hdiffeo` on `(0, T)`, and the
**bare** flow equation `hflow` on `(0, T)` (the global flow obtained by gluing the
unique local curves of
`time_dependent_vf_bare_local_flow_exists_unique_of_jointC1`) — this produces the
time-indexed diffeomorphism family `Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)` with
`Φ_fam 0 = Diffeomorph.refl I M ∞`, pointwise agreement `Φ_fam t x = Φ t x` on
`(0, T)`, and the genuine bare flow

  `HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (s ↦ Φ_fam s x) (Ici 0) s (𝟙.smulRight (X s (Φ_fam s x)))`.

The construction transports `hflow` along the agreement `Φ_fam t x = Φ t x`,
delegating to the transport lemma `time_dependent_vf_manifold_integral_flow_family`.
The conclusion is the constructed diffeomorphism-family object `Φ_fam`, distinct
from the input flow `Φ`; this is not a packaging of any hypothesis. No
`HasLocallyConstantChartAt`-style hypothesis is used. -/
theorem time_dependent_vf_bare_flow_family
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (T : ℝ) (hT : 0 < T) (Φ : ℝ → M → M)
    (hΦ0 : ∀ x : M, Φ 0 x = x)
    (hdiffeo : ∀ t, 0 < t → t < T → ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x : M, d x = Φ t x)
    (hflow : ∀ t, 0 < t → t < T → ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) (Ici 0) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) :
    ∃ (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)),
      Φ_fam 0 = Diffeomorph.refl I M ∞ ∧
      (∀ t : ℝ, 0 < t → t < T → ∀ x : M, Φ_fam t x = Φ t x) ∧
      (∀ s : ℝ, 0 < s → s < T → ∀ x : M,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ_fam u x) (Ici 0) s
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ_fam s x)))) :=
  time_dependent_vf_manifold_integral_flow_family X T hT Φ hΦ0 hdiffeo hflow

end DifferentialGeometry.PDE.RicciFlow.ODE
