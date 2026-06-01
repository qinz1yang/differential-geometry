import DifferentialGeometry.Analysis.ODE.FlowC1Continuous

/-!
# `ContDiffOn ℝ k` regularity of the local flow

For a time-dependent vector field `f : ℝ → E → E` on a Banach space `E` and a local
Picard–Lindelöf flow `Φ : E × ℝ → E` packaged by `IsLocalFlow`, the previous file
`FlowC1Continuous.lean` established the joint `C^1` regularity of `Φ` on a strictly
interior open neighbourhood of `(x₀, t₀)`, under the assumption that `f` is jointly
`C^1`.

This file is the entry-point for the *general* `C^k` regularity question: if `f` is
jointly `C^k`, then `Φ` is jointly `C^k`.  The mathematical content has two stages.

## Stage 1: `C^1` headline theorem (proved here).

The headline theorem `contDiffOn_flow_of_isLocalFlow_of_contDiff` takes a `ContDiffOn ℝ k`
hypothesis on `f` for any `k ∈ ℕ∞` with `1 ≤ k`, and delivers `ContDiffOn ℝ 1 Φ U` on the
same strictly-interior neighbourhood as `FlowC1Continuous`.  Internally it reduces to
`contDiffOn_flow_of_isLocalFlow` via `ContDiffOn.of_le`.

## Stage 2: induction `k → k + 1` (deferred).

The genuine `C^k` claim is proved by induction on `k`.  The inductive step requires that
the joint Fréchet derivative `D Φ : E × ℝ → ((E × ℝ) →L[ℝ] E)` is itself jointly `C^{k-1}`.
By V.2.c.2 the derivative decomposes as a coproduct

```
D Φ (x, t) = Lsp (x, t) .coprod (Lti (x, t))
```

where

* `Lti (x, t) : ℝ →L[ℝ] E` is the time-direction CLM `(id_ℝ).smulRight (f t (Φ ⟨x, t⟩))`.
  Its smoothness in `(x, t)` reduces to the smoothness of the composition
  `(x, t) ↦ f t (Φ ⟨x, t⟩)` — straightforward from `ContDiff.comp` once `Φ` is `C^k` and
  `f` is `C^{k+1}`.  The CLM-construction `v ↦ (id_ℝ).smulRight v` is itself a bounded
  linear map, hence smooth.  This piece is fully addressed in the preparatory section
  `TimePieceSmoothness` below.

* `Lsp (x, t) : E →L[ℝ] E` is the variational linear map at `(x, t)`, defined by the
  variational ODE `y'(t) = (D_x f)(t, Φ(x, t)) y(t)`.  Proving that `Lsp` is jointly
  `C^{k-1}` on its parameter domain requires a *smooth dependence on parameters* theorem
  for linear ODEs: if the coefficient map `A : E × ℝ → (E →L[ℝ] E)` is `C^j` jointly
  (here `A (x, t) = (D_x f)(t, Φ(x, t))`), the solution `y_δ (x, t)` of `y'(x, t) =
  A(x, t) y(x, t)` with `y_δ(x, t₀) = δ` is `C^j` jointly in `(x, t)`.  This is itself
  an inductive theorem; its core inductive step in turn requires the parameter version
  of `contDiffOn_enat_Icc_of_hasDerivWithinAt` for solutions of `t`-dependent linear
  ODEs.  That infrastructure is not yet present and is left for a follow-up.

## Files

This file imports `FlowC1Continuous.lean` and provides the headline `C^1` theorem in the
unified `C^k` signature, together with the preparatory smoothness lemma for the time
piece `(x, t) ↦ f t (Φ ⟨x, t⟩)` which will plug into the eventual induction.

All theorems are formulated on a generic Banach space `E`; `[InnerProductSpace ℝ E]` is
*not* used.  No manifold or tensor file is imported.
-/

noncomputable section

open Set Function Filter Metric Asymptotics Real
open scoped Topology NNReal

namespace DifferentialGeometry
namespace Analysis
namespace ODE
namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

section TimePieceSmoothness

variable {f : ℝ → E → E} {Φ : E × ℝ → E}

/-- The "graph map" `(x, t) ↦ (t, Φ ⟨x, t⟩)` is jointly `C^k` on the open neighbourhood
`U`, provided `Φ` is jointly `C^k` on `U`.  This is a building block for showing the
time piece of the Fréchet derivative is `C^k`. -/
lemma contDiffOn_graphMap_of_contDiffOn_flow
    {k : ℕ∞} {U : Set (E × ℝ)} (hΦ_Ck : ContDiffOn ℝ k Φ U) :
    ContDiffOn ℝ k (fun q : E × ℝ => ((q.2, Φ q) : ℝ × E)) U := by
  refine ContDiffOn.prodMk ?_ hΦ_Ck
  exact contDiff_snd.contDiffOn

/-- **Smoothness of the time piece `(x, t) ↦ f t (Φ ⟨x, t⟩)`.**  If `f` is jointly
`C^k` on `Set.univ` and `Φ` is jointly `C^k` on the open set `U`, then the composition
`(x, t) ↦ f t (Φ ⟨x, t⟩)` is jointly `C^k` on `U`. -/
theorem contDiffOn_orbit_composition
    {k : ℕ∞} {U : Set (E × ℝ)}
    (hf_Ck : ContDiffOn ℝ k (uncurry f) (Set.univ : Set (ℝ × E)))
    (hΦ_Ck : ContDiffOn ℝ k Φ U) :
    ContDiffOn ℝ k (fun q : E × ℝ => f q.2 (Φ q)) U := by
  set g : E × ℝ → ℝ × E := fun q => (q.2, Φ q) with hg_def
  have hg : ContDiffOn ℝ k g U := contDiffOn_graphMap_of_contDiffOn_flow hΦ_Ck
  have hmaps : MapsTo g U (Set.univ : Set (ℝ × E)) := fun _ _ => mem_univ _
  have hcomp : ContDiffOn ℝ k (uncurry f ∘ g) U := hf_Ck.comp hg hmaps
  convert hcomp using 1

/-- The CLM-valued time piece `(x, t) ↦ (id_ℝ).smulRight (f t (Φ ⟨x, t⟩))` is
jointly `C^k` on `U` whenever `(x, t) ↦ f t (Φ ⟨x, t⟩)` is `C^k`.  The construction
`v ↦ (id_ℝ).smulRight v` is a bounded linear map `E →L[ℝ] (ℝ →L[ℝ] E)` and so smooth. -/
theorem contDiffOn_timePiece_CLM
    {k : ℕ∞} {U : Set (E × ℝ)}
    (hf_Ck : ContDiffOn ℝ k (uncurry f) (Set.univ : Set (ℝ × E)))
    (hΦ_Ck : ContDiffOn ℝ k Φ U) :
    ContDiffOn ℝ k (fun q : E × ℝ =>
      (ContinuousLinearMap.id ℝ ℝ).smulRight (f q.2 (Φ q))) U := by
  set h : E × ℝ → E := fun q => f q.2 (Φ q) with hh_def
  have hh : ContDiffOn ℝ k h U := contDiffOn_orbit_composition hf_Ck hΦ_Ck
  set S : E →L[ℝ] (ℝ →L[ℝ] E) :=
    ContinuousLinearMap.smulRightL ℝ ℝ E (ContinuousLinearMap.id ℝ ℝ) with hS_def
  have hSeq : (fun v : E => (ContinuousLinearMap.id ℝ ℝ).smulRight v) = fun v => S v := by
    funext v
    simp [S, ContinuousLinearMap.smulRightL]
  have heq : (fun q : E × ℝ => (ContinuousLinearMap.id ℝ ℝ).smulRight (f q.2 (Φ q)))
      = S ∘ h := by
    funext q
    change (ContinuousLinearMap.id ℝ ℝ).smulRight (f q.2 (Φ q))
      = S (f q.2 (Φ q))
    simp [S, ContinuousLinearMap.smulRightL]
  rw [heq]
  exact ContDiffOn.continuousLinearMap_comp S hh

end TimePieceSmoothness

section MainTheorem

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-- **Local flow of a `C^k` vector field is locally `C^1` (and hence `C^min(k, 1)`).**

For a time-dependent vector field `f : ℝ → E → E` that is jointly `ContDiffOn ℝ k` on
`Set.univ` with `1 ≤ k`, and a local Picard–Lindelöf flow `Φ` packaged by `IsLocalFlow`,
the flow `Φ` is jointly `C^1` on the strictly-interior open neighbourhood
`ball x₀ ρ ×ˢ Ioo (t₀ - T) (t₀ + T)` provided by V.2.c.2.

The conclusion is stated at the constant regularity `1`, not at `k` itself.  Promoting
the conclusion to `C^k` for `k ≥ 2` requires a separate smooth-dependence-on-parameters
theorem for linear ODEs (the spatial piece of the Fréchet derivative is the variational
linear map of a linear ODE with parameter-dependent coefficients).  This promotion is
left for a follow-up; see the file header. -/
theorem contDiffOn_flow_of_isLocalFlow_of_contDiff
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {k : ℕ∞} (hk : 1 ≤ k)
    (hf_Ck : ContDiffOn ℝ k (uncurry f) (Set.univ : Set (ℝ × E)))
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M) :
    ContDiffOn ℝ 1 Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  have hk' : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((k : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast hk
  have hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)) := by
    have h := hf_Ck.of_le hk'
    simpa using h
  exact contDiffOn_flow_of_isLocalFlow (f := f) (t₀ := t₀) (x₀ := x₀) (r := r)
    (tmin := tmin) (tmax := tmax) (Φ := Φ) hΦ hf_C1 hT hT_lt_mid hT_mid_lt_out hM hMT_mid
    hsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd

/-- **Convenient packaged form.**  Existence of an open neighbourhood of `(x₀, t₀)` on
which the flow is jointly `C^1`, from `ContDiffOn ℝ k` of the vector field for any
`k ∈ ℕ∞` with `1 ≤ k`.

The neighbourhood is `ball x₀ ρ ×ˢ Ioo (t₀ - T) (t₀ + T)` with strictly positive `ρ` and
`T` extracted from the local flow's regularity data.  Hypotheses `hbnd` packages a uniform
bound on the spatial derivative of `f` along the orbits in a closed ball / closed time
interval; in concrete applications this follows from compactness + joint continuity. -/
theorem exists_contDiffOn_flow_of_contDiff
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {k : ℕ∞} (hk : 1 ≤ k)
    (hf_Ck : ContDiffOn ℝ k (uncurry f) (Set.univ : Set (ℝ × E)))
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r') (hρ_pos : 0 < (ρ : ℝ))
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M) :
    ∃ U : Set (E × ℝ), IsOpen U ∧ (x₀, t₀) ∈ U ∧
      ContDiffOn ℝ 1 Φ U := by
  set U : Set (E × ℝ) := ball x₀ (ρ : ℝ) ×ˢ Ioo (t₀ - T) (t₀ + T) with hU_def
  refine ⟨U, ?_, ?_, ?_⟩
  · exact isOpen_ball.prod isOpen_Ioo
  · refine ⟨?_, ?_⟩
    · exact mem_ball_self hρ_pos
    · exact ⟨by linarith, by linarith⟩
  · exact contDiffOn_flow_of_isLocalFlow_of_contDiff hΦ hk hf_Ck hT hT_lt_mid hT_mid_lt_out
      hM hMT_mid hsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd

end MainTheorem

section InductiveStep

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-- The **time piece** of the joint Fréchet derivative: the CLM `s ↦ s • f t (Φ ⟨x, t⟩)`
viewed as a function of `(x, t)`.  This is total on `E × ℝ` and, by V.2.c.2's joint
derivative formula, agrees with the time-direction partial Fréchet derivative of `Φ` at
every interior `(x, t)`. -/
def timePieceFn (f : ℝ → E → E) (Φ : E × ℝ → E) : E × ℝ → (ℝ →L[ℝ] E) :=
  fun q => (ContinuousLinearMap.id ℝ ℝ).smulRight (f q.2 (Φ q))

@[simp]
lemma timePieceFn_apply (f : ℝ → E → E) (Φ : E × ℝ → E) (q : E × ℝ) :
    timePieceFn f Φ q = (ContinuousLinearMap.id ℝ ℝ).smulRight (f q.2 (Φ q)) := rfl

/-- The **time piece** is jointly `C^k` on any open set on which both `f` (on `Set.univ`)
and `Φ` are jointly `C^k`. -/
theorem contDiffOn_timePieceFn
    {k : ℕ∞} {U : Set (E × ℝ)}
    (hf_Ck : ContDiffOn ℝ k (uncurry f) (Set.univ : Set (ℝ × E)))
    (hΦ_Ck : ContDiffOn ℝ k Φ U) :
    ContDiffOn ℝ k (timePieceFn f Φ) U :=
  contDiffOn_timePiece_CLM hf_Ck hΦ_Ck

/-- **Inductive promotion.**  If `Φ` is differentiable on the open set `U` and its Fréchet
derivative is jointly `C^j` on `U`, then `Φ` is jointly `C^{j+1}` on `U`. -/
theorem contDiffOn_succ_of_contDiffOn_fderiv
    {U : Set (E × ℝ)} (hU_open : IsOpen U) {j : ℕ∞}
    (hΦ_diff : DifferentiableOn ℝ Φ U)
    (h_fderiv : ContDiffOn ℝ j (fderiv ℝ Φ) U) :
    ContDiffOn ℝ (j + 1) Φ U := by
  rw [contDiffOn_succ_iff_fderiv_of_isOpen hU_open]
  refine ⟨hΦ_diff, ?_, h_fderiv⟩
  intro h
  exact absurd h (by exact_mod_cast WithTop.coe_ne_top)

/-- **Inductive step (coproduct form).**

If on the open set `U`:

* `Φ` is differentiable;
* `Lsp : E × ℝ → (E →L[ℝ] E)` is jointly `C^k`;
* the time piece `timePieceFn f Φ` is jointly `C^k`;
* the joint Fréchet derivative of `Φ` agrees with `Lsp.coprod (timePieceFn f Φ)`,

then `Φ` is jointly `C^{k+1}` on `U`. -/
theorem contDiffOn_succ_of_fderiv_coprod_smooth
    {U : Set (E × ℝ)} (hU_open : IsOpen U) {k : ℕ∞}
    {Lsp : E × ℝ → (E →L[ℝ] E)}
    (hΦ_diff : DifferentiableOn ℝ Φ U)
    (hLsp_Ck : ContDiffOn ℝ k Lsp U)
    (hLti_Ck : ContDiffOn ℝ k (timePieceFn f Φ) U)
    (h_fderiv_eq : ∀ q ∈ U, fderiv ℝ Φ q = (Lsp q).coprod (timePieceFn f Φ q)) :
    ContDiffOn ℝ (k + 1) Φ U := by
  set coprodCLM : ((E →L[ℝ] E) × (ℝ →L[ℝ] E)) →L[ℝ] ((E × ℝ) →L[ℝ] E) :=
    (ContinuousLinearMap.coprodEquivL (𝕜 := ℝ) (E := E) (F := ℝ) (G := E) ℝ
      : ((E →L[ℝ] E) × (ℝ →L[ℝ] E)) ≃L[ℝ] ((E × ℝ) →L[ℝ] E)).toContinuousLinearMap
    with hcoprodCLM_def
  have hcoprod_apply :
      ∀ (a : E →L[ℝ] E) (b : ℝ →L[ℝ] E), coprodCLM (a, b) = a.coprod b := by
    intro a b
    change (ContinuousLinearMap.coprodEquivL ℝ (a, b) : (E × ℝ) →L[ℝ] E) = a.coprod b
    rfl
  have hpair_Ck : ContDiffOn ℝ k (fun q : E × ℝ => (Lsp q, timePieceFn f Φ q)) U :=
    hLsp_Ck.prodMk hLti_Ck
  have hcomp_Ck : ContDiffOn ℝ k
      (fun q : E × ℝ => coprodCLM (Lsp q, timePieceFn f Φ q)) U :=
    hpair_Ck.continuousLinearMap_comp coprodCLM
  have heq : ∀ q ∈ U, fderiv ℝ Φ q = coprodCLM (Lsp q, timePieceFn f Φ q) := by
    intro q hq
    rw [hcoprod_apply]
    exact h_fderiv_eq q hq
  have h_fderiv_Ck : ContDiffOn ℝ k (fderiv ℝ Φ) U := hcomp_Ck.congr heq
  exact contDiffOn_succ_of_contDiffOn_fderiv hU_open hΦ_diff h_fderiv_Ck

end InductiveStep

section GeneralHeadline

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-- **The inductive headline.**

Suppose `Φ` is a local flow of a jointly `C^{k+1}` vector field `f`.  The flow is jointly
`C^{k+1}` on the strictly-interior open neighbourhood `U = ball x₀ ρ ×ˢ Ioo (t₀-T) (t₀+T)`
of `(x₀, t₀)` given by V.2.c.2's three-layer nested setup, provided:

* the inductive hypothesis: `Φ` is already jointly `C^k` on `U`;
* a spatial-piece candidate `Lsp : E × ℝ → (E →L[ℝ] E)` is jointly `C^k` on `U`, and
  agrees on `U` with the spatial partial Fréchet derivative of `Φ`.

The agreement condition is phrased via the explicit coproduct identity for the joint
Fréchet derivative.  Combined with `hasFDerivAt_flow_jointly_at` (V.2.c.1), it pins
`Lsp(x, t)` down as the variational linear map at the orbit `Φ ⟨x, ·⟩` evaluated at
time `t`, at every `(x, t) ∈ U`.  Hence the user-supplied `Lsp` is essentially the
variational linear map. -/
theorem contDiffOn_flow_succ_of_spatial_smooth
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    {k : ℕ∞}
    (hf_Csucc : ContDiffOn ℝ (k + 1) (uncurry f) (Set.univ : Set (ℝ × E)))
    (hΦ_Ck : ContDiffOn ℝ k Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)))
    {Lsp : E × ℝ → (E →L[ℝ] E)}
    (hLsp_Ck : ContDiffOn ℝ k Lsp ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)))
    (hLsp_eq : ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
      fderiv ℝ Φ q = (Lsp q).coprod (timePieceFn f Φ q)) :
    ContDiffOn ℝ (k + 1) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  set U : Set (E × ℝ) := (ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)
  have hU_open : IsOpen U := isOpen_ball.prod isOpen_Ioo
  have hk_one : (1 : WithTop ℕ∞) ≤ ((k + 1 : ℕ∞) : WithTop ℕ∞) := by
    have hone_le : (1 : ℕ∞) ≤ k + 1 := by
      calc (1 : ℕ∞) = 0 + 1 := by simp
        _ ≤ k + 1 := by gcongr; exact zero_le _
    exact_mod_cast hone_le
  have hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)) := by
    have h := hf_Csucc.of_le hk_one
    simpa using h
  have hΦ_C1 : ContDiffOn ℝ 1 Φ U :=
    contDiffOn_flow_of_isLocalFlow hΦ hf_C1 hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub hr'
      hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd
  have hΦ_diff : DifferentiableOn ℝ Φ U :=
    hΦ_C1.differentiableOn (by decide)
  have hf_Ck : ContDiffOn ℝ k (uncurry f) (Set.univ : Set (ℝ × E)) := by
    have h_le : ((k : ℕ∞) : WithTop ℕ∞) ≤ ((k + 1 : ℕ∞) : WithTop ℕ∞) := by
      have hk_le : (k : ℕ∞) ≤ k + 1 := le_self_add
      exact_mod_cast hk_le
    exact hf_Csucc.of_le h_le
  have hLti_Ck : ContDiffOn ℝ k (timePieceFn f Φ) U :=
    contDiffOn_timePieceFn hf_Ck hΦ_Ck
  exact contDiffOn_succ_of_fderiv_coprod_smooth hU_open hΦ_diff hLsp_Ck hLti_Ck hLsp_eq

/-- **The generic `C^k` headline driven by a parametric-smoothness sequence.**

Given, for every level `j < k`, the spatial-piece smoothness at level `j` together with
the coproduct identity for the Fréchet derivative, the flow is jointly `C^k` on the
strictly-interior open neighbourhood, for any `k : ℕ`.

The hypothesis is a *sequence* of candidate spatial-piece functions
`Lsp_seq : ℕ → E × ℝ → (E →L[ℝ] E)`, one per inductive level: at level `j` the candidate
`Lsp_seq j` must be jointly `C^j` and agree with the spatial partial of `Φ` on the open
neighbourhood (in the coproduct form with the time piece).

In practice all of these candidates are equal — the unique spatial partial Fréchet
derivative of `Φ`, by uniqueness of the Fréchet derivative once it exists — so this
sequence-of-hypotheses formulation captures exactly the parametric-smoothness Mathlib
gap. -/
theorem contDiffOn_flow_of_spatial_smooth_seq
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    (k : ℕ)
    (hf_Ck : ContDiffOn ℝ (k : ℕ∞) (uncurry f) (Set.univ : Set (ℝ × E)))
    (Lsp_seq : ℕ → E × ℝ → (E →L[ℝ] E))
    (hLsp_smooth : ∀ j : ℕ, j + 1 ≤ k →
      ContDiffOn ℝ (j : ℕ∞) (Lsp_seq j)
        ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)))
    (hLsp_eq : ∀ j : ℕ, j + 1 ≤ k →
      ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
      fderiv ℝ Φ q = (Lsp_seq j q).coprod (timePieceFn f Φ q)) :
    ContDiffOn ℝ (k : ℕ∞) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  induction k with
  | zero =>
    show ContDiffOn ℝ (((0 : ℕ) : ℕ∞)) Φ _
    have h_ρ_r : (ρ : ℝ) ≤ (r : ℝ) :=
      le_trans (le_of_lt hρ_lt_mid) (le_trans (le_of_lt hρ_mid_lt_out) hρ_out_le_r)
    have h_T_out : Icc (t₀ - T) (t₀ + T) ⊆ Icc (t₀ - T_out) (t₀ + T_out) :=
      Icc_subset_Icc (by linarith) (by linarith)
    have hsub_U : (ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)
        ⊆ closedBall x₀ (r : ℝ) ×ˢ Icc tmin tmax := by
      intro q hq
      refine ⟨?_, ?_⟩
      · exact closedBall_subset_closedBall h_ρ_r
          (mem_closedBall.mpr (le_of_lt (mem_ball.mp hq.1)))
      · exact hsub (h_T_out (Ioo_subset_Icc_self hq.2))
    have hcont : ContinuousOn Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) :=
      hΦ.continuousOn.mono hsub_U
    have hzero : ((0 : ℕ) : ℕ∞) = (0 : ℕ∞) := by simp
    rw [hzero]
    exact contDiffOn_zero.mpr hcont
  | succ k ih =>
    have hf_Csucc : ContDiffOn ℝ (((k : ℕ∞)) + 1) (uncurry f) (Set.univ : Set (ℝ × E)) := by
      have hconv : ((k + 1 : ℕ) : ℕ∞) = (k : ℕ∞) + 1 := by push_cast; rfl
      rw [hconv] at hf_Ck
      exact hf_Ck
    have hf_Ck' : ContDiffOn ℝ (k : ℕ∞) (uncurry f) (Set.univ : Set (ℝ × E)) := by
      have h_le : ((k : ℕ∞) : WithTop ℕ∞) ≤ (((k : ℕ∞) + 1 : ℕ∞) : WithTop ℕ∞) := by
        have hk_le : (k : ℕ∞) ≤ (k : ℕ∞) + 1 := le_self_add
        exact_mod_cast hk_le
      exact hf_Csucc.of_le h_le
    have hLsp_smooth' : ∀ j : ℕ, j + 1 ≤ k →
        ContDiffOn ℝ (j : ℕ∞) (Lsp_seq j)
          ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
      intro j hj
      exact hLsp_smooth j (by omega)
    have hLsp_eq' : ∀ j : ℕ, j + 1 ≤ k →
        ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
        fderiv ℝ Φ q = (Lsp_seq j q).coprod (timePieceFn f Φ q) := by
      intro j hj q hq
      exact hLsp_eq j (by omega) q hq
    have hΦ_Ck := ih hf_Ck' hLsp_smooth' hLsp_eq'
    have h_at_k_smooth : ContDiffOn ℝ (k : ℕ∞) (Lsp_seq k)
        ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := hLsp_smooth k (le_refl _)
    have h_at_k_eq : ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
        fderiv ℝ Φ q = (Lsp_seq k q).coprod (timePieceFn f Φ q) :=
      hLsp_eq k (le_refl _)
    have h_succ := contDiffOn_flow_succ_of_spatial_smooth hΦ hT hT_lt_mid hT_mid_lt_out hM
      hMT_mid hsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd
      (k := (k : ℕ∞)) hf_Csucc hΦ_Ck h_at_k_smooth h_at_k_eq
    have hconv : ((k + 1 : ℕ) : ℕ∞) = (k : ℕ∞) + 1 := by push_cast; rfl
    rw [hconv]; exact h_succ

end GeneralHeadline

section PublicHeadline

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-- **Joint `C^k` regularity of the local flow** (general `k : ℕ`, conditional on
parametric-smoothness hypotheses).

For a time-dependent vector field `f : ℝ → E → E` that is jointly `ContDiffOn ℝ k` on
`Set.univ` and a local Picard–Lindelöf flow `Φ` packaged by `IsLocalFlow`, the flow `Φ`
is jointly `C^k` on the strictly-interior open neighbourhood
`ball x₀ ρ ×ˢ Ioo (t₀ - T) (t₀ + T)` provided by V.2.c.2's three-layer nested setup,
*provided* a parametric-smoothness sequence `(Lsp_seq j)` for the spatial partial
Fréchet derivative is supplied.

For `k = 1` the parametric-smoothness hypothesis is satisfied automatically: the
spatial piece is jointly continuous, by V.2.c.2's
`continuousOn_fderiv_flow_of_isLocalFlow`.  For `k ≥ 2` the hypothesis is a Mathlib gap
to be discharged by parametric-ODE-smoothness theorems for variational linear ODEs. -/
theorem contDiffOn_flow_of_isLocalFlow_of_contDiff_general
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (k : ℕ)
    (hf_Ck : ContDiffOn ℝ (k : ℕ∞) (uncurry f) (Set.univ : Set (ℝ × E)))
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    (Lsp_seq : ℕ → E × ℝ → (E →L[ℝ] E))
    (hLsp_smooth : ∀ j : ℕ, j + 1 ≤ k →
      ContDiffOn ℝ (j : ℕ∞) (Lsp_seq j)
        ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)))
    (hLsp_eq : ∀ j : ℕ, j + 1 ≤ k →
      ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
      fderiv ℝ Φ q = (Lsp_seq j q).coprod (timePieceFn f Φ q)) :
    ContDiffOn ℝ (k : ℕ∞) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) :=
  contDiffOn_flow_of_spatial_smooth_seq hΦ hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub hr'
    hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd k hf_Ck Lsp_seq hLsp_smooth hLsp_eq

end PublicHeadline

end Flow
end ODE
end Analysis
end DifferentialGeometry

end
