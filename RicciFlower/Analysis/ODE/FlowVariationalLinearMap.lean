import RicciFlower.Analysis.ODE.FlowCkVariational
import Mathlib.Analysis.ODE.Gronwall
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# Joint `C^1` smoothness of the variational linear map (building blocks)

The goal: for a time-dependent vector field `f : ℝ → E → E` jointly `C^2` in
`(t, x)` and a local Picard–Lindelöf flow `Φ`, build a joint-`C^1`
spatial-piece function `Y : E × ℝ → (E →L[ℝ] E)` satisfying
`IsVariationalFlowProjection hΦ T_eff ρ_eff Y 1` for some shrunk
`(T_eff, ρ_eff)`.

The clean construction uses the *augmented flow*: the augmented vector field
`augVF f` on `E × (E →L[ℝ] E)` is jointly `C^1` whenever `f` is jointly
`C^2`, so its Picard–Lindelöf flow `aΦ` is jointly `C^1` on a strictly-interior
open neighbourhood of `((x₀, id), t₀)` by `contDiffOn_flow_of_isLocalFlow`
applied to `aΦ` itself.  The projection `Y(x, t) := (aΦ ⟨(x, id), t⟩).2`
inherits joint `C^1`-smoothness via `contDiffOn_fromAugFlow`, and the
variational identification `Y q = variationalLinearMapAt(...)` holds pointwise.

This file ships **two atomic building-block lemmas** that the orchestrator
combines downstream to close the projection witness:

## Headlines

* `orbit_eq_of_augFlow_isLocalFlow` — orbit-equality identification.  The first
  projection of an augmented PL flow agrees with the original PL flow on a
  neighbourhood of `t₀`, via `ODE_solution_unique_of_eventually`.  This is the
  bridge that lets us identify `variationalLinearMapAt(α := Φ⟨x, ·⟩, t)` with
  `variationalLinearMapAt(α := s ↦ (aΦ ⟨(x, id), s⟩).1, t)` once the two
  orbits agree pointwise.

* `contDiffOn_fromAugFlow_inherits` — the joint smoothness of the projection
  inherits from the joint smoothness of the augmented flow.  Given `aΦ` is
  jointly `C^1` on a neighbourhood of `((x₀, id), t₀)`, the function
  `Y := fromAugFlow aΦ` is jointly `C^1` on the embedded neighbourhood of
  `(x₀, t₀)`.

The remaining unconditional step — running `contDiffOn_flow_of_isLocalFlow` on
the augmented system requires a uniform-in-orbit operator-norm bound `M_aug`
on the augmented linearization — needs either `[FiniteDimensional ℝ E]` (so
closed balls are compact, giving `M_aug` from joint continuity) or a careful
Grönwall-based bound using the augmented PL constants.  Both routes are
independent of this file and shipped downstream.

All theorems are formulated on a generic Banach space `E`; `[InnerProductSpace ℝ E]`
is *not* used.  No manifold or tensor file is imported.
-/

noncomputable section

open Set Function Filter Metric Asymptotics Real
open scoped Topology NNReal

namespace RicciFlower
namespace Analysis
namespace ODE
namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-! ## Orbit-equality lemma

Both the original local flow `Φ` and the first projection of the augmented local
flow `aΦ` are solutions of the original ODE `y' = f t y` with initial value `x`
at time `t₀`.  By Picard–Lindelöf uniqueness applied locally near `t₀`, they
agree on a neighbourhood of `t₀`. -/

section OrbitEquality

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ}
  {Φ : E × ℝ → E}

set_option maxHeartbeats 2400000 in
/--
**Orbit-equality lemma.**  If `aΦ` is a local flow of the augmented field
`augVF f` centred at `((x₀, id), t₀)`, `Φ` is a local flow of `f` centred at
`(x₀, t₀)`, and `(t₀, x)` lies in the interior of both flows' time domains,
then the orbit `s ↦ Φ ⟨x, s⟩` agrees with the first projection
`s ↦ (aΦ ⟨(x, id), s⟩).1` on a neighbourhood of `t₀`.

The proof uses `ODE_solution_unique_of_eventually` applied to the original ODE
`v t y := f t y`, with the local Lipschitz constant of `uncurry f` at `(t₀, x)`
supplied by `ContDiffAt.exists_lipschitzOnWith`.
-/
theorem orbit_eq_of_augFlow_isLocalFlow
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {R_aug : ℝ≥0} {tmin_a tmax_a : ℝ}
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    (haΦ : IsLocalFlow (augVF f) t₀ (x₀, ContinuousLinearMap.id ℝ E) R_aug
      tmin_a tmax_a aΦ)
    {x : E} (hx_Φ : x ∈ closedBall x₀ (r : ℝ))
    (hx_a : (x, ContinuousLinearMap.id ℝ E) ∈ closedBall
      ((x₀, ContinuousLinearMap.id ℝ E) : E × (E →L[ℝ] E)) (R_aug : ℝ))
    (ht₀_Φ : t₀ ∈ Ioo tmin tmax) (ht₀_a : t₀ ∈ Ioo tmin_a tmax_a) :
    (fun s => Φ ⟨x, s⟩) =ᶠ[𝓝 t₀]
      (fun s => (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1) := by
  -- The "ambient" Lipschitz constant for `f` at `(t₀, x)`.
  have hcd_at : ContDiffAt ℝ 1 (uncurry f) (t₀, x) :=
    hf_C1.contDiffAt (IsOpen.mem_nhds isOpen_univ (mem_univ _))
  obtain ⟨K, sNhd, hsNhd, hl⟩ := hcd_at.exists_lipschitzOnWith
  -- Shrink to a metric ball around `(t₀, x)` inside the Lipschitz neighbourhood.
  obtain ⟨ρ_Lip, hρ_Lip_pos, hρ_Lip_sub⟩ := Metric.mem_nhds_iff.mp hsNhd
  -- The two orbits.
  set α_Φ : ℝ → E := fun s => Φ ⟨x, s⟩ with hα_Φ_def
  set α_a : ℝ → E := fun s => (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1
    with hα_a_def
  have hα_Φ_init : α_Φ t₀ = x := hΦ.apply_initial x hx_Φ
  have hα_a_init : α_a t₀ = x := by
    change (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t₀⟩).1 = x
    rw [haΦ.apply_initial _ hx_a]
  -- Continuity of `α_Φ` at `t₀`.
  have hIcc_nhds_Φ : Icc tmin tmax ∈ 𝓝 t₀ :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht₀_Φ) Ioo_subset_Icc_self
  have hIcc_nhds_a : Icc tmin_a tmax_a ∈ 𝓝 t₀ :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht₀_a) Ioo_subset_Icc_self
  have hα_Φ_cont_on : ContinuousOn α_Φ (Icc tmin tmax) := hΦ.orbit_continuousOn x hx_Φ
  have hα_Φ_cont : ContinuousAt α_Φ t₀ :=
    hα_Φ_cont_on.continuousAt hIcc_nhds_Φ
  -- Continuity of `α_a` at `t₀`.
  have h_orbit_cont_on : ContinuousOn
      (fun s => aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩)
      (Icc tmin_a tmax_a) :=
    haΦ.orbit_continuousOn (x, ContinuousLinearMap.id ℝ E) hx_a
  have hα_a_cont : ContinuousAt α_a t₀ := by
    have h_pair_cont_at : ContinuousAt
        (fun s => aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩) t₀ :=
      h_orbit_cont_on.continuousAt hIcc_nhds_a
    exact continuous_fst.continuousAt.comp h_pair_cont_at
  -- The set `S := ball x (ρ_Lip / 2)`.
  set ρ' : ℝ := ρ_Lip / 2 with hρ'_def
  have hρ'_pos : 0 < ρ' := by positivity
  have hρ'_lt_Lip : ρ' < ρ_Lip := by rw [hρ'_def]; linarith
  set S : Set E := ball x ρ' with hS_def
  have hS_nhds_x : S ∈ 𝓝 x := ball_mem_nhds x hρ'_pos
  -- Eventually near `t₀`: `α_Φ t ∈ S` and `α_a t ∈ S`.
  have hα_Φ_eventually : ∀ᶠ t in 𝓝 t₀, α_Φ t ∈ S := by
    have h := hα_Φ_cont (show S ∈ 𝓝 (α_Φ t₀) by rw [hα_Φ_init]; exact hS_nhds_x)
    exact h
  have hα_a_eventually : ∀ᶠ t in 𝓝 t₀, α_a t ∈ S := by
    have h := hα_a_cont (show S ∈ 𝓝 (α_a t₀) by rw [hα_a_init]; exact hS_nhds_x)
    exact h
  -- Eventually near `t₀`: `f t` is `K`-Lipschitz on `S`.
  have h_v_lip_event : ∀ᶠ t in 𝓝 t₀, LipschitzOnWith K (f t) S := by
    rw [eventually_iff_exists_mem]
    refine ⟨ball t₀ ρ', ball_mem_nhds t₀ hρ'_pos, ?_⟩
    intro t ht
    rw [mem_ball] at ht
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro y₁ hy₁ y₂ hy₂
    have h_pair₁ : ((t, y₁) : ℝ × E) ∈ ball (t₀, x) ρ_Lip := by
      rw [mem_ball, Prod.dist_eq]
      rw [mem_ball] at hy₁
      have hmax_le_ρ' : max (dist t t₀) (dist y₁ x) ≤ ρ' :=
        max_le (le_of_lt ht) (le_of_lt hy₁)
      exact lt_of_le_of_lt hmax_le_ρ' hρ'_lt_Lip
    have h_pair₂ : ((t, y₂) : ℝ × E) ∈ ball (t₀, x) ρ_Lip := by
      rw [mem_ball, Prod.dist_eq]
      rw [mem_ball] at hy₂
      have hmax_le_ρ' : max (dist t t₀) (dist y₂ x) ≤ ρ' :=
        max_le (le_of_lt ht) (le_of_lt hy₂)
      exact lt_of_le_of_lt hmax_le_ρ' hρ'_lt_Lip
    have h_in_S₁ : ((t, y₁) : ℝ × E) ∈ sNhd := hρ_Lip_sub h_pair₁
    have h_in_S₂ : ((t, y₂) : ℝ × E) ∈ sNhd := hρ_Lip_sub h_pair₂
    have hd : dist (uncurry f (t, y₁)) (uncurry f (t, y₂))
        ≤ K * dist ((t, y₁) : ℝ × E) (t, y₂) :=
      hl.dist_le_mul _ h_in_S₁ _ h_in_S₂
    have hdist_eq : dist ((t, y₁) : ℝ × E) (t, y₂) = dist y₁ y₂ := by
      rw [Prod.dist_eq]; simp [dist_self]
    rw [hdist_eq] at hd
    change dist (uncurry f (t, y₁)) (uncurry f (t, y₂)) ≤ K * dist y₁ y₂
    exact hd
  -- Derivative hypotheses for `α_Φ` and `α_a` near `t₀`.
  have hα_Φ_deriv_event : ∀ᶠ t in 𝓝 t₀,
      HasDerivAt α_Φ (f t (α_Φ t)) t ∧ α_Φ t ∈ S := by
    have h_int : Ioo tmin tmax ∈ 𝓝 t₀ := isOpen_Ioo.mem_nhds ht₀_Φ
    refine Filter.eventually_of_mem (Filter.inter_mem h_int hα_Φ_eventually) ?_
    intro t ht
    rcases ht with ⟨ht_int, ht_S⟩
    refine ⟨?_, ht_S⟩
    have h_dw : HasDerivWithinAt (fun s => Φ ⟨x, s⟩) (f t (Φ ⟨x, t⟩))
        (Icc tmin tmax) t :=
      hΦ.hasDerivWithinAt x hx_Φ t (Ioo_subset_Icc_self ht_int)
    have hIcc_nhds_t : Icc tmin tmax ∈ 𝓝 t :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht_int) Ioo_subset_Icc_self
    exact h_dw.hasDerivAt hIcc_nhds_t
  have hα_a_deriv_event : ∀ᶠ t in 𝓝 t₀,
      HasDerivAt α_a (f t (α_a t)) t ∧ α_a t ∈ S := by
    have h_int : Ioo tmin_a tmax_a ∈ 𝓝 t₀ := isOpen_Ioo.mem_nhds ht₀_a
    refine Filter.eventually_of_mem (Filter.inter_mem h_int hα_a_eventually) ?_
    intro t ht
    rcases ht with ⟨ht_int, ht_S⟩
    refine ⟨?_, ht_S⟩
    have h_orbit_dw : HasDerivWithinAt
        (fun s => aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩)
        (augVF f t (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩))
        (Icc tmin_a tmax_a) t :=
      haΦ.hasDerivWithinAt _ hx_a t (Ioo_subset_Icc_self ht_int)
    have hIcc_a_nhds_t : Icc tmin_a tmax_a ∈ 𝓝 t :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht_int) Ioo_subset_Icc_self
    have h_orbit_at : HasDerivAt
        (fun s => aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩)
        (augVF f t (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩)) t :=
      h_orbit_dw.hasDerivAt hIcc_a_nhds_t
    -- Project to the first component via `ContinuousLinearMap.fst`.
    have h_fst_fd : HasFDerivAt
        (fun p : E × (E →L[ℝ] E) => p.1)
        (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))
        (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩) :=
      (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)).hasFDerivAt
    have h_comp : HasDerivAt α_a
        ((ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))
          (augVF f t (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩))) t :=
      h_fst_fd.comp_hasDerivAt t h_orbit_at
    -- `fst (augVF f t (a, b)) = f t a`.
    have h_first_eq :
        (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))
          (augVF f t (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩))
        = f t (α_a t) := by
      change (augVF f t (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩)).1
        = f t (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).1
      rfl
    rw [h_first_eq] at h_comp
    exact h_comp
  -- Apply `ODE_solution_unique_of_eventually`.
  have h_init_eq : α_Φ t₀ = α_a t₀ := by rw [hα_Φ_init, hα_a_init]
  exact ODE_solution_unique_of_eventually
    (K := K) (v := fun t y => f t y) (s := fun _ => S)
    h_v_lip_event hα_Φ_deriv_event hα_a_deriv_event h_init_eq

end OrbitEquality

/-! ## Smoothness inheritance for the projection

The function `Y(x, t) := (aΦ ⟨(x, id), t⟩).2` (i.e. `fromAugFlow aΦ`) inherits
joint smoothness from the augmented flow `aΦ`.  This is a direct repackaging of
`contDiffOn_fromAugFlow` and reduces the joint `C^1`-smoothness of `Y` to that
of `aΦ`, which is in turn delivered by `contDiffOn_flow_of_isLocalFlow` applied
to the augmented system. -/

section SmoothnessInheritance

variable {f : ℝ → E → E} {x₀ : E} {t₀ : ℝ}

/-- **Smoothness inheritance for the projection.**  If `aΦ` is jointly `C^1` on
the open neighbourhood `(ball (x₀, id) (ρ_a : ℝ)) ×ˢ Ioo (t₀ - T_a) (t₀ + T_a)`,
and the spatial radius `ρ` and time width `T` satisfy `(ρ : ℝ) ≤ (ρ_a : ℝ)` and
`T ≤ T_a`, then the projection `fromAugFlow aΦ` is jointly `C^1` on the
corresponding neighbourhood `ball x₀ (ρ : ℝ) ×ˢ Ioo (t₀ - T) (t₀ + T)`. -/
theorem contDiffOn_fromAugFlow_inherits
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {ρ_a ρ : ℝ≥0} {T_a T : ℝ}
    (hρ_le : (ρ : ℝ) ≤ (ρ_a : ℝ)) (hT_le : T ≤ T_a)
    (haΦ_C1 : ContDiffOn ℝ 1 aΦ
      ((ball ((x₀, ContinuousLinearMap.id ℝ E) : E × (E →L[ℝ] E))
          (ρ_a : ℝ)) ×ˢ Ioo (t₀ - T_a) (t₀ + T_a))) :
    ContDiffOn ℝ 1 (fromAugFlow aΦ)
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  -- Embedding `(x, t) ↦ ((x, id), t)` maps the small neighbourhood into the large.
  set p₀ : E × (E →L[ℝ] E) := (x₀, ContinuousLinearMap.id ℝ E) with hp₀_def
  set U : Set (E × ℝ) := ball x₀ (ρ : ℝ) ×ˢ Ioo (t₀ - T) (t₀ + T) with hU_def
  set U_a : Set ((E × (E →L[ℝ] E)) × ℝ) :=
    ball p₀ (ρ_a : ℝ) ×ˢ Ioo (t₀ - T_a) (t₀ + T_a) with hU_a_def
  have hmap : MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2)) U U_a := by
    intro q hq
    rcases hq with ⟨hq_x, hq_t⟩
    refine ⟨?_, ?_⟩
    · rw [mem_ball] at hq_x ⊢
      have hd : dist ((q.1, ContinuousLinearMap.id ℝ E) : E × (E →L[ℝ] E)) p₀
          = dist q.1 x₀ := by
        change max (dist q.1 x₀) (dist (ContinuousLinearMap.id ℝ E)
          (ContinuousLinearMap.id ℝ E)) = dist q.1 x₀
        rw [dist_self, max_eq_left dist_nonneg]
      rw [hd]
      exact lt_of_lt_of_le hq_x hρ_le
    · rcases hq_t with ⟨h1, h2⟩
      refine ⟨?_, ?_⟩ <;> linarith
  exact contDiffOn_fromAugFlow (k := (1 : ℕ∞)) (Ω := U_a) (U := U) haΦ_C1 hmap

end SmoothnessInheritance

/-! ## Orbit-equality on a closed interval

Strengthening `orbit_eq_of_augFlow_isLocalFlow`: under the same hypotheses, plus a
uniform Lipschitz bound for `f` on a slab `closedBall x₀ r₀ ⊆ E` that contains both
orbits on the closed interval `Icc (t₀ - T) (t₀ + T)`, the two orbit projections agree
on the entire closed interval (not merely on a neighbourhood of `t₀`).  The proof
specialises `ODE_solution_unique_of_mem_Icc` to the original ODE `y' = f t y` with
the uniform Lipschitz constant supplied on the slab. -/

section OrbitEqualityIcc

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ}
  {Φ : E × ℝ → E}

/-- **Orbit-equality on a closed interval.**  If both orbits land in a closed ball
`closedBall x₀ r₀` on which `f t` is uniformly `K`-Lipschitz for `t` in the open
interval `Ioo (t₀ - T) (t₀ + T)`, then `Φ ⟨x, ·⟩` and `(aΦ ⟨(x, id), ·⟩).1` agree on
the entire closed interval `Icc (t₀ - T) (t₀ + T)`.  The hypotheses package the
orbit-stays-in-the-ball condition for each side and the uniform Lipschitz property of
`f` on the slab. -/
theorem orbit_eq_Icc_of_augFlow_isLocalFlow
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {R_aug : ℝ≥0} {tmin_a tmax_a : ℝ}
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    (haΦ : IsLocalFlow (augVF f) t₀ (x₀, ContinuousLinearMap.id ℝ E) R_aug
      tmin_a tmax_a aΦ)
    {x : E} (hx_Φ : x ∈ closedBall x₀ (r : ℝ))
    (hx_a : (x, ContinuousLinearMap.id ℝ E) ∈ closedBall
      ((x₀, ContinuousLinearMap.id ℝ E) : E × (E →L[ℝ] E)) (R_aug : ℝ))
    {T : ℝ} (hT_sub_Φ : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    (hT_sub_a : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin_a tmax_a)
    (ht₀_Ioo : t₀ ∈ Ioo (t₀ - T) (t₀ + T))
    {r₀ : ℝ} {K : ℝ≥0}
    (h_Φ_in : ∀ t ∈ Ioo (t₀ - T) (t₀ + T), Φ ⟨x, t⟩ ∈ closedBall x₀ r₀)
    (h_a_in : ∀ t ∈ Ioo (t₀ - T) (t₀ + T),
      (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).1 ∈ closedBall x₀ r₀)
    (h_lip : ∀ t ∈ Ioo (t₀ - T) (t₀ + T),
      LipschitzOnWith K (f t) (closedBall x₀ r₀)) :
    EqOn (fun s => Φ ⟨x, s⟩)
      (fun s => (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1)
      (Icc (t₀ - T) (t₀ + T)) := by
  -- Both orbits satisfy the original ODE.
  set α_Φ : ℝ → E := fun s => Φ ⟨x, s⟩ with hα_Φ_def
  set α_a : ℝ → E := fun s => (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1
    with hα_a_def
  have hα_Φ_init : α_Φ t₀ = x := hΦ.apply_initial x hx_Φ
  have hα_a_init : α_a t₀ = x := by
    change (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t₀⟩).1 = x
    rw [haΦ.apply_initial _ hx_a]
  have hα_Φ_cont : ContinuousOn α_Φ (Icc (t₀ - T) (t₀ + T)) :=
    (hΦ.orbit_continuousOn x hx_Φ).mono hT_sub_Φ
  have hα_a_cont : ContinuousOn α_a (Icc (t₀ - T) (t₀ + T)) := by
    have h_pair_cont : ContinuousOn
        (fun s => aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩)
        (Icc tmin_a tmax_a) :=
      haΦ.orbit_continuousOn (x, ContinuousLinearMap.id ℝ E) hx_a
    have h_fst_cont : ContinuousOn α_a (Icc tmin_a tmax_a) :=
      continuous_fst.continuousOn.comp h_pair_cont (fun _ _ => mem_univ _)
    exact h_fst_cont.mono hT_sub_a
  -- Derivative at every interior point.
  have hα_Φ_deriv : ∀ s ∈ Ioo (t₀ - T) (t₀ + T),
      HasDerivAt α_Φ (f s (α_Φ s)) s := by
    intro s hs
    have h_in_Icc_Φ : s ∈ Icc tmin tmax := hT_sub_Φ (Ioo_subset_Icc_self hs)
    have h_dw : HasDerivWithinAt (fun u => Φ ⟨x, u⟩) (f s (Φ ⟨x, s⟩))
        (Icc tmin tmax) s := hΦ.hasDerivWithinAt x hx_Φ s h_in_Icc_Φ
    -- Promote to HasDerivAt using the fact that s ∈ Ioo (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax.
    -- The latter set is in 𝓝 s because Ioo (t₀ - T) (t₀ + T) is open and contained in it.
    have h_nhds : Icc tmin tmax ∈ 𝓝 s :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds hs)
        (fun u hu => hT_sub_Φ (Ioo_subset_Icc_self hu))
    exact h_dw.hasDerivAt h_nhds
  have hα_a_deriv : ∀ s ∈ Ioo (t₀ - T) (t₀ + T),
      HasDerivAt α_a (f s (α_a s)) s := by
    intro s hs
    have h_in_Icc_a : s ∈ Icc tmin_a tmax_a := hT_sub_a (Ioo_subset_Icc_self hs)
    have h_orbit_dw : HasDerivWithinAt
        (fun u => aΦ ⟨(x, ContinuousLinearMap.id ℝ E), u⟩)
        (augVF f s (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩))
        (Icc tmin_a tmax_a) s :=
      haΦ.hasDerivWithinAt _ hx_a s h_in_Icc_a
    have h_nhds : Icc tmin_a tmax_a ∈ 𝓝 s :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds hs)
        (fun u hu => hT_sub_a (Ioo_subset_Icc_self hu))
    have h_orbit_at : HasDerivAt
        (fun u => aΦ ⟨(x, ContinuousLinearMap.id ℝ E), u⟩)
        (augVF f s (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩)) s :=
      h_orbit_dw.hasDerivAt h_nhds
    -- Project to first component.
    have h_fst_fd : HasFDerivAt
        (fun p : E × (E →L[ℝ] E) => p.1)
        (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))
        (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩) :=
      (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)).hasFDerivAt
    have h_comp : HasDerivAt α_a
        ((ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))
          (augVF f s (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩))) s :=
      h_fst_fd.comp_hasDerivAt s h_orbit_at
    have h_first_eq :
        (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))
          (augVF f s (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩))
        = f s (α_a s) := rfl
    rw [h_first_eq] at h_comp
    exact h_comp
  -- Initial value agreement.
  have h_init_eq : α_Φ t₀ = α_a t₀ := by rw [hα_Φ_init, hα_a_init]
  -- Apply ODE uniqueness on the closed interval.
  exact ODE_solution_unique_of_mem_Icc
    (v := fun t y => f t y)
    (s := fun _ => closedBall x₀ r₀)
    (K := K)
    (fun t ht => h_lip t ht)
    ht₀_Ioo hα_Φ_cont
    (fun t ht => hα_Φ_deriv t ht)
    (fun t ht => h_Φ_in t ht)
    hα_a_cont
    (fun t ht => hα_a_deriv t ht)
    (fun t ht => h_a_in t ht)
    h_init_eq

end OrbitEqualityIcc

/-! ## Smoothness-clause witness of the level-1 variational-flow projection

The construction: build the augmented flow `aΦ` on `E × (E →L[ℝ] E)` via
`exists_isLocalFlow_augVF_of_C2`, apply `contDiffOn_flow_of_isLocalFlow_of_contDiff`
to `aΦ` to get joint `C^1`-smoothness of `aΦ` on an open neighbourhood (using closed-ball
compactness in finite dimensions to extract the uniform operator-norm bound on the
augmented linearization), and inherit this smoothness to the projection
`Y := fromAugFlow aΦ` via `contDiffOn_fromAugFlow_inherits`.

This produces the **smoothness clause** of the `IsVariationalFlowProjection hΦ T ρ Y 1`
witness, namely `ContDiffOn ℝ 1 Y ((ball x₀ ρ) ×ˢ Ioo (t₀ - T) (t₀ + T))`, together
with positive `T` and `ρ`.  The remaining `fderiv_eq` clause requires
`Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax` (so that the orbit `Φ ⟨x, ·⟩` is differentiable
on the slab), which in turn requires `t₀ ∈ Ioo tmin tmax` for positivity of `T`.  In
the natural usage downstream, `Φ` is constructed via `exists_isLocalFlow_of_contDiffOn_univ`
which always yields a positive interior; the headline below produces a positive
witness `(T, ρ, Y)` regardless, with the augmented-flow's positive `ε_aug` driving
the inner time width. -/

section LevelOneSmoothnessClause

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E}

set_option maxHeartbeats 4000000 in
/-- **Smoothness clause of the level-1 variational-flow projection witness.**

If `f : ℝ → E → E` is jointly `C^2` on `Set.univ` and `E` is a finite-dimensional
Banach space, then there exist positive `T` and `ρ` together with a function
`Y : E × ℝ → (E →L[ℝ] E)` that is jointly `C^1` on the open neighbourhood
`(ball x₀ ρ) ×ˢ Ioo (t₀ - T) (t₀ + T)`.

The function `Y` is `fromAugFlow aΦ` where `aΦ` is the local flow of the augmented
vector field `augVF f` on `E × (E →L[ℝ] E)` centred at `((x₀, id), t₀)`.

This headline is the **smoothness clause** of the full level-1
`IsVariationalFlowProjection` witness; the remaining `fderiv_eq` clause is shipped
separately and requires the orbit-equality identification on a closed time interval
(see `orbit_eq_Icc_of_augFlow_isLocalFlow`). -/
theorem exists_contDiffOn_fromAugFlow_one_of_C2
    [FiniteDimensional ℝ E]
    (hf_C2 : ContDiffOn ℝ 2 (uncurry f) (Set.univ : Set (ℝ × E)))
    (t₀ : ℝ) (x₀ : E) :
    ∃ (T : ℝ) (ρ : ℝ≥0) (_hT : 0 < T) (_hρ : 0 < (ρ : ℝ))
      (aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)),
      ContDiffOn ℝ 1 (fromAugFlow aΦ)
        ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  -- Step 1: get the augmented flow.
  set p₀ : E × (E →L[ℝ] E) := (x₀, ContinuousLinearMap.id ℝ E) with hp₀_def
  obtain ⟨R_aug, ε_aug, hR_aug_pos, hε_aug_pos, aΦ, haΦ⟩ :=
    exists_isLocalFlow_augVF_of_C2 hf_C2 t₀ p₀
  -- Step 2: extract the C^1 regularity of `augVF f`.
  have hf_succ : ContDiffOn ℝ ((1 : ℕ∞) + 1) (uncurry f) (Set.univ : Set (ℝ × E)) := by
    simpa using hf_C2
  have h_augVF_C1 : ContDiffOn ℝ 1 (uncurry (augVF f))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    augVF_uncurry_contDiff (k := (1 : ℕ∞)) hf_succ
  -- Step 3: pick the outer slab for compactness-based M extraction.
  set R_a_out : ℝ := (R_aug : ℝ) / 2 with hR_a_out_def
  have hR_aug_R : (0 : ℝ) < (R_aug : ℝ) := by exact_mod_cast hR_aug_pos
  have hR_a_out_pos : 0 < R_a_out := by rw [hR_a_out_def]; linarith
  have hR_a_out_lt : R_a_out < (R_aug : ℝ) := by rw [hR_a_out_def]; linarith
  set T_a_out : ℝ := ε_aug / 2 with hT_a_out_def
  have hT_a_out_pos : 0 < T_a_out := by rw [hT_a_out_def]; linarith
  have hT_a_out_lt : T_a_out < ε_aug := by rw [hT_a_out_def]; linarith
  have hslab_sub_a : closedBall p₀ R_a_out ×ˢ Icc (t₀ - T_a_out) (t₀ + T_a_out)
      ⊆ closedBall p₀ (R_aug : ℝ) ×ˢ Icc (t₀ - ε_aug) (t₀ + ε_aug) := by
    refine Set.prod_mono ?_ ?_
    · exact closedBall_subset_closedBall (le_of_lt hR_a_out_lt)
    · exact Icc_subset_Icc (by linarith) (by linarith)
  -- Step 4: extract M_aug via finite-dim compactness + continuity.
  have hpartial_a : ContDiffOn ℝ 0 (fun p : ℝ × (E × (E →L[ℝ] E)) =>
      fderiv ℝ (augVF f p.1) p.2)
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    contDiffOn_partial_fderiv_of_succ (f := augVF f) (k := (0 : ℕ∞))
      (by simpa using h_augVF_C1)
  have hpartial_a_cont : ContinuousOn (fun p : ℝ × (E × (E →L[ℝ] E)) =>
      fderiv ℝ (augVF f p.1) p.2) (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    hpartial_a.continuousOn
  have haΦ_cont_full : ContinuousOn aΦ
      (closedBall p₀ (R_aug : ℝ) ×ˢ Icc (t₀ - ε_aug) (t₀ + ε_aug)) :=
    haΦ.continuousOn
  have haΦ_cont : ContinuousOn aΦ
      (closedBall p₀ R_a_out ×ˢ Icc (t₀ - T_a_out) (t₀ + T_a_out)) :=
    haΦ_cont_full.mono hslab_sub_a
  set Slab : Set ((E × (E →L[ℝ] E)) × ℝ) :=
    closedBall p₀ R_a_out ×ˢ Icc (t₀ - T_a_out) (t₀ + T_a_out) with hSlab_def
  have hSlab_cpt : IsCompact Slab :=
    (isCompact_closedBall (p₀ : E × (E →L[ℝ] E)) R_a_out).prod isCompact_Icc
  have hSlab_ne : Slab.Nonempty :=
    ⟨(p₀, t₀), Metric.mem_closedBall_self (le_of_lt hR_a_out_pos),
      ⟨by linarith, by linarith⟩⟩
  have h_aΦ_pair_cont : ContinuousOn
      (fun q : (E × (E →L[ℝ] E)) × ℝ => (q.2, aΦ q)) Slab :=
    ContinuousOn.prodMk continuous_snd.continuousOn haΦ_cont
  have h_fderiv_along_cont : ContinuousOn
      (fun q : (E × (E →L[ℝ] E)) × ℝ => fderiv ℝ (augVF f q.2) (aΦ q))
      Slab := by
    have hmaps : MapsTo (fun q : (E × (E →L[ℝ] E)) × ℝ => (q.2, aΦ q))
        Slab (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := fun _ _ => mem_univ _
    exact hpartial_a_cont.comp h_aΦ_pair_cont hmaps
  have h_norm_cont : ContinuousOn
      (fun q : (E × (E →L[ℝ] E)) × ℝ => ‖fderiv ℝ (augVF f q.2) (aΦ q)‖)
      Slab := by
    exact
      (continuous_norm
          (E := (E × (E →L[ℝ] E)) →L[ℝ] (E × (E →L[ℝ] E)))).comp_continuousOn
        h_fderiv_along_cont
  rcases hSlab_cpt.exists_isMaxOn hSlab_ne h_norm_cont with ⟨qmax, _, hqmax⟩
  set M_aug_pre : ℝ := ‖fderiv ℝ (augVF f qmax.2) (aΦ qmax)‖ with hM_aug_pre_def
  have hM_aug_pre_nn : 0 ≤ M_aug_pre := by
    rw [hM_aug_pre_def]
    exact ContinuousLinearMap.opNorm_nonneg _
  have hM_aug_pre_bd : ∀ q ∈ Slab, ‖fderiv ℝ (augVF f q.2) (aΦ q)‖ ≤ M_aug_pre :=
    fun q hq => hqmax hq
  -- Step 5: pick nested params for the augmented system.
  set M_aug : ℝ := M_aug_pre + 1 with hM_aug_def
  have hM_aug_nn : 0 ≤ M_aug := by rw [hM_aug_def]; linarith
  have hM_aug_pos : 0 < M_aug := by rw [hM_aug_def]; linarith
  -- Pick T_a_mid' strictly less than T_a_out with `M_aug * T_a_mid' < 1`.
  set T_a_mid' : ℝ := min (T_a_out * 3 / 4) (1 / (2 * M_aug)) with hT_a_mid'_def
  have hT_a_mid'_pos : 0 < T_a_mid' := by
    refine lt_min ?_ ?_
    · positivity
    · have : 0 < 2 * M_aug := by linarith
      positivity
  have hT_a_mid'_lt_out : T_a_mid' < T_a_out := by
    have h1 : T_a_mid' ≤ T_a_out * 3 / 4 := min_le_left _ _
    have h2 : T_a_out * 3 / 4 < T_a_out := by linarith
    linarith
  have hMTmid' : M_aug * T_a_mid' < 1 := by
    have h1 : T_a_mid' ≤ 1 / (2 * M_aug) := min_le_right _ _
    have h2 : M_aug * T_a_mid' ≤ M_aug * (1 / (2 * M_aug)) :=
      mul_le_mul_of_nonneg_left h1 hM_aug_nn
    have h3 : M_aug * (1 / (2 * M_aug)) = 1 / 2 := by field_simp
    linarith
  set T_a : ℝ := T_a_mid' / 2 with hT_a_def
  have hT_a_pos : 0 < T_a := by rw [hT_a_def]; linarith
  have hT_a_lt_mid' : T_a < T_a_mid' := by rw [hT_a_def]; linarith
  -- Spatial nesting: R_a < R_a_mid < R_a_out.
  set R_a_mid : ℝ := R_a_out * 3 / 4 with hR_a_mid_def
  have hR_a_mid_pos : 0 < R_a_mid := by rw [hR_a_mid_def]; positivity
  have hR_a_mid_lt_out : R_a_mid < R_a_out := by rw [hR_a_mid_def]; linarith
  set R_a : ℝ := R_a_mid / 2 with hR_a_def
  have hR_a_pos : 0 < R_a := by rw [hR_a_def]; linarith
  have hR_a_lt_mid : R_a < R_a_mid := by rw [hR_a_def]; linarith
  set R_aN : ℝ≥0 := ⟨R_a, le_of_lt hR_a_pos⟩ with hR_aN_def
  set R_a_midN : ℝ≥0 := ⟨R_a_mid, le_of_lt hR_a_mid_pos⟩ with hR_a_midN_def
  set R_a_outN : ℝ≥0 := ⟨R_a_out, le_of_lt hR_a_out_pos⟩ with hR_a_outN_def
  set r'a : ℝ≥0 := ⟨R_aug / 8, by positivity⟩ with hr'a_def
  have hr'a_pos : (0 : ℝ) < (r'a : ℝ) := by
    rw [hr'a_def]
    change 0 < (R_aug : ℝ) / 8
    linarith
  have hR_a_outN_eq : (R_a_outN : ℝ) = R_a_out := rfl
  have hR_a_midN_eq : (R_a_midN : ℝ) = R_a_mid := rfl
  have hR_aN_eq : (R_aN : ℝ) = R_a := rfl
  have hρρ_aux : (R_a_midN : ℝ) + (r'a : ℝ) ≤ (R_aug : ℝ) := by
    rw [hR_a_midN_eq, hR_a_mid_def, hR_a_out_def]
    have : (r'a : ℝ) = (R_aug : ℝ) / 8 := rfl
    linarith
  have hR_a_out_le_R_aug : (R_a_outN : ℝ) ≤ (R_aug : ℝ) := by
    rw [hR_a_outN_eq, hR_a_out_def]; linarith
  -- Convert bound on Slab into the form needed.
  have hA_bd_a : ∀ p ∈ closedBall p₀ (R_a_outN : ℝ),
      ∀ τ ∈ Icc (t₀ - T_a_out) (t₀ + T_a_out),
        ‖fderiv ℝ (augVF f τ) (aΦ ⟨p, τ⟩)‖ ≤ M_aug := by
    intro p hp τ hτ
    have hq_in : ((p, τ) : (E × (E →L[ℝ] E)) × ℝ) ∈ Slab := ⟨hp, hτ⟩
    have h_pre : ‖fderiv ℝ (augVF f τ) (aΦ ⟨p, τ⟩)‖ ≤ M_aug_pre :=
      hM_aug_pre_bd _ hq_in
    linarith
  have hsub_a : Icc (t₀ - T_a_out) (t₀ + T_a_out) ⊆ Icc (t₀ - ε_aug) (t₀ + ε_aug) :=
    Icc_subset_Icc (by linarith) (by linarith)
  -- Apply V.2.c.2 to `aΦ` for the augmented system to get joint C^1.
  have h_aug_C1 : ContDiffOn ℝ 1 aΦ ((ball p₀ (R_aN : ℝ))
      ×ˢ Ioo (t₀ - T_a) (t₀ + T_a)) := by
    have hk_aug : (1 : ℕ∞) ≤ 1 := le_refl _
    refine contDiffOn_flow_of_isLocalFlow_of_contDiff (f := augVF f)
      (t₀ := t₀) (x₀ := p₀) (r := R_aug) (tmin := t₀ - ε_aug) (tmax := t₀ + ε_aug)
      (Φ := aΦ) haΦ hk_aug h_augVF_C1 hT_a_pos hT_a_lt_mid' hT_a_mid'_lt_out
      hM_aug_nn hMTmid' hsub_a (ρ_out := R_a_outN) (ρ_mid := R_a_midN) (ρ := R_aN)
      hr'a_pos
      ?_ ?_ ?_ ?_ hA_bd_a
    · rw [hR_aN_eq, hR_a_midN_eq]; linarith [hR_a_lt_mid]
    · rw [hR_a_midN_eq, hR_a_outN_eq]; linarith [hR_a_mid_lt_out]
    · exact hρρ_aux
    · exact hR_a_out_le_R_aug
  -- Step 6: inherit C^1 smoothness to the projection.
  -- Pick T and ρ strictly less than (T_a, R_a) so that ball x₀ ρ × Ioo (t₀ - T) (t₀ + T)
  -- maps into ball p₀ R_a × Ioo (t₀ - T_a) (t₀ + T_a) via the (x, t) ↦ ((x, id), t) embedding.
  set T : ℝ := T_a / 2 with hT_def
  have hT_pos : 0 < T := by rw [hT_def]; linarith
  have hT_le_T_a : T ≤ T_a := by rw [hT_def]; linarith
  set ρ : ℝ := R_a / 2 with hρ_def
  have hρ_pos : 0 < ρ := by rw [hρ_def]; linarith
  have hρ_le_R_a : ρ ≤ R_a := by rw [hρ_def]; linarith
  set ρN : ℝ≥0 := ⟨ρ, le_of_lt hρ_pos⟩ with hρN_def
  have hρN_eq : (ρN : ℝ) = ρ := rfl
  have hρN_le_R_aN : (ρN : ℝ) ≤ (R_aN : ℝ) := by rw [hρN_eq, hR_aN_eq]; exact hρ_le_R_a
  -- Apply smoothness inheritance.
  refine ⟨T, ρN, hT_pos, hρ_pos, aΦ, ?_⟩
  refine contDiffOn_fromAugFlow_inherits (ρ_a := R_aN) (ρ := ρN) (T_a := T_a) (T := T)
    hρN_le_R_aN hT_le_T_a h_aug_C1

end LevelOneSmoothnessClause

/-! ## Congruence of the variational linear map under orbit equality

The variational linear map `variationalLinearMapAt(α, t)` depends on `α` only through the
values `fderiv ℝ (f s) (α s)` for `s ∈ Icc (t₀ - T) (t₀ + T)`.  If two reference curves
`α₁, α₂` agree pointwise on this closed interval, then the two variational linear maps at
any `t ∈ Icc (t₀ - T) (t₀ + T)` are equal as continuous linear maps.

This is the key ingredient that lets us identify
`(aΦ ⟨(x, id), t⟩).2 = variationalLinearMapAt(α := Φ ⟨x, ·⟩, t)`:
the augmented-flow lemma gives the identity along its own central orbit, and orbit equality
transfers it to `Φ`'s orbit. -/

section VariationalLinearMapCongr

variable {f : ℝ → E → E} {t₀ : ℝ}

/-- **Congruence of the variational linear map under orbit equality.**  If
`α₁ = α₂` on `Icc (t₀ - T) (t₀ + T)`, then `variationalLinearMapAt(α₁, t) = variationalLinearMapAt(α₂, t)`
as continuous linear maps for every `t ∈ Icc (t₀ - T) (t₀ + T)`. -/
theorem variationalLinearMapAt_congr_of_eqOn
    {α₁ α₂ : ℝ → E} {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hA_cont_1 : ContinuousOn (fun t => fderiv ℝ (f t) (α₁ t)) (Icc (t₀ - T) (t₀ + T)))
    (hA_bd_1 : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f t) (α₁ t)‖ ≤ M)
    (hA_cont_2 : ContinuousOn (fun t => fderiv ℝ (f t) (α₂ t)) (Icc (t₀ - T) (t₀ + T)))
    (hA_bd_2 : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f t) (α₂ t)‖ ≤ M)
    (h_eq : EqOn α₁ α₂ (Icc (t₀ - T) (t₀ + T)))
    {t : ℝ} (ht : t ∈ Icc (t₀ - T) (t₀ + T)) :
    variationalLinearMapAt (f := f) (α := α₁) (t₀ := t₀) hT hM hMT hA_cont_1 hA_bd_1 ht
      = variationalLinearMapAt (f := f) (α := α₂) (t₀ := t₀) hT hM hMT hA_cont_2 hA_bd_2 ht := by
  apply ContinuousLinearMap.ext
  intro δ
  -- Both `variationalSolutionFun(αᵢ) δ` are valid solutions along their respective orbits.
  have h_sol_1 := variationalSolutionFun_isSolution hT hM hMT hA_cont_1 hA_bd_1 δ
  have h_sol_2 := variationalSolutionFun_isSolution hT hM hMT hA_cont_2 hA_bd_2 δ
  -- The α₂-solution `y₂` is also an α₁-solution because the linearizations agree on Icc.
  set y₂ : ℝ → E := variationalSolutionFun hT hM hMT hA_cont_2 hA_bd_2 δ
  have h_sol_2_as_1 : IsVariationalSolutionOn f α₁ δ t₀ y₂ (Icc (t₀ - T) (t₀ + T)) := by
    refine ⟨h_sol_2.initial, fun s hs => ?_⟩
    have h_dw := h_sol_2.hasDerivWithinAt s hs
    have hα_eq : α₁ s = α₂ s := h_eq hs
    rw [hα_eq]
    exact h_dw
  -- Uniqueness on Icc: the α₁-solutions y₁ and y₂ agree on Icc.
  have h_eq_y := IsVariationalSolutionOn.unique_Icc hT hA_cont_1 h_sol_1 h_sol_2_as_1
  rw [variationalLinearMapAt_apply, variationalLinearMapAt_apply]
  exact h_eq_y ht

end VariationalLinearMapCongr

/-! ## Coproduct identity helper

Auxiliary theorem extracted from the coproduct-identity portion of the level-1
witness.  Given the original local flow `Φ`, a local flow `aΦ` of the augmented
vector field `augVF f`, joint `C^1`-smoothness of `f`, and finite-dimensionality
of `E`, there exists a strictly-interior open neighbourhood of `(x₀, t₀)` on
which the coproduct identity
`fderiv ℝ Φ q = (fromAugFlow aΦ q).coprod (timePieceFn f Φ q)` holds.

The proof is independent of the smoothness level of `aΦ`: only continuity of
`aΦ` (provided by `IsLocalFlow`) is used.  This makes the helper directly
reusable for higher-regularity variational projection witnesses, where `aΦ` is
constructed with stronger smoothness but the coproduct identity is established
the same way. -/

section CoproductHelper

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ}
  {Φ : E × ℝ → E}

set_option maxHeartbeats 16000000 in
/-- **Coproduct identity helper.**  Given a local flow `Φ` of `f`, a local
flow `aΦ` of the augmented vector field `augVF f` centred at `((x₀, id), t₀)`,
joint `C^1`-smoothness of `f` on `Set.univ`, and finite-dimensionality of `E`,
there exist positive `T` and `ρ` such that the coproduct identity
`fderiv ℝ Φ q = (fromAugFlow aΦ q).coprod (timePieceFn f Φ q)` holds at every
`q ∈ ball x₀ ρ ×ˢ Ioo (t₀ - T) (t₀ + T)`. -/
theorem fderiv_Phi_eq_coprod_fromAugFlow_aux
    [FiniteDimensional ℝ E]
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    (ht₀_Ioo : t₀ ∈ Ioo tmin tmax)
    (hr_pos : (0 : ℝ) < (r : ℝ))
    {R_aug : ℝ≥0} {tmin_a tmax_a : ℝ}
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    (haΦ : IsLocalFlow (augVF f) t₀ (x₀, ContinuousLinearMap.id ℝ E) R_aug
      tmin_a tmax_a aΦ)
    (ht₀_a_Ioo : t₀ ∈ Ioo tmin_a tmax_a)
    (hR_aug_pos : (0 : ℝ) < (R_aug : ℝ)) :
    ∃ (T : ℝ) (ρ : ℝ≥0) (_hT : 0 < T) (_hρ : 0 < (ρ : ℝ)),
      ∀ q ∈ (Metric.ball x₀ (ρ : ℝ)) ×ˢ Set.Ioo (t₀ - T) (t₀ + T),
        fderiv ℝ Φ q = (fromAugFlow aΦ q).coprod (timePieceFn f Φ q) := by
  classical
  -- Bookkeeping for the augmented base point.
  set p₀ : E × (E →L[ℝ] E) := (x₀, ContinuousLinearMap.id ℝ E) with hp₀_def
  -- Width-positivity for the time and augmented-time intervals.
  have ht₀_minus_tmin : 0 < t₀ - tmin := by linarith [ht₀_Ioo.1]
  have htmax_minus_t₀ : 0 < tmax - t₀ := by linarith [ht₀_Ioo.2]
  have ht₀_minus_tmin_a : 0 < t₀ - tmin_a := by linarith [ht₀_a_Ioo.1]
  have htmax_a_minus_t₀ : 0 < tmax_a - t₀ := by linarith [ht₀_a_Ioo.2]
  -- Outer time width: half of the smallest interior margin.
  set T_outer : ℝ := min (min (t₀ - tmin) (tmax - t₀))
      (min (t₀ - tmin_a) (tmax_a - t₀)) / 2 with hT_outer_def
  have hT_outer_pos : 0 < T_outer := by
    rw [hT_outer_def]
    refine div_pos
      (lt_min (lt_min ht₀_minus_tmin htmax_minus_t₀)
        (lt_min ht₀_minus_tmin_a htmax_a_minus_t₀)) (by norm_num)
  have hT_outer_le_tmin_half : T_outer ≤ (t₀ - tmin) / 2 := by
    rw [hT_outer_def]
    have h1 : min (min (t₀ - tmin) (tmax - t₀)) (min (t₀ - tmin_a) (tmax_a - t₀))
        ≤ min (t₀ - tmin) (tmax - t₀) := min_le_left _ _
    have h2 : min (t₀ - tmin) (tmax - t₀) ≤ t₀ - tmin := min_le_left _ _
    linarith
  have hT_outer_le_tmax_half : T_outer ≤ (tmax - t₀) / 2 := by
    rw [hT_outer_def]
    have h1 : min (min (t₀ - tmin) (tmax - t₀)) (min (t₀ - tmin_a) (tmax_a - t₀))
        ≤ min (t₀ - tmin) (tmax - t₀) := min_le_left _ _
    have h2 : min (t₀ - tmin) (tmax - t₀) ≤ tmax - t₀ := min_le_right _ _
    linarith
  have hT_outer_le_tmin_a_half : T_outer ≤ (t₀ - tmin_a) / 2 := by
    rw [hT_outer_def]
    have h1 : min (min (t₀ - tmin) (tmax - t₀)) (min (t₀ - tmin_a) (tmax_a - t₀))
        ≤ min (t₀ - tmin_a) (tmax_a - t₀) := min_le_right _ _
    have h2 : min (t₀ - tmin_a) (tmax_a - t₀) ≤ t₀ - tmin_a := min_le_left _ _
    linarith
  have hT_outer_le_tmax_a_half : T_outer ≤ (tmax_a - t₀) / 2 := by
    rw [hT_outer_def]
    have h1 : min (min (t₀ - tmin) (tmax - t₀)) (min (t₀ - tmin_a) (tmax_a - t₀))
        ≤ min (t₀ - tmin_a) (tmax_a - t₀) := min_le_right _ _
    have h2 : min (t₀ - tmin_a) (tmax_a - t₀) ≤ tmax_a - t₀ := min_le_right _ _
    linarith
  have hsub_outer_orig : Icc (t₀ - T_outer) (t₀ + T_outer) ⊆ Icc tmin tmax :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hsub_outer_aug : Icc (t₀ - T_outer) (t₀ + T_outer) ⊆ Icc tmin_a tmax_a :=
    Icc_subset_Icc (by linarith) (by linarith)
  -- Outer spatial radii ρ_outer = r/2 and R_aug_out = R_aug/2.
  set ρ_outer : ℝ := (r : ℝ) / 2 with hρ_outer_def
  have hρ_outer_pos : 0 < ρ_outer := by rw [hρ_outer_def]; linarith
  have hρ_outer_le_r : ρ_outer ≤ (r : ℝ) := by rw [hρ_outer_def]; linarith
  set R_aug_out : ℝ := (R_aug : ℝ) / 2 with hR_aug_out_def
  have hR_aug_out_pos : 0 < R_aug_out := by rw [hR_aug_out_def]; linarith
  have hR_aug_out_lt : R_aug_out < (R_aug : ℝ) := by rw [hR_aug_out_def]; linarith
  -- Slabs.
  set Slab_a_outer : Set ((E × (E →L[ℝ] E)) × ℝ) :=
    closedBall p₀ R_aug_out ×ˢ Icc (t₀ - T_outer) (t₀ + T_outer) with hSlab_a_outer_def
  have hSlab_a_outer_cpt : IsCompact Slab_a_outer :=
    (isCompact_closedBall (p₀ : E × (E →L[ℝ] E)) R_aug_out).prod isCompact_Icc
  have hSlab_a_outer_ne : Slab_a_outer.Nonempty :=
    ⟨(p₀, t₀), Metric.mem_closedBall_self (le_of_lt hR_aug_out_pos),
      ⟨by linarith, by linarith⟩⟩
  have hslab_aug_sub : closedBall p₀ R_aug_out ×ˢ Icc (t₀ - T_outer) (t₀ + T_outer)
      ⊆ closedBall p₀ (R_aug : ℝ) ×ˢ Icc tmin_a tmax_a := by
    refine Set.prod_mono ?_ ?_
    · exact closedBall_subset_closedBall (le_of_lt hR_aug_out_lt)
    · exact hsub_outer_aug
  -- Continuity of `aΦ` on the slab.
  have haΦ_cont_full : ContinuousOn aΦ
      (closedBall p₀ (R_aug : ℝ) ×ˢ Icc tmin_a tmax_a) := haΦ.continuousOn
  have haΦ_cont : ContinuousOn aΦ Slab_a_outer :=
    haΦ_cont_full.mono hslab_aug_sub
  -- Phase 5: aΦ-image radius `R_aΦ_image_pre`.
  have h_aΦ_norm_cont : ContinuousOn (fun q : (E × (E →L[ℝ] E)) × ℝ => ‖(aΦ q).1 - x₀‖)
      Slab_a_outer := by
    have h_fst_cont : ContinuousOn (fun q : (E × (E →L[ℝ] E)) × ℝ => (aΦ q).1) Slab_a_outer :=
      continuous_fst.continuousOn.comp haΦ_cont (fun _ _ => mem_univ _)
    have h_sub_cont : ContinuousOn (fun q : (E × (E →L[ℝ] E)) × ℝ => (aΦ q).1 - x₀)
        Slab_a_outer := h_fst_cont.sub continuousOn_const
    exact continuous_norm.comp_continuousOn h_sub_cont
  rcases hSlab_a_outer_cpt.exists_isMaxOn hSlab_a_outer_ne h_aΦ_norm_cont
    with ⟨qmax_R, _, hqmax_R⟩
  set R_aΦ_image_pre : ℝ := ‖(aΦ qmax_R).1 - x₀‖ with hR_aΦ_image_pre_def
  have hR_aΦ_image_pre_nn : 0 ≤ R_aΦ_image_pre := norm_nonneg _
  have hR_aΦ_image_pre_bd : ∀ q ∈ Slab_a_outer, ‖(aΦ q).1 - x₀‖ ≤ R_aΦ_image_pre :=
    fun q hq => hqmax_R hq
  -- Phase 6: Φ-image radius `R_Φ_image_pre`.
  set Slab_Φ_outer : Set (E × ℝ) :=
    closedBall x₀ ρ_outer ×ˢ Icc (t₀ - T_outer) (t₀ + T_outer) with hSlab_Φ_outer_def
  have hSlab_Φ_outer_cpt : IsCompact Slab_Φ_outer :=
    (isCompact_closedBall x₀ ρ_outer).prod isCompact_Icc
  have hSlab_Φ_outer_ne : Slab_Φ_outer.Nonempty :=
    ⟨(x₀, t₀), Metric.mem_closedBall_self (le_of_lt hρ_outer_pos),
      ⟨by linarith, by linarith⟩⟩
  have hSlab_Φ_outer_sub_orig : Slab_Φ_outer ⊆ closedBall x₀ (r : ℝ) ×ˢ Icc tmin tmax := by
    refine Set.prod_mono ?_ ?_
    · exact closedBall_subset_closedBall hρ_outer_le_r
    · exact hsub_outer_orig
  have hΦ_cont_slab : ContinuousOn Φ Slab_Φ_outer := hΦ.continuousOn.mono hSlab_Φ_outer_sub_orig
  have h_Φ_norm_cont : ContinuousOn (fun p : E × ℝ => ‖Φ p - x₀‖) Slab_Φ_outer := by
    have h_sub_cont : ContinuousOn (fun p : E × ℝ => Φ p - x₀) Slab_Φ_outer :=
      hΦ_cont_slab.sub continuousOn_const
    exact continuous_norm.comp_continuousOn h_sub_cont
  rcases hSlab_Φ_outer_cpt.exists_isMaxOn hSlab_Φ_outer_ne h_Φ_norm_cont
    with ⟨pmax_R, _, hpmax_R⟩
  set R_Φ_image_pre : ℝ := ‖Φ pmax_R - x₀‖ with hR_Φ_image_pre_def
  have hR_Φ_image_pre_nn : 0 ≤ R_Φ_image_pre := norm_nonneg _
  have hR_Φ_image_pre_bd : ∀ p ∈ Slab_Φ_outer, ‖Φ p - x₀‖ ≤ R_Φ_image_pre :=
    fun p hp => hpmax_R hp
  -- Phase 7: unified Lipschitz radius `r₀_lip` and Lipschitz constant `K_orig`.
  set r₀_lip : ℝ := max R_aΦ_image_pre R_Φ_image_pre + 1 with hr₀_lip_def
  have hr₀_lip_pos : 0 < r₀_lip := by
    rw [hr₀_lip_def]
    have : 0 ≤ max R_aΦ_image_pre R_Φ_image_pre :=
      le_max_of_le_left hR_aΦ_image_pre_nn
    linarith
  have hr₀_lip_ge_aΦ : R_aΦ_image_pre ≤ r₀_lip := by
    rw [hr₀_lip_def]
    have : R_aΦ_image_pre ≤ max R_aΦ_image_pre R_Φ_image_pre := le_max_left _ _
    linarith
  have hr₀_lip_ge_Φ : R_Φ_image_pre ≤ r₀_lip := by
    rw [hr₀_lip_def]
    have : R_Φ_image_pre ≤ max R_aΦ_image_pre R_Φ_image_pre := le_max_right _ _
    linarith
  set Slab_f : Set (ℝ × E) :=
    Icc (t₀ - T_outer) (t₀ + T_outer) ×ˢ closedBall x₀ r₀_lip with hSlab_f_def
  have hSlab_f_cpt : IsCompact Slab_f :=
    isCompact_Icc.prod (isCompact_closedBall x₀ r₀_lip)
  have hSlab_f_ne : Slab_f.Nonempty :=
    ⟨(t₀, x₀), ⟨by linarith, by linarith⟩, Metric.mem_closedBall_self (le_of_lt hr₀_lip_pos)⟩
  have hpartial_f : ContDiffOn ℝ 0 (fun p : ℝ × E => fderiv ℝ (f p.1) p.2)
      (Set.univ : Set (ℝ × E)) :=
    contDiffOn_partial_fderiv_of_succ (f := f) (k := (0 : ℕ∞))
      (by simpa using hf_C1)
  have hpartial_f_cont : ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) Slab_f :=
    hpartial_f.continuousOn.mono (subset_univ _)
  have hpartial_f_norm_cont : ContinuousOn (fun p : ℝ × E => ‖fderiv ℝ (f p.1) p.2‖) Slab_f :=
    continuous_norm.comp_continuousOn hpartial_f_cont
  rcases hSlab_f_cpt.exists_isMaxOn hSlab_f_ne hpartial_f_norm_cont
    with ⟨pmax_K, _, hpmax_K⟩
  set K_pre : ℝ := ‖fderiv ℝ (f pmax_K.1) pmax_K.2‖ with hK_pre_def
  have hK_pre_nn : 0 ≤ K_pre := norm_nonneg _
  have hK_pre_bd : ∀ p ∈ Slab_f, ‖fderiv ℝ (f p.1) p.2‖ ≤ K_pre := fun p hp => hpmax_K hp
  set K_orig : ℝ := K_pre + 1 with hK_orig_def
  have hK_orig_pos : 0 < K_orig := by rw [hK_orig_def]; linarith
  have hK_orig_nn : 0 ≤ K_orig := le_of_lt hK_orig_pos
  set K_origN : ℝ≥0 := ⟨K_orig, hK_orig_nn⟩ with hK_origN_def
  have hK_origN_eq : (K_origN : ℝ) = K_orig := rfl
  -- Phase 8: mid time width `T_mid` with `K_orig · T_mid < 1`.
  set T_mid : ℝ := min (T_outer * 3 / 4) (1 / (2 * K_orig)) with hT_mid_def
  have hT_mid_pos : 0 < T_mid := by
    refine lt_min ?_ ?_
    · positivity
    · have : 0 < 2 * K_orig := by linarith
      positivity
  have hT_mid_lt_outer : T_mid < T_outer := by
    have h1 : T_mid ≤ T_outer * 3 / 4 := min_le_left _ _
    linarith
  have hKT_mid : K_orig * T_mid < 1 := by
    have h1 : T_mid ≤ 1 / (2 * K_orig) := min_le_right _ _
    have h2 : K_orig * T_mid ≤ K_orig * (1 / (2 * K_orig)) :=
      mul_le_mul_of_nonneg_left h1 hK_orig_nn
    have h3 : K_orig * (1 / (2 * K_orig)) = 1 / 2 := by field_simp
    linarith
  -- Phase 9: final time width `T_final < T_mid` and final spatial radius `ρ_final`.
  set T_final : ℝ := T_mid / 2 with hT_final_def
  have hT_final_pos : 0 < T_final := by rw [hT_final_def]; linarith
  have hT_final_lt_mid : T_final < T_mid := by rw [hT_final_def]; linarith
  set ρ_final : ℝ := min ρ_outer R_aug_out / 8 with hρ_final_def
  have hρ_final_pos : 0 < ρ_final := by
    rw [hρ_final_def]
    refine div_pos (lt_min hρ_outer_pos hR_aug_out_pos) (by norm_num)
  have hρ_final_le_outer_8 : ρ_final ≤ ρ_outer / 8 := by
    rw [hρ_final_def]
    have : min ρ_outer R_aug_out ≤ ρ_outer := min_le_left _ _
    linarith
  have hρ_final_le_outer : ρ_final ≤ ρ_outer := by linarith
  have hρ_final_le_R_aug_out_8 : ρ_final ≤ R_aug_out / 8 := by
    rw [hρ_final_def]
    have : min ρ_outer R_aug_out ≤ R_aug_out := min_le_right _ _
    linarith
  have hρ_final_le_R_aug_out : ρ_final ≤ R_aug_out := by linarith
  set ρ_finalN : ℝ≥0 := ⟨ρ_final, le_of_lt hρ_final_pos⟩ with hρ_finalN_def
  have hρ_finalN_eq : (ρ_finalN : ℝ) = ρ_final := rfl
  -- Phase 11: assemble the coproduct identity at each `q ∈ ball x₀ ρ_final × Ioo`.
  refine ⟨T_final, ρ_finalN, hT_final_pos, hρ_final_pos, ?_⟩
  intro q hq
  rcases hq with ⟨hq_x, hq_t⟩
  obtain ⟨x, t⟩ := q
  rw [mem_ball] at hq_x
  change dist x x₀ < ρ_final at hq_x
  have hx_closed_ρ_final : x ∈ closedBall x₀ ρ_final := mem_closedBall.mpr (le_of_lt hq_x)
  have hx_closed_ρ_outer : x ∈ closedBall x₀ ρ_outer :=
    closedBall_subset_closedBall hρ_final_le_outer hx_closed_ρ_final
  have hx_closed_r : x ∈ closedBall x₀ (r : ℝ) :=
    closedBall_subset_closedBall hρ_outer_le_r hx_closed_ρ_outer
  have hx_id_closed_R_aug_out : (x, ContinuousLinearMap.id ℝ E) ∈ closedBall p₀ R_aug_out := by
    rw [mem_closedBall]
    change max (dist x x₀) (dist (ContinuousLinearMap.id ℝ E)
      (ContinuousLinearMap.id ℝ E)) ≤ R_aug_out
    rw [dist_self, max_eq_left dist_nonneg]
    rw [mem_closedBall] at hx_closed_ρ_final
    exact le_trans hx_closed_ρ_final hρ_final_le_R_aug_out
  have hx_id_closed_R_aug : (x, ContinuousLinearMap.id ℝ E) ∈ closedBall p₀ (R_aug : ℝ) :=
    closedBall_subset_closedBall (le_of_lt hR_aug_out_lt) hx_id_closed_R_aug_out
  have ht_Ioo_final : t ∈ Ioo (t₀ - T_final) (t₀ + T_final) := hq_t
  have ht_Icc_final : t ∈ Icc (t₀ - T_final) (t₀ + T_final) := Ioo_subset_Icc_self ht_Ioo_final
  -- Phase 11.A: orbit-equality on Icc (t₀ - T_final) (t₀ + T_final).
  have hsub_final_outer : Icc (t₀ - T_final) (t₀ + T_final) ⊆ Icc (t₀ - T_outer) (t₀ + T_outer) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hsub_final_orig : Icc (t₀ - T_final) (t₀ + T_final) ⊆ Icc tmin tmax :=
    hsub_final_outer.trans hsub_outer_orig
  have hsub_final_aug : Icc (t₀ - T_final) (t₀ + T_final) ⊆ Icc tmin_a tmax_a :=
    hsub_final_outer.trans hsub_outer_aug
  have h_Φ_in_r₀ : ∀ s ∈ Ioo (t₀ - T_final) (t₀ + T_final), Φ ⟨x, s⟩ ∈ closedBall x₀ r₀_lip := by
    intro s hs
    have hs_Icc_outer : s ∈ Icc (t₀ - T_outer) (t₀ + T_outer) :=
      hsub_final_outer (Ioo_subset_Icc_self hs)
    have h_pair_in_outer : ((x, s) : E × ℝ) ∈ Slab_Φ_outer :=
      ⟨hx_closed_ρ_outer, hs_Icc_outer⟩
    have h_pre : ‖Φ (x, s) - x₀‖ ≤ R_Φ_image_pre := hR_Φ_image_pre_bd _ h_pair_in_outer
    rw [mem_closedBall, dist_eq_norm]
    exact le_trans h_pre hr₀_lip_ge_Φ
  have h_aΦ_fst_in_r₀ : ∀ s ∈ Ioo (t₀ - T_final) (t₀ + T_final),
      (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1 ∈ closedBall x₀ r₀_lip := by
    intro s hs
    have hs_Icc_outer : s ∈ Icc (t₀ - T_outer) (t₀ + T_outer) :=
      hsub_final_outer (Ioo_subset_Icc_self hs)
    have h_pair_in_a_outer : (((x, ContinuousLinearMap.id ℝ E), s) :
        (E × (E →L[ℝ] E)) × ℝ) ∈ Slab_a_outer :=
      ⟨hx_id_closed_R_aug_out, hs_Icc_outer⟩
    have h_pre : ‖(aΦ ((x, ContinuousLinearMap.id ℝ E), s)).1 - x₀‖ ≤ R_aΦ_image_pre :=
      hR_aΦ_image_pre_bd _ h_pair_in_a_outer
    rw [mem_closedBall, dist_eq_norm]
    exact le_trans h_pre hr₀_lip_ge_aΦ
  have h_lip_on_r₀ : ∀ τ ∈ Ioo (t₀ - T_final) (t₀ + T_final),
      LipschitzOnWith K_origN (f τ) (closedBall x₀ r₀_lip) := by
    intro τ hτ
    have hτ_Icc : τ ∈ Icc (t₀ - T_outer) (t₀ + T_outer) :=
      hsub_final_outer (Ioo_subset_Icc_self hτ)
    have hf_τ_diff_at : ∀ z, DifferentiableAt ℝ (f τ) z := fun z => by
      have hcd_at : ContDiffAt ℝ 1 (uncurry f) (τ, z) :=
        hf_C1.contDiffAt (IsOpen.mem_nhds isOpen_univ (mem_univ _))
      exact (hcd_at.differentiableAt one_ne_zero).comp z
        (((differentiableAt_const τ).prodMk differentiableAt_id))
    have hbound : ∀ z ∈ closedBall x₀ r₀_lip, ‖fderiv ℝ (f τ) z‖₊ ≤ K_origN := by
      intro z hz
      have hp_in : ((τ, z) : ℝ × E) ∈ Slab_f := ⟨hτ_Icc, hz⟩
      have h_pre : ‖fderiv ℝ (f τ) z‖ ≤ K_pre := hK_pre_bd _ hp_in
      have h_le_K_orig : ‖fderiv ℝ (f τ) z‖ ≤ K_orig := by rw [hK_orig_def]; linarith
      rw [← NNReal.coe_le_coe, coe_nnnorm, hK_origN_eq]
      exact h_le_K_orig
    exact (convex_closedBall x₀ r₀_lip).lipschitzOnWith_of_nnnorm_fderiv_le
      (f := f τ) (C := K_origN) (fun z _ => hf_τ_diff_at z) hbound
  have ht₀_Ioo_final : t₀ ∈ Ioo (t₀ - T_final) (t₀ + T_final) :=
    ⟨by linarith, by linarith⟩
  have h_orbit_eqOn : EqOn (fun s => Φ ⟨x, s⟩)
      (fun s => (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1)
      (Icc (t₀ - T_final) (t₀ + T_final)) :=
    orbit_eq_Icc_of_augFlow_isLocalFlow hΦ haΦ hx_closed_r hx_id_closed_R_aug
      hsub_final_orig hsub_final_aug ht₀_Ioo_final
      (r₀ := r₀_lip) (K := K_origN) h_Φ_in_r₀ h_aΦ_fst_in_r₀ h_lip_on_r₀
  -- Phase 11.B: identify `(aΦ⟨(x, id), t⟩).2 = variationalLinearMapAt(α := Φ⟨x, ·⟩, t)`.
  have hA_cont_orbit_a : ContinuousOn (fun s : ℝ => fderiv ℝ (f s)
      ((aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1)) (Icc (t₀ - T_final) (t₀ + T_final)) := by
    have h_pair_cont : ContinuousOn (fun s : ℝ => (s, (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1))
        (Icc (t₀ - T_final) (t₀ + T_final)) := by
      have h_orbit_cont : ContinuousOn
          (fun s : ℝ => aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩)
          (Icc (t₀ - T_final) (t₀ + T_final)) :=
        (haΦ.orbit_continuousOn (x, ContinuousLinearMap.id ℝ E) hx_id_closed_R_aug).mono
          (by intro s hs; exact hsub_final_aug hs)
      have h_fst_cont : ContinuousOn (fun s : ℝ => (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1)
          (Icc (t₀ - T_final) (t₀ + T_final)) :=
        continuous_fst.continuousOn.comp h_orbit_cont (fun _ _ => mem_univ _)
      exact continuousOn_id.prodMk h_fst_cont
    have hpartial_cont : ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2)
        (Set.univ : Set (ℝ × E)) := hpartial_f.continuousOn
    have hmaps : MapsTo (fun s : ℝ => (s, (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1))
        (Icc (t₀ - T_final) (t₀ + T_final)) (Set.univ : Set (ℝ × E)) :=
      fun _ _ => mem_univ _
    exact hpartial_cont.comp h_pair_cont hmaps
  have hA_bd_orbit_a : ∀ s ∈ Icc (t₀ - T_final) (t₀ + T_final),
      ‖fderiv ℝ (f s) ((aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1)‖ ≤ K_orig := by
    intro s hs
    have hs_outer_Icc : s ∈ Icc (t₀ - T_outer) (t₀ + T_outer) := hsub_final_outer hs
    have h_orbit_in_r₀ : (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1 ∈ closedBall x₀ r₀_lip := by
      have h_pair_in_a_outer : (((x, ContinuousLinearMap.id ℝ E), s) :
          (E × (E →L[ℝ] E)) × ℝ) ∈ Slab_a_outer :=
        ⟨hx_id_closed_R_aug_out, hs_outer_Icc⟩
      have h_pre : ‖(aΦ ((x, ContinuousLinearMap.id ℝ E), s)).1 - x₀‖ ≤ R_aΦ_image_pre :=
        hR_aΦ_image_pre_bd _ h_pair_in_a_outer
      rw [mem_closedBall, dist_eq_norm]
      exact le_trans h_pre hr₀_lip_ge_aΦ
    have h_pair_in_f : ((s, (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1) : ℝ × E) ∈ Slab_f :=
      ⟨hs_outer_Icc, h_orbit_in_r₀⟩
    have h_pre : ‖fderiv ℝ (f s) ((aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1)‖ ≤ K_pre :=
      hK_pre_bd _ h_pair_in_f
    linarith
  have h_KT_final : K_orig * T_final < 1 := by
    have : K_orig * T_final < K_orig * T_mid :=
      mul_lt_mul_of_pos_left hT_final_lt_mid hK_orig_pos
    linarith
  have h_aΦ_snd_eq : (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).2
      = variationalLinearMapAt (f := f)
          (α := fun s => (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1) (t₀ := t₀)
          hT_final_pos hK_orig_nn h_KT_final hA_cont_orbit_a hA_bd_orbit_a ht_Icc_final :=
    augFlow_snd_eq_variationalLinearMapAt (aΦ := aΦ) (R := R_aug) (tmin' := tmin_a)
      (tmax' := tmax_a) (p₀ := p₀) haΦ
      (T := T_final) (M := K_orig) hT_final_pos hK_orig_nn h_KT_final hsub_final_aug
      (x := x) hx_id_closed_R_aug hA_cont_orbit_a hA_bd_orbit_a ht_Icc_final
  have hA_cont_orbit_Φ : ContinuousOn (fun s : ℝ => fderiv ℝ (f s) (Φ ⟨x, s⟩))
      (Icc (t₀ - T_final) (t₀ + T_final)) := by
    have h_pair_cont : ContinuousOn (fun s : ℝ => (s, Φ ⟨x, s⟩))
        (Icc (t₀ - T_final) (t₀ + T_final)) := by
      have h_orbit_cont : ContinuousOn (fun s : ℝ => Φ ⟨x, s⟩) (Icc tmin tmax) :=
        hΦ.orbit_continuousOn x hx_closed_r
      have h_orbit_cont_final : ContinuousOn (fun s : ℝ => Φ ⟨x, s⟩)
          (Icc (t₀ - T_final) (t₀ + T_final)) := h_orbit_cont.mono hsub_final_orig
      exact continuousOn_id.prodMk h_orbit_cont_final
    exact hpartial_f.continuousOn.comp h_pair_cont (fun _ _ => mem_univ _)
  have hA_bd_orbit_Φ : ∀ s ∈ Icc (t₀ - T_final) (t₀ + T_final),
      ‖fderiv ℝ (f s) (Φ ⟨x, s⟩)‖ ≤ K_orig := by
    intro s hs
    have hs_outer_Icc : s ∈ Icc (t₀ - T_outer) (t₀ + T_outer) := hsub_final_outer hs
    have h_pair_in_outer : ((x, s) : E × ℝ) ∈ Slab_Φ_outer :=
      ⟨hx_closed_ρ_outer, hs_outer_Icc⟩
    have h_orbit_in_r₀ : Φ ⟨x, s⟩ ∈ closedBall x₀ r₀_lip := by
      have h_pre : ‖Φ (x, s) - x₀‖ ≤ R_Φ_image_pre := hR_Φ_image_pre_bd _ h_pair_in_outer
      rw [mem_closedBall, dist_eq_norm]
      exact le_trans h_pre hr₀_lip_ge_Φ
    have h_pair_in_f : ((s, Φ ⟨x, s⟩) : ℝ × E) ∈ Slab_f := ⟨hs_outer_Icc, h_orbit_in_r₀⟩
    have h_pre : ‖fderiv ℝ (f s) (Φ ⟨x, s⟩)‖ ≤ K_pre := hK_pre_bd _ h_pair_in_f
    linarith
  have h_var_congr := variationalLinearMapAt_congr_of_eqOn (f := f)
    (α₁ := fun s => (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1)
    (α₂ := fun s => Φ ⟨x, s⟩) (t₀ := t₀) (T := T_final) (M := K_orig)
    hT_final_pos hK_orig_nn h_KT_final
    hA_cont_orbit_a hA_bd_orbit_a hA_cont_orbit_Φ hA_bd_orbit_Φ
    h_orbit_eqOn.symm ht_Icc_final
  have h_aΦ_snd_eq_Φ : (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).2
      = variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x, s⟩) (t₀ := t₀)
          hT_final_pos hK_orig_nn h_KT_final hA_cont_orbit_Φ hA_bd_orbit_Φ ht_Icc_final := by
    rw [h_aΦ_snd_eq, h_var_congr]
  -- Phase 11.C: joint Fréchet derivative formula for Φ at (x, t).
  set ρ_outerN : ℝ≥0 := ⟨ρ_outer, le_of_lt hρ_outer_pos⟩
  set r'_φ : ℝ≥0 := ⟨ρ_outer / 2, by positivity⟩
  have hr'_φ_pos : (0 : ℝ) < (r'_φ : ℝ) := by change 0 < ρ_outer / 2; linarith
  have hρρ'_φ : (ρ_outerN : ℝ) + (r'_φ : ℝ) ≤ (r : ℝ) := by
    change ρ_outer + ρ_outer / 2 ≤ (r : ℝ)
    have : ρ_outer + ρ_outer / 2 = ρ_outer * 3 / 2 := by ring
    rw [this, hρ_outer_def]
    have : (r : ℝ) / 2 * 3 / 2 ≤ (r : ℝ) := by linarith
    linarith
  have hA_bd_Φ_jointly : ∀ y ∈ closedBall x₀ (ρ_outerN : ℝ),
      ∀ τ ∈ Icc (t₀ - T_mid) (t₀ + T_mid),
        ‖fderiv ℝ (f τ) (Φ ⟨y, τ⟩)‖ ≤ K_orig := by
    intro y hy τ hτ
    have hy_closed_ρ_outer : y ∈ closedBall x₀ ρ_outer := by
      change dist y x₀ ≤ ρ_outer
      rw [mem_closedBall] at hy
      exact hy
    have hy_closed_r : y ∈ closedBall x₀ (r : ℝ) :=
      closedBall_subset_closedBall hρ_outer_le_r hy_closed_ρ_outer
    have hτ_outer : τ ∈ Icc (t₀ - T_outer) (t₀ + T_outer) := by
      refine ⟨?_, ?_⟩ <;> [linarith [hτ.1]; linarith [hτ.2]]
    have h_pair_in_outer : ((y, τ) : E × ℝ) ∈ Slab_Φ_outer := ⟨hy_closed_ρ_outer, hτ_outer⟩
    have h_orbit_in_r₀ : Φ ⟨y, τ⟩ ∈ closedBall x₀ r₀_lip := by
      have h_pre : ‖Φ (y, τ) - x₀‖ ≤ R_Φ_image_pre := hR_Φ_image_pre_bd _ h_pair_in_outer
      rw [mem_closedBall, dist_eq_norm]
      exact le_trans h_pre hr₀_lip_ge_Φ
    have h_pair_in_f : ((τ, Φ ⟨y, τ⟩) : ℝ × E) ∈ Slab_f := ⟨hτ_outer, h_orbit_in_r₀⟩
    have h_pre : ‖fderiv ℝ (f τ) (Φ ⟨y, τ⟩)‖ ≤ K_pre := hK_pre_bd _ h_pair_in_f
    linarith
  have hsub_mid_orig : Icc (t₀ - T_mid) (t₀ + T_mid) ⊆ Icc tmin tmax := by
    refine Icc_subset_Icc ?_ ?_ <;> [linarith [hT_mid_lt_outer]; linarith [hT_mid_lt_outer]]
  have ht_Ioo_mid : t ∈ Ioo (t₀ - T_mid) (t₀ + T_mid) := by
    refine ⟨?_, ?_⟩ <;> [linarith [ht_Ioo_final.1, hT_final_lt_mid]; linarith [ht_Ioo_final.2, hT_final_lt_mid]]
  have hx_closed_ρ_outerN : x ∈ closedBall x₀ (ρ_outerN : ℝ) := by
    change dist x x₀ ≤ ρ_outer
    rw [mem_closedBall] at hx_closed_ρ_outer
    exact hx_closed_ρ_outer
  have h_jointFD := hasFDerivAt_flow_jointly_at hΦ hf_C1
    hT_mid_pos hK_orig_nn hKT_mid hsub_mid_orig hr'_φ_pos hρρ'_φ hA_bd_Φ_jointly
    hx_closed_ρ_outerN ht_Ioo_mid
  have hfderiv_Φ_eq := h_jointFD.fderiv
  set Lmap_mid := variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x, s⟩) (t₀ := t₀)
    hT_mid_pos hK_orig_nn hKT_mid
    ((hΦ.continuousOn_fderiv_along_orbit hf_C1 x hx_closed_r).mono hsub_mid_orig)
    (fun τ hτ => hA_bd_Φ_jointly x hx_closed_ρ_outerN τ hτ)
    (Ioo_subset_Icc_self ht_Ioo_mid)
  set Lti : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight (f t (Φ ⟨x, t⟩))
  have hgoal_lhs : fderiv ℝ Φ (x, t) = Lmap_mid.coprod Lti := hfderiv_Φ_eq
  have hLmap_mid_restricted_to_final : Lmap_mid =
      variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x, s⟩) (t₀ := t₀)
        hT_final_pos hK_orig_nn h_KT_final hA_cont_orbit_Φ hA_bd_orbit_Φ ht_Icc_final := by
    apply ContinuousLinearMap.ext
    intro δ
    have h_sol_mid := variationalSolutionFun_isSolution hT_mid_pos hK_orig_nn hKT_mid
      ((hΦ.continuousOn_fderiv_along_orbit hf_C1 x hx_closed_r).mono hsub_mid_orig)
      (fun τ hτ => hA_bd_Φ_jointly x hx_closed_ρ_outerN τ hτ) δ
    have h_sol_final := variationalSolutionFun_isSolution hT_final_pos hK_orig_nn h_KT_final
      hA_cont_orbit_Φ hA_bd_orbit_Φ δ
    have hsub_final_mid : Icc (t₀ - T_final) (t₀ + T_final) ⊆ Icc (t₀ - T_mid) (t₀ + T_mid) :=
      Icc_subset_Icc (by linarith [hT_final_lt_mid]) (by linarith [hT_final_lt_mid])
    have h_sol_mid_restricted := h_sol_mid.mono hsub_final_mid
    have h_eq_y := IsVariationalSolutionOn.unique_Icc hT_final_pos hA_cont_orbit_Φ
      h_sol_mid_restricted h_sol_final
    rw [variationalLinearMapAt_apply, variationalLinearMapAt_apply]
    exact h_eq_y ht_Icc_final
  have hLmap_mid_eq_aΦ_snd : Lmap_mid = (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).2 := by
    rw [hLmap_mid_restricted_to_final, ← h_aΦ_snd_eq_Φ]
  rw [hgoal_lhs, hLmap_mid_eq_aΦ_snd]
  rfl

end CoproductHelper

/-! ## The full level-1 variational-flow projection witness

The headline theorem `exists_isVariationalFlowProjection_one_of_C2` combines:
* the joint `C^1` smoothness of `Y := fromAugFlow aΦ` on a strictly-interior open
  neighbourhood of `(x₀, t₀)`, established by running `contDiffOn_flow_of_isLocalFlow_of_contDiff`
  on the augmented system `(augVF f, aΦ)` and inheriting via `contDiffOn_fromAugFlow_inherits`;
* the coproduct identity `fderiv ℝ Φ q = (Y q).coprod (timePieceFn f Φ q)`, obtained by
  combining the joint Fréchet derivative formula `hasFDerivAt_flow_jointly_at` with the orbit
  equality on a closed interval (built from continuity of `Φ` and `aΦ` plus uniform
  Lipschitz of `f`, all extracted from finite-dim compactness) and the variational
  identification `augFlow_snd_eq_variationalLinearMapAt`.

**On hypotheses.**  The headline carries two mathematical hypotheses beyond joint `C²` of
`f` and finite dimensionality of `E`: `ht₀_Ioo : t₀ ∈ Ioo tmin tmax` (so a positive-width
interior interval exists) and `hr_pos : 0 < (r : ℝ)` (so the joint Fréchet derivative
formula applies on a nontrivial spatial ball). -/

section LevelOneFullWitness

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

set_option maxHeartbeats 16000000 in
/-- **Full level-1 variational-flow projection witness.**

If `f : ℝ → E → E` is jointly `C^2` on `Set.univ`, `E` is a finite-dimensional Banach
space, `Φ` is a local Picard–Lindelöf flow centered at `(x₀, t₀)` with `t₀` strictly inside
its time domain, and the flow's spatial radius `r` is positive, then there exist positive
`T` and `ρ` together with a function `Y : E × ℝ → (E →L[ℝ] E)` that is a level-1
variational-flow projection of `Φ` on the strictly-interior open neighbourhood
`(ball x₀ ρ) ×ˢ Ioo (t₀ - T) (t₀ + T)`.

The function `Y` is `fromAugFlow aΦ` where `aΦ` is the local flow of the augmented vector
field `augVF f` on `E × (E →L[ℝ] E)` centred at `((x₀, id), t₀)`. -/
theorem exists_isVariationalFlowProjection_one_of_C2
    [FiniteDimensional ℝ E]
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (ht₀_Ioo : t₀ ∈ Ioo tmin tmax)
    (hr_pos : (0 : ℝ) < (r : ℝ))
    (hf_C2 : ContDiffOn ℝ 2 (uncurry f) (Set.univ : Set (ℝ × E))) :
    ∃ (T : ℝ) (ρ : ℝ≥0) (_hT : 0 < T) (_hρ : 0 < (ρ : ℝ))
      (Y : E × ℝ → (E →L[ℝ] E)),
      IsVariationalFlowProjection hΦ T ρ Y 1 := by
  classical
  -- ## Phase 1: augmented flow `aΦ` from joint C² of `f`.
  set p₀ : E × (E →L[ℝ] E) := (x₀, ContinuousLinearMap.id ℝ E) with hp₀_def
  obtain ⟨R_aug, ε_aug, hR_aug_pos, hε_aug_pos, aΦ, haΦ⟩ :=
    exists_isLocalFlow_augVF_of_C2 hf_C2 t₀ p₀
  have hR_aug_R : (0 : ℝ) < (R_aug : ℝ) := by exact_mod_cast hR_aug_pos
  have hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)) := by
    have h_le : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast (by decide : (1 : ℕ∞) ≤ 2)
    exact hf_C2.of_le h_le
  have hf_succ : ContDiffOn ℝ ((1 : ℕ∞) + 1) (uncurry f) (Set.univ : Set (ℝ × E)) := by
    simpa using hf_C2
  have h_augVF_C1 : ContDiffOn ℝ 1 (uncurry (augVF f))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    augVF_uncurry_contDiff (k := (1 : ℕ∞)) hf_succ
  -- ## Phase 2: pick the outer time width T_outer for which:
  -- (i) Icc(t₀-T_outer, t₀+T_outer) ⊆ Icc tmin tmax;
  -- (ii) Icc(t₀-T_outer, t₀+T_outer) ⊆ Icc(t₀-ε_aug, t₀+ε_aug).
  have ht₀_minus_tmin : 0 < t₀ - tmin := by linarith [ht₀_Ioo.1]
  have htmax_minus_t₀ : 0 < tmax - t₀ := by linarith [ht₀_Ioo.2]
  set T_outer : ℝ := min (ε_aug / 2) (min (t₀ - tmin) (tmax - t₀)) / 2 with hT_outer_def
  have hT_outer_pos : 0 < T_outer := by
    rw [hT_outer_def]
    refine div_pos (lt_min ?_ (lt_min ht₀_minus_tmin htmax_minus_t₀)) (by norm_num)
    linarith
  have hT_outer_le_eps_half : T_outer ≤ ε_aug / 4 := by
    rw [hT_outer_def]
    have h1 : min (ε_aug / 2) (min (t₀ - tmin) (tmax - t₀)) ≤ ε_aug / 2 :=
      min_le_left _ _
    linarith
  have hT_outer_lt_eps : T_outer < ε_aug := by linarith
  have hT_outer_le_tmin_half : T_outer ≤ (t₀ - tmin) / 2 := by
    rw [hT_outer_def]
    have h1 : min (ε_aug / 2) (min (t₀ - tmin) (tmax - t₀)) ≤ min (t₀ - tmin) (tmax - t₀) :=
      min_le_right _ _
    have h2 : min (t₀ - tmin) (tmax - t₀) ≤ t₀ - tmin := min_le_left _ _
    linarith
  have hT_outer_le_tmax_half : T_outer ≤ (tmax - t₀) / 2 := by
    rw [hT_outer_def]
    have h1 : min (ε_aug / 2) (min (t₀ - tmin) (tmax - t₀)) ≤ min (t₀ - tmin) (tmax - t₀) :=
      min_le_right _ _
    have h2 : min (t₀ - tmin) (tmax - t₀) ≤ tmax - t₀ := min_le_right _ _
    linarith
  have hsub_outer_orig : Icc (t₀ - T_outer) (t₀ + T_outer) ⊆ Icc tmin tmax :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hsub_outer_aug : Icc (t₀ - T_outer) (t₀ + T_outer) ⊆ Icc (t₀ - ε_aug) (t₀ + ε_aug) :=
    Icc_subset_Icc (by linarith) (by linarith)
  -- ## Phase 3: pick outer spatial radii ρ_outer ≤ r/2 (for Φ-orbit lookup) and
  -- R_aug_out := R_aug/2 (for aΦ-orbit lookup).
  set ρ_outer : ℝ := (r : ℝ) / 2 with hρ_outer_def
  have hρ_outer_pos : 0 < ρ_outer := by rw [hρ_outer_def]; linarith
  have hρ_outer_le_r : ρ_outer ≤ (r : ℝ) := by rw [hρ_outer_def]; linarith
  set R_aug_out : ℝ := (R_aug : ℝ) / 2 with hR_aug_out_def
  have hR_aug_out_pos : 0 < R_aug_out := by rw [hR_aug_out_def]; linarith
  have hR_aug_out_lt : R_aug_out < (R_aug : ℝ) := by rw [hR_aug_out_def]; linarith
  -- Embedding: (x, t) ↦ ((x, id), t) maps closedBall x₀ ρ_outer × Icc ↪ closedBall p₀ R_aug_out × Icc
  -- requires ρ_outer ≤ R_aug_out. (We'll instead use a smaller ρ later.)
  -- Slab_a_outer for augmented: closedBall p₀ R_aug_out × Icc(t₀-T_outer, t₀+T_outer).
  set Slab_a_outer : Set ((E × (E →L[ℝ] E)) × ℝ) :=
    closedBall p₀ R_aug_out ×ˢ Icc (t₀ - T_outer) (t₀ + T_outer) with hSlab_a_outer_def
  have hSlab_a_outer_cpt : IsCompact Slab_a_outer :=
    (isCompact_closedBall (p₀ : E × (E →L[ℝ] E)) R_aug_out).prod isCompact_Icc
  have hSlab_a_outer_ne : Slab_a_outer.Nonempty :=
    ⟨(p₀, t₀), Metric.mem_closedBall_self (le_of_lt hR_aug_out_pos),
      ⟨by linarith, by linarith⟩⟩
  have hslab_aug_sub : closedBall p₀ R_aug_out ×ˢ Icc (t₀ - T_outer) (t₀ + T_outer)
      ⊆ closedBall p₀ (R_aug : ℝ) ×ˢ Icc (t₀ - ε_aug) (t₀ + ε_aug) := by
    refine Set.prod_mono ?_ ?_
    · exact closedBall_subset_closedBall (le_of_lt hR_aug_out_lt)
    · exact hsub_outer_aug
  -- ## Phase 4: extract M_aug for augmented operator-norm bound.
  have hpartial_a : ContDiffOn ℝ 0 (fun p : ℝ × (E × (E →L[ℝ] E)) =>
      fderiv ℝ (augVF f p.1) p.2)
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    contDiffOn_partial_fderiv_of_succ (f := augVF f) (k := (0 : ℕ∞))
      (by simpa using h_augVF_C1)
  have hpartial_a_cont : ContinuousOn (fun p : ℝ × (E × (E →L[ℝ] E)) =>
      fderiv ℝ (augVF f p.1) p.2) (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    hpartial_a.continuousOn
  have haΦ_cont_full : ContinuousOn aΦ
      (closedBall p₀ (R_aug : ℝ) ×ˢ Icc (t₀ - ε_aug) (t₀ + ε_aug)) :=
    haΦ.continuousOn
  have haΦ_cont : ContinuousOn aΦ Slab_a_outer :=
    haΦ_cont_full.mono hslab_aug_sub
  have h_aΦ_pair_cont : ContinuousOn
      (fun q : (E × (E →L[ℝ] E)) × ℝ => (q.2, aΦ q)) Slab_a_outer :=
    ContinuousOn.prodMk continuous_snd.continuousOn haΦ_cont
  have h_fderiv_along_cont : ContinuousOn
      (fun q : (E × (E →L[ℝ] E)) × ℝ => fderiv ℝ (augVF f q.2) (aΦ q))
      Slab_a_outer := by
    have hmaps : MapsTo (fun q : (E × (E →L[ℝ] E)) × ℝ => (q.2, aΦ q))
        Slab_a_outer (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := fun _ _ => mem_univ _
    exact hpartial_a_cont.comp h_aΦ_pair_cont hmaps
  have h_norm_cont_aug : ContinuousOn
      (fun q : (E × (E →L[ℝ] E)) × ℝ => ‖fderiv ℝ (augVF f q.2) (aΦ q)‖)
      Slab_a_outer := by
    exact
      (continuous_norm
          (E := (E × (E →L[ℝ] E)) →L[ℝ] (E × (E →L[ℝ] E)))).comp_continuousOn
        h_fderiv_along_cont
  rcases hSlab_a_outer_cpt.exists_isMaxOn hSlab_a_outer_ne h_norm_cont_aug
    with ⟨qmax_a, _, hqmax_a⟩
  set M_aug_pre : ℝ := ‖fderiv ℝ (augVF f qmax_a.2) (aΦ qmax_a)‖ with hM_aug_pre_def
  have hM_aug_pre_nn : 0 ≤ M_aug_pre := by
    rw [hM_aug_pre_def]
    exact ContinuousLinearMap.opNorm_nonneg _
  have hM_aug_pre_bd : ∀ q ∈ Slab_a_outer, ‖fderiv ℝ (augVF f q.2) (aΦ q)‖ ≤ M_aug_pre :=
    fun q hq => hqmax_a hq
  set M_aug : ℝ := M_aug_pre + 1 with hM_aug_def
  have hM_aug_nn : 0 ≤ M_aug := by rw [hM_aug_def]; linarith
  have hM_aug_pos : 0 < M_aug := by rw [hM_aug_def]; linarith
  -- ## Phase 5: extract R_image bound for aΦ-image on Slab_a_outer (orbit-containment).
  have h_aΦ_norm_cont : ContinuousOn (fun q : (E × (E →L[ℝ] E)) × ℝ => ‖(aΦ q).1 - x₀‖)
      Slab_a_outer := by
    have h_fst_cont : ContinuousOn (fun q : (E × (E →L[ℝ] E)) × ℝ => (aΦ q).1) Slab_a_outer :=
      continuous_fst.continuousOn.comp haΦ_cont (fun _ _ => mem_univ _)
    have h_sub_cont : ContinuousOn (fun q : (E × (E →L[ℝ] E)) × ℝ => (aΦ q).1 - x₀)
        Slab_a_outer := h_fst_cont.sub continuousOn_const
    exact continuous_norm.comp_continuousOn h_sub_cont
  rcases hSlab_a_outer_cpt.exists_isMaxOn hSlab_a_outer_ne h_aΦ_norm_cont
    with ⟨qmax_R, _, hqmax_R⟩
  set R_aΦ_image_pre : ℝ := ‖(aΦ qmax_R).1 - x₀‖ with hR_aΦ_image_pre_def
  have hR_aΦ_image_pre_nn : 0 ≤ R_aΦ_image_pre := norm_nonneg _
  have hR_aΦ_image_pre_bd : ∀ q ∈ Slab_a_outer, ‖(aΦ q).1 - x₀‖ ≤ R_aΦ_image_pre :=
    fun q hq => hqmax_R hq
  -- ## Phase 6: extract R_Φ_image bound for Φ-image on closedBall x₀ ρ_outer × Icc.
  set Slab_Φ_outer : Set (E × ℝ) :=
    closedBall x₀ ρ_outer ×ˢ Icc (t₀ - T_outer) (t₀ + T_outer) with hSlab_Φ_outer_def
  have hSlab_Φ_outer_cpt : IsCompact Slab_Φ_outer :=
    (isCompact_closedBall x₀ ρ_outer).prod isCompact_Icc
  have hSlab_Φ_outer_ne : Slab_Φ_outer.Nonempty :=
    ⟨(x₀, t₀), Metric.mem_closedBall_self (le_of_lt hρ_outer_pos),
      ⟨by linarith, by linarith⟩⟩
  have hSlab_Φ_outer_sub_orig : Slab_Φ_outer ⊆ closedBall x₀ (r : ℝ) ×ˢ Icc tmin tmax := by
    refine Set.prod_mono ?_ ?_
    · exact closedBall_subset_closedBall hρ_outer_le_r
    · exact hsub_outer_orig
  have hΦ_cont_slab : ContinuousOn Φ Slab_Φ_outer := hΦ.continuousOn.mono hSlab_Φ_outer_sub_orig
  have h_Φ_norm_cont : ContinuousOn (fun p : E × ℝ => ‖Φ p - x₀‖) Slab_Φ_outer := by
    have h_sub_cont : ContinuousOn (fun p : E × ℝ => Φ p - x₀) Slab_Φ_outer :=
      hΦ_cont_slab.sub continuousOn_const
    exact continuous_norm.comp_continuousOn h_sub_cont
  rcases hSlab_Φ_outer_cpt.exists_isMaxOn hSlab_Φ_outer_ne h_Φ_norm_cont
    with ⟨pmax_R, _, hpmax_R⟩
  set R_Φ_image_pre : ℝ := ‖Φ pmax_R - x₀‖ with hR_Φ_image_pre_def
  have hR_Φ_image_pre_nn : 0 ≤ R_Φ_image_pre := norm_nonneg _
  have hR_Φ_image_pre_bd : ∀ p ∈ Slab_Φ_outer, ‖Φ p - x₀‖ ≤ R_Φ_image_pre :=
    fun p hp => hpmax_R hp
  -- ## Phase 7: pick the unified Lipschitz ball radius `r₀_lip` and extract K_orig.
  set r₀_lip : ℝ := max R_aΦ_image_pre R_Φ_image_pre + 1 with hr₀_lip_def
  have hr₀_lip_pos : 0 < r₀_lip := by
    rw [hr₀_lip_def]
    have : 0 ≤ max R_aΦ_image_pre R_Φ_image_pre :=
      le_max_of_le_left hR_aΦ_image_pre_nn
    linarith
  have hr₀_lip_ge_aΦ : R_aΦ_image_pre ≤ r₀_lip := by
    rw [hr₀_lip_def]
    have : R_aΦ_image_pre ≤ max R_aΦ_image_pre R_Φ_image_pre := le_max_left _ _
    linarith
  have hr₀_lip_ge_Φ : R_Φ_image_pre ≤ r₀_lip := by
    rw [hr₀_lip_def]
    have : R_Φ_image_pre ≤ max R_aΦ_image_pre R_Φ_image_pre := le_max_right _ _
    linarith
  -- Slab_f: Icc(t₀-T_outer, t₀+T_outer) × closedBall x₀ r₀_lip (compact in finite dim).
  set Slab_f : Set (ℝ × E) :=
    Icc (t₀ - T_outer) (t₀ + T_outer) ×ˢ closedBall x₀ r₀_lip with hSlab_f_def
  have hSlab_f_cpt : IsCompact Slab_f :=
    isCompact_Icc.prod (isCompact_closedBall x₀ r₀_lip)
  have hSlab_f_ne : Slab_f.Nonempty :=
    ⟨(t₀, x₀), ⟨by linarith, by linarith⟩, Metric.mem_closedBall_self (le_of_lt hr₀_lip_pos)⟩
  -- `fderiv ℝ (f τ) z` is continuous on Slab_f.
  have hpartial_f : ContDiffOn ℝ 0 (fun p : ℝ × E => fderiv ℝ (f p.1) p.2)
      (Set.univ : Set (ℝ × E)) :=
    contDiffOn_partial_fderiv_of_succ (f := f) (k := (0 : ℕ∞))
      (by simpa using hf_C1)
  have hpartial_f_cont : ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) Slab_f :=
    hpartial_f.continuousOn.mono (subset_univ _)
  have hpartial_f_norm_cont : ContinuousOn (fun p : ℝ × E => ‖fderiv ℝ (f p.1) p.2‖) Slab_f :=
    continuous_norm.comp_continuousOn hpartial_f_cont
  rcases hSlab_f_cpt.exists_isMaxOn hSlab_f_ne hpartial_f_norm_cont
    with ⟨pmax_K, _, hpmax_K⟩
  set K_pre : ℝ := ‖fderiv ℝ (f pmax_K.1) pmax_K.2‖ with hK_pre_def
  have hK_pre_nn : 0 ≤ K_pre := norm_nonneg _
  have hK_pre_bd : ∀ p ∈ Slab_f, ‖fderiv ℝ (f p.1) p.2‖ ≤ K_pre := fun p hp => hpmax_K hp
  set K_orig : ℝ := K_pre + 1 with hK_orig_def
  have hK_orig_pos : 0 < K_orig := by rw [hK_orig_def]; linarith
  have hK_orig_nn : 0 ≤ K_orig := le_of_lt hK_orig_pos
  set K_origN : ℝ≥0 := ⟨K_orig, hK_orig_nn⟩ with hK_origN_def
  have hK_origN_eq : (K_origN : ℝ) = K_orig := rfl
  -- ## Phase 8: pick T_mid for orbit-equality: K_orig · T_mid < 1 and T_mid < T_outer.
  set T_mid : ℝ := min (T_outer * 3 / 4) (1 / (2 * K_orig)) with hT_mid_def
  have hT_mid_pos : 0 < T_mid := by
    refine lt_min ?_ ?_
    · positivity
    · have : 0 < 2 * K_orig := by linarith
      positivity
  have hT_mid_lt_outer : T_mid < T_outer := by
    have h1 : T_mid ≤ T_outer * 3 / 4 := min_le_left _ _
    linarith
  have hKT_mid : K_orig * T_mid < 1 := by
    have h1 : T_mid ≤ 1 / (2 * K_orig) := min_le_right _ _
    have h2 : K_orig * T_mid ≤ K_orig * (1 / (2 * K_orig)) :=
      mul_le_mul_of_nonneg_left h1 hK_orig_nn
    have h3 : K_orig * (1 / (2 * K_orig)) = 1 / 2 := by field_simp
    linarith
  -- Also: M_aug · T_mid'_a < 1 with T_mid'_a from augmented system: same pattern.
  set T_a_mid : ℝ := min (T_outer * 3 / 4) (1 / (2 * M_aug)) with hT_a_mid_def
  have hT_a_mid_pos : 0 < T_a_mid := by
    refine lt_min ?_ ?_
    · positivity
    · have : 0 < 2 * M_aug := by linarith
      positivity
  have hT_a_mid_lt_outer : T_a_mid < T_outer := by
    have h1 : T_a_mid ≤ T_outer * 3 / 4 := min_le_left _ _
    linarith
  have hMTa_mid : M_aug * T_a_mid < 1 := by
    have h1 : T_a_mid ≤ 1 / (2 * M_aug) := min_le_right _ _
    have h2 : M_aug * T_a_mid ≤ M_aug * (1 / (2 * M_aug)) :=
      mul_le_mul_of_nonneg_left h1 hM_aug_nn
    have h3 : M_aug * (1 / (2 * M_aug)) = 1 / 2 := by field_simp
    linarith
  -- ## Phase 9: pick T_final < min(T_mid, T_a_mid) and ρ_final < min(ρ_outer, R_aug_out)/4.
  set T_final : ℝ := min T_mid T_a_mid / 2 with hT_final_def
  have hT_final_pos : 0 < T_final := by
    rw [hT_final_def]
    refine div_pos (lt_min hT_mid_pos hT_a_mid_pos) (by norm_num)
  have hT_final_lt_mid : T_final < T_mid := by
    rw [hT_final_def]
    have : min T_mid T_a_mid ≤ T_mid := min_le_left _ _
    linarith
  have hT_final_lt_a_mid : T_final < T_a_mid := by
    rw [hT_final_def]
    have : min T_mid T_a_mid ≤ T_a_mid := min_le_right _ _
    linarith
  -- ρ_final: must be ≤ ρ_outer (for closedBall x₀ ρ_final ⊆ closedBall x₀ ρ_outer ⊆ closedBall x₀ r),
  -- ≤ R_aug_out (for embedding into augmented ball), and ≤ ρ_outer · 1/4 (with `hr' := ρ_outer/2`).
  set ρ_final : ℝ := min ρ_outer R_aug_out / 8 with hρ_final_def
  have hρ_final_pos : 0 < ρ_final := by
    rw [hρ_final_def]
    refine div_pos (lt_min hρ_outer_pos hR_aug_out_pos) (by norm_num)
  have hρ_final_le_outer_8 : ρ_final ≤ ρ_outer / 8 := by
    rw [hρ_final_def]
    have : min ρ_outer R_aug_out ≤ ρ_outer := min_le_left _ _
    linarith
  have hρ_final_le_outer : ρ_final ≤ ρ_outer := by linarith
  have hρ_final_le_R_aug_out_8 : ρ_final ≤ R_aug_out / 8 := by
    rw [hρ_final_def]
    have : min ρ_outer R_aug_out ≤ R_aug_out := min_le_right _ _
    linarith
  have hρ_final_le_R_aug_out : ρ_final ≤ R_aug_out := by linarith
  set ρ_finalN : ℝ≥0 := ⟨ρ_final, le_of_lt hρ_final_pos⟩ with hρ_finalN_def
  have hρ_finalN_eq : (ρ_finalN : ℝ) = ρ_final := rfl
  -- ## Phase 10: smoothness of Y on (ball x₀ ρ_final) × Ioo(t₀-T_final, t₀+T_final).
  -- Use the EXISTING nested-3-layer pattern to get aΦ smoothness, then inherit to Y.
  -- For the nesting: R_a_outN := R_aug_outN; R_a_midN := R_aug_out * 3/4; R_aN := R_aug_out * 1/2.
  set R_a_mid : ℝ := R_aug_out * 3 / 4 with hR_a_mid_def
  have hR_a_mid_pos : 0 < R_a_mid := by rw [hR_a_mid_def]; positivity
  have hR_a_mid_lt_out : R_a_mid < R_aug_out := by rw [hR_a_mid_def]; linarith
  set R_a : ℝ := R_aug_out / 2 with hR_a_def
  have hR_a_pos2 : 0 < R_a := by rw [hR_a_def]; linarith
  have hR_a_lt_mid : R_a < R_a_mid := by
    rw [hR_a_def, hR_a_mid_def]; linarith
  set R_aN : ℝ≥0 := ⟨R_a, le_of_lt hR_a_pos2⟩
  set R_a_midN : ℝ≥0 := ⟨R_a_mid, le_of_lt hR_a_mid_pos⟩
  set R_a_outN : ℝ≥0 := ⟨R_aug_out, le_of_lt hR_aug_out_pos⟩
  set r'a : ℝ≥0 := ⟨R_aug / 8, by positivity⟩
  have hr'a_pos : (0 : ℝ) < (r'a : ℝ) := by
    change 0 < (R_aug : ℝ) / 8
    linarith
  have hR_aN_eq : (R_aN : ℝ) = R_a := rfl
  have hR_a_midN_eq : (R_a_midN : ℝ) = R_a_mid := rfl
  have hR_a_outN_eq : (R_a_outN : ℝ) = R_aug_out := rfl
  have hρρ_aux : (R_a_midN : ℝ) + (r'a : ℝ) ≤ (R_aug : ℝ) := by
    rw [hR_a_midN_eq, hR_a_mid_def, hR_aug_out_def]
    change R_aug_out * 3 / 4 + (R_aug : ℝ) / 8 ≤ (R_aug : ℝ)
    rw [hR_aug_out_def]
    linarith
  have hR_a_out_le_R_aug : (R_a_outN : ℝ) ≤ (R_aug : ℝ) := by
    rw [hR_a_outN_eq, hR_aug_out_def]; linarith
  -- For augmented Phase-9 inner: T_a_inner from contDiffOn_flow lemma's slab.  We use T_a_mid
  -- (already nested) and pick T_a_inner < T_a_mid.  We unify with T_final by using T_final ≤ T_a_mid/2.
  -- Actually contDiffOn_flow_of_isLocalFlow_of_contDiff has its own three-layer; pass T_outer, T_a_mid, T_final.
  have hA_bd_a : ∀ p ∈ closedBall p₀ (R_a_outN : ℝ),
      ∀ τ ∈ Icc (t₀ - T_outer) (t₀ + T_outer),
        ‖fderiv ℝ (augVF f τ) (aΦ ⟨p, τ⟩)‖ ≤ M_aug := by
    intro p hp τ hτ
    have hq_in : ((p, τ) : (E × (E →L[ℝ] E)) × ℝ) ∈ Slab_a_outer := by
      refine ⟨?_, hτ⟩
      rw [hR_a_outN_eq] at hp
      exact hp
    have h_pre : ‖fderiv ℝ (augVF f τ) (aΦ ⟨p, τ⟩)‖ ≤ M_aug_pre := hM_aug_pre_bd _ hq_in
    linarith
  have h_aug_C1 : ContDiffOn ℝ 1 aΦ ((ball p₀ (R_aN : ℝ))
      ×ˢ Ioo (t₀ - T_final) (t₀ + T_final)) := by
    have hk_aug : (1 : ℕ∞) ≤ 1 := le_refl _
    refine contDiffOn_flow_of_isLocalFlow_of_contDiff (f := augVF f)
      (t₀ := t₀) (x₀ := p₀) (r := R_aug) (tmin := t₀ - ε_aug) (tmax := t₀ + ε_aug)
      (Φ := aΦ) haΦ hk_aug h_augVF_C1
      hT_final_pos hT_final_lt_a_mid hT_a_mid_lt_outer hM_aug_nn hMTa_mid hsub_outer_aug
      (ρ_out := R_a_outN) (ρ_mid := R_a_midN) (ρ := R_aN) hr'a_pos
      ?_ ?_ ?_ ?_ hA_bd_a
    · rw [hR_aN_eq, hR_a_midN_eq]; linarith
    · rw [hR_a_midN_eq, hR_a_outN_eq]; linarith
    · exact hρρ_aux
    · exact hR_a_out_le_R_aug
  -- Inherit smoothness to Y := fromAugFlow aΦ on (ball x₀ ρ_final) × Ioo.
  -- Need ρ_finalN ≤ R_aN.
  have hρ_finalN_le_R_aN : (ρ_finalN : ℝ) ≤ (R_aN : ℝ) := by
    rw [hρ_finalN_eq, hR_aN_eq, hR_a_def]
    -- ρ_final ≤ R_aug_out / 8 ≤ R_aug_out / 2 = R_a
    have h1 : ρ_final ≤ R_aug_out / 8 := hρ_final_le_R_aug_out_8
    linarith
  have h_Y_smooth : ContDiffOn ℝ 1 (fromAugFlow aΦ)
      ((ball x₀ (ρ_finalN : ℝ)) ×ˢ Ioo (t₀ - T_final) (t₀ + T_final)) :=
    contDiffOn_fromAugFlow_inherits (ρ_a := R_aN) (ρ := ρ_finalN) (T_a := T_final) (T := T_final)
      hρ_finalN_le_R_aN (le_refl _) h_aug_C1
  -- ## Phase 11: invoke the coproduct-identity helper and intersect its neighbourhood with
  -- the smoothness neighbourhood from Phase 10.
  have ht₀_a_Ioo : t₀ ∈ Ioo (t₀ - ε_aug) (t₀ + ε_aug) :=
    ⟨by linarith, by linarith⟩
  obtain ⟨T_help, ρ_help, hT_help_pos, hρ_help_pos, h_help⟩ :=
    fderiv_Phi_eq_coprod_fromAugFlow_aux (Φ := Φ) hΦ hf_C1 ht₀_Ioo hr_pos haΦ ht₀_a_Ioo hR_aug_R
  -- The effective time width / spatial radius for the level-1 witness: the min of
  -- Phase 10's smoothness widths and the helper's coproduct widths.
  set T_eff : ℝ := min T_final T_help with hT_eff_def
  have hT_eff_pos : 0 < T_eff := lt_min hT_final_pos hT_help_pos
  have hT_eff_le_final : T_eff ≤ T_final := min_le_left _ _
  have hT_eff_le_help : T_eff ≤ T_help := min_le_right _ _
  set ρ_eff : ℝ := min (ρ_finalN : ℝ) (ρ_help : ℝ) with hρ_eff_def
  have hρ_eff_pos : 0 < ρ_eff := lt_min hρ_final_pos hρ_help_pos
  set ρ_effN : ℝ≥0 := ⟨ρ_eff, le_of_lt hρ_eff_pos⟩
  have hρ_effN_eq : (ρ_effN : ℝ) = ρ_eff := rfl
  have hρ_eff_le_finalN : ρ_eff ≤ (ρ_finalN : ℝ) := min_le_left _ _
  have hρ_eff_le_help : ρ_eff ≤ (ρ_help : ℝ) := min_le_right _ _
  have hρ_effN_le_finalN : (ρ_effN : ℝ) ≤ (ρ_finalN : ℝ) := by
    rw [hρ_effN_eq]; exact hρ_eff_le_finalN
  have hρ_effN_le_help : (ρ_effN : ℝ) ≤ (ρ_help : ℝ) := by
    rw [hρ_effN_eq]; exact hρ_eff_le_help
  -- Containment of the effective neighbourhood in Phase 10's smoothness neighbourhood.
  have h_eff_sub_smooth : (ball x₀ (ρ_effN : ℝ)) ×ˢ Ioo (t₀ - T_eff) (t₀ + T_eff)
      ⊆ (ball x₀ (ρ_finalN : ℝ)) ×ˢ Ioo (t₀ - T_final) (t₀ + T_final) := by
    refine Set.prod_mono ?_ ?_
    · intro y hy
      rw [mem_ball] at hy ⊢
      exact lt_of_lt_of_le hy hρ_effN_le_finalN
    · intro s hs
      rcases hs with ⟨h1, h2⟩
      refine ⟨?_, ?_⟩ <;> linarith
  -- Containment of the effective neighbourhood in the helper's coproduct neighbourhood.
  have h_eff_sub_help : (ball x₀ (ρ_effN : ℝ)) ×ˢ Ioo (t₀ - T_eff) (t₀ + T_eff)
      ⊆ (ball x₀ (ρ_help : ℝ)) ×ˢ Ioo (t₀ - T_help) (t₀ + T_help) := by
    refine Set.prod_mono ?_ ?_
    · intro y hy
      rw [mem_ball] at hy ⊢
      exact lt_of_lt_of_le hy hρ_effN_le_help
    · intro s hs
      rcases hs with ⟨h1, h2⟩
      refine ⟨?_, ?_⟩ <;> linarith
  -- Final assembly: produce the witness with the effective `T_eff` and `ρ_effN`.
  refine ⟨T_eff, ρ_effN, hT_eff_pos, hρ_eff_pos, fromAugFlow aΦ, ?_⟩
  refine { contDiffOn := h_Y_smooth.mono h_eff_sub_smooth, fderiv_eq := ?_ }
  intro q hq
  exact h_help q (h_eff_sub_help hq)

end LevelOneFullWitness

/-! ## Inductive successor step for the variational-flow projection witness

Given a variational-flow projection witness at level `n` for the *augmented* local
flow `aΦ` of `augVF f`, build a witness at level `n+1` for the original local flow
`Φ` of `f`.  The smoothness clause is upgraded using `contDiffOn_flow_of_isVariationalFlowProjection_top`
applied to `aΦ` (giving `ContDiffOn (n+1) aΦ`), and the projection `fromAugFlow aΦ`
inherits this regularity via `contDiffOn_fromAugFlow`.  The coproduct-identity clause
is supplied by `fderiv_Phi_eq_coprod_fromAugFlow_aux`, which depends only on
continuity of `aΦ` and joint `C^1` of `f`.  The two open neighbourhoods are
intersected to a common one carrying both clauses. -/

section SuccStepWitness

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

set_option maxHeartbeats 16000000 in
/-- **Inductive successor step for the variational-flow projection witness.**

If `f : ℝ → E → E` is jointly `C^{n+2}` on `Set.univ`, `Φ` is a local Picard–Lindelöf
flow of `f` centred at `(x₀, t₀)` with `t₀ ∈ Ioo tmin tmax`, `aΦ` is a local
Picard–Lindelöf flow of the augmented field `augVF f` centred at `((x₀, id), t₀)`
with `t₀ ∈ Ioo tmin_a tmax_a`, and a level-`n` variational-flow projection
witness `Y_ih` for `aΦ` is available, then there exist positive `T` and `ρ` together
with a function `Y : E × ℝ → (E →L[ℝ] E)` that is a level-`(n+1)` variational-flow
projection witness for `Φ` on the strictly-interior open neighbourhood
`ball x₀ ρ × Ioo (t₀ - T) (t₀ + T)`.

The output function `Y` is `fromAugFlow aΦ`.

The inductive hypothesis `hY_ih` packages the level-`n` regularity of the projection of
`aΦ` itself (one level *down*): `Y_ih` is `ContDiffOn n` on `ball ((x₀, id)) ρ_ih × Ioo`,
which combined with `aΦ`'s own variational identity bumps `aΦ`'s regularity to
`ContDiffOn (n+1)` on that neighbourhood; the projection `fromAugFlow aΦ` then inherits
joint `C^{n+1}` regularity.  This is the natural shape of an inductive step on
`IsVariationalFlowProjection`: the conclusion is at level `n+1` while the hypothesis
is at level `n`, so it is *not* hypothesis-packaging. -/
theorem exists_isVariationalFlowProjection_succ_C_step
    [FiniteDimensional ℝ E]
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (ht₀_Ioo : t₀ ∈ Ioo tmin tmax)
    (hr_pos : (0 : ℝ) < (r : ℝ))
    (n : ℕ)
    (hf_C : ContDiffOn ℝ ((n : ℕ∞) + 2) (uncurry f) (Set.univ : Set (ℝ × E)))
    {R_aug : ℝ≥0} {tmin_a tmax_a : ℝ}
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    (haΦ : IsLocalFlow (augVF f) t₀ (x₀, ContinuousLinearMap.id ℝ E) R_aug
      tmin_a tmax_a aΦ)
    (ht₀_a_Ioo : t₀ ∈ Ioo tmin_a tmax_a)
    (hR_aug_pos : (0 : ℝ) < (R_aug : ℝ))
    {T_ih : ℝ} {ρ_ih : ℝ≥0}
    {Y_ih : (E × (E →L[ℝ] E)) × ℝ → ((E × (E →L[ℝ] E)) →L[ℝ] (E × (E →L[ℝ] E)))}
    (_hT_ih_pos : 0 < T_ih) (_hρ_ih_pos : 0 < (ρ_ih : ℝ))
    (hY_ih : IsVariationalFlowProjection haΦ T_ih ρ_ih Y_ih (n : ℕ∞)) :
    ∃ (T : ℝ) (ρ : ℝ≥0) (_hT : 0 < T) (_hρ : 0 < (ρ : ℝ))
      (Y : E × ℝ → (E →L[ℝ] E)),
      IsVariationalFlowProjection hΦ T ρ Y ((n : ℕ∞) + 1) := by
  classical
  -- ## Phase 1: regularity bookkeeping for `f` and `augVF f`.
  set p₀ : E × (E →L[ℝ] E) := (x₀, ContinuousLinearMap.id ℝ E) with hp₀_def
  have hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)) := by
    refine hf_C.of_le ?_
    have h1 : (1 : WithTop ℕ∞) ≤ ((n : ℕ∞) : WithTop ℕ∞) + 2 := by
      have h2 : (1 : WithTop ℕ∞) ≤ 2 := by decide
      have h3 : (2 : WithTop ℕ∞) ≤ ((n : ℕ∞) : WithTop ℕ∞) + 2 := le_add_self
      exact le_trans h2 h3
    exact h1
  -- `uncurry (augVF f)` is `C^{n+1}`, since `uncurry f` is `C^{n+2} = (n+1)+1`.
  have hf_Cn_plus_2_as_succ : ContDiffOn ℝ (((n : ℕ∞) + 1) + 1) (uncurry f)
      (Set.univ : Set (ℝ × E)) := by
    have h_eq_wt :
        ((((n : ℕ∞) : WithTop ℕ∞) + 1) + 1 : WithTop ℕ∞) =
        (((n : ℕ∞) : WithTop ℕ∞) + 2 : WithTop ℕ∞) := by
      have h2 : ((2 : WithTop ℕ∞) = 1 + 1) := by decide
      rw [h2, ← add_assoc]
    rw [h_eq_wt]
    exact hf_C
  have h_augVF_Cn_plus_1 : ContDiffOn ℝ ((n : ℕ∞) + 1) (uncurry (augVF f))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    augVF_uncurry_contDiff (k := ((n : ℕ∞) + 1)) hf_Cn_plus_2_as_succ
  -- ## Phase 2: shrink the IH open set to a strictly-interior neighbourhood of `t₀`
  -- that fits inside both `Icc tmin_a tmax_a` and `closedBall p₀ R_aug` (after we
  -- pick the augmented three-layer nesting).  Concretely we will pick T_inner, ρ_inner
  -- with `T_inner ≤ T_ih`, `ρ_inner ≤ ρ_ih`, strictly less than time / spatial outer
  -- bounds for the augmented flow.
  -- First: outer time width for `augVF f` that fits inside `Icc tmin_a tmax_a`.
  have ht₀_minus_tmin_a : 0 < t₀ - tmin_a := by linarith [ht₀_a_Ioo.1]
  have htmax_a_minus_t₀ : 0 < tmax_a - t₀ := by linarith [ht₀_a_Ioo.2]
  set T_a_out : ℝ := min (t₀ - tmin_a) (tmax_a - t₀) / 2 with hT_a_out_def
  have hT_a_out_pos : 0 < T_a_out := by
    rw [hT_a_out_def]; refine div_pos (lt_min ht₀_minus_tmin_a htmax_a_minus_t₀) (by norm_num)
  have hT_a_out_le_tmin_a_half : T_a_out ≤ (t₀ - tmin_a) / 2 := by
    rw [hT_a_out_def]
    have : min (t₀ - tmin_a) (tmax_a - t₀) ≤ t₀ - tmin_a := min_le_left _ _
    linarith
  have hT_a_out_le_tmax_a_half : T_a_out ≤ (tmax_a - t₀) / 2 := by
    rw [hT_a_out_def]
    have : min (t₀ - tmin_a) (tmax_a - t₀) ≤ tmax_a - t₀ := min_le_right _ _
    linarith
  have hsub_T_a_out_aug : Icc (t₀ - T_a_out) (t₀ + T_a_out) ⊆ Icc tmin_a tmax_a :=
    Icc_subset_Icc (by linarith) (by linarith)
  -- Outer spatial radius for the augmented flow.
  set R_a_out : ℝ := (R_aug : ℝ) / 2 with hR_a_out_def
  have hR_a_out_pos : 0 < R_a_out := by rw [hR_a_out_def]; linarith
  have hR_a_out_lt : R_a_out < (R_aug : ℝ) := by rw [hR_a_out_def]; linarith
  -- Mid spatial radius.
  set R_a_mid : ℝ := R_a_out * 3 / 4 with hR_a_mid_def
  have hR_a_mid_pos : 0 < R_a_mid := by rw [hR_a_mid_def]; positivity
  have hR_a_mid_lt_out : R_a_mid < R_a_out := by rw [hR_a_mid_def]; linarith
  -- Inner spatial radius `R_a`: chosen `≤ ρ_ih` so the IH covers it, and `< R_a_mid`.
  set R_a : ℝ := min R_a_mid (ρ_ih : ℝ) / 2 with hR_a_def
  have hR_a_pos : 0 < R_a := by
    rw [hR_a_def]; refine div_pos (lt_min hR_a_mid_pos _hρ_ih_pos) (by norm_num)
  have hR_a_lt_mid : R_a < R_a_mid := by
    rw [hR_a_def]
    have : min R_a_mid (ρ_ih : ℝ) ≤ R_a_mid := min_le_left _ _
    linarith
  have hR_a_le_ρ_ih : R_a ≤ (ρ_ih : ℝ) := by
    rw [hR_a_def]
    have : min R_a_mid (ρ_ih : ℝ) ≤ (ρ_ih : ℝ) := min_le_right _ _
    linarith
  set R_aN : ℝ≥0 := ⟨R_a, le_of_lt hR_a_pos⟩
  set R_a_midN : ℝ≥0 := ⟨R_a_mid, le_of_lt hR_a_mid_pos⟩
  set R_a_outN : ℝ≥0 := ⟨R_a_out, le_of_lt hR_a_out_pos⟩
  set r'a : ℝ≥0 := ⟨R_aug / 8, by positivity⟩
  have hr'a_pos : (0 : ℝ) < (r'a : ℝ) := by
    change 0 < (R_aug : ℝ) / 8; linarith
  have hR_aN_eq : (R_aN : ℝ) = R_a := rfl
  have hR_a_midN_eq : (R_a_midN : ℝ) = R_a_mid := rfl
  have hR_a_outN_eq : (R_a_outN : ℝ) = R_a_out := rfl
  have hρρ_aux : (R_a_midN : ℝ) + (r'a : ℝ) ≤ (R_aug : ℝ) := by
    rw [hR_a_midN_eq, hR_a_mid_def, hR_a_out_def]
    change (R_aug : ℝ) / 2 * 3 / 4 + (R_aug : ℝ) / 8 ≤ (R_aug : ℝ)
    linarith
  have hR_a_out_le_R_aug : (R_a_outN : ℝ) ≤ (R_aug : ℝ) := by
    rw [hR_a_outN_eq, hR_a_out_def]; linarith
  -- ## Phase 3: extract uniform operator-norm bound `M_aug` for `fderiv (augVF f τ) (aΦ ⟨p, τ⟩)`
  -- on the outer slab `closedBall p₀ R_a_out × Icc (t₀ - T_a_out) (t₀ + T_a_out)`.
  set Slab_a : Set ((E × (E →L[ℝ] E)) × ℝ) :=
    closedBall p₀ R_a_out ×ˢ Icc (t₀ - T_a_out) (t₀ + T_a_out)
  have hSlab_a_cpt : IsCompact Slab_a :=
    (isCompact_closedBall (p₀ : E × (E →L[ℝ] E)) R_a_out).prod isCompact_Icc
  have hSlab_a_ne : Slab_a.Nonempty :=
    ⟨(p₀, t₀), Metric.mem_closedBall_self (le_of_lt hR_a_out_pos),
      ⟨by linarith, by linarith⟩⟩
  have hslab_a_sub_full : Slab_a ⊆ closedBall p₀ (R_aug : ℝ) ×ˢ Icc tmin_a tmax_a := by
    refine Set.prod_mono ?_ ?_
    · exact closedBall_subset_closedBall (le_of_lt hR_a_out_lt)
    · exact hsub_T_a_out_aug
  have haΦ_cont : ContinuousOn aΦ Slab_a := haΦ.continuousOn.mono hslab_a_sub_full
  have hpartial_a : ContDiffOn ℝ 0 (fun p : ℝ × (E × (E →L[ℝ] E)) =>
      fderiv ℝ (augVF f p.1) p.2) (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by
    have h_augVF_C1 : ContDiffOn ℝ 1 (uncurry (augVF f))
        (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by
      refine h_augVF_Cn_plus_1.of_le ?_
      have h1 : (1 : ℕ∞) ≤ (n : ℕ∞) + 1 := le_add_self
      exact_mod_cast h1
    exact contDiffOn_partial_fderiv_of_succ (f := augVF f) (k := (0 : ℕ∞))
      (by simpa using h_augVF_C1)
  have hpartial_a_cont : ContinuousOn (fun p : ℝ × (E × (E →L[ℝ] E)) =>
      fderiv ℝ (augVF f p.1) p.2) (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    hpartial_a.continuousOn
  have h_pair_cont_a : ContinuousOn (fun q : (E × (E →L[ℝ] E)) × ℝ => (q.2, aΦ q)) Slab_a :=
    ContinuousOn.prodMk continuous_snd.continuousOn haΦ_cont
  have h_fderiv_a_cont : ContinuousOn
      (fun q : (E × (E →L[ℝ] E)) × ℝ => fderiv ℝ (augVF f q.2) (aΦ q)) Slab_a := by
    have hmaps : MapsTo (fun q : (E × (E →L[ℝ] E)) × ℝ => (q.2, aΦ q))
        Slab_a (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := fun _ _ => mem_univ _
    exact hpartial_a_cont.comp h_pair_cont_a hmaps
  have h_norm_cont_a : ContinuousOn
      (fun q : (E × (E →L[ℝ] E)) × ℝ => ‖fderiv ℝ (augVF f q.2) (aΦ q)‖) Slab_a :=
    by
      exact
        (continuous_norm
            (E := (E × (E →L[ℝ] E)) →L[ℝ] (E × (E →L[ℝ] E)))).comp_continuousOn
          h_fderiv_a_cont
  rcases hSlab_a_cpt.exists_isMaxOn hSlab_a_ne h_norm_cont_a with ⟨qmax, _, hqmax⟩
  set M_aug_pre : ℝ := ‖fderiv ℝ (augVF f qmax.2) (aΦ qmax)‖ with hM_aug_pre_def
  have hM_aug_pre_nn : 0 ≤ M_aug_pre := by
    rw [hM_aug_pre_def]
    exact ContinuousLinearMap.opNorm_nonneg _
  have hM_aug_pre_bd : ∀ q ∈ Slab_a, ‖fderiv ℝ (augVF f q.2) (aΦ q)‖ ≤ M_aug_pre :=
    fun q hq => hqmax hq
  set M_aug : ℝ := M_aug_pre + 1 with hM_aug_def
  have hM_aug_nn : 0 ≤ M_aug := by rw [hM_aug_def]; linarith
  have hM_aug_pos : 0 < M_aug := by rw [hM_aug_def]; linarith
  -- Pick `T_a_mid` strictly less than `T_a_out` with `M_aug · T_a_mid < 1`.
  set T_a_mid : ℝ := min (T_a_out * 3 / 4) (1 / (2 * M_aug)) with hT_a_mid_def
  have hT_a_mid_pos : 0 < T_a_mid := by
    refine lt_min ?_ ?_
    · positivity
    · have : 0 < 2 * M_aug := by linarith
      positivity
  have hT_a_mid_lt_out : T_a_mid < T_a_out := by
    have h1 : T_a_mid ≤ T_a_out * 3 / 4 := min_le_left _ _
    linarith
  have hMTa_mid : M_aug * T_a_mid < 1 := by
    have h1 : T_a_mid ≤ 1 / (2 * M_aug) := min_le_right _ _
    have h2 : M_aug * T_a_mid ≤ M_aug * (1 / (2 * M_aug)) :=
      mul_le_mul_of_nonneg_left h1 hM_aug_nn
    have h3 : M_aug * (1 / (2 * M_aug)) = 1 / 2 := by field_simp
    linarith
  -- Inner time `T_a := min(T_a_mid, T_ih) / 2`.
  set T_a : ℝ := min T_a_mid T_ih / 2 with hT_a_def
  have hT_a_pos : 0 < T_a := by
    rw [hT_a_def]; refine div_pos (lt_min hT_a_mid_pos _hT_ih_pos) (by norm_num)
  have hT_a_lt_mid : T_a < T_a_mid := by
    rw [hT_a_def]
    have : min T_a_mid T_ih ≤ T_a_mid := min_le_left _ _
    linarith
  have hT_a_le_T_ih : T_a ≤ T_ih := by
    rw [hT_a_def]
    have h1 : min T_a_mid T_ih ≤ T_ih := min_le_right _ _
    linarith
  -- Convert the bound `M_aug_pre` into the `hA_bd` shape required by the projection lemma.
  have hA_bd_a : ∀ p ∈ closedBall p₀ (R_a_outN : ℝ),
      ∀ τ ∈ Icc (t₀ - T_a_out) (t₀ + T_a_out),
        ‖fderiv ℝ (augVF f τ) (aΦ ⟨p, τ⟩)‖ ≤ M_aug := by
    intro p hp τ hτ
    have hq_in : ((p, τ) : (E × (E →L[ℝ] E)) × ℝ) ∈ Slab_a := by
      refine ⟨?_, hτ⟩
      rw [hR_a_outN_eq] at hp; exact hp
    have h_pre : ‖fderiv ℝ (augVF f τ) (aΦ ⟨p, τ⟩)‖ ≤ M_aug_pre := hM_aug_pre_bd _ hq_in
    linarith
  -- ## Phase 4: shrink the IH from `(T_ih, ρ_ih)` to `(T_a, R_aN)`.
  -- The shrunk IH lives on `ball p₀ R_aN × Ioo (t₀ - T_a) (t₀ + T_a)`.
  have hR_aN_le_ρ_ih : (R_aN : ℝ) ≤ (ρ_ih : ℝ) := by rw [hR_aN_eq]; exact hR_a_le_ρ_ih
  have h_shrink_sub : (ball p₀ (R_aN : ℝ)) ×ˢ Ioo (t₀ - T_a) (t₀ + T_a)
      ⊆ (ball p₀ (ρ_ih : ℝ)) ×ˢ Ioo (t₀ - T_ih) (t₀ + T_ih) := by
    refine Set.prod_mono ?_ ?_
    · intro y hy
      rw [mem_ball] at hy ⊢
      exact lt_of_lt_of_le hy hR_aN_le_ρ_ih
    · intro s hs
      rcases hs with ⟨h1, h2⟩
      refine ⟨?_, ?_⟩ <;> linarith
  have hY_ih_shrunk : IsVariationalFlowProjection haΦ T_a R_aN Y_ih (n : ℕ∞) := by
    refine
    { contDiffOn := hY_ih.contDiffOn.mono h_shrink_sub,
      fderiv_eq := fun q hq => hY_ih.fderiv_eq q (h_shrink_sub hq) }
  -- ## Phase 5: apply `contDiffOn_flow_of_isVariationalFlowProjection_top` to `aΦ` with
  -- k = n+1 and the shrunk IH at level n.  Conclusion: `aΦ` is `ContDiffOn (n+1)` on
  -- `ball p₀ R_aN × Ioo (t₀ - T_a) (t₀ + T_a)`.
  have hk_pos : (1 : ℕ) ≤ n + 1 := by omega
  have hk_minus_one : ((n + 1 - 1 : ℕ) : ℕ∞) = (n : ℕ∞) := by
    have : n + 1 - 1 = n := by omega
    rw [this]
  have hY_ih_at_top : IsVariationalFlowProjection haΦ T_a R_aN Y_ih
      ((n + 1 - 1 : ℕ) : ℕ∞) := by rw [hk_minus_one]; exact hY_ih_shrunk
  have h_aug_Cn_plus_1 : ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞) aΦ
      ((ball p₀ (R_aN : ℝ)) ×ˢ Ioo (t₀ - T_a) (t₀ + T_a)) := by
    refine contDiffOn_flow_of_isVariationalFlowProjection_top
      (f := augVF f) (t₀ := t₀) (x₀ := p₀) (r := R_aug) (tmin := tmin_a) (tmax := tmax_a)
      (Φ := aΦ) haΦ hT_a_pos hT_a_lt_mid hT_a_mid_lt_out hM_aug_nn hMTa_mid hsub_T_a_out_aug
      (ρ_out := R_a_outN) (ρ_mid := R_a_midN) (ρ := R_aN) hr'a_pos ?_ ?_ ?_ ?_ hA_bd_a
      (n + 1) hk_pos ?_ hY_ih_at_top
    · rw [hR_aN_eq, hR_a_midN_eq]; linarith
    · rw [hR_a_midN_eq, hR_a_outN_eq]; linarith
    · exact hρρ_aux
    · exact hR_a_out_le_R_aug
    · -- `uncurry (augVF f)` is `ContDiffOn ((n + 1 : ℕ) : ℕ∞)`.
      have h_eq_succ : (((n + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) =
          ((n : ℕ∞) : WithTop ℕ∞) + 1 := by push_cast; ring
      rw [h_eq_succ]
      exact h_augVF_Cn_plus_1
  -- Rewrite the level to the `(n : ℕ∞) + 1` shape.
  have h_aug_Cn_plus_1' : ContDiffOn ℝ ((n : ℕ∞) + 1) aΦ
      ((ball p₀ (R_aN : ℝ)) ×ˢ Ioo (t₀ - T_a) (t₀ + T_a)) := by
    have h_eq_succ : (((n + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) =
        ((n : ℕ∞) : WithTop ℕ∞) + 1 := by push_cast; ring
    rw [← h_eq_succ]
    exact h_aug_Cn_plus_1
  -- ## Phase 6: inherit smoothness to `Y := fromAugFlow aΦ` via `contDiffOn_fromAugFlow`.
  -- Embedding `(x, t) ↦ ((x, id), t)` maps `ball x₀ R_aN × Ioo` into `ball p₀ R_aN × Ioo`.
  set U_E : Set (E × ℝ) := ball x₀ (R_aN : ℝ) ×ˢ Ioo (t₀ - T_a) (t₀ + T_a) with hU_E_def
  set U_a : Set ((E × (E →L[ℝ] E)) × ℝ) :=
    ball p₀ (R_aN : ℝ) ×ˢ Ioo (t₀ - T_a) (t₀ + T_a) with hU_a_def
  have hmap : MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2)) U_E U_a := by
    intro q hq
    rcases hq with ⟨hq_x, hq_t⟩
    refine ⟨?_, hq_t⟩
    rw [mem_ball] at hq_x ⊢
    have hd : dist ((q.1, ContinuousLinearMap.id ℝ E) : E × (E →L[ℝ] E)) p₀
        = dist q.1 x₀ := by
      change max (dist q.1 x₀) (dist (ContinuousLinearMap.id ℝ E)
        (ContinuousLinearMap.id ℝ E)) = dist q.1 x₀
      rw [dist_self, max_eq_left dist_nonneg]
    rw [hd]; exact hq_x
  have h_Y_smooth : ContDiffOn ℝ ((n : ℕ∞) + 1) (fromAugFlow aΦ) U_E :=
    contDiffOn_fromAugFlow (k := ((n : ℕ∞) + 1)) (Ω := U_a) (U := U_E)
      h_aug_Cn_plus_1' hmap
  -- ## Phase 7: invoke the coproduct-identity helper and intersect the two neighbourhoods.
  obtain ⟨T_help, ρ_help, hT_help_pos, hρ_help_pos, h_help⟩ :=
    fderiv_Phi_eq_coprod_fromAugFlow_aux (Φ := Φ) hΦ hf_C1 ht₀_Ioo hr_pos haΦ ht₀_a_Ioo hR_aug_pos
  -- Effective time width / spatial radius.
  set T_eff : ℝ := min T_a T_help with hT_eff_def
  have hT_eff_pos : 0 < T_eff := lt_min hT_a_pos hT_help_pos
  have hT_eff_le_T_a : T_eff ≤ T_a := min_le_left _ _
  have hT_eff_le_T_help : T_eff ≤ T_help := min_le_right _ _
  set ρ_eff : ℝ := min (R_aN : ℝ) (ρ_help : ℝ) with hρ_eff_def
  have hρ_eff_pos : 0 < ρ_eff := lt_min hR_a_pos hρ_help_pos
  set ρ_effN : ℝ≥0 := ⟨ρ_eff, le_of_lt hρ_eff_pos⟩
  have hρ_effN_eq : (ρ_effN : ℝ) = ρ_eff := rfl
  have hρ_eff_le_R_a : ρ_eff ≤ (R_aN : ℝ) := min_le_left _ _
  have hρ_eff_le_help : ρ_eff ≤ (ρ_help : ℝ) := min_le_right _ _
  have hρ_effN_le_R_a : (ρ_effN : ℝ) ≤ (R_aN : ℝ) := by rw [hρ_effN_eq]; exact hρ_eff_le_R_a
  have hρ_effN_le_help : (ρ_effN : ℝ) ≤ (ρ_help : ℝ) := by rw [hρ_effN_eq]; exact hρ_eff_le_help
  -- Containment of the effective neighbourhood in the smoothness neighbourhood `U_E`.
  have h_eff_sub_smooth : (ball x₀ (ρ_effN : ℝ)) ×ˢ Ioo (t₀ - T_eff) (t₀ + T_eff) ⊆ U_E := by
    rw [hU_E_def]
    refine Set.prod_mono ?_ ?_
    · intro y hy
      rw [mem_ball] at hy ⊢
      exact lt_of_lt_of_le hy hρ_effN_le_R_a
    · intro s hs
      rcases hs with ⟨h1, h2⟩
      refine ⟨?_, ?_⟩ <;> linarith
  -- Containment of the effective neighbourhood in the helper's coproduct-identity neighbourhood.
  have h_eff_sub_help : (ball x₀ (ρ_effN : ℝ)) ×ˢ Ioo (t₀ - T_eff) (t₀ + T_eff)
      ⊆ (ball x₀ (ρ_help : ℝ)) ×ˢ Ioo (t₀ - T_help) (t₀ + T_help) := by
    refine Set.prod_mono ?_ ?_
    · intro y hy
      rw [mem_ball] at hy ⊢
      exact lt_of_lt_of_le hy hρ_effN_le_help
    · intro s hs
      rcases hs with ⟨h1, h2⟩
      refine ⟨?_, ?_⟩ <;> linarith
  -- ## Final assembly.
  refine ⟨T_eff, ρ_effN, hT_eff_pos, hρ_eff_pos, fromAugFlow aΦ, ?_⟩
  refine { contDiffOn := h_Y_smooth.mono h_eff_sub_smooth, fderiv_eq := ?_ }
  intro q hq
  exact h_help q (h_eff_sub_help hq)

end SuccStepWitness

/-! ## The level-0 variational-flow projection witness from joint `C^1` of `f`

At level `0`, the smoothness clause reduces to joint continuity of `Y` on the
open neighbourhood, and the augmented-flow construction is not required:
the spatial piece can be read off directly from the joint Fréchet derivative
of `Φ` via the inverse of `ContinuousLinearMap.coprodEquivL`, which is itself
a continuous linear map.  Joint continuity of `fderiv ℝ Φ` is then supplied by
`continuousOn_fderiv_flow_of_isLocalFlow`, and the coproduct identity for
`fderiv ℝ Φ` is supplied pointwise by `hasFDerivAt_flow_jointly_at`.

Both ingredients consume the same nested three-layer Lipschitz / Fréchet setup
on `(T_out, T_mid, T)` and `(ρ_out, ρ_mid, ρ)`, built by extracting a uniform
operator-norm bound on the spatial linearization `(τ, y) ↦ fderiv ℝ (f τ) y`
from finite-dimensional compactness of a closed-ball × closed-interval slab. -/

section LevelZeroFullWitness

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

set_option maxHeartbeats 8000000 in
/-- **Level-0 variational-flow projection witness.**

If `f : ℝ → E → E` is jointly `C^1` on `Set.univ`, `E` is a finite-dimensional
Banach space, `Φ` is a local Picard–Lindelöf flow centered at `(x₀, t₀)` with
`t₀` strictly inside its time domain, and the flow's spatial radius `r` is
positive, then there exist positive `T` and `ρ` together with a function
`Y : E × ℝ → (E →L[ℝ] E)` that is a level-`0` variational-flow projection of
`Φ` on the strictly-interior open neighbourhood
`(ball x₀ ρ) ×ˢ Ioo (t₀ - T) (t₀ + T)`.

The function `Y` is defined directly from `fderiv ℝ Φ` by inverting the
coproduct decomposition `(E →L[ℝ] E) × (ℝ →L[ℝ] E) ≃L[ℝ] (E × ℝ →L[ℝ] E)`
and extracting the spatial component.  Joint continuity of `Y` follows from
joint continuity of `fderiv ℝ Φ` and continuity of the inverse coproduct
equivalence; the coproduct identity for `fderiv ℝ Φ` is pinned by
`hasFDerivAt_flow_jointly_at`. -/
theorem exists_isVariationalFlowProjection_zero_of_C1
    [FiniteDimensional ℝ E]
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (ht₀_Ioo : t₀ ∈ Ioo tmin tmax)
    (hr_pos : (0 : ℝ) < (r : ℝ))
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E))) :
    ∃ (T : ℝ) (ρ : ℝ≥0) (_hT : 0 < T) (_hρ : 0 < (ρ : ℝ))
      (Y : E × ℝ → (E →L[ℝ] E)),
      IsVariationalFlowProjection hΦ T ρ Y (0 : ℕ∞) := by
  classical
  -- The coproduct equivalence and its components, used throughout.
  set CE : ((E →L[ℝ] E) × (ℝ →L[ℝ] E)) ≃L[ℝ] ((E × ℝ) →L[ℝ] E) :=
    ContinuousLinearMap.coprodEquivL (𝕜 := ℝ) (E := E) (F := ℝ) (G := E) ℝ
    with hCE_def
  -- Phase 1: outer time width `T_outer` with `Icc(t₀±T_outer) ⊆ Icc tmin tmax`.
  have ht₀_minus_tmin : 0 < t₀ - tmin := by linarith [ht₀_Ioo.1]
  have htmax_minus_t₀ : 0 < tmax - t₀ := by linarith [ht₀_Ioo.2]
  set T_outer : ℝ := min (t₀ - tmin) (tmax - t₀) / 2 with hT_outer_def
  have hT_outer_pos : 0 < T_outer := by
    rw [hT_outer_def]
    refine div_pos (lt_min ht₀_minus_tmin htmax_minus_t₀) (by norm_num)
  have hT_outer_le_tmin_half : T_outer ≤ (t₀ - tmin) / 2 := by
    rw [hT_outer_def]
    have h1 : min (t₀ - tmin) (tmax - t₀) ≤ t₀ - tmin := min_le_left _ _
    linarith
  have hT_outer_le_tmax_half : T_outer ≤ (tmax - t₀) / 2 := by
    rw [hT_outer_def]
    have h1 : min (t₀ - tmin) (tmax - t₀) ≤ tmax - t₀ := min_le_right _ _
    linarith
  have hsub_outer_orig : Icc (t₀ - T_outer) (t₀ + T_outer) ⊆ Icc tmin tmax :=
    Icc_subset_Icc (by linarith) (by linarith)
  -- Phase 2: outer spatial radius ρ_outer = r/2.
  set ρ_outer : ℝ := (r : ℝ) / 2 with hρ_outer_def
  have hρ_outer_pos : 0 < ρ_outer := by rw [hρ_outer_def]; linarith
  have hρ_outer_le_r : ρ_outer ≤ (r : ℝ) := by rw [hρ_outer_def]; linarith
  set ρ_outerN : ℝ≥0 := ⟨ρ_outer, le_of_lt hρ_outer_pos⟩ with hρ_outerN_def
  have hρ_outerN_eq : (ρ_outerN : ℝ) = ρ_outer := rfl
  -- Phase 3: Φ-image radius on the slab `closedBall x₀ ρ_outer ×ˢ Icc (t₀-T_outer) (t₀+T_outer)`.
  set Slab_Φ_outer : Set (E × ℝ) :=
    closedBall x₀ ρ_outer ×ˢ Icc (t₀ - T_outer) (t₀ + T_outer) with hSlab_Φ_outer_def
  have hSlab_Φ_outer_cpt : IsCompact Slab_Φ_outer :=
    (isCompact_closedBall x₀ ρ_outer).prod isCompact_Icc
  have hSlab_Φ_outer_ne : Slab_Φ_outer.Nonempty :=
    ⟨(x₀, t₀), Metric.mem_closedBall_self (le_of_lt hρ_outer_pos),
      ⟨by linarith, by linarith⟩⟩
  have hSlab_Φ_outer_sub_orig : Slab_Φ_outer ⊆ closedBall x₀ (r : ℝ) ×ˢ Icc tmin tmax := by
    refine Set.prod_mono ?_ ?_
    · exact closedBall_subset_closedBall hρ_outer_le_r
    · exact hsub_outer_orig
  have hΦ_cont_slab : ContinuousOn Φ Slab_Φ_outer :=
    hΦ.continuousOn.mono hSlab_Φ_outer_sub_orig
  have h_Φ_norm_cont : ContinuousOn (fun p : E × ℝ => ‖Φ p - x₀‖) Slab_Φ_outer := by
    have h_sub_cont : ContinuousOn (fun p : E × ℝ => Φ p - x₀) Slab_Φ_outer :=
      hΦ_cont_slab.sub continuousOn_const
    exact continuous_norm.comp_continuousOn h_sub_cont
  rcases hSlab_Φ_outer_cpt.exists_isMaxOn hSlab_Φ_outer_ne h_Φ_norm_cont
    with ⟨pmax_R, _, hpmax_R⟩
  set R_Φ_image_pre : ℝ := ‖Φ pmax_R - x₀‖ with hR_Φ_image_pre_def
  have hR_Φ_image_pre_nn : 0 ≤ R_Φ_image_pre := norm_nonneg _
  have hR_Φ_image_pre_bd : ∀ p ∈ Slab_Φ_outer, ‖Φ p - x₀‖ ≤ R_Φ_image_pre :=
    fun p hp => hpmax_R hp
  -- Phase 4: unified Lipschitz radius and Lipschitz constant for `f`.
  set r₀_lip : ℝ := R_Φ_image_pre + 1 with hr₀_lip_def
  have hr₀_lip_pos : 0 < r₀_lip := by rw [hr₀_lip_def]; linarith
  have hr₀_lip_ge_Φ : R_Φ_image_pre ≤ r₀_lip := by rw [hr₀_lip_def]; linarith
  set Slab_f : Set (ℝ × E) :=
    Icc (t₀ - T_outer) (t₀ + T_outer) ×ˢ closedBall x₀ r₀_lip with hSlab_f_def
  have hSlab_f_cpt : IsCompact Slab_f :=
    isCompact_Icc.prod (isCompact_closedBall x₀ r₀_lip)
  have hSlab_f_ne : Slab_f.Nonempty :=
    ⟨(t₀, x₀), ⟨by linarith, by linarith⟩, Metric.mem_closedBall_self (le_of_lt hr₀_lip_pos)⟩
  have hpartial_f : ContDiffOn ℝ 0 (fun p : ℝ × E => fderiv ℝ (f p.1) p.2)
      (Set.univ : Set (ℝ × E)) :=
    contDiffOn_partial_fderiv_of_succ (f := f) (k := (0 : ℕ∞))
      (by simpa using hf_C1)
  have hpartial_f_cont : ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) Slab_f :=
    hpartial_f.continuousOn.mono (subset_univ _)
  have hpartial_f_norm_cont : ContinuousOn (fun p : ℝ × E => ‖fderiv ℝ (f p.1) p.2‖) Slab_f :=
    continuous_norm.comp_continuousOn hpartial_f_cont
  rcases hSlab_f_cpt.exists_isMaxOn hSlab_f_ne hpartial_f_norm_cont
    with ⟨pmax_K, _, hpmax_K⟩
  set K_pre : ℝ := ‖fderiv ℝ (f pmax_K.1) pmax_K.2‖ with hK_pre_def
  have hK_pre_nn : 0 ≤ K_pre := norm_nonneg _
  have hK_pre_bd : ∀ p ∈ Slab_f, ‖fderiv ℝ (f p.1) p.2‖ ≤ K_pre := fun p hp => hpmax_K hp
  set K_orig : ℝ := K_pre + 1 with hK_orig_def
  have hK_orig_pos : 0 < K_orig := by rw [hK_orig_def]; linarith
  have hK_orig_nn : 0 ≤ K_orig := le_of_lt hK_orig_pos
  -- Phase 5: pick `T_mid < T_outer` with `K_orig · T_mid < 1`, and `T_final < T_mid`.
  set T_mid : ℝ := min (T_outer * 3 / 4) (1 / (2 * K_orig)) with hT_mid_def
  have hT_mid_pos : 0 < T_mid := by
    refine lt_min ?_ ?_
    · positivity
    · have : 0 < 2 * K_orig := by linarith
      positivity
  have hT_mid_lt_outer : T_mid < T_outer := by
    have h1 : T_mid ≤ T_outer * 3 / 4 := min_le_left _ _
    linarith
  have hKT_mid : K_orig * T_mid < 1 := by
    have h1 : T_mid ≤ 1 / (2 * K_orig) := min_le_right _ _
    have h2 : K_orig * T_mid ≤ K_orig * (1 / (2 * K_orig)) :=
      mul_le_mul_of_nonneg_left h1 hK_orig_nn
    have h3 : K_orig * (1 / (2 * K_orig)) = 1 / 2 := by field_simp
    linarith
  set T_final : ℝ := T_mid / 2 with hT_final_def
  have hT_final_pos : 0 < T_final := by rw [hT_final_def]; linarith
  have hT_final_lt_mid : T_final < T_mid := by rw [hT_final_def]; linarith
  -- Phase 6: nested spatial radii `ρ_mid_N`, `ρ_N`, slack `r'_N` for the Fréchet hypotheses.
  set ρ_mid : ℝ := ρ_outer * 3 / 4 with hρ_mid_def
  have hρ_mid_pos : 0 < ρ_mid := by rw [hρ_mid_def]; positivity
  have hρ_mid_lt_outer : ρ_mid < ρ_outer := by rw [hρ_mid_def]; linarith
  set ρ_inner : ℝ := ρ_outer / 2 with hρ_inner_def
  have hρ_inner_pos : 0 < ρ_inner := by rw [hρ_inner_def]; linarith
  have hρ_inner_lt_mid : ρ_inner < ρ_mid := by
    rw [hρ_inner_def, hρ_mid_def]; linarith
  set ρ_innerN : ℝ≥0 := ⟨ρ_inner, le_of_lt hρ_inner_pos⟩
  set ρ_midN : ℝ≥0 := ⟨ρ_mid, le_of_lt hρ_mid_pos⟩
  have hρ_innerN_eq : (ρ_innerN : ℝ) = ρ_inner := rfl
  have hρ_midN_eq : (ρ_midN : ℝ) = ρ_mid := rfl
  have hρ_outerN_le_r : (ρ_outerN : ℝ) ≤ (r : ℝ) := by
    rw [hρ_outerN_eq]; exact hρ_outer_le_r
  have hρ_innerN_lt_midN : (ρ_innerN : ℝ) < (ρ_midN : ℝ) := by
    rw [hρ_innerN_eq, hρ_midN_eq]; exact hρ_inner_lt_mid
  have hρ_midN_lt_outerN : (ρ_midN : ℝ) < (ρ_outerN : ℝ) := by
    rw [hρ_midN_eq, hρ_outerN_eq]; exact hρ_mid_lt_outer
  set r'_φ : ℝ≥0 := ⟨ρ_outer / 2, by positivity⟩
  have hr'_φ_pos : (0 : ℝ) < (r'_φ : ℝ) := by
    change 0 < ρ_outer / 2
    linarith
  have hρρ'_φ_outer : (ρ_outerN : ℝ) + (r'_φ : ℝ) ≤ (r : ℝ) := by
    rw [hρ_outerN_eq]
    change ρ_outer + ρ_outer / 2 ≤ (r : ℝ)
    have h_eq : ρ_outer + ρ_outer / 2 = ρ_outer * 3 / 2 := by ring
    rw [h_eq, hρ_outer_def]
    linarith
  have hρρ'_φ : (ρ_midN : ℝ) + (r'_φ : ℝ) ≤ (r : ℝ) := by
    have h1 : (ρ_midN : ℝ) + (r'_φ : ℝ) ≤ (ρ_outerN : ℝ) + (r'_φ : ℝ) := by
      linarith [hρ_midN_lt_outerN]
    linarith [hρρ'_φ_outer]
  -- Phase 7: uniform `hA_bd` on `closedBall x₀ ρ_outer × Icc (t₀ - T_outer) (t₀ + T_outer)`.
  have hA_bd_outer : ∀ x ∈ closedBall x₀ (ρ_outerN : ℝ),
      ∀ τ ∈ Icc (t₀ - T_outer) (t₀ + T_outer),
        ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ K_orig := by
    intro x hx τ hτ
    have hx_closed_ρ_outer : x ∈ closedBall x₀ ρ_outer := by
      change dist x x₀ ≤ ρ_outer
      rw [mem_closedBall] at hx
      exact hx
    have h_pair_in_outer : ((x, τ) : E × ℝ) ∈ Slab_Φ_outer :=
      ⟨hx_closed_ρ_outer, hτ⟩
    have h_orbit_in_r₀ : Φ ⟨x, τ⟩ ∈ closedBall x₀ r₀_lip := by
      have h_pre : ‖Φ (x, τ) - x₀‖ ≤ R_Φ_image_pre := hR_Φ_image_pre_bd _ h_pair_in_outer
      rw [mem_closedBall, dist_eq_norm]
      exact le_trans h_pre hr₀_lip_ge_Φ
    have h_pair_in_f : ((τ, Φ ⟨x, τ⟩) : ℝ × E) ∈ Slab_f := ⟨hτ, h_orbit_in_r₀⟩
    have h_pre : ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ K_pre := hK_pre_bd _ h_pair_in_f
    linarith
  -- Phase 8: smoothness clause via `continuousOn_fderiv_flow_of_isLocalFlow`.
  have h_fderiv_cont : ContinuousOn (fderiv ℝ Φ)
      ((ball x₀ (ρ_innerN : ℝ)) ×ˢ Ioo (t₀ - T_final) (t₀ + T_final)) :=
    continuousOn_fderiv_flow_of_isLocalFlow hΦ hf_C1
      hT_final_pos hT_final_lt_mid hT_mid_lt_outer hK_orig_nn hKT_mid hsub_outer_orig
      hr'_φ_pos hρ_innerN_lt_midN hρ_midN_lt_outerN hρρ'_φ hρ_outerN_le_r hA_bd_outer
  -- The candidate `Y` extracts the spatial piece via the inverse of `coprodEquivL`.
  set Y : E × ℝ → (E →L[ℝ] E) := fun q => (CE.symm (fderiv ℝ Φ q)).1 with hY_def
  -- Continuity of `Y`: compose `fderiv ℝ Φ` with the continuous `CE.symm` and `Prod.fst`.
  have hY_cont : ContinuousOn Y
      ((ball x₀ (ρ_innerN : ℝ)) ×ˢ Ioo (t₀ - T_final) (t₀ + T_final)) := by
    have h1 : ContinuousOn (fun q => CE.symm (fderiv ℝ Φ q))
        ((ball x₀ (ρ_innerN : ℝ)) ×ˢ Ioo (t₀ - T_final) (t₀ + T_final)) :=
      CE.symm.continuous.comp_continuousOn h_fderiv_cont
    exact continuous_fst.comp_continuousOn h1
  have hY_C0 : ContDiffOn ℝ 0 Y
      ((ball x₀ (ρ_innerN : ℝ)) ×ˢ Ioo (t₀ - T_final) (t₀ + T_final)) :=
    contDiffOn_zero.mpr hY_cont
  -- Phase 9: pointwise coproduct identity for `fderiv ℝ Φ` via `hasFDerivAt_flow_jointly_at`.
  have h_fderiv_eq : ∀ q ∈ ((ball x₀ (ρ_innerN : ℝ)) ×ˢ Ioo (t₀ - T_final) (t₀ + T_final)),
      fderiv ℝ Φ q = (Y q).coprod (timePieceFn f Φ q) := by
    intro q hq
    rcases hq with ⟨hq_x, hq_t⟩
    obtain ⟨x, t⟩ := q
    rw [mem_ball] at hq_x
    -- `x ∈ closedBall x₀ ρ_inner ⊆ closedBall x₀ ρ_mid ⊆ closedBall x₀ ρ_outer`.
    have hx_cb_inner : x ∈ closedBall x₀ (ρ_innerN : ℝ) := mem_closedBall.mpr (le_of_lt hq_x)
    have hx_cb_mid : x ∈ closedBall x₀ (ρ_midN : ℝ) :=
      closedBall_subset_closedBall (le_of_lt hρ_innerN_lt_midN) hx_cb_inner
    have hx_cb_outer : x ∈ closedBall x₀ (ρ_outerN : ℝ) :=
      closedBall_subset_closedBall (le_of_lt hρ_midN_lt_outerN) hx_cb_mid
    -- `t ∈ Ioo (t₀ - T_final) (t₀ + T_final) ⊂ Ioo (t₀ - T_mid) (t₀ + T_mid)`.
    have ht_Ioo_mid : t ∈ Ioo (t₀ - T_mid) (t₀ + T_mid) := by
      refine ⟨?_, ?_⟩
      · linarith [hq_t.1, hT_final_lt_mid]
      · linarith [hq_t.2, hT_final_lt_mid]
    -- The mid-level subset `Icc (t₀-T_mid) (t₀+T_mid) ⊆ Icc tmin tmax` is needed by
    -- `hasFDerivAt_flow_jointly_at`.
    have hsub_mid_orig : Icc (t₀ - T_mid) (t₀ + T_mid) ⊆ Icc tmin tmax := by
      have hsub_mid_outer : Icc (t₀ - T_mid) (t₀ + T_mid) ⊆ Icc (t₀ - T_outer) (t₀ + T_outer) :=
        Icc_subset_Icc (by linarith) (by linarith)
      exact hsub_mid_outer.trans hsub_outer_orig
    -- Restrict the uniform bound to `closedBall x₀ ρ_outer × Icc (t₀-T_mid) (t₀+T_mid)`.
    have hA_bd_mid : ∀ y ∈ closedBall x₀ (ρ_outerN : ℝ),
        ∀ τ ∈ Icc (t₀ - T_mid) (t₀ + T_mid),
          ‖fderiv ℝ (f τ) (Φ ⟨y, τ⟩)‖ ≤ K_orig := by
      intro y hy τ hτ
      have hτ_outer : τ ∈ Icc (t₀ - T_outer) (t₀ + T_outer) := by
        refine ⟨?_, ?_⟩
        · linarith [hτ.1, hT_mid_lt_outer]
        · linarith [hτ.2, hT_mid_lt_outer]
      exact hA_bd_outer y hy τ hτ_outer
    -- Apply the joint Fréchet derivative formula at `(x, t)`.
    have h_fd := hasFDerivAt_flow_jointly_at (ρ := ρ_outerN) hΦ hf_C1
      hT_mid_pos hK_orig_nn hKT_mid hsub_mid_orig hr'_φ_pos hρρ'_φ_outer hA_bd_mid
      hx_cb_outer ht_Ioo_mid
    have hfd_eq : fderiv ℝ Φ (x, t) =
        (variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x, s⟩) (t₀ := t₀)
            hT_mid_pos hK_orig_nn hKT_mid
            (((((hΦ.restrict_center_of_norm_le
                (x₁ := x) (r' := r'_φ) (by
                  rw [mem_closedBall] at hx_cb_outer
                  have hx_le : dist x x₀ ≤ (ρ_outerN : ℝ) := hx_cb_outer
                  linarith))).continuousOn_fderiv_along_orbit hf_C1 x
              (Metric.mem_closedBall_self
                (by exact_mod_cast (le_of_lt hr'_φ_pos))))).mono hsub_mid_orig)
            (fun τ hτ => hA_bd_mid x hx_cb_outer τ hτ)
            (Ioo_subset_Icc_self ht_Ioo_mid)).coprod
          ((ContinuousLinearMap.id ℝ ℝ).smulRight (f t (Φ ⟨x, t⟩))) := h_fd.fderiv
    -- Identify the time piece of the coproduct with `timePieceFn`.
    have h_timePiece_eq : (ContinuousLinearMap.id ℝ ℝ).smulRight (f t (Φ ⟨x, t⟩))
        = timePieceFn f Φ (x, t) := rfl
    -- Abbreviate the spatial-piece part.
    set Lmap : E →L[ℝ] E :=
      variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x, s⟩) (t₀ := t₀)
        hT_mid_pos hK_orig_nn hKT_mid
        (((((hΦ.restrict_center_of_norm_le
            (x₁ := x) (r' := r'_φ) (by
              rw [mem_closedBall] at hx_cb_outer
              have hx_le : dist x x₀ ≤ (ρ_outerN : ℝ) := hx_cb_outer
              linarith))).continuousOn_fderiv_along_orbit hf_C1 x
          (Metric.mem_closedBall_self
            (by exact_mod_cast (le_of_lt hr'_φ_pos))))).mono hsub_mid_orig)
        (fun τ hτ => hA_bd_mid x hx_cb_outer τ hτ)
        (Ioo_subset_Icc_self ht_Ioo_mid) with hLmap_def
    set Lti : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight (f t (Φ ⟨x, t⟩))
      with hLti_def
    have hfd_eq' : fderiv ℝ Φ (x, t) = Lmap.coprod Lti := hfd_eq
    -- Decompose `fderiv ℝ Φ (x, t)` via the inverse coproduct equivalence.
    have hCE_apply : CE (Lmap, Lti) = Lmap.coprod Lti := rfl
    have hCE_inv : CE.symm (Lmap.coprod Lti) = (Lmap, Lti) := by
      rw [← hCE_apply]
      exact CE.symm_apply_apply (Lmap, Lti)
    have hY_eq : Y (x, t) = Lmap := by
      change (CE.symm (fderiv ℝ Φ (x, t))).1 = Lmap
      rw [hfd_eq', hCE_inv]
    rw [hfd_eq', hY_eq, ← h_timePiece_eq]
  -- Final assembly.
  refine ⟨T_final, ρ_innerN, hT_final_pos, hρ_inner_pos, Y, ?_⟩
  refine { contDiffOn := hY_C0, fderiv_eq := h_fderiv_eq }

end LevelZeroFullWitness

/-! ## The parameterized `C^{k+1}` variational-flow projection witness

Combining the level-0 base case `exists_isVariationalFlowProjection_zero_of_C1`
and the inductive successor step `exists_isVariationalFlowProjection_succ_C_step`,
we obtain a variational-flow projection at every level `k : ℕ` from joint
`C^{k+1}` regularity of `f`.  The induction is over `k`, and at each step the
inductive hypothesis is applied to the augmented flow `aΦ` of `augVF f` on the
augmented Banach space `E × (E →L[ℝ] E)`, so we package the statement as a
universally-quantified auxiliary lemma over the Banach-space parameter `E`. -/

section ParameterizedCkWitness

set_option maxHeartbeats 800000 in
/-- **Parameterized variational-flow projection witness.**

If `f : ℝ → E → E` is jointly `C^{k+1}` on `Set.univ`, `E` is a finite-dimensional
Banach space, `Φ` is a local Picard–Lindelöf flow centered at `(x₀, t₀)` with
`t₀` strictly inside its time domain, and the flow's spatial radius `r` is
positive, then there exist positive `T` and `ρ` together with a function
`Y : E × ℝ → (E →L[ℝ] E)` that is a level-`k` variational-flow projection of
`Φ` on the strictly-interior open neighbourhood
`(ball x₀ ρ) ×ˢ Ioo (t₀ - T) (t₀ + T)`. -/
theorem exists_isVariationalFlowProjection_of_C
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [CompleteSpace E] [FiniteDimensional ℝ E]
    {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ}
    {Φ : E × ℝ → E}
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (ht₀_Ioo : t₀ ∈ Set.Ioo tmin tmax)
    (hr_pos : (0 : ℝ) < (r : ℝ))
    (k : ℕ)
    (hf_C : ContDiffOn ℝ ((k : ℕ∞) + 1) (Function.uncurry f)
      (Set.univ : Set (ℝ × E))) :
    ∃ (T : ℝ) (ρ : ℝ≥0) (_hT : 0 < T) (_hρ : 0 < (ρ : ℝ))
      (Y : E × ℝ → (E →L[ℝ] E)),
      IsVariationalFlowProjection hΦ T ρ Y (k : ℕ∞) := by
  classical
  -- Package the statement as a universally-quantified claim over the Banach-space
  -- parameter `E`, so that the inductive step can specialize it to
  -- `E × (E →L[ℝ] E)` for the augmented flow.
  suffices haux : ∀ (k : ℕ) (E : Type _) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [CompleteSpace E] [FiniteDimensional ℝ E]
      {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ}
      {Φ : E × ℝ → E}
      (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
      (_ht₀_Ioo : t₀ ∈ Set.Ioo tmin tmax)
      (_hr_pos : (0 : ℝ) < (r : ℝ))
      (_hf_C : ContDiffOn ℝ ((k : ℕ∞) + 1) (Function.uncurry f)
        (Set.univ : Set (ℝ × E))),
      ∃ (T : ℝ) (ρ : ℝ≥0) (_hT : 0 < T) (_hρ : 0 < (ρ : ℝ))
        (Y : E × ℝ → (E →L[ℝ] E)),
        IsVariationalFlowProjection hΦ T ρ Y (k : ℕ∞) by
    exact haux k E hΦ ht₀_Ioo hr_pos hf_C
  clear hΦ ht₀_Ioo hr_pos hf_C
  intro k
  induction k with
  | zero =>
      intro E _ _ _ _ f t₀ x₀ r tmin tmax Φ hΦ ht₀_Ioo hr_pos hf_C
      -- `(0 : ℕ∞) + 1 = 1` definitionally, so `hf_C : ContDiffOn ℝ 1 (uncurry f) univ`.
      have hf_C1 : ContDiffOn ℝ 1 (Function.uncurry f) (Set.univ : Set (ℝ × E)) := by
        simpa using hf_C
      have h_witness := exists_isVariationalFlowProjection_zero_of_C1
        hΦ ht₀_Ioo hr_pos hf_C1
      -- The witness lives at level `(0 : ℕ∞)`, which is what we need (since `((0 : ℕ) : ℕ∞) = 0`).
      obtain ⟨T, ρ, hT, hρ, Y, hY⟩ := h_witness
      refine ⟨T, ρ, hT, hρ, Y, ?_⟩
      -- `((0 : ℕ) : ℕ∞) = 0` and the predicate matches.
      have h_zero : ((0 : ℕ) : ℕ∞) = (0 : ℕ∞) := by norm_cast
      rw [h_zero]
      exact hY
  | succ n IH =>
      intro E _ _ _ _ f t₀ x₀ r tmin tmax Φ hΦ ht₀_Ioo hr_pos hf_C
      -- `hf_C : ContDiffOn ℝ (((n+1 : ℕ) : ℕ∞) + 1) (uncurry f) univ`.
      -- Re-cast to the `(n : ℕ∞) + 2` shape required by the successor step.
      have h_eq_succ_plus_one : (((n + 1 : ℕ) : ℕ∞) + 1 : WithTop ℕ∞) =
          ((n : ℕ∞) + 2 : WithTop ℕ∞) := by push_cast; ring
      have hf_Cn_plus_2 : ContDiffOn ℝ ((n : ℕ∞) + 2)
          (Function.uncurry f) (Set.univ : Set (ℝ × E)) := by
        have := hf_C
        rw [h_eq_succ_plus_one] at this
        exact this
      -- Derive joint `C^1` of `f` for building `aΦ` via Picard–Lindelöf.
      have hf_C1 : ContDiffOn ℝ 1 (Function.uncurry f) (Set.univ : Set (ℝ × E)) := by
        refine hf_Cn_plus_2.of_le ?_
        have h1 : (1 : WithTop ℕ∞) ≤ 2 := by decide
        have h2 : (2 : WithTop ℕ∞) ≤ ((n : ℕ∞) : WithTop ℕ∞) + 2 := le_add_self
        exact le_trans h1 h2
      -- `uncurry (augVF f)` is `ContDiffOn ℝ ((n : ℕ∞) + 1)` since `uncurry f` is
      -- `ContDiffOn ℝ ((n : ℕ∞) + 2) = ((n+1 : ℕ∞) + 1)`.  This rearrangement
      -- mirrors the one inside `exists_isVariationalFlowProjection_succ_C_step`.
      have hf_Cn_plus_2_as_succ : ContDiffOn ℝ (((n : ℕ∞) + 1) + 1)
          (Function.uncurry f) (Set.univ : Set (ℝ × E)) := by
        have h_eq_wt :
            ((((n : ℕ∞) : WithTop ℕ∞) + 1) + 1 : WithTop ℕ∞) =
            (((n : ℕ∞) : WithTop ℕ∞) + 2 : WithTop ℕ∞) := by
          have h2 : ((2 : WithTop ℕ∞) = 1 + 1) := by decide
          rw [h2, ← add_assoc]
        rw [h_eq_wt]
        exact hf_Cn_plus_2
      have h_augVF_Cn_plus_1 :
          ContDiffOn ℝ ((n : ℕ∞) + 1) (Function.uncurry (augVF f))
            (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
        augVF_uncurry_contDiff (k := ((n : ℕ∞) + 1)) hf_Cn_plus_2_as_succ
      -- Build the augmented flow `aΦ` from joint `C^1` of `augVF f` (the `((n : ℕ∞) + 1)`-
      -- regularity downgraded to `1`).
      have h_augVF_C1 : ContDiffOn ℝ 1 (Function.uncurry (augVF f))
          (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by
        refine h_augVF_Cn_plus_1.of_le ?_
        have h1 : (1 : ℕ∞) ≤ (n : ℕ∞) + 1 := le_add_self
        exact_mod_cast h1
      obtain ⟨R_aug, ε_aug, hR_aug_pos, hε_aug_pos, aΦ, haΦ⟩ :=
        exists_isLocalFlow_of_contDiffOn_univ (augVF f) h_augVF_C1 t₀
          (x₀, ContinuousLinearMap.id ℝ E)
      have hR_aug_R : (0 : ℝ) < (R_aug : ℝ) := by exact_mod_cast hR_aug_pos
      have ht₀_a_Ioo : t₀ ∈ Set.Ioo (t₀ - ε_aug) (t₀ + ε_aug) :=
        ⟨by linarith, by linarith⟩
      -- Apply IH on `(augVF f, aΦ)` at level `n`, over the Banach space `E × (E →L[ℝ] E)`.
      have hIH := IH (E × (E →L[ℝ] E)) (f := augVF f) (t₀ := t₀)
        (x₀ := (x₀, ContinuousLinearMap.id ℝ E)) (r := R_aug)
        (tmin := t₀ - ε_aug) (tmax := t₀ + ε_aug) (Φ := aΦ)
        haΦ ht₀_a_Ioo hR_aug_R h_augVF_Cn_plus_1
      obtain ⟨T_ih, ρ_ih, hT_ih_pos, hρ_ih_pos, Y_ih, hY_ih⟩ := hIH
      -- Plug into the successor step.
      have h_succ := exists_isVariationalFlowProjection_succ_C_step
        (f := f) (t₀ := t₀) (x₀ := x₀) (r := r) (tmin := tmin) (tmax := tmax)
        (Φ := Φ) hΦ ht₀_Ioo hr_pos n hf_Cn_plus_2
        (R_aug := R_aug) (tmin_a := t₀ - ε_aug) (tmax_a := t₀ + ε_aug)
        (aΦ := aΦ) haΦ ht₀_a_Ioo hR_aug_R
        (T_ih := T_ih) (ρ_ih := ρ_ih) (Y_ih := Y_ih)
        hT_ih_pos hρ_ih_pos hY_ih
      obtain ⟨T, ρ, hT, hρ, Y, hY⟩ := h_succ
      refine ⟨T, ρ, hT, hρ, Y, ?_⟩
      -- Adjust the level: `((n+1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1`.
      have h_lvl : ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by push_cast; ring
      rw [h_lvl]
      exact hY

end ParameterizedCkWitness

end Flow
end ODE
end Analysis
end RicciFlower

end
