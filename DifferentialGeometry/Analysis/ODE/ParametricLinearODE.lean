import DifferentialGeometry.Analysis.ODE.FlowVariationalLinearMap
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Parametric linear ODE solution operator

For a continuous family of bounded linear operators `A : F → ℝ → (G →L[ℝ] G)`
on a Banach space `G`, parametric in `x ∈ F`, this file builds the solution
operator of the linear ODE

`Z'(t) = A(x, t) Z(t),  Z(h₀) = Z₀(x)`

on an open interval `Ioo a b` around `h₀`, together with the initial-condition
and ODE clauses.

## Main definitions

* `HasLinearODESolution A a b h₀ Z₀ x` — per-parameter existence predicate
  on the open interval `Ioo a b`:  there is a curve `Z : ℝ → G` satisfying
  `Z h₀ = Z₀ x` and the ODE pointwise on `Ioo a b`.
* `linearODESolution A a b h₀ Z₀ : F → ℝ → G` — the parametric solution
  on the open interval `Ioo a b`.  Defined unconditionally via
  `Classical.choose`: returns *the* solution on `Ioo a b` when
  `HasLinearODESolution` holds, and the constant fallback `fun _ => Z₀ x`
  otherwise.

## Main results

* `exists_linearODE_solution_of_short` — short-interval existence on
  `Icc (h₀ - T) (h₀ + T)` via Mathlib `IsPicardLindelof`, assuming `M · T < 1`
  for the operator-norm bound `M` on this interval.
* `linearODE_unique_on_Ioo` — uniqueness on `Ioo a b` via Mathlib
  `ODE_solution_unique_of_mem_Ioo`.
* `linearODESolution_init` — unconditional: `linearODESolution A a b h₀ Z₀ x h₀ = Z₀ x`.
* `linearODESolution_hasDerivAt_of_hasSolution` — ODE clause under the
  `HasLinearODESolution` hypothesis.
* `hasLinearODESolution_of_continuousOn` — discharges the per-parameter
  existence predicate from joint continuity of `A` on `U ×ˢ Ioo a b` and
  `x ∈ U`.  The construction iterates `exists_linearODE_solution_of_short`
  finitely many times to cover each closed sub-interval `Icc α β ⊂ Ioo a b`,
  then exhausts `Ioo a b` by a countable family of such sub-intervals.
* `linearODESolution_hasDerivAt` — wrapped ODE clause: combines
  `hasLinearODESolution_of_continuousOn` and
  `linearODESolution_hasDerivAt_of_hasSolution`.

All results are formulated on generic Banach spaces `F` and `G`; the parameter
space `F` carries no completeness assumption.  `[CompleteSpace G]` is required
for Picard–Lindelöf to apply to the state space.
-/

noncomputable section

open Set Function Filter Metric Asymptotics Real
open scoped Topology NNReal ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace ODE
namespace Flow

section ShortIntervalExistence

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/--
**Short-interval existence** for the linear ODE `Z'(t) = A(t) Z(t)` on
`Icc (h₀ - T) (h₀ + T)`, assuming `‖A t‖ ≤ M` on this interval and `M · T < 1`.
The solution exists for **every** initial value `Z₀ ∈ G`.

This is the elementary Picard step on which the global existence theory
(forthcoming in the follow-up substep) is built.
-/
theorem exists_linearODE_solution_of_short
    {A : ℝ → (G →L[ℝ] G)} {h₀ : ℝ} {T M : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hA_cont : ContinuousOn A (Icc (h₀ - T) (h₀ + T)))
    (hA_bd : ∀ t ∈ Icc (h₀ - T) (h₀ + T), ‖A t‖ ≤ M)
    (Z₀ : G) :
    ∃ Z : ℝ → G, Z h₀ = Z₀ ∧
      ∀ t ∈ Icc (h₀ - T) (h₀ + T), HasDerivWithinAt Z (A t (Z t))
        (Icc (h₀ - T) (h₀ + T)) t := by
  set v : ℝ → G → G := fun t y => A t y with hv_def
  set r₀ : ℝ := ‖Z₀‖ with hr₀_def
  have hr₀_nn : 0 ≤ r₀ := norm_nonneg _
  have h1mMT_pos : 0 < 1 - M * T := by linarith
  set a₀ : ℝ := (r₀ + 1) / (1 - M * T) with ha₀_def
  have ha₀_pos : 0 < a₀ := div_pos (by linarith [hr₀_nn]) h1mMT_pos
  have ha₀_nn : 0 ≤ a₀ := le_of_lt ha₀_pos
  have hMaT_le : M * a₀ * T ≤ a₀ - r₀ := by
    have hkey : a₀ * (1 - M * T) = r₀ + 1 := by
      rw [ha₀_def]; field_simp
    have h1 : a₀ - M * a₀ * T = r₀ + 1 := by
      have : a₀ - M * a₀ * T = a₀ * (1 - M * T) := by ring
      rw [this, hkey]
    linarith
  let tmin : ℝ := h₀ - T
  let tmax : ℝ := h₀ + T
  have htmin_le_t₀ : tmin ≤ h₀ := by change h₀ - T ≤ h₀; linarith
  have ht₀_le_tmax : h₀ ≤ tmax := by change h₀ ≤ h₀ + T; linarith
  let t₀Icc : Icc tmin tmax := ⟨h₀, ⟨htmin_le_t₀, ht₀_le_tmax⟩⟩
  let aN : ℝ≥0 := ⟨a₀, ha₀_nn⟩
  let rN : ℝ≥0 := ⟨r₀, hr₀_nn⟩
  let LN : ℝ≥0 := ⟨M * a₀, mul_nonneg hM ha₀_nn⟩
  let KN : ℝ≥0 := ⟨M, hM⟩
  have hpl : IsPicardLindelof v t₀Icc (0 : G) aN rN LN KN := by
    refine
    { lipschitzOnWith := ?_,
      continuousOn := ?_,
      norm_le := ?_,
      mul_max_le := ?_ }
    · intro t ht
      have hAτ_bd : ‖A t‖ ≤ M := hA_bd t ht
      have hlip : LipschitzWith KN (A t) := (A t).lipschitzWith_of_opNorm_le hAτ_bd
      exact hlip.lipschitzOnWith (s := closedBall (0 : G) aN)
    · intro y _
      have happly : Continuous (fun B : G →L[ℝ] G => B y) :=
        (ContinuousLinearMap.apply ℝ G y).continuous
      exact happly.comp_continuousOn hA_cont
    · intro t ht y hy
      have hAt_bd : ‖A t‖ ≤ M := hA_bd t ht
      have hy_norm : ‖y‖ ≤ a₀ := by
        simpa [mem_closedBall_zero_iff] using hy
      change ‖v t y‖ ≤ (LN : ℝ)
      calc ‖v t y‖ = ‖A t y‖ := rfl
        _ ≤ ‖A t‖ * ‖y‖ := (A t).le_opNorm y
        _ ≤ M * a₀ := mul_le_mul hAt_bd hy_norm (norm_nonneg _) hM
    · change (LN : ℝ) * max (tmax - h₀) (h₀ - tmin) ≤ (aN : ℝ) - (rN : ℝ)
      have hmax_eq : max (tmax - h₀) (h₀ - tmin) = T := by
        have h1 : tmax - h₀ = T := by change (h₀ + T) - h₀ = T; ring
        have h2 : h₀ - tmin = T := by change h₀ - (h₀ - T) = T; ring
        rw [h1, h2]; exact max_self _
      rw [hmax_eq]
      change M * a₀ * T ≤ a₀ - r₀
      exact hMaT_le
  have hZ₀_mem : Z₀ ∈ closedBall (0 : G) rN := by
    rw [mem_closedBall_zero_iff]; change ‖Z₀‖ ≤ r₀; rfl
  obtain ⟨Z, hZ_init, hZ_deriv⟩ :=
    hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt hZ₀_mem
  exact ⟨Z, hZ_init, hZ_deriv⟩

end ShortIntervalExistence

section Uniqueness

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Uniqueness** of solutions to a linear ODE on an open interval `Ioo a b`. -/
theorem linearODE_unique_on_Ioo
    {A : ℝ → (G →L[ℝ] G)} {a b h₀ : ℝ}
    (ht₀ : h₀ ∈ Ioo a b)
    (hA_cont : ContinuousOn A (Ioo a b))
    {Z₁ Z₂ : ℝ → G}
    (hZ₁ : ∀ t ∈ Ioo a b, HasDerivAt Z₁ (A t (Z₁ t)) t)
    (hZ₂ : ∀ t ∈ Ioo a b, HasDerivAt Z₂ (A t (Z₂ t)) t)
    (heq : Z₁ h₀ = Z₂ h₀) :
    EqOn Z₁ Z₂ (Ioo a b) := by
  intro t ht
  let v : ℝ → G → G := fun t y => A t y
  set a' := (a + min t h₀) / 2 with ha'
  set b' := (b + max t h₀) / 2 with hb'
  have hmin_lt : a < min t h₀ := lt_min ht.1 ht₀.1
  have hmax_lt : max t h₀ < b := max_lt ht.2 ht₀.2
  have hmin_le_t : min t h₀ ≤ t := min_le_left _ _
  have hmin_le_t₀ : min t h₀ ≤ h₀ := min_le_right _ _
  have ht_le_max : t ≤ max t h₀ := le_max_left _ _
  have ht₀_le_max : h₀ ≤ max t h₀ := le_max_right _ _
  have ha'_lt_min : a' < min t h₀ := by rw [ha']; linarith
  have ha_lt_a' : a < a' := by rw [ha']; linarith
  have hmax_lt_b' : max t h₀ < b' := by rw [hb']; linarith
  have hb'_lt_b : b' < b := by rw [hb']; linarith
  have hsub : Ioo a' b' ⊆ Ioo a b := fun s hs =>
    ⟨lt_trans ha_lt_a' hs.1, lt_trans hs.2 hb'_lt_b⟩
  have ht_mem' : t ∈ Ioo a' b' :=
    ⟨lt_of_lt_of_le ha'_lt_min hmin_le_t, lt_of_le_of_lt ht_le_max hmax_lt_b'⟩
  have ht₀_mem' : h₀ ∈ Ioo a' b' :=
    ⟨lt_of_lt_of_le ha'_lt_min hmin_le_t₀, lt_of_le_of_lt ht₀_le_max hmax_lt_b'⟩
  have hab_le : a' ≤ b' := le_of_lt (lt_trans ha'_lt_min (lt_of_le_of_lt hmin_le_t
    (lt_of_lt_of_le ht_mem'.2 (le_refl _))))
  have hIcc_sub : Icc a' b' ⊆ Ioo a b := fun s hs =>
    ⟨lt_of_lt_of_le ha_lt_a' hs.1, lt_of_le_of_lt hs.2 hb'_lt_b⟩
  have hbd : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Icc a' b', ‖A τ‖ ≤ M := by
    have hcont' : ContinuousOn A (Icc a' b') := hA_cont.mono hIcc_sub
    have hcont_norm : ContinuousOn (fun τ => ‖A τ‖) (Icc a' b') :=
      continuous_norm.comp_continuousOn hcont'
    have hcpt : IsCompact (Icc a' b') := isCompact_Icc
    have hne : (Icc a' b').Nonempty := ⟨a', left_mem_Icc.mpr hab_le⟩
    rcases hcpt.exists_isMaxOn hne hcont_norm with ⟨τ₁, _, hτ₁_max⟩
    exact ⟨‖A τ₁‖, norm_nonneg _, fun τ hτ => hτ₁_max hτ⟩
  obtain ⟨M, hM_nn, hMbd⟩ := hbd
  let K : ℝ≥0 := ⟨M, hM_nn⟩
  have hv_lip : ∀ τ ∈ Ioo a' b', LipschitzOnWith K (v τ) univ := by
    intro τ hτ
    have hlip : LipschitzWith K (A τ) :=
      (A τ).lipschitzWith_of_opNorm_le (hMbd τ (Ioo_subset_Icc_self hτ))
    exact (LipschitzWith.lipschitzOnWith (s := (univ : Set G)) hlip)
  exact (ODE_solution_unique_of_mem_Ioo (v := v) (s := fun _ => univ) (K := K)
    hv_lip ht₀_mem'
    (fun τ hτ => ⟨hZ₁ τ (hsub hτ), mem_univ _⟩)
    (fun τ hτ => ⟨hZ₂ τ (hsub hτ), mem_univ _⟩)
    heq) ht_mem'

end Uniqueness

section SolutionOperator

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/--
**Per-parameter existence predicate.**  `HasLinearODESolution A a b h₀ Z₀ x`
asserts that for the fixed parameter `x : F`, there exists a curve `Z : ℝ → G`
with `Z h₀ = Z₀ x` and `HasDerivAt Z (A x t (Z t)) t` for every `t ∈ Ioo a b`.

This predicate is used internally by `linearODESolution` to decide whether to
return the chosen solution on `Ioo a b` or the constant fallback.
-/
def HasLinearODESolution
    (A : F → ℝ → (G →L[ℝ] G)) (a b h₀ : ℝ) (Z₀ : F → G) (x : F) : Prop :=
  ∃ Z : ℝ → G, Z h₀ = Z₀ x ∧ ∀ t ∈ Ioo a b, HasDerivAt Z (A x t (Z t)) t

/--
**Parametric solution of the linear ODE** `Z'(t) = A(x, t) Z(t)` with initial
condition `Z(x, h₀) = Z₀ x` on the open interval `Ioo a b`.

Defined unconditionally:

* If a solution on `Ioo a b` exists for the parameter `x` (predicate
  `HasLinearODESolution`), `linearODESolution A a b h₀ Z₀ x` is *the* chosen
  solution, via `Classical.choose`.
* Otherwise, it is the constant curve `fun _ => Z₀ x`.

The unconditional choice makes `linearODESolution` total; the headline
theorems `linearODESolution_init` and
`linearODESolution_hasDerivAt_of_hasSolution` extract the meaningful clauses
under the appropriate hypotheses.
-/
noncomputable def linearODESolution
    (A : F → ℝ → (G →L[ℝ] G)) (a b h₀ : ℝ) (Z₀ : F → G) :
    F → ℝ → G := by
  classical
  exact fun x =>
    if h : HasLinearODESolution A a b h₀ Z₀ x then
      Classical.choose h
    else
      fun _ => Z₀ x

/--
**Initial condition** for `linearODESolution`.  At `t = h₀`, the parametric
solution equals the initial datum `Z₀ x`.

This identity is unconditional: it holds regardless of whether the
per-parameter existence predicate `HasLinearODESolution` holds.
-/
theorem linearODESolution_init
    (A : F → ℝ → (G →L[ℝ] G)) (a b h₀ : ℝ) (Z₀ : F → G) (x : F) :
    linearODESolution A a b h₀ Z₀ x h₀ = Z₀ x := by
  unfold linearODESolution
  by_cases h : HasLinearODESolution A a b h₀ Z₀ x
  · simp only [dif_pos h]
    exact (Classical.choose_spec h).1
  · simp only [dif_neg h]

/--
**ODE clause** for `linearODESolution` under the per-parameter existence
hypothesis.

When `HasLinearODESolution A a b h₀ Z₀ x` holds, the parametric solution at
`x` satisfies the linear ODE pointwise on `Ioo a b`.
-/
theorem linearODESolution_hasDerivAt_of_hasSolution
    (A : F → ℝ → (G →L[ℝ] G)) (a b h₀ : ℝ) (Z₀ : F → G)
    {x : F} (hx : HasLinearODESolution A a b h₀ Z₀ x) {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (linearODESolution A a b h₀ Z₀ x ·)
      (A x t (linearODESolution A a b h₀ Z₀ x t)) t := by
  have hZ_eq : linearODESolution A a b h₀ Z₀ x = Classical.choose hx := by
    unfold linearODESolution
    simp only [dif_pos hx]
  rw [hZ_eq]
  exact (Classical.choose_spec hx).2 t ht

end SolutionOperator

section GlobalExistence

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- **One Picard step** at a non-centered base time `c`.  Given a continuous,
operator-norm-bounded coefficient `A` on a closed interval `[c - T, c + T]`
with `M · T < 1`, the linear ODE `Z'(t) = A(t) Z(t),  Z(c) = Y_c` has a
solution on `[c - T, c + T]`.

This is `exists_linearODE_solution_of_short` re-stated with the initial time
`c` named separately so it can be used in an inductive Picard-extension
argument. -/
theorem exists_linearODE_solution_of_short_at
    {A : ℝ → (G →L[ℝ] G)} {c T M : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hA_cont : ContinuousOn A (Icc (c - T) (c + T)))
    (hA_bd : ∀ t ∈ Icc (c - T) (c + T), ‖A t‖ ≤ M)
    (Y_c : G) :
    ∃ Z : ℝ → G, Z c = Y_c ∧
      ∀ t ∈ Icc (c - T) (c + T), HasDerivWithinAt Z (A t (Z t))
        (Icc (c - T) (c + T)) t :=
  exists_linearODE_solution_of_short (A := A) (h₀ := c) (T := T) (M := M)
    hT hM hMT hA_cont hA_bd Y_c

/-- **Glue two Picard-style segments** sharing the time `t₁` into a single
function defined on `Icc α β = Icc α t₁ ∪ Icc t₁ β` (when `α ≤ t₁ ≤ β`).

The hypothesis is that two functions `f, g` satisfy the ODE on their
respective closed intervals and agree at the shared endpoint `t₁`.  We use
`f` on `(-∞, t₁]` and `g` on `(t₁, ∞)`, patched via `if t ≤ t₁ then f t else g t`. -/
private theorem hasDerivWithinAt_glue_Icc_at_pt
    {f g : ℝ → G} {A : ℝ → (G →L[ℝ] G)} {α t₁ β : ℝ}
    (hα_le : α ≤ t₁) (hβ_ge : t₁ ≤ β)
    (hf : ∀ t ∈ Icc α t₁, HasDerivWithinAt f (A t (f t)) (Icc α t₁) t)
    (hg : ∀ t ∈ Icc t₁ β, HasDerivWithinAt g (A t (g t)) (Icc t₁ β) t)
    (h_match : f t₁ = g t₁) :
    let Z : ℝ → G := fun t => if t ≤ t₁ then f t else g t
    Z t₁ = f t₁ ∧
      ∀ t ∈ Icc α β, HasDerivWithinAt Z (A t (Z t)) (Icc α β) t := by
  intro Z
  have hZ_t1 : Z t₁ = f t₁ := by simp [Z]
  refine ⟨hZ_t1, ?_⟩
  have hZ_eq_f : ∀ t, t ≤ t₁ → Z t = f t := by
    intro t ht; simp [Z, ht]
  have hZ_eq_g : ∀ t, t₁ ≤ t → Z t = g t := by
    intro t ht
    by_cases htle : t ≤ t₁
    · have : t = t₁ := le_antisymm htle ht
      simp [Z, this, h_match]
    · simp [Z, htle]
  intro t ht
  have hunion : Icc α t₁ ∪ Icc t₁ β = Icc α β :=
    Set.Icc_union_Icc_eq_Icc hα_le hβ_ge
  rcases le_total t t₁ with htle | htge
  · have ht_left : t ∈ Icc α t₁ := ⟨ht.1, htle⟩
    have hf_deriv : HasDerivWithinAt f (A t (f t)) (Icc α t₁) t := hf t ht_left
    have hZ_eq_set : EqOn Z f (Icc α t₁) := fun s hs => hZ_eq_f s hs.2
    have hZf_deriv : HasDerivWithinAt Z (A t (f t)) (Icc α t₁) t :=
      hf_deriv.congr (fun s hs => hZ_eq_set hs) (hZ_eq_f t htle)
    by_cases hteq : t = t₁
    · subst hteq
      have ht_right : t ∈ Icc t β := ⟨le_rfl, hβ_ge⟩
      have hg_deriv : HasDerivWithinAt g (A t (g t)) (Icc t β) t := hg t ht_right
      have hZ_eq_set_r : EqOn Z g (Icc t β) := fun s hs => hZ_eq_g s hs.1
      have hZg_deriv : HasDerivWithinAt Z (A t (g t)) (Icc t β) t :=
        hg_deriv.congr (fun s hs => hZ_eq_set_r hs) (hZ_eq_g t le_rfl)
      have h_ZAt_val : Z t = f t := hZ_t1
      have h_AZ_eq_Af : A t (Z t) = A t (f t) := by rw [h_ZAt_val]
      have h_AZ_eq_Ag : A t (Z t) = A t (g t) := by rw [h_ZAt_val, h_match]
      have hZf_at_t1 : HasDerivWithinAt Z (A t (Z t)) (Icc α t) t := by
        rw [h_AZ_eq_Af]; exact hZf_deriv
      have hZg_at_t1 : HasDerivWithinAt Z (A t (Z t)) (Icc t β) t := by
        rw [h_AZ_eq_Ag]; exact hZg_deriv
      have := (hZf_at_t1).union hZg_at_t1
      rwa [hunion] at this
    · have htlt : t < t₁ := lt_of_le_of_ne htle hteq
      have h_AZ_eq : A t (Z t) = A t (f t) := by rw [hZ_eq_f t htle]
      have hZf_at_t : HasDerivWithinAt Z (A t (Z t)) (Icc α t₁) t := by
        rw [h_AZ_eq]; exact hZf_deriv
      have h_nhds_eq : 𝓝[Icc α β] t = 𝓝[Icc α t₁] t := by
        apply le_antisymm
        · rw [nhdsWithin_le_iff]
          have h_Iic_nhd : Iic t₁ ∈ 𝓝 t := Iic_mem_nhds htlt
          have : Iic t₁ ∈ 𝓝[Icc α β] t := mem_nhdsWithin_of_mem_nhds h_Iic_nhd
          have h_inter : Icc α β ∩ Iic t₁ = Icc α t₁ := by
            ext s; constructor
            · intro ⟨h1, h2⟩; exact ⟨h1.1, h2⟩
            · intro ⟨h1, h2⟩; exact ⟨⟨h1, le_trans h2 hβ_ge⟩, h2⟩
          have := inter_mem_nhdsWithin (Icc α β) h_Iic_nhd
          rw [h_inter] at this; exact this
        · exact nhdsWithin_mono _ (Icc_subset_Icc_right hβ_ge)
      rw [HasDerivWithinAt, h_nhds_eq.symm] at hZf_at_t
      exact hZf_at_t
  · have ht_right : t ∈ Icc t₁ β := ⟨htge, ht.2⟩
    have hg_deriv : HasDerivWithinAt g (A t (g t)) (Icc t₁ β) t := hg t ht_right
    have hZ_eq_set_r : EqOn Z g (Icc t₁ β) := fun s hs => hZ_eq_g s hs.1
    have hZg_deriv : HasDerivWithinAt Z (A t (g t)) (Icc t₁ β) t :=
      hg_deriv.congr (fun s hs => hZ_eq_set_r hs) (hZ_eq_g t htge)
    by_cases hteq : t = t₁
    · subst hteq
      have ht_left : t ∈ Icc α t := ⟨hα_le, le_rfl⟩
      have hf_deriv : HasDerivWithinAt f (A t (f t)) (Icc α t) t := hf t ht_left
      have hZ_eq_set : EqOn Z f (Icc α t) := fun s hs => hZ_eq_f s hs.2
      have hZf_deriv : HasDerivWithinAt Z (A t (f t)) (Icc α t) t :=
        hf_deriv.congr (fun s hs => hZ_eq_set hs) (hZ_eq_f t le_rfl)
      have h_ZAt_val : Z t = f t := hZ_t1
      have h_AZ_eq_Af : A t (Z t) = A t (f t) := by rw [h_ZAt_val]
      have h_AZ_eq_Ag : A t (Z t) = A t (g t) := by rw [h_ZAt_val, h_match]
      have hZf_at_t1 : HasDerivWithinAt Z (A t (Z t)) (Icc α t) t := by
        rw [h_AZ_eq_Af]; exact hZf_deriv
      have hZg_at_t1 : HasDerivWithinAt Z (A t (Z t)) (Icc t β) t := by
        rw [h_AZ_eq_Ag]; exact hZg_deriv
      have := (hZf_at_t1).union hZg_at_t1
      rwa [hunion] at this
    · have htgt : t₁ < t := lt_of_le_of_ne htge (Ne.symm hteq)
      have h_AZ_eq : A t (Z t) = A t (g t) := by rw [hZ_eq_g t htge]
      have hZg_at_t : HasDerivWithinAt Z (A t (Z t)) (Icc t₁ β) t := by
        rw [h_AZ_eq]; exact hZg_deriv
      have h_nhds_eq : 𝓝[Icc α β] t = 𝓝[Icc t₁ β] t := by
        apply le_antisymm
        · rw [nhdsWithin_le_iff]
          have h_Ici_nhd : Ici t₁ ∈ 𝓝 t := Ici_mem_nhds htgt
          have h_inter : Icc α β ∩ Ici t₁ = Icc t₁ β := by
            ext s; constructor
            · intro ⟨h1, h2⟩; exact ⟨h2, h1.2⟩
            · intro ⟨h1, h2⟩; exact ⟨⟨le_trans hα_le h1, h2⟩, h1⟩
          have := inter_mem_nhdsWithin (Icc α β) h_Ici_nhd
          rw [h_inter] at this; exact this
        · exact nhdsWithin_mono _ (Icc_subset_Icc_left hα_le)
      rw [HasDerivWithinAt, h_nhds_eq.symm] at hZg_at_t
      exact hZg_at_t

/-- **Right-extension** of a linear-ODE solution by iterated Picard.

Given a continuous, operator-norm-bounded coefficient `A` on `Icc h₀ (h₀ + B)`
with `‖A‖ ≤ M` there and `M · T < 1`, for any natural number `n` with
`h₀ + n · T ≤ h₀ + B` (equivalently `n · T ≤ B`), there exists a function
`Z : ℝ → G` with `Z h₀ = Y₀` and satisfying the ODE on `Icc h₀ (h₀ + n · T)`. -/
private theorem exists_linearODE_solution_right_iterated
    {A : ℝ → (G →L[ℝ] G)} {h₀ M T B : ℝ}
    (hT_pos : 0 < T) (hM_nn : 0 ≤ M) (hMT : M * T < 1)
    (hA_cont : ContinuousOn A (Icc (h₀ - T) (h₀ + B + T)))
    (hA_bd : ∀ t ∈ Icc (h₀ - T) (h₀ + B + T), ‖A t‖ ≤ M)
    (Y₀ : G) :
    ∀ n : ℕ, (n : ℝ) * T ≤ B →
      ∃ Z : ℝ → G, Z h₀ = Y₀ ∧
        ∀ t ∈ Icc h₀ (h₀ + (n : ℝ) * T),
          HasDerivWithinAt Z (A t (Z t)) (Icc h₀ (h₀ + (n : ℝ) * T)) t := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨fun _ => Y₀, rfl, fun t ht => ?_⟩
    simp only [Nat.cast_zero, zero_mul, add_zero] at ht ⊢
    have hsub : (Icc h₀ h₀).Subsingleton := by
      intro x hx y hy
      have hx_eq : x = h₀ := le_antisymm hx.2 hx.1
      have hy_eq : y = h₀ := le_antisymm hy.2 hy.1
      rw [hx_eq, hy_eq]
    rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
    exact HasFDerivWithinAt.of_finite hsub.finite
  | succ k ih =>
    intro hkT
    have hkT_prev : (k : ℝ) * T ≤ B := by
      have : ((k : ℝ) + 1) * T = (k : ℝ) * T + T := by ring
      push_cast at hkT
      linarith [hT_pos]
    obtain ⟨Z_k, hZ_k_init, hZ_k_deriv⟩ := ih hkT_prev
    set c : ℝ := h₀ + (k : ℝ) * T + T with hc_def
    have hsub_picard : Icc (c - T) (c + T) ⊆ Icc (h₀ - T) (h₀ + B + T) := by
      intro s hs
      refine ⟨?_, ?_⟩
      · have : h₀ - T ≤ c - T := by
          rw [hc_def]; have hkT_nn : (0 : ℝ) ≤ k * T := by positivity
          linarith
        linarith [hs.1]
      · have : c + T ≤ h₀ + B + T := by
          rw [hc_def]; have h_step : (↑k + 1) * T ≤ B := by push_cast at hkT; exact hkT
          have : (k : ℝ) * T + T + T = ((k : ℝ) + 1) * T + T := by ring
          linarith
        linarith [hs.2]
    have hA_cont_picard : ContinuousOn A (Icc (c - T) (c + T)) := hA_cont.mono hsub_picard
    have hA_bd_picard : ∀ t ∈ Icc (c - T) (c + T), ‖A t‖ ≤ M :=
      fun t ht => hA_bd t (hsub_picard ht)
    set Y_c : G := Z_k (h₀ + (k : ℝ) * T) with hY_c_def
    have h_t1_mem : h₀ + (k : ℝ) * T ∈ Icc (c - T) (c + T) := by
      rw [hc_def]; refine ⟨by linarith, by linarith [hT_pos]⟩
    set t₁ : ℝ := h₀ + (k : ℝ) * T with ht₁_def
    have h_picard_sub : Icc (t₁ - T) (t₁ + T) ⊆ Icc (h₀ - T) (h₀ + B + T) := by
      intro s hs
      refine ⟨?_, ?_⟩
      · have : h₀ - T ≤ t₁ - T := by
          rw [ht₁_def]; have hkT_nn : (0 : ℝ) ≤ k * T := by positivity
          linarith
        linarith [hs.1]
      · have : t₁ + T ≤ h₀ + B + T := by
          rw [ht₁_def]; have h_step : (↑k + 1) * T ≤ B := by push_cast at hkT; exact hkT
          have : (k : ℝ) * T + T = ((k : ℝ) + 1) * T := by ring
          linarith
        linarith [hs.2]
    have hA_cont_picard' : ContinuousOn A (Icc (t₁ - T) (t₁ + T)) := hA_cont.mono h_picard_sub
    have hA_bd_picard' : ∀ t ∈ Icc (t₁ - T) (t₁ + T), ‖A t‖ ≤ M :=
      fun t ht => hA_bd t (h_picard_sub ht)
    obtain ⟨Z_pic, hZ_pic_init, hZ_pic_deriv⟩ :=
      exists_linearODE_solution_of_short_at hT_pos hM_nn hMT hA_cont_picard' hA_bd_picard' Y_c
    have h_pic_right : ∀ t ∈ Icc t₁ (t₁ + T),
        HasDerivWithinAt Z_pic (A t (Z_pic t)) (Icc t₁ (t₁ + T)) t := by
      intro t ht
      have ht_in_picard : t ∈ Icc (t₁ - T) (t₁ + T) :=
        ⟨by linarith [ht.1, hT_pos], ht.2⟩
      have hd : HasDerivWithinAt Z_pic (A t (Z_pic t)) (Icc (t₁ - T) (t₁ + T)) t :=
        hZ_pic_deriv t ht_in_picard
      exact hd.mono (Icc_subset_Icc_left (by linarith [hT_pos]))
    have h_match : Z_k t₁ = Z_pic t₁ := by
      rw [hZ_pic_init]
    have h_prev_deriv : ∀ t ∈ Icc h₀ t₁,
        HasDerivWithinAt Z_k (A t (Z_k t)) (Icc h₀ t₁) t := by
      intro t ht
      exact hZ_k_deriv t ht
    have h_ht1_le_top : t₁ ≤ t₁ + T := by linarith [hT_pos]
    have h_h0_le_t1 : h₀ ≤ t₁ := by
      change h₀ ≤ h₀ + (k : ℝ) * T
      have hkT_nn : (0 : ℝ) ≤ k * T := mul_nonneg (Nat.cast_nonneg _) hT_pos.le
      linarith
    have h_glued :=
      hasDerivWithinAt_glue_Icc_at_pt (f := Z_k) (g := Z_pic) (A := A)
        (α := h₀) (t₁ := t₁) (β := t₁ + T) h_h0_le_t1 h_ht1_le_top
        h_prev_deriv h_pic_right h_match
    set Z : ℝ → G := fun t => if t ≤ t₁ then Z_k t else Z_pic t with hZ_def
    obtain ⟨hZ_t1, hZ_deriv⟩ := h_glued
    have hZ_init : Z h₀ = Y₀ := by
      simp [Z, h_h0_le_t1, hZ_k_init]
    have h_dom_eq : h₀ + ((k : ℝ) + 1) * T = t₁ + T := by
      rw [ht₁_def]; ring
    refine ⟨Z, hZ_init, fun t ht => ?_⟩
    have h_dom_eq' : h₀ + ((k : ℕ) + 1 : ℝ) * T = t₁ + T := by
      change h₀ + ((k : ℝ) + 1) * T = (h₀ + (k : ℝ) * T) + T; ring
    have h_dom_cast : h₀ + (↑(k + 1) : ℝ) * T = t₁ + T := by
      have : (↑(k + 1) : ℝ) = (k : ℝ) + 1 := by push_cast; rfl
      rw [this]; exact h_dom_eq'
    have ht_cast : t ∈ Icc h₀ (t₁ + T) := by
      rcases ht with ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [h_dom_cast] at h2; exact h2
    have hd := hZ_deriv t ht_cast
    have hset_eq : Icc h₀ (t₁ + T) = Icc h₀ (h₀ + (↑(k + 1) : ℝ) * T) := by
      rw [h_dom_cast]
    rw [hset_eq] at hd
    exact hd

/-- **Left-extension** of a linear-ODE solution by iterated Picard (the
mirror of `exists_linearODE_solution_right_iterated`). -/
private theorem exists_linearODE_solution_left_iterated
    {A : ℝ → (G →L[ℝ] G)} {h₀ M T B : ℝ}
    (hT_pos : 0 < T) (hM_nn : 0 ≤ M) (hMT : M * T < 1)
    (hA_cont : ContinuousOn A (Icc (h₀ - B - T) (h₀ + T)))
    (hA_bd : ∀ t ∈ Icc (h₀ - B - T) (h₀ + T), ‖A t‖ ≤ M)
    (Y₀ : G) :
    ∀ n : ℕ, (n : ℝ) * T ≤ B →
      ∃ Z : ℝ → G, Z h₀ = Y₀ ∧
        ∀ t ∈ Icc (h₀ - (n : ℝ) * T) h₀,
          HasDerivWithinAt Z (A t (Z t)) (Icc (h₀ - (n : ℝ) * T) h₀) t := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨fun _ => Y₀, rfl, fun t ht => ?_⟩
    simp only [Nat.cast_zero, zero_mul, sub_zero] at ht ⊢
    have hsub : (Icc h₀ h₀).Subsingleton := by
      intro x hx y hy
      have hx_eq : x = h₀ := le_antisymm hx.2 hx.1
      have hy_eq : y = h₀ := le_antisymm hy.2 hy.1
      rw [hx_eq, hy_eq]
    rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
    exact HasFDerivWithinAt.of_finite hsub.finite
  | succ k ih =>
    intro hkT
    have hkT_prev : (k : ℝ) * T ≤ B := by
      have : ((k : ℝ) + 1) * T = (k : ℝ) * T + T := by ring
      push_cast at hkT
      linarith [hT_pos]
    obtain ⟨Z_k, hZ_k_init, hZ_k_deriv⟩ := ih hkT_prev
    set t₁ : ℝ := h₀ - (k : ℝ) * T with ht₁_def
    have h_picard_sub : Icc (t₁ - T) (t₁ + T) ⊆ Icc (h₀ - B - T) (h₀ + T) := by
      intro s hs
      refine ⟨?_, ?_⟩
      · have : h₀ - B - T ≤ t₁ - T := by
          rw [ht₁_def]; have h_step : (↑k + 1) * T ≤ B := by push_cast at hkT; exact hkT
          have : (k : ℝ) * T + T = ((k : ℝ) + 1) * T := by ring
          linarith
        linarith [hs.1]
      · have : t₁ + T ≤ h₀ + T := by
          rw [ht₁_def]; have hkT_nn : (0 : ℝ) ≤ k * T := mul_nonneg (Nat.cast_nonneg _) hT_pos.le
          linarith
        linarith [hs.2]
    have hA_cont_picard' : ContinuousOn A (Icc (t₁ - T) (t₁ + T)) := hA_cont.mono h_picard_sub
    have hA_bd_picard' : ∀ t ∈ Icc (t₁ - T) (t₁ + T), ‖A t‖ ≤ M :=
      fun t ht => hA_bd t (h_picard_sub ht)
    set Y_c : G := Z_k t₁ with hY_c_def
    obtain ⟨Z_pic, hZ_pic_init, hZ_pic_deriv⟩ :=
      exists_linearODE_solution_of_short_at hT_pos hM_nn hMT hA_cont_picard' hA_bd_picard' Y_c
    have h_pic_left : ∀ t ∈ Icc (t₁ - T) t₁,
        HasDerivWithinAt Z_pic (A t (Z_pic t)) (Icc (t₁ - T) t₁) t := by
      intro t ht
      have ht_in_picard : t ∈ Icc (t₁ - T) (t₁ + T) :=
        ⟨ht.1, by linarith [ht.2, hT_pos]⟩
      have hd : HasDerivWithinAt Z_pic (A t (Z_pic t)) (Icc (t₁ - T) (t₁ + T)) t :=
        hZ_pic_deriv t ht_in_picard
      exact hd.mono (Icc_subset_Icc_right (by linarith [hT_pos]))
    have h_match : Z_pic t₁ = Z_k t₁ := hZ_pic_init
    have h_next_deriv : ∀ t ∈ Icc t₁ h₀,
        HasDerivWithinAt Z_k (A t (Z_k t)) (Icc t₁ h₀) t := by
      intro t ht
      exact hZ_k_deriv t ht
    have h_t1_le_h0 : t₁ ≤ h₀ := by
      change h₀ - (k : ℝ) * T ≤ h₀
      have hkT_nn : (0 : ℝ) ≤ k * T := mul_nonneg (Nat.cast_nonneg _) hT_pos.le
      linarith
    have h_ht1m_le_t1 : t₁ - T ≤ t₁ := by linarith [hT_pos]
    have h_glued :=
      hasDerivWithinAt_glue_Icc_at_pt (f := Z_pic) (g := Z_k) (A := A)
        (α := t₁ - T) (t₁ := t₁) (β := h₀) h_ht1m_le_t1 h_t1_le_h0
        h_pic_left h_next_deriv h_match
    set Z : ℝ → G := fun t => if t ≤ t₁ then Z_pic t else Z_k t with hZ_def
    obtain ⟨hZ_t1, hZ_deriv⟩ := h_glued
    have hZ_init : Z h₀ = Y₀ := by
      by_cases h : h₀ ≤ t₁
      · have h_eq : h₀ = t₁ := le_antisymm h h_t1_le_h0
        have h_match' : Z_pic t₁ = Y₀ := by rw [hY_c_def] at hZ_pic_init
                                            rw [hZ_pic_init, ← h_eq, hZ_k_init]
        simp only [Z, h, ↓reduceIte]
        rw [h_eq]; exact h_match'
      · rw [not_le] at h
        simp only [Z, not_le.mpr h, ↓reduceIte, hZ_k_init]
    have h_dom_cast : h₀ - (↑(k + 1) : ℝ) * T = t₁ - T := by
      rw [ht₁_def]; push_cast; ring
    refine ⟨Z, hZ_init, fun t ht => ?_⟩
    have ht_cast : t ∈ Icc (t₁ - T) h₀ := by
      rcases ht with ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rw [h_dom_cast] at h1; exact h1
    have hd := hZ_deriv t ht_cast
    have hset_eq : Icc (t₁ - T) h₀ = Icc (h₀ - (↑(k + 1) : ℝ) * T) h₀ := by
      rw [h_dom_cast]
    rw [hset_eq] at hd
    exact hd

/-- **Solution on an arbitrary closed sub-interval** `Icc α β ⊂ Ioo a b`,
constructed by combining `exists_linearODE_solution_left_iterated` (leftward
from `h₀`) and `exists_linearODE_solution_right_iterated` (rightward from
`h₀`) and patching at `h₀`. -/
private theorem exists_linearODE_solution_on_Icc_subset
    {A : ℝ → (G →L[ℝ] G)} {a b α β h₀ : ℝ}
    (hα_lt : a < α) (hβ_lt : β < b)
    (hα_le : α ≤ h₀) (hβ_ge : h₀ ≤ β)
    (hA_cont : ContinuousOn A (Ioo a b))
    (Y₀ : G) :
    ∃ Z : ℝ → G, Z h₀ = Y₀ ∧
      ∀ t ∈ Icc α β, HasDerivWithinAt Z (A t (Z t)) (Icc α β) t := by
  set α'' : ℝ := (a + α) / 2 with hα''_def
  set β'' : ℝ := (β + b) / 2 with hβ''_def
  have hα''_lt : a < α'' := by rw [hα''_def]; linarith
  have hα''_le_α : α'' < α := by rw [hα''_def]; linarith
  have hβ''_lt : β'' < b := by rw [hβ''_def]; linarith
  have hβ''_ge_β : β < β'' := by rw [hβ''_def]; linarith
  have h_subset : Icc α'' β'' ⊆ Ioo a b := fun s hs =>
    ⟨lt_of_lt_of_le hα''_lt hs.1, lt_of_le_of_lt hs.2 hβ''_lt⟩
  have hα''_le : α'' ≤ β'' := by linarith [hα_le.trans hβ_ge]
  have hα''_lt_β'' : α'' < β'' := by linarith [hα_le.trans hβ_ge]
  have hcont' : ContinuousOn A (Icc α'' β'') := hA_cont.mono h_subset
  have hcont_norm : ContinuousOn (fun t => ‖A t‖) (Icc α'' β'') :=
    continuous_norm.comp_continuousOn hcont'
  have hcpt : IsCompact (Icc α'' β'') := isCompact_Icc
  have hne : (Icc α'' β'').Nonempty := ⟨α'', left_mem_Icc.mpr hα''_le⟩
  rcases hcpt.exists_isMaxOn hne hcont_norm with ⟨τ_max, _, hτ_max⟩
  set M : ℝ := ‖A τ_max‖ with hM_def
  have hM_nn : 0 ≤ M := norm_nonneg _
  have hM_bd : ∀ t ∈ Icc α'' β'', ‖A t‖ ≤ M := fun t ht => hτ_max ht
  set T : ℝ := 1 / (2 * (M + 1)) with hT_def
  have hT_pos : 0 < T := by
    rw [hT_def]; positivity
  have hMT : M * T < 1 := by
    have h_denom_pos : 0 < 2 * (M + 1) := by positivity
    have hT_eq : T = 1 / (2 * (M + 1)) := hT_def
    rw [hT_eq]
    have : M * (1 / (2 * (M + 1))) = M / (2 * (M + 1)) := by ring
    rw [this, div_lt_one h_denom_pos]
    have h_M_le_M1 : M ≤ M + 1 := by linarith
    calc M = M * 1 := (mul_one _).symm
      _ ≤ (M + 1) * 1 := mul_le_mul_of_nonneg_right h_M_le_M1 zero_le_one
      _ < 2 * (M + 1) := by linarith
  set δ_R : ℝ := (β'' - β) / 2 with hδ_R_def
  set δ_L : ℝ := (α - α'') / 2 with hδ_L_def
  have hδ_R_pos : 0 < δ_R := by rw [hδ_R_def]; linarith
  have hδ_L_pos : 0 < δ_L := by rw [hδ_L_def]; linarith
  set T' : ℝ := min T (min δ_R δ_L) with hT'_def
  have hT'_pos : 0 < T' := by
    rw [hT'_def]; exact lt_min hT_pos (lt_min hδ_R_pos hδ_L_pos)
  have hT'_le_T : T' ≤ T := by rw [hT'_def]; exact min_le_left _ _
  have hT'_le_δ_R : T' ≤ δ_R := by
    rw [hT'_def]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hT'_le_δ_L : T' ≤ δ_L := by
    rw [hT'_def]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hMT' : M * T' < 1 := by
    have : M * T' ≤ M * T := mul_le_mul_of_nonneg_left hT'_le_T hM_nn
    linarith
  set B_R : ℝ := β - h₀ with hB_R_def
  set B_L : ℝ := h₀ - α with hB_L_def
  have hB_R_nn : 0 ≤ B_R := by rw [hB_R_def]; linarith
  have hB_L_nn : 0 ≤ B_L := by rw [hB_L_def]; linarith
  set n_R : ℕ := ⌈B_R / T'⌉₊ with hn_R_def
  have hn_R_bound : B_R ≤ (n_R : ℝ) * T' := by
    rw [hn_R_def]
    have := Nat.le_ceil (B_R / T')
    have h_div : B_R / T' * T' = B_R := by
      field_simp
    calc B_R = B_R / T' * T' := h_div.symm
      _ ≤ (⌈B_R / T'⌉₊ : ℝ) * T' := mul_le_mul_of_nonneg_right this hT'_pos.le
  have hn_R_step_bound : (n_R : ℝ) * T' ≤ B_R + T' := by
    rw [hn_R_def]
    have hceil := Nat.ceil_lt_add_one (a := B_R / T') (div_nonneg hB_R_nn hT'_pos.le)
    have : (⌈B_R / T'⌉₊ : ℝ) ≤ B_R / T' + 1 := le_of_lt hceil
    calc (⌈B_R / T'⌉₊ : ℝ) * T' ≤ (B_R / T' + 1) * T' :=
          mul_le_mul_of_nonneg_right this hT'_pos.le
      _ = B_R / T' * T' + T' := by ring
      _ = B_R + T' := by field_simp
  set n_L : ℕ := ⌈B_L / T'⌉₊ with hn_L_def
  have hn_L_bound : B_L ≤ (n_L : ℝ) * T' := by
    rw [hn_L_def]
    have := Nat.le_ceil (B_L / T')
    have h_div : B_L / T' * T' = B_L := by field_simp
    calc B_L = B_L / T' * T' := h_div.symm
      _ ≤ (⌈B_L / T'⌉₊ : ℝ) * T' := mul_le_mul_of_nonneg_right this hT'_pos.le
  have hn_L_step_bound : (n_L : ℝ) * T' ≤ B_L + T' := by
    rw [hn_L_def]
    have hceil := Nat.ceil_lt_add_one (a := B_L / T') (div_nonneg hB_L_nn hT'_pos.le)
    have : (⌈B_L / T'⌉₊ : ℝ) ≤ B_L / T' + 1 := le_of_lt hceil
    calc (⌈B_L / T'⌉₊ : ℝ) * T' ≤ (B_L / T' + 1) * T' :=
          mul_le_mul_of_nonneg_right this hT'_pos.le
      _ = B_L / T' * T' + T' := by ring
      _ = B_L + T' := by field_simp
  have h_right_end : h₀ + (n_R : ℝ) * T' + T' ≤ β'' := by
    have : (n_R : ℝ) * T' + T' ≤ B_R + 2 * T' := by linarith
    have h1 : h₀ + (B_R + 2 * T') = β + 2 * T' := by rw [hB_R_def]; ring
    have h2 : β + 2 * T' ≤ β + 2 * δ_R := by linarith
    have h3 : β + 2 * δ_R = β'' := by rw [hδ_R_def]; ring
    linarith
  have h_left_end : α'' ≤ h₀ - (n_L : ℝ) * T' - T' := by
    have h1 : (n_L : ℝ) * T' + T' ≤ B_L + 2 * T' := by linarith
    have h2 : h₀ - (B_L + 2 * T') = α - 2 * T' := by rw [hB_L_def]; ring
    have h3 : α - 2 * T' ≥ α - 2 * δ_L := by linarith
    have h4 : α - 2 * δ_L = α'' := by rw [hδ_L_def]; ring
    linarith
  have h_R_sub_α'β'' : Icc (h₀ - T') (h₀ + (n_R : ℝ) * T' + T') ⊆ Icc α'' β'' := by
    intro s hs
    refine ⟨?_, ?_⟩
    · have : α'' ≤ h₀ - T' := by
        have hL_step : h₀ - (n_L : ℝ) * T' - T' ≤ h₀ - T' := by
          have : (0 : ℝ) ≤ (n_L : ℝ) * T' := by positivity
          linarith
        linarith
      linarith [hs.1]
    · linarith [hs.2, h_right_end]
  have hA_cont_R : ContinuousOn A (Icc (h₀ - T') (h₀ + (n_R : ℝ) * T' + T')) :=
    hcont'.mono h_R_sub_α'β''
  have hA_bd_R : ∀ t ∈ Icc (h₀ - T') (h₀ + (n_R : ℝ) * T' + T'), ‖A t‖ ≤ M :=
    fun t ht => hM_bd t (h_R_sub_α'β'' ht)
  obtain ⟨Z_R, hZ_R_init, hZ_R_deriv⟩ :=
    exists_linearODE_solution_right_iterated (A := A) (h₀ := h₀) (M := M) (T := T')
      (B := (n_R : ℝ) * T') hT'_pos hM_nn hMT' hA_cont_R hA_bd_R Y₀ n_R le_rfl
  have h_L_sub_α'β'' : Icc (h₀ - (n_L : ℝ) * T' - T') (h₀ + T') ⊆ Icc α'' β'' := by
    intro s hs
    refine ⟨?_, ?_⟩
    · linarith [hs.1, h_left_end]
    · have : h₀ + T' ≤ β'' := by
        have hR_step : h₀ + T' ≤ h₀ + (n_R : ℝ) * T' + T' := by
          have : (0 : ℝ) ≤ (n_R : ℝ) * T' := by positivity
          linarith
        linarith
      linarith [hs.2]
  have hA_cont_L : ContinuousOn A (Icc (h₀ - (n_L : ℝ) * T' - T') (h₀ + T')) :=
    hcont'.mono h_L_sub_α'β''
  have hA_bd_L : ∀ t ∈ Icc (h₀ - (n_L : ℝ) * T' - T') (h₀ + T'), ‖A t‖ ≤ M :=
    fun t ht => hM_bd t (h_L_sub_α'β'' ht)
  obtain ⟨Z_L, hZ_L_init, hZ_L_deriv⟩ :=
    exists_linearODE_solution_left_iterated (A := A) (h₀ := h₀) (M := M) (T := T')
      (B := (n_L : ℝ) * T') hT'_pos hM_nn hMT' hA_cont_L hA_bd_L Y₀ n_L le_rfl
  have h_match : Z_L h₀ = Z_R h₀ := by rw [hZ_L_init, hZ_R_init]
  have h_α_ge_L : h₀ - (n_L : ℝ) * T' ≤ h₀ := by
    have h : (0 : ℝ) ≤ (n_L : ℝ) * T' := by positivity
    linarith
  have h_R_ge_β : h₀ ≤ h₀ + (n_R : ℝ) * T' := by
    have h : (0 : ℝ) ≤ (n_R : ℝ) * T' := by positivity
    linarith
  have h_glued := hasDerivWithinAt_glue_Icc_at_pt
    (f := Z_L) (g := Z_R) (A := A)
    (α := h₀ - (n_L : ℝ) * T') (t₁ := h₀) (β := h₀ + (n_R : ℝ) * T')
    h_α_ge_L h_R_ge_β hZ_L_deriv hZ_R_deriv h_match
  set Z : ℝ → G := fun t => if t ≤ h₀ then Z_L t else Z_R t with hZ_def
  obtain ⟨hZ_h0, hZ_LR_deriv⟩ := h_glued
  have hZ_init : Z h₀ = Y₀ := by
    simp only [Z, le_refl, ↓reduceIte, hZ_L_init]
  refine ⟨Z, hZ_init, ?_⟩
  have h_α_lb : h₀ - (n_L : ℝ) * T' ≤ α := by
    have : (n_L : ℝ) * T' ≥ B_L := hn_L_bound
    have hα_eq : h₀ - B_L = α := by rw [hB_L_def]; ring
    linarith
  have h_β_ub : β ≤ h₀ + (n_R : ℝ) * T' := by
    have : (n_R : ℝ) * T' ≥ B_R := hn_R_bound
    have hβ_eq : h₀ + B_R = β := by rw [hB_R_def]; ring
    linarith
  have h_Icc_sub : Icc α β ⊆ Icc (h₀ - (n_L : ℝ) * T') (h₀ + (n_R : ℝ) * T') := fun s hs =>
    ⟨le_trans h_α_lb hs.1, le_trans hs.2 h_β_ub⟩
  intro t ht
  have ht' : t ∈ Icc (h₀ - (n_L : ℝ) * T') (h₀ + (n_R : ℝ) * T') := h_Icc_sub ht
  have hd := hZ_LR_deriv t ht'
  exact hd.mono h_Icc_sub

/-- **Monotonic sub-interval sequence** `αₙ ↘ a`, `βₙ ↗ b` strictly inside
`Ioo a b`, with `h₀ ∈ Ioo (αₙ n) (βₙ n)` for every `n`. -/
private def subIntervalSeq (a h₀ b : ℝ) (n : ℕ) : ℝ × ℝ :=
  (a + (h₀ - a) / ((n : ℝ) + 2), b - (b - h₀) / ((n : ℝ) + 2))

/-- **Discharge of the per-parameter existence predicate** from joint
continuity of `A` on `U ×ˢ Ioo a b`.

For any `x` in the open parameter set `U` and any `h₀ ∈ Ioo a b`, the linear
ODE `Z'(t) = A(x, t) Z(t),  Z(h₀) = Z₀(x)` has a solution on `Ioo a b`. -/
theorem hasLinearODESolution_of_continuousOn
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {A : F → ℝ → (G →L[ℝ] G)} {h₀ : ℝ} {Z₀ : F → G}
    {a b : ℝ} (_hab_lt : a < b) (h₀_mem : h₀ ∈ Set.Ioo a b)
    {U : Set F} (_hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b))
    {x : F} (hx : x ∈ U) :
    HasLinearODESolution A a b h₀ Z₀ x := by
  classical
  have hA_x_cont : ContinuousOn (A x) (Ioo a b) :=
    ContinuousOn.uncurry_left (a := x) (sα := U) (sβ := Ioo a b) hx hA_cont
  have hh0a : a < h₀ := h₀_mem.1
  have hh0b : h₀ < b := h₀_mem.2
  let α : ℕ → ℝ := fun n => a + (h₀ - a) / ((n : ℝ) + 2)
  let β : ℕ → ℝ := fun n => b - (b - h₀) / ((n : ℝ) + 2)
  have hden : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 2 := fun n => by positivity
  have hden_ge1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 2 := fun n => by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg _; linarith
  have hα_lt_a : ∀ n, a < α n := fun n => by
    change a < a + (h₀ - a) / ((n : ℝ) + 2)
    have h : 0 < (h₀ - a) / ((n : ℝ) + 2) := div_pos (by linarith) (hden n)
    linarith
  have hβ_lt_b : ∀ n, β n < b := fun n => by
    change b - (b - h₀) / ((n : ℝ) + 2) < b
    have h : 0 < (b - h₀) / ((n : ℝ) + 2) := div_pos (by linarith) (hden n)
    linarith
  have hα_le_h0 : ∀ n, α n ≤ h₀ := fun n => by
    change a + (h₀ - a) / ((n : ℝ) + 2) ≤ h₀
    have h : (h₀ - a) / ((n : ℝ) + 2) ≤ h₀ - a := by
      rw [div_le_iff₀ (hden n)]
      calc h₀ - a = (h₀ - a) * 1 := (mul_one _).symm
        _ ≤ (h₀ - a) * ((n : ℝ) + 2) :=
            mul_le_mul_of_nonneg_left (hden_ge1 n) (by linarith)
    linarith
  have hh0_le_β : ∀ n, h₀ ≤ β n := fun n => by
    change h₀ ≤ b - (b - h₀) / ((n : ℝ) + 2)
    have h : (b - h₀) / ((n : ℝ) + 2) ≤ b - h₀ := by
      rw [div_le_iff₀ (hden n)]
      calc b - h₀ = (b - h₀) * 1 := (mul_one _).symm
        _ ≤ (b - h₀) * ((n : ℝ) + 2) :=
            mul_le_mul_of_nonneg_left (hden_ge1 n) (by linarith)
    linarith
  have h_exists : ∀ n : ℕ, ∃ Z : ℝ → G, Z h₀ = Z₀ x ∧
      ∀ t ∈ Icc (α n) (β n), HasDerivWithinAt Z (A x t (Z t)) (Icc (α n) (β n)) t :=
    fun n => exists_linearODE_solution_on_Icc_subset
      (hα_lt_a n) (hβ_lt_b n) (hα_le_h0 n) (hh0_le_β n) hA_x_cont (Z₀ x)
  choose Zn hZn_init hZn_deriv using h_exists
  have hα_mono : ∀ k₁ k₂, k₁ ≤ k₂ → α k₂ ≤ α k₁ := by
    intro k₁ k₂ hk
    change a + (h₀ - a) / ((k₂ : ℝ) + 2) ≤ a + (h₀ - a) / ((k₁ : ℝ) + 2)
    have h_le : (k₁ : ℝ) + 2 ≤ (k₂ : ℝ) + 2 := by exact_mod_cast by linarith
    have hd2 : (h₀ - a) / ((k₂ : ℝ) + 2) ≤ (h₀ - a) / ((k₁ : ℝ) + 2) :=
      div_le_div_of_nonneg_left (by linarith) (hden k₁) h_le
    linarith
  have hβ_mono : ∀ k₁ k₂, k₁ ≤ k₂ → β k₁ ≤ β k₂ := by
    intro k₁ k₂ hk
    change b - (b - h₀) / ((k₁ : ℝ) + 2) ≤ b - (b - h₀) / ((k₂ : ℝ) + 2)
    have h_le : (k₁ : ℝ) + 2 ≤ (k₂ : ℝ) + 2 := by exact_mod_cast by linarith
    have hd2 : (b - h₀) / ((k₂ : ℝ) + 2) ≤ (b - h₀) / ((k₁ : ℝ) + 2) :=
      div_le_div_of_nonneg_left (by linarith) (hden k₁) h_le
    linarith
  have h_unique : ∀ n m : ℕ, ∀ s ∈ Ioo (α (min n m)) (β (min n m)),
      Zn n s = Zn m s := by
    intro n m s hs_min
    set N := min n m
    have hαn_le : α n ≤ α N := hα_mono N n (min_le_left _ _)
    have hαm_le : α m ≤ α N := hα_mono N m (min_le_right _ _)
    have hβn_ge : β N ≤ β n := hβ_mono N n (min_le_left _ _)
    have hβm_ge : β N ≤ β m := hβ_mono N m (min_le_right _ _)
    have h_subset_n : Ioo (α N) (β N) ⊆ Icc (α n) (β n) := fun u hu =>
      ⟨le_of_lt (lt_of_le_of_lt hαn_le hu.1), le_of_lt (lt_of_lt_of_le hu.2 hβn_ge)⟩
    have h_subset_m : Ioo (α N) (β N) ⊆ Icc (α m) (β m) := fun u hu =>
      ⟨le_of_lt (lt_of_le_of_lt hαm_le hu.1), le_of_lt (lt_of_lt_of_le hu.2 hβm_ge)⟩
    have h_h0_in_N : h₀ ∈ Ioo (α N) (β N) := by
      refine ⟨?_, ?_⟩
      · change a + (h₀ - a) / ((N : ℝ) + 2) < h₀
        have h_pos : 0 < (h₀ - a) / ((N : ℝ) + 2) :=
          div_pos (by linarith) (hden N)
        have h_lt : (h₀ - a) / ((N : ℝ) + 2) < h₀ - a := by
          have h_den_gt1 : (1 : ℝ) < (N : ℝ) + 2 := by
            have : (0 : ℝ) ≤ N := Nat.cast_nonneg _; linarith
          have h_h0a_pos : 0 < h₀ - a := by linarith
          calc (h₀ - a) / ((N : ℝ) + 2)
              < (h₀ - a) / 1 := by
                apply div_lt_div_of_pos_left h_h0a_pos (by norm_num) h_den_gt1
            _ = h₀ - a := by norm_num
        linarith
      · change h₀ < b - (b - h₀) / ((N : ℝ) + 2)
        have h_pos : 0 < (b - h₀) / ((N : ℝ) + 2) :=
          div_pos (by linarith) (hden N)
        have h_lt : (b - h₀) / ((N : ℝ) + 2) < b - h₀ := by
          have h_den_gt1 : (1 : ℝ) < (N : ℝ) + 2 := by
            have : (0 : ℝ) ≤ N := Nat.cast_nonneg _; linarith
          have h_bh0_pos : 0 < b - h₀ := by linarith
          calc (b - h₀) / ((N : ℝ) + 2)
              < (b - h₀) / 1 := by
                apply div_lt_div_of_pos_left h_bh0_pos (by norm_num) h_den_gt1
            _ = b - h₀ := by norm_num
        linarith
    have h_subN_to_Ioo : Ioo (α N) (β N) ⊆ Ioo a b := fun u hu =>
      ⟨lt_of_lt_of_le (hα_lt_a N) hu.1.le, lt_of_le_of_lt hu.2.le (hβ_lt_b N)⟩
    have hA_cont_N : ContinuousOn (A x) (Ioo (α N) (β N)) :=
      hA_x_cont.mono h_subN_to_Ioo
    have h_Zn_deriv_open : ∀ u ∈ Ioo (α N) (β N), HasDerivAt (Zn n) (A x u (Zn n u)) u := by
      intro u hu
      have hd := hZn_deriv n u (h_subset_n hu)
      exact hd.hasDerivAt
        (Icc_mem_nhds (lt_of_le_of_lt hαn_le hu.1) (lt_of_lt_of_le hu.2 hβn_ge))
    have h_Zm_deriv_open : ∀ u ∈ Ioo (α N) (β N), HasDerivAt (Zn m) (A x u (Zn m u)) u := by
      intro u hu
      have hd := hZn_deriv m u (h_subset_m hu)
      exact hd.hasDerivAt
        (Icc_mem_nhds (lt_of_le_of_lt hαm_le hu.1) (lt_of_lt_of_le hu.2 hβm_ge))
    have h_match : Zn n h₀ = Zn m h₀ := by rw [hZn_init, hZn_init]
    exact linearODE_unique_on_Ioo (A := A x) h_h0_in_N hA_cont_N
      h_Zn_deriv_open h_Zm_deriv_open h_match hs_min
  have h_exhaust : ∀ t ∈ Ioo a b, ∃ n : ℕ, t ∈ Ioo (α n) (β n) := by
    intro t ht
    have hta : 0 < t - a := by linarith [ht.1]
    have htb : 0 < b - t := by linarith [ht.2]
    obtain ⟨N, hN⟩ :=
      exists_nat_gt (max ((h₀ - a) / (t - a)) ((b - h₀) / (b - t)))
    have hN1 : (h₀ - a) / (t - a) < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
    have hN2 : (b - h₀) / (b - t) < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
    refine ⟨N, ?_, ?_⟩
    · change a + (h₀ - a) / ((N : ℝ) + 2) < t
      have h_den : (0 : ℝ) < (N : ℝ) + 2 := by positivity
      have h_key : (h₀ - a) / ((N : ℝ) + 2) < t - a := by
        rw [div_lt_iff₀ h_den]
        have h_eq : (h₀ - a) = (h₀ - a) / (t - a) * (t - a) := by field_simp
        rw [h_eq]
        rw [mul_comm (t - a) ((N : ℝ) + 2)]
        calc (h₀ - a) / (t - a) * (t - a)
            < (N : ℝ) * (t - a) := mul_lt_mul_of_pos_right hN1 hta
          _ ≤ ((N : ℝ) + 2) * (t - a) :=
              mul_le_mul_of_nonneg_right (by linarith) hta.le
      linarith
    · change t < b - (b - h₀) / ((N : ℝ) + 2)
      have h_den : (0 : ℝ) < (N : ℝ) + 2 := by positivity
      have h_key : (b - h₀) / ((N : ℝ) + 2) < b - t := by
        rw [div_lt_iff₀ h_den]
        have h_eq : (b - h₀) = (b - h₀) / (b - t) * (b - t) := by field_simp
        rw [h_eq]
        rw [mul_comm (b - t) ((N : ℝ) + 2)]
        calc (b - h₀) / (b - t) * (b - t)
            < (N : ℝ) * (b - t) := mul_lt_mul_of_pos_right hN2 htb
          _ ≤ ((N : ℝ) + 2) * (b - t) :=
              mul_le_mul_of_nonneg_right (by linarith) htb.le
      linarith
  let Z : ℝ → G := fun t =>
    if h : ∃ n, t ∈ Ioo (α n) (β n) then Zn (Nat.find h) t else Z₀ x
  refine ⟨Z, ?_, ?_⟩
  · have h_h0_mem : ∃ n, h₀ ∈ Ioo (α n) (β n) := by
      refine ⟨0, ?_, ?_⟩
      · change a + (h₀ - a) / ((0 : ℕ) + 2 : ℝ) < h₀
        have : 0 < (h₀ - a) / ((0 : ℕ) + 2 : ℝ) :=
          div_pos (by linarith) (by norm_num)
        linarith
      · change h₀ < b - (b - h₀) / ((0 : ℕ) + 2 : ℝ)
        have : 0 < (b - h₀) / ((0 : ℕ) + 2 : ℝ) :=
          div_pos (by linarith) (by norm_num)
        linarith
    change (if h : ∃ n, h₀ ∈ Ioo (α n) (β n) then Zn (Nat.find h) h₀ else Z₀ x) = Z₀ x
    rw [dif_pos h_h0_mem]
    exact hZn_init _
  · intro t ht
    obtain ⟨N, hN⟩ := h_exhaust t ht
    have h_ex_t : ∃ n, t ∈ Ioo (α n) (β n) := ⟨N, hN⟩
    let N₀ := Nat.find h_ex_t
    have hN0_spec : t ∈ Ioo (α N₀) (β N₀) := Nat.find_spec h_ex_t
    have h_in_Icc : t ∈ Icc (α N₀) (β N₀) := ⟨hN0_spec.1.le, hN0_spec.2.le⟩
    have h_nhd : Icc (α N₀) (β N₀) ∈ 𝓝 t := Icc_mem_nhds hN0_spec.1 hN0_spec.2
    have hd_within := hZn_deriv N₀ t h_in_Icc
    have hd : HasDerivAt (Zn N₀) (A x t (Zn N₀ t)) t := hd_within.hasDerivAt h_nhd
    have h_Z_eq_eventually : Z =ᶠ[𝓝 t] Zn N₀ := by
      have h_nhd_open : Ioo (α N₀) (β N₀) ∈ 𝓝 t := Ioo_mem_nhds hN0_spec.1 hN0_spec.2
      filter_upwards [h_nhd_open] with s hs
      have h_ex_s : ∃ n, s ∈ Ioo (α n) (β n) := ⟨N₀, hs⟩
      change (if h : ∃ n, s ∈ Ioo (α n) (β n) then Zn (Nat.find h) s else Z₀ x) = Zn N₀ s
      rw [dif_pos h_ex_s]
      let M_s := Nat.find h_ex_s
      have hMs_spec : s ∈ Ioo (α M_s) (β M_s) := Nat.find_spec h_ex_s
      apply h_unique M_s N₀ s
      refine ⟨?_, ?_⟩
      · rcases le_total M_s N₀ with h | h
        · rw [min_eq_left h]; exact hMs_spec.1
        · rw [min_eq_right h]; exact hs.1
      · rcases le_total M_s N₀ with h | h
        · rw [min_eq_left h]; exact hMs_spec.2
        · rw [min_eq_right h]; exact hs.2
    have h_Z_t_eq : Z t = Zn N₀ t := h_Z_eq_eventually.eq_of_nhds
    rw [h_Z_t_eq]
    exact hd.congr_of_eventuallyEq h_Z_eq_eventually

/-- **Wrapped ODE clause** for `linearODESolution`.

Combines `hasLinearODESolution_of_continuousOn` (existence) and
`linearODESolution_hasDerivAt_of_hasSolution` (extraction of the ODE clause)
to give the ODE clause directly from joint continuity. -/
theorem linearODESolution_hasDerivAt
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {A : F → ℝ → (G →L[ℝ] G)} {h₀ : ℝ} {Z₀ : F → G}
    {a b : ℝ} (hab_lt : a < b) (h₀_mem : h₀ ∈ Set.Ioo a b)
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b))
    {x : F} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Set.Ioo a b) :
    HasDerivAt (linearODESolution A a b h₀ Z₀ x ·)
      (A x t (linearODESolution A a b h₀ Z₀ x t)) t :=
  linearODESolution_hasDerivAt_of_hasSolution A a b h₀ Z₀
    (hasLinearODESolution_of_continuousOn hab_lt h₀_mem hU hA_cont hx) ht

end GlobalExistence

section JointContinuity

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- **A priori growth bound for a linear ODE on a closed sub-interval**.

If `Z` solves `Z' t = A t (Z t)` on `Ioo a b` and `‖A t‖ ≤ M` on `Icc α β ⊂ Ioo a b`,
then for any base time `c ∈ Icc α β` and any `t ∈ Icc α β`,
`‖Z t‖ ≤ ‖Z c‖ · exp (M · (β - α))`. -/
private theorem linearODE_apriori_bound
    {A : ℝ → (G →L[ℝ] G)} {a b α β c M : ℝ}
    (_hαβ : α ≤ β) (hα_lt : a < α) (hβ_lt : β < b)
    (hc_mem : c ∈ Icc α β) (hM_nn : 0 ≤ M)
    (hA_bd : ∀ s ∈ Icc α β, ‖A s‖ ≤ M)
    {Z : ℝ → G} (hZ_deriv : ∀ t ∈ Ioo a b, HasDerivAt Z (A t (Z t)) t)
    (t : ℝ) (ht : t ∈ Icc α β) :
    ‖Z t‖ ≤ ‖Z c‖ * Real.exp (M * (β - α)) := by
  have hsub : Icc α β ⊆ Ioo a b := fun s hs =>
    ⟨lt_of_lt_of_le hα_lt hs.1, lt_of_le_of_lt hs.2 hβ_lt⟩
  have hZ_cont : ContinuousOn Z (Icc α β) := fun s hs =>
    ((hZ_deriv s (hsub hs)).continuousAt).continuousWithinAt
  have hZ_deriv_within_right : ∀ s ∈ Icc α β, HasDerivWithinAt Z (A s (Z s)) (Ici s) s :=
    fun s hs => ((hZ_deriv s (hsub hs)).hasDerivWithinAt)
  have hZ'_bound : ∀ s ∈ Icc α β, ‖A s (Z s)‖ ≤ M * ‖Z s‖ + 0 := by
    intro s hs
    have h1 : ‖A s (Z s)‖ ≤ ‖A s‖ * ‖Z s‖ := (A s).le_opNorm (Z s)
    have h2 : ‖A s‖ * ‖Z s‖ ≤ M * ‖Z s‖ :=
      mul_le_mul_of_nonneg_right (hA_bd s hs) (norm_nonneg _)
    linarith
  rcases le_total c t with hct | htc
  · have hsub' : Icc c t ⊆ Icc α β := fun s hs =>
      ⟨le_trans hc_mem.1 hs.1, le_trans hs.2 ht.2⟩
    have hZ_cont_ct : ContinuousOn Z (Icc c t) := hZ_cont.mono hsub'
    have hZ_deriv_within_right_ct :
        ∀ s ∈ Ico c t, HasDerivWithinAt Z (A s (Z s)) (Ici s) s :=
      fun s hs => hZ_deriv_within_right s (hsub' (Ico_subset_Icc_self hs))
    have hZ'_bound_ct : ∀ s ∈ Ico c t, ‖A s (Z s)‖ ≤ M * ‖Z s‖ + 0 :=
      fun s hs => hZ'_bound s (hsub' (Ico_subset_Icc_self hs))
    have habs := norm_le_gronwallBound_of_norm_deriv_right_le hZ_cont_ct
      hZ_deriv_within_right_ct (le_refl _) hZ'_bound_ct t (right_mem_Icc.mpr hct)
    rw [gronwallBound_ε0] at habs
    have h_mono : M * (t - c) ≤ M * (β - α) := by
      apply mul_le_mul_of_nonneg_left _ hM_nn
      linarith [ht.2, hc_mem.1]
    have h_exp_mono : Real.exp (M * (t - c)) ≤ Real.exp (M * (β - α)) :=
      Real.exp_le_exp.mpr h_mono
    calc ‖Z t‖ ≤ ‖Z c‖ * Real.exp (M * (t - c)) := habs
      _ ≤ ‖Z c‖ * Real.exp (M * (β - α)) :=
          mul_le_mul_of_nonneg_left h_exp_mono (norm_nonneg _)
  · set W : ℝ → G := fun s => Z (2 * c - s) with hW_def
    have h_t_le_c : t ≤ c := htc
    have h_2ctmt_ge_c : c ≤ 2 * c - t := by linarith
    have h_dom_sub : ∀ s ∈ Icc c (2 * c - t), 2 * c - s ∈ Icc α β := by
      intro s hs
      refine ⟨?_, ?_⟩
      · have h_eq : 2 * c - (2 * c - t) = t := by ring
        linarith [ht.1, hs.2]
      · have h_eq : 2 * c - c = c := by ring
        linarith [hc_mem.2, hs.1]
    have hW_cont : ContinuousOn W (Icc c (2 * c - t)) := by
      apply ContinuousOn.comp hZ_cont (s := Icc c (2 * c - t))
        (t := Icc α β) (f := fun s => 2 * c - s)
      · exact (continuous_const.sub continuous_id).continuousOn
      · exact h_dom_sub
    have hW_deriv : ∀ s ∈ Icc c (2 * c - t),
        HasDerivAt W (-(A (2 * c - s) (Z (2 * c - s)))) s := by
      intro s hs
      have hs_mem : (2 * c - s) ∈ Ioo a b := hsub (h_dom_sub s hs)
      have hd : HasDerivAt Z (A (2 * c - s) (Z (2 * c - s))) (2 * c - s) :=
        hZ_deriv (2 * c - s) hs_mem
      have h_chain : HasDerivAt (fun s => 2 * c - s) (-1 : ℝ) s := by
        simpa using ((hasDerivAt_const s (2 * c)).sub (hasDerivAt_id s))
      have hd' : HasDerivAt (Z ∘ (fun s => 2 * c - s))
          ((-1 : ℝ) • A (2 * c - s) (Z (2 * c - s))) s := hd.scomp s h_chain
      have hZ_eq : (Z ∘ (fun s => 2 * c - s)) = W := rfl
      rw [hZ_eq] at hd'
      have h_smul_eq : ((-1 : ℝ) • A (2 * c - s) (Z (2 * c - s)) : G) =
          -(A (2 * c - s) (Z (2 * c - s))) := by
        rw [neg_one_smul]
      rw [h_smul_eq] at hd'
      exact hd'
    have hW_deriv_within_right :
        ∀ s ∈ Icc c (2 * c - t),
          HasDerivWithinAt W (-(A (2 * c - s) (Z (2 * c - s)))) (Ici s) s :=
      fun s hs => (hW_deriv s hs).hasDerivWithinAt
    have hW'_bound : ∀ s ∈ Ico c (2 * c - t),
        ‖-(A (2 * c - s) (Z (2 * c - s)))‖ ≤ M * ‖W s‖ + 0 := by
      intro s hs
      have h_in : 2 * c - s ∈ Icc α β := h_dom_sub s (Ico_subset_Icc_self hs)
      have h1 : ‖A (2 * c - s) (Z (2 * c - s))‖ ≤ ‖A (2 * c - s)‖ * ‖Z (2 * c - s)‖ :=
        (A _).le_opNorm _
      have h2 : ‖A (2 * c - s)‖ * ‖Z (2 * c - s)‖ ≤ M * ‖Z (2 * c - s)‖ :=
        mul_le_mul_of_nonneg_right (hA_bd _ h_in) (norm_nonneg _)
      have hWs_eq : W s = Z (2 * c - s) := rfl
      rw [hWs_eq, norm_neg]
      linarith
    have hW_init : ‖W c‖ ≤ ‖Z c‖ := by
      have h_eq : W c = Z c := by
        change Z (2 * c - c) = Z c
        have : 2 * c - c = c := by ring
        rw [this]
      rw [h_eq]
    have habs := norm_le_gronwallBound_of_norm_deriv_right_le hW_cont
      (fun s hs => hW_deriv_within_right s (Ico_subset_Icc_self hs)) hW_init
      hW'_bound (2 * c - t) (right_mem_Icc.mpr h_2ctmt_ge_c)
    rw [gronwallBound_ε0] at habs
    have hW_eq_Z : W (2 * c - t) = Z t := by
      change Z (2 * c - (2 * c - t)) = Z t
      have : 2 * c - (2 * c - t) = t := by ring
      rw [this]
    rw [hW_eq_Z] at habs
    have h_sub : (2 * c - t) - c = c - t := by ring
    rw [h_sub] at habs
    have h_mono : M * (c - t) ≤ M * (β - α) := by
      apply mul_le_mul_of_nonneg_left _ hM_nn
      linarith [hc_mem.2, ht.1]
    have h_exp_mono : Real.exp (M * (c - t)) ≤ Real.exp (M * (β - α)) :=
      Real.exp_le_exp.mpr h_mono
    calc ‖Z t‖ ≤ ‖Z c‖ * Real.exp (M * (c - t)) := habs
      _ ≤ ‖Z c‖ * Real.exp (M * (β - α)) :=
          mul_le_mul_of_nonneg_left h_exp_mono (norm_nonneg _)

/-- **Forward Grönwall comparison** for linear ODEs.

If `Z₁` solves `Z₁' = A₁ Z₁` and `Z₂` solves `Z₂' = A₂ Z₂` on `Icc h₀ β`,
with `‖A₁ s‖ ≤ K` and `‖(A₂ s - A₁ s)(Z₂ s)‖ ≤ η` on `[h₀, β]`, then for
`t ∈ [h₀, β]`:
`‖Z₁ t - Z₂ t‖ ≤ gronwallBound ‖Z₁ h₀ - Z₂ h₀‖ K η (t - h₀)`. -/
theorem linearODE_gronwall_forward
    {A₁ A₂ : ℝ → (G →L[ℝ] G)} {Z₁ Z₂ : ℝ → G} {h₀ β K η : ℝ}
    (_hh₀β : h₀ ≤ β) (hK_nn : 0 ≤ K)
    (hZ₁_cont : ContinuousOn Z₁ (Icc h₀ β))
    (hZ₂_cont : ContinuousOn Z₂ (Icc h₀ β))
    (hZ₁_deriv : ∀ t ∈ Icc h₀ β, HasDerivAt Z₁ (A₁ t (Z₁ t)) t)
    (hZ₂_deriv : ∀ t ∈ Icc h₀ β, HasDerivAt Z₂ (A₂ t (Z₂ t)) t)
    (hA₁_bd : ∀ t ∈ Icc h₀ β, ‖A₁ t‖ ≤ K)
    (hdiff_bd : ∀ t ∈ Icc h₀ β, ‖(A₂ t - A₁ t) (Z₂ t)‖ ≤ η)
    (t : ℝ) (ht : t ∈ Icc h₀ β) :
    ‖Z₁ t - Z₂ t‖ ≤ gronwallBound ‖Z₁ h₀ - Z₂ h₀‖ K η (t - h₀) := by
  let v : ℝ → G → G := fun s y => A₁ s y
  let Knn : ℝ≥0 := ⟨K, hK_nn⟩
  have hv_lip : ∀ s ∈ Ico h₀ β, LipschitzOnWith Knn (v s) (univ : Set G) := by
    intro s hs
    have h_lip : LipschitzWith Knn (A₁ s) :=
      (A₁ s).lipschitzWith_of_opNorm_le (hA₁_bd s (Ico_subset_Icc_self hs))
    exact h_lip.lipschitzOnWith
  have hZ₁_deriv_right : ∀ s ∈ Ico h₀ β, HasDerivWithinAt Z₁ (A₁ s (Z₁ s)) (Ici s) s :=
    fun s hs => (hZ₁_deriv s (Ico_subset_Icc_self hs)).hasDerivWithinAt
  have hZ₂_deriv_right : ∀ s ∈ Ico h₀ β, HasDerivWithinAt Z₂ (A₂ s (Z₂ s)) (Ici s) s :=
    fun s hs => (hZ₂_deriv s (Ico_subset_Icc_self hs)).hasDerivWithinAt
  have f_bound : ∀ s ∈ Ico h₀ β, dist (A₁ s (Z₁ s)) (v s (Z₁ s)) ≤ 0 := by
    intro s _; change dist (A₁ s (Z₁ s)) (A₁ s (Z₁ s)) ≤ 0; rw [dist_self]
  have g_bound : ∀ s ∈ Ico h₀ β, dist (A₂ s (Z₂ s)) (v s (Z₂ s)) ≤ η := by
    intro s hs
    have hsmem : s ∈ Icc h₀ β := Ico_subset_Icc_self hs
    change dist (A₂ s (Z₂ s)) (A₁ s (Z₂ s)) ≤ η
    rw [dist_eq_norm]
    have h_eq : A₂ s (Z₂ s) - A₁ s (Z₂ s) = (A₂ s - A₁ s) (Z₂ s) := by
      simp [ContinuousLinearMap.sub_apply]
    rw [h_eq]
    exact hdiff_bd s hsmem
  have hres := dist_le_of_approx_trajectories_ODE_of_mem (v := v) (s := fun _ => univ)
    (K := Knn) (f := Z₁) (g := Z₂) (f' := fun s => A₁ s (Z₁ s))
    (g' := fun s => A₂ s (Z₂ s))
    (a := h₀) (b := β) (εf := 0) (εg := η) (δ := ‖Z₁ h₀ - Z₂ h₀‖)
    hv_lip hZ₁_cont hZ₁_deriv_right f_bound (fun _ _ => mem_univ _)
    hZ₂_cont hZ₂_deriv_right g_bound (fun _ _ => mem_univ _)
    (by rw [dist_eq_norm])
  have := hres t ht
  rw [dist_eq_norm] at this
  rw [zero_add] at this
  exact this

/-- **Backward Grönwall comparison** for linear ODEs (mirror of
`linearODE_gronwall_forward` via time reversal). -/
theorem linearODE_gronwall_backward
    {A₁ A₂ : ℝ → (G →L[ℝ] G)} {Z₁ Z₂ : ℝ → G} {α h₀ K η : ℝ}
    (hαh₀ : α ≤ h₀) (hK_nn : 0 ≤ K)
    (hZ₁_cont : ContinuousOn Z₁ (Icc α h₀))
    (hZ₂_cont : ContinuousOn Z₂ (Icc α h₀))
    (hZ₁_deriv : ∀ t ∈ Icc α h₀, HasDerivAt Z₁ (A₁ t (Z₁ t)) t)
    (hZ₂_deriv : ∀ t ∈ Icc α h₀, HasDerivAt Z₂ (A₂ t (Z₂ t)) t)
    (hA₁_bd : ∀ t ∈ Icc α h₀, ‖A₁ t‖ ≤ K)
    (hdiff_bd : ∀ t ∈ Icc α h₀, ‖(A₂ t - A₁ t) (Z₂ t)‖ ≤ η)
    (t : ℝ) (ht : t ∈ Icc α h₀) :
    ‖Z₁ t - Z₂ t‖ ≤ gronwallBound ‖Z₁ h₀ - Z₂ h₀‖ K η (h₀ - t) := by
  set W₁ : ℝ → G := fun s => Z₁ (2 * h₀ - s)
  set W₂ : ℝ → G := fun s => Z₂ (2 * h₀ - s)
  set B₁ : ℝ → (G →L[ℝ] G) := fun s => -A₁ (2 * h₀ - s)
  set B₂ : ℝ → (G →L[ℝ] G) := fun s => -A₂ (2 * h₀ - s)
  have h_h₀_le_2h₀mα : h₀ ≤ 2 * h₀ - α := by linarith
  have h_dom_swap : ∀ s ∈ Icc h₀ (2 * h₀ - α), 2 * h₀ - s ∈ Icc α h₀ := by
    intro s hs
    refine ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hW₁_cont : ContinuousOn W₁ (Icc h₀ (2 * h₀ - α)) := by
    apply ContinuousOn.comp hZ₁_cont (s := Icc h₀ (2 * h₀ - α))
      (t := Icc α h₀) (f := fun s => 2 * h₀ - s)
    · exact (continuous_const.sub continuous_id).continuousOn
    · exact h_dom_swap
  have hW₂_cont : ContinuousOn W₂ (Icc h₀ (2 * h₀ - α)) := by
    apply ContinuousOn.comp hZ₂_cont (s := Icc h₀ (2 * h₀ - α))
      (t := Icc α h₀) (f := fun s => 2 * h₀ - s)
    · exact (continuous_const.sub continuous_id).continuousOn
    · exact h_dom_swap
  have hW₁_deriv : ∀ s ∈ Icc h₀ (2 * h₀ - α), HasDerivAt W₁ (B₁ s (W₁ s)) s := by
    intro s hs
    have hd : HasDerivAt Z₁ (A₁ (2 * h₀ - s) (Z₁ (2 * h₀ - s))) (2 * h₀ - s) :=
      hZ₁_deriv (2 * h₀ - s) (h_dom_swap s hs)
    have h_chain : HasDerivAt (fun s => 2 * h₀ - s) (-1 : ℝ) s := by
      simpa using ((hasDerivAt_const s (2 * h₀)).sub (hasDerivAt_id s))
    have hd' : HasDerivAt (Z₁ ∘ (fun s => 2 * h₀ - s))
        ((-1 : ℝ) • A₁ (2 * h₀ - s) (Z₁ (2 * h₀ - s))) s := hd.scomp s h_chain
    have hZ₁_eq : (Z₁ ∘ (fun s => 2 * h₀ - s)) = W₁ := rfl
    rw [hZ₁_eq] at hd'
    have hW₁s_eq : W₁ s = Z₁ (2 * h₀ - s) := rfl
    have hB₁s_eq : B₁ s = -A₁ (2 * h₀ - s) := rfl
    have h_eq : ((-1 : ℝ) • A₁ (2 * h₀ - s) (Z₁ (2 * h₀ - s)) : G) = B₁ s (W₁ s) := by
      rw [hB₁s_eq, hW₁s_eq, ContinuousLinearMap.neg_apply, neg_one_smul]
    rw [h_eq] at hd'
    exact hd'
  have hW₂_deriv : ∀ s ∈ Icc h₀ (2 * h₀ - α), HasDerivAt W₂ (B₂ s (W₂ s)) s := by
    intro s hs
    have hd : HasDerivAt Z₂ (A₂ (2 * h₀ - s) (Z₂ (2 * h₀ - s))) (2 * h₀ - s) :=
      hZ₂_deriv (2 * h₀ - s) (h_dom_swap s hs)
    have h_chain : HasDerivAt (fun s => 2 * h₀ - s) (-1 : ℝ) s := by
      simpa using ((hasDerivAt_const s (2 * h₀)).sub (hasDerivAt_id s))
    have hd' : HasDerivAt (Z₂ ∘ (fun s => 2 * h₀ - s))
        ((-1 : ℝ) • A₂ (2 * h₀ - s) (Z₂ (2 * h₀ - s))) s := hd.scomp s h_chain
    have hZ₂_eq : (Z₂ ∘ (fun s => 2 * h₀ - s)) = W₂ := rfl
    rw [hZ₂_eq] at hd'
    have hW₂s_eq : W₂ s = Z₂ (2 * h₀ - s) := rfl
    have hB₂s_eq : B₂ s = -A₂ (2 * h₀ - s) := rfl
    have h_eq : ((-1 : ℝ) • A₂ (2 * h₀ - s) (Z₂ (2 * h₀ - s)) : G) = B₂ s (W₂ s) := by
      rw [hB₂s_eq, hW₂s_eq, ContinuousLinearMap.neg_apply, neg_one_smul]
    rw [h_eq] at hd'
    exact hd'
  have hB₁_bd : ∀ s ∈ Icc h₀ (2 * h₀ - α), ‖B₁ s‖ ≤ K := by
    intro s hs
    change ‖-A₁ (2 * h₀ - s)‖ ≤ K
    rw [norm_neg]
    exact hA₁_bd _ (h_dom_swap s hs)
  have hdiff_bd' : ∀ s ∈ Icc h₀ (2 * h₀ - α), ‖(B₂ s - B₁ s) (W₂ s)‖ ≤ η := by
    intro s hs
    have h_in : 2 * h₀ - s ∈ Icc α h₀ := h_dom_swap s hs
    have h_eq : B₂ s - B₁ s = -(A₂ (2 * h₀ - s) - A₁ (2 * h₀ - s)) := by
      change -A₂ (2 * h₀ - s) - (-A₁ (2 * h₀ - s)) =
        -(A₂ (2 * h₀ - s) - A₁ (2 * h₀ - s))
      abel
    rw [h_eq]
    have hW₂s : W₂ s = Z₂ (2 * h₀ - s) := rfl
    rw [hW₂s, ContinuousLinearMap.neg_apply, norm_neg]
    exact hdiff_bd _ h_in
  have hres := linearODE_gronwall_forward (A₁ := B₁) (A₂ := B₂) (Z₁ := W₁) (Z₂ := W₂)
    (h₀ := h₀) (β := 2 * h₀ - α) (K := K) (η := η) h_h₀_le_2h₀mα hK_nn
    hW₁_cont hW₂_cont hW₁_deriv hW₂_deriv hB₁_bd hdiff_bd' (2 * h₀ - t)
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have h_W_init : ‖W₁ h₀ - W₂ h₀‖ = ‖Z₁ h₀ - Z₂ h₀‖ := by
    have hW₁h : W₁ h₀ = Z₁ h₀ := by
      change Z₁ (2 * h₀ - h₀) = Z₁ h₀
      have : 2 * h₀ - h₀ = h₀ := by ring
      rw [this]
    have hW₂h : W₂ h₀ = Z₂ h₀ := by
      change Z₂ (2 * h₀ - h₀) = Z₂ h₀
      have : 2 * h₀ - h₀ = h₀ := by ring
      rw [this]
    rw [hW₁h, hW₂h]
  have h_W_t : W₁ (2 * h₀ - t) - W₂ (2 * h₀ - t) = Z₁ t - Z₂ t := by
    change Z₁ (2 * h₀ - (2 * h₀ - t)) - Z₂ (2 * h₀ - (2 * h₀ - t)) = Z₁ t - Z₂ t
    have h_eq : 2 * h₀ - (2 * h₀ - t) = t := by ring
    rw [h_eq]
  have h_time : 2 * h₀ - t - h₀ = h₀ - t := by ring
  rw [h_time, h_W_init] at hres
  have h_lhs : ‖W₁ (2 * h₀ - t) - W₂ (2 * h₀ - t)‖ = ‖Z₁ t - Z₂ t‖ := by
    rw [h_W_t]
  rw [h_lhs] at hres
  exact hres

/-- **Joint continuity of `linearODESolution` in `(x, t)`**.

If `A` is jointly continuous on `U × Ioo a b` and `Z₀` is continuous on `U`,
then the parametric solution `(x, t) ↦ linearODESolution A a b h₀ Z₀ x t` is
jointly continuous on `U × Ioo a b`. -/
theorem linearODESolution_continuousOn
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {A : F → ℝ → (G →L[ℝ] G)} {h₀ : ℝ} {Z₀ : F → G}
    {a b : ℝ} (hab_lt : a < b) (h₀_mem : h₀ ∈ Set.Ioo a b)
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b))
    (hZ₀_cont : ContinuousOn Z₀ U) :
    ContinuousOn
      (Function.uncurry (linearODESolution A a b h₀ Z₀))
      (U ×ˢ Set.Ioo a b) := by
  set Z : F → ℝ → G := linearODESolution A a b h₀ Z₀ with hZ_def
  have hZ_exists : ∀ x ∈ U, HasLinearODESolution A a b h₀ Z₀ x := fun x hx =>
    hasLinearODESolution_of_continuousOn hab_lt h₀_mem hU hA_cont hx
  have hZ_deriv : ∀ x ∈ U, ∀ t ∈ Ioo a b, HasDerivAt (Z x) (A x t (Z x t)) t := by
    intro x hx t ht
    exact linearODESolution_hasDerivAt_of_hasSolution A a b h₀ Z₀ (hZ_exists x hx) ht
  have hZ_cont_t : ∀ x ∈ U, ContinuousOn (Z x) (Ioo a b) := by
    intro x hx t ht
    exact ((hZ_deriv x hx t ht).continuousAt).continuousWithinAt
  have hZ_init : ∀ x, Z x h₀ = Z₀ x := fun x => linearODESolution_init A a b h₀ Z₀ x
  have hS_open : IsOpen (U ×ˢ Set.Ioo a b : Set (F × ℝ)) := hU.prod isOpen_Ioo
  refine IsOpen.continuousOn_iff hS_open |>.mpr ?_
  rintro ⟨x₀, t₀⟩ hp
  obtain ⟨hx₀U, ht₀⟩ := hp
  rw [Metric.continuousAt_iff]
  intro ε hε
  set α : ℝ := (a + min t₀ h₀) / 2 with hα_def
  set β : ℝ := (b + max t₀ h₀) / 2 with hβ_def
  have hα_lt_min : α < min t₀ h₀ := by
    rw [hα_def]
    have := lt_min ht₀.1 h₀_mem.1
    linarith
  have hα_lt_a : a < α := by
    rw [hα_def]
    have := lt_min ht₀.1 h₀_mem.1
    linarith
  have hmax_lt_β : max t₀ h₀ < β := by
    rw [hβ_def]
    have := max_lt ht₀.2 h₀_mem.2
    linarith
  have hβ_lt_b : β < b := by
    rw [hβ_def]
    have := max_lt ht₀.2 h₀_mem.2
    linarith
  have hα_le_t₀ : α ≤ t₀ := le_of_lt (lt_of_lt_of_le hα_lt_min (min_le_left _ _))
  have hα_le_h₀ : α ≤ h₀ := le_of_lt (lt_of_lt_of_le hα_lt_min (min_le_right _ _))
  have ht₀_le_β : t₀ ≤ β := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hmax_lt_β)
  have hh₀_le_β : h₀ ≤ β := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hmax_lt_β)
  have hα_le_β : α ≤ β := le_trans hα_le_h₀ hh₀_le_β
  have hIcc_sub_Ioo : Icc α β ⊆ Ioo a b := fun s hs =>
    ⟨lt_of_lt_of_le hα_lt_a hs.1, lt_of_le_of_lt hs.2 hβ_lt_b⟩
  have ht₀_mem_Icc : t₀ ∈ Icc α β := ⟨hα_le_t₀, ht₀_le_β⟩
  have hh₀_mem_Icc : h₀ ∈ Icc α β := ⟨hα_le_h₀, hh₀_le_β⟩
  have hIcc_compact : IsCompact (Icc α β) := isCompact_Icc
  obtain ⟨M, hM_nn, hM_x₀_bd⟩ :
      ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Icc α β, ‖A x₀ s‖ ≤ M := by
    have hAx₀_cont : ContinuousOn (A x₀) (Icc α β) := by
      have hAx₀_uncurry : ContinuousOn (A x₀) (Ioo a b) :=
        ContinuousOn.uncurry_left x₀ hx₀U hA_cont
      exact hAx₀_uncurry.mono (fun s hs => hIcc_sub_Ioo hs)
    have hnorm_Ax₀ : ContinuousOn (fun s => ‖A x₀ s‖) (Icc α β) :=
      continuous_norm.comp_continuousOn hAx₀_cont
    have hne : (Icc α β).Nonempty := ⟨h₀, hh₀_mem_Icc⟩
    rcases hIcc_compact.exists_isMaxOn hne hnorm_Ax₀ with ⟨τ, _, hτ_max⟩
    exact ⟨‖A x₀ τ‖, norm_nonneg _, fun s hs => hτ_max hs⟩
  have hS_open' : IsOpen (U ×ˢ Set.Ioo a b : Set (F × ℝ)) := hS_open
  have h_open_set : IsOpen
      {q : F × ℝ | q.1 ∈ U ∧ q.2 ∈ Ioo a b ∧ ‖A q.1 q.2‖ < M + 1} := by
    set normA : F × ℝ → ℝ := fun p => ‖A p.1 p.2‖
    have hnormA_cont : ContinuousOn normA (U ×ˢ Set.Ioo a b) :=
      continuous_norm.comp_continuousOn hA_cont
    have hpre_open : IsOpen ((U ×ˢ Set.Ioo a b) ∩ normA ⁻¹' Set.Iio (M + 1)) :=
      hnormA_cont.isOpen_inter_preimage hS_open' isOpen_Iio
    have h_eq : {q : F × ℝ | q.1 ∈ U ∧ q.2 ∈ Ioo a b ∧ ‖A q.1 q.2‖ < M + 1} =
        (U ×ˢ Set.Ioo a b) ∩ normA ⁻¹' Set.Iio (M + 1) := by
      ext q
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    rw [h_eq]
    exact hpre_open
  have h_slice_in_open : ({x₀} : Set F) ×ˢ Icc α β ⊆
      {q : F × ℝ | q.1 ∈ U ∧ q.2 ∈ Ioo a b ∧ ‖A q.1 q.2‖ < M + 1} := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := hq
    rw [Set.mem_singleton_iff] at hq1
    subst hq1
    refine ⟨hx₀U, hIcc_sub_Ioo hq2, ?_⟩
    exact lt_of_le_of_lt (hM_x₀_bd q.2 hq2) (by linarith)
  obtain ⟨W₀, V, hW₀_open, _hV_open, hx₀_W₀, hIcc_V, hWV_sub⟩ :=
    generalized_tube_lemma isCompact_singleton hIcc_compact h_open_set h_slice_in_open
  have hx₀_W₀' : x₀ ∈ W₀ := hx₀_W₀ (Set.mem_singleton x₀)
  set Wopen : Set F := W₀ ∩ U with hWopen_def
  have hWopen_open : IsOpen Wopen := hW₀_open.inter hU
  have hx₀_Wopen : x₀ ∈ Wopen := ⟨hx₀_W₀', hx₀U⟩
  have hWopen_sub_U : Wopen ⊆ U := fun x hx => hx.2
  have hMbd_W : ∀ x ∈ Wopen, ∀ s ∈ Icc α β, ‖A x s‖ ≤ M + 1 := by
    intro x hx s hs
    have hx_W₀ : x ∈ W₀ := hx.1
    have hs_V : s ∈ V := hIcc_V hs
    have hxs_sub : (x, s) ∈ W₀ ×ˢ V := ⟨hx_W₀, hs_V⟩
    have := hWV_sub hxs_sub
    exact le_of_lt this.2.2
  set K : ℝ := M + 1 with hK_def
  have hK_nn : 0 ≤ K := by rw [hK_def]; linarith
  have hZ_apriori : ∀ x ∈ Wopen, ∀ t ∈ Icc α β,
      ‖Z x t‖ ≤ ‖Z₀ x‖ * Real.exp (K * (β - α)) := by
    intro x hx t ht
    have hZxh₀_eq : Z x h₀ = Z₀ x := hZ_init x
    have hZx_deriv_all : ∀ s ∈ Ioo a b, HasDerivAt (Z x) (A x s (Z x s)) s :=
      hZ_deriv x (hWopen_sub_U hx)
    have habs := linearODE_apriori_bound (A := A x) (a := a) (b := b) (α := α) (β := β)
      (c := h₀) (M := K) hα_le_β hα_lt_a hβ_lt_b hh₀_mem_Icc hK_nn
      (fun s hs => hMbd_W x hx s hs) hZx_deriv_all t ht
    rw [hZxh₀_eq] at habs
    exact habs
  set T : ℝ := β - α with hT_def
  have hT_nn : 0 ≤ T := by rw [hT_def]; linarith
  have hgb_eq_zero : gronwallBound 0 K 0 T = 0 := by simp [gronwallBound_ε0_δ0]
  have hK_pos : 0 < K := by rw [hK_def]; linarith
  have hK_ne : K ≠ 0 := ne_of_gt hK_pos
  have hgb_cont : Continuous (fun p : ℝ × ℝ => gronwallBound p.1 K p.2 T) := by
    simp only [gronwallBound_of_K_ne_0 hK_ne]
    fun_prop
  have hgb_tendsto : Tendsto (fun p : ℝ × ℝ => gronwallBound p.1 K p.2 T)
      (𝓝 (0, 0)) (𝓝 0) := by
    have := hgb_cont.continuousAt (x := (0, 0))
    rw [ContinuousAt, hgb_eq_zero] at this
    exact this
  rw [Metric.tendsto_nhds] at hgb_tendsto
  obtain ⟨ρ, hρ_pos, hρ_bd⟩ := Metric.mem_nhds_iff.mp (hgb_tendsto (ε / 2) (by linarith))
  set δ_target : ℝ := ρ / 2 with hδ_target_def
  set η_target : ℝ := ρ / 2 with hη_target_def
  have hδ_target_pos : 0 < δ_target := by rw [hδ_target_def]; linarith
  have hη_target_pos : 0 < η_target := by rw [hη_target_def]; linarith
  have hbd_gb : ∀ δ η : ℝ, 0 ≤ δ → 0 ≤ η → δ < δ_target → η < η_target →
      gronwallBound δ K η T < ε / 2 := by
    intro δ η hδ_nn hη_nn hδ_lt hη_lt
    have h_pair_mem : (δ, η) ∈ Metric.ball ((0 : ℝ), (0 : ℝ)) ρ := by
      rw [Metric.mem_ball, Prod.dist_eq]
      have h1 : dist δ 0 < ρ := by
        rw [Real.dist_0_eq_abs, abs_of_nonneg hδ_nn]
        exact lt_of_lt_of_le hδ_lt (by rw [hδ_target_def]; linarith)
      have h2 : dist η 0 < ρ := by
        rw [Real.dist_0_eq_abs, abs_of_nonneg hη_nn]
        exact lt_of_lt_of_le hη_lt (by rw [hη_target_def]; linarith)
      exact max_lt h1 h2
    have hd := hρ_bd h_pair_mem
    simp only [Set.mem_setOf_eq] at hd
    rw [Real.dist_0_eq_abs] at hd
    exact lt_of_le_of_lt (le_abs_self _) hd
  set R' : ℝ := (‖Z₀ x₀‖ + 1) * Real.exp (K * T) with hR'_def
  have hR'_pos : 0 < R' := by
    rw [hR'_def]
    apply mul_pos
    · linarith [norm_nonneg (Z₀ x₀)]
    · exact Real.exp_pos _
  set η_op : ℝ := η_target / (R' + 1) with hη_op_def
  have hη_op_pos : 0 < η_op := div_pos hη_target_pos (by linarith)
  set g : F × ℝ → ℝ := fun p => ‖A p.1 p.2 - A x₀ p.2‖
  have hg_cont : ContinuousOn g (U ×ˢ Set.Ioo a b) := by
    have h_swap : ContinuousOn (fun p : F × ℝ => A x₀ p.2) (U ×ˢ Set.Ioo a b) := by
      have h_A_x₀_cont : ContinuousOn (A x₀) (Ioo a b) :=
        ContinuousOn.uncurry_left x₀ hx₀U hA_cont
      exact h_A_x₀_cont.comp continuousOn_snd (fun _ hp => hp.2)
    have : ContinuousOn (fun p : F × ℝ => A p.1 p.2 - A x₀ p.2) (U ×ˢ Set.Ioo a b) :=
      hA_cont.sub h_swap
    exact continuous_norm.comp_continuousOn this
  have hg_x₀ : ∀ s, g (x₀, s) = 0 := fun s => by
    change ‖A x₀ s - A x₀ s‖ = 0
    rw [sub_self, norm_zero]
  have h_gopen : IsOpen
      {p : F × ℝ | p.1 ∈ U ∧ p.2 ∈ Ioo a b ∧ g p < η_op} := by
    have hpre_open : IsOpen ((U ×ˢ Set.Ioo a b) ∩ g ⁻¹' Set.Iio η_op) :=
      hg_cont.isOpen_inter_preimage hS_open' isOpen_Iio
    have h_eq : {p : F × ℝ | p.1 ∈ U ∧ p.2 ∈ Ioo a b ∧ g p < η_op} =
        (U ×ˢ Set.Ioo a b) ∩ g ⁻¹' Set.Iio η_op := by
      ext p; constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    rw [h_eq]
    exact hpre_open
  have h_slice_in_gopen : ({x₀} : Set F) ×ˢ Icc α β ⊆
      {p : F × ℝ | p.1 ∈ U ∧ p.2 ∈ Ioo a b ∧ g p < η_op} := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [Set.mem_singleton_iff] at hp1; subst hp1
    refine ⟨hx₀U, hIcc_sub_Ioo hp2, ?_⟩
    rw [hg_x₀]; exact hη_op_pos
  obtain ⟨W₁, V₁, hW₁_open, _hV₁_open, hx₀_W₁, hIccα_V₁, hW₁V₁_sub⟩ :=
    generalized_tube_lemma isCompact_singleton hIcc_compact h_gopen h_slice_in_gopen
  have hx₀_W₁' : x₀ ∈ W₁ := hx₀_W₁ (Set.mem_singleton x₀)
  have hZ₀_cont_at : ContinuousAt Z₀ x₀ := (hZ₀_cont x₀ hx₀U).continuousAt (hU.mem_nhds hx₀U)
  have hZ₀_diff_eps : ∀ᶠ x in 𝓝 x₀, ‖Z₀ x - Z₀ x₀‖ < δ_target := by
    have h_tendsto_diff : Tendsto (fun x => Z₀ x - Z₀ x₀) (𝓝 x₀) (𝓝 0) := by
      have h_tendsto : Tendsto Z₀ (𝓝 x₀) (𝓝 (Z₀ x₀)) := hZ₀_cont_at
      have := h_tendsto.sub (tendsto_const_nhds (x := Z₀ x₀))
      simpa using this
    rw [Metric.tendsto_nhds] at h_tendsto_diff
    have := h_tendsto_diff δ_target hδ_target_pos
    filter_upwards [this] with x hx
    have h_eq : dist (Z₀ x - Z₀ x₀) 0 = ‖Z₀ x - Z₀ x₀‖ := by
      rw [dist_zero_right]
    rwa [h_eq] at hx
  have hZ₀_norm_eps : ∀ᶠ x in 𝓝 x₀, ‖Z₀ x‖ < ‖Z₀ x₀‖ + 1 := by
    have h_norm_cont : ContinuousAt (fun x => ‖Z₀ x‖) x₀ :=
      continuous_norm.continuousAt.comp hZ₀_cont_at
    have h_one_pos : ‖Z₀ x₀‖ < ‖Z₀ x₀‖ + 1 := by linarith
    have h_open : IsOpen {y : ℝ | y < ‖Z₀ x₀‖ + 1} := isOpen_Iio
    have hmem : ‖Z₀ x₀‖ ∈ {y : ℝ | y < ‖Z₀ x₀‖ + 1} := h_one_pos
    exact h_norm_cont.preimage_mem_nhds (h_open.mem_nhds hmem)
  obtain ⟨W_diff, hZ₀_diff_in, hW_diff_open, hx₀_W_diff⟩ := _root_.mem_nhds_iff.mp hZ₀_diff_eps
  obtain ⟨W_norm, hZ₀_norm_in, hW_norm_open, hx₀_W_norm⟩ := _root_.mem_nhds_iff.mp hZ₀_norm_eps
  set Wparam : Set F := Wopen ∩ W₁ ∩ W_diff ∩ W_norm with hWparam_def
  have hWparam_open : IsOpen Wparam :=
    ((hWopen_open.inter hW₁_open).inter hW_diff_open).inter hW_norm_open
  have hx₀_Wparam : x₀ ∈ Wparam :=
    ⟨⟨⟨hx₀_Wopen, hx₀_W₁'⟩, hx₀_W_diff⟩, hx₀_W_norm⟩
  have hWparam_sub_Wopen : Wparam ⊆ Wopen := fun x hx => hx.1.1.1
  have hWparam_sub_U : Wparam ⊆ U := fun x hx => hWopen_sub_U (hWparam_sub_Wopen hx)
  have hWparam_diff_lt : ∀ x ∈ Wparam, ‖Z₀ x - Z₀ x₀‖ < δ_target :=
    fun x hx => hZ₀_diff_in hx.1.2
  have hWparam_norm_lt : ∀ x ∈ Wparam, ‖Z₀ x‖ < ‖Z₀ x₀‖ + 1 :=
    fun x hx => hZ₀_norm_in hx.2
  have hWparam_g_lt : ∀ x ∈ Wparam, ∀ s ∈ Icc α β, ‖A x s - A x₀ s‖ < η_op := by
    intro x hx s hs
    have hx_W₁ : x ∈ W₁ := hx.1.1.2
    have hs_V₁ : s ∈ V₁ := hIccα_V₁ hs
    have hxs_sub : (x, s) ∈ W₁ ×ˢ V₁ := ⟨hx_W₁, hs_V₁⟩
    exact (hW₁V₁_sub hxs_sub).2.2
  have hbd_diff : ∀ x ∈ Wparam, ∀ t ∈ Icc α β,
      ‖Z x t - Z x₀ t‖ ≤ gronwallBound ‖Z₀ x - Z₀ x₀‖ K η_target |t - h₀| := by
    intro x hx t ht
    have hxU : x ∈ U := hWparam_sub_U hx
    have h_Zxs_bd : ∀ s ∈ Icc α β, ‖Z x s‖ ≤ R' := by
      intro s hs
      have hZx_apr := hZ_apriori x (hWparam_sub_Wopen hx) s hs
      have hZ₀x_lt : ‖Z₀ x‖ < ‖Z₀ x₀‖ + 1 := hWparam_norm_lt x hx
      have hexp_pos : 0 < Real.exp (K * T) := Real.exp_pos _
      have h_bound : ‖Z₀ x‖ * Real.exp (K * T) ≤ (‖Z₀ x₀‖ + 1) * Real.exp (K * T) :=
        mul_le_mul_of_nonneg_right hZ₀x_lt.le hexp_pos.le
      exact le_trans hZx_apr h_bound
    have hAx_bd : ∀ s ∈ Icc α β, ‖A x s‖ ≤ K :=
      fun s hs => hMbd_W x (hWparam_sub_Wopen hx) s hs
    have hAx₀_bd : ∀ s ∈ Icc α β, ‖A x₀ s‖ ≤ K :=
      fun s hs => le_trans (hM_x₀_bd s hs) (by linarith)
    have hZx_cont : ContinuousOn (Z x) (Icc α β) := by
      intro s hs; exact (hZ_cont_t x hxU s (hIcc_sub_Ioo hs)).mono (fun u hu => hIcc_sub_Ioo hu)
    have hZx₀_cont : ContinuousOn (Z x₀) (Icc α β) := by
      intro s hs; exact (hZ_cont_t x₀ hx₀U s (hIcc_sub_Ioo hs)).mono (fun u hu => hIcc_sub_Ioo hu)
    have hZx_deriv_Icc : ∀ s ∈ Icc α β, HasDerivAt (Z x) (A x s (Z x s)) s :=
      fun s hs => hZ_deriv x hxU s (hIcc_sub_Ioo hs)
    have hZx₀_deriv_Icc : ∀ s ∈ Icc α β, HasDerivAt (Z x₀) (A x₀ s (Z x₀ s)) s :=
      fun s hs => hZ_deriv x₀ hx₀U s (hIcc_sub_Ioo hs)
    have hdiff_bd_full : ∀ s ∈ Icc α β, ‖(A x s - A x₀ s) (Z x s)‖ ≤ η_target := by
      intro s hs
      have h1 : ‖(A x s - A x₀ s) (Z x s)‖ ≤ ‖A x s - A x₀ s‖ * ‖Z x s‖ :=
        (A x s - A x₀ s).le_opNorm _
      have h2 : ‖A x s - A x₀ s‖ * ‖Z x s‖ ≤ η_op * R' := by
        have hop_lt : ‖A x s - A x₀ s‖ < η_op := hWparam_g_lt x hx s hs
        have hZ_lt : ‖Z x s‖ ≤ R' := h_Zxs_bd s hs
        have h_nn_Z : 0 ≤ ‖Z x s‖ := norm_nonneg _
        have h_op_nn : 0 ≤ ‖A x s - A x₀ s‖ := norm_nonneg _
        have h_η_op_nn : 0 ≤ η_op := le_of_lt hη_op_pos
        have h_R'_nn : 0 ≤ R' := le_of_lt hR'_pos
        calc ‖A x s - A x₀ s‖ * ‖Z x s‖
            ≤ η_op * ‖Z x s‖ := mul_le_mul_of_nonneg_right hop_lt.le h_nn_Z
          _ ≤ η_op * R' := mul_le_mul_of_nonneg_left hZ_lt h_η_op_nn
      have h3 : η_op * R' ≤ η_target := by
        rw [hη_op_def]
        rw [div_mul_eq_mul_div, mul_comm]
        rw [div_le_iff₀ (by linarith)]
        have hR'_nn : 0 ≤ R' := le_of_lt hR'_pos
        have h_η_t_nn : 0 ≤ η_target := le_of_lt hη_target_pos
        have h_le : R' ≤ R' + 1 := by linarith
        calc R' * η_target ≤ (R' + 1) * η_target :=
              mul_le_mul_of_nonneg_right h_le h_η_t_nn
          _ = η_target * (R' + 1) := by ring
      linarith
    rcases le_total h₀ t with hht | hth
    · have hh₀_le_t : h₀ ≤ t := hht
      have hZ₁_cont_ht : ContinuousOn (Z x₀) (Icc h₀ β) := by
        intro s hs
        exact (hZx₀_cont s ⟨le_trans hα_le_h₀ hs.1, hs.2⟩).mono
          (fun u hu => ⟨le_trans hα_le_h₀ hu.1, hu.2⟩)
      have hZ₂_cont_ht : ContinuousOn (Z x) (Icc h₀ β) := by
        intro s hs
        exact (hZx_cont s ⟨le_trans hα_le_h₀ hs.1, hs.2⟩).mono
          (fun u hu => ⟨le_trans hα_le_h₀ hu.1, hu.2⟩)
      have hZ₁_deriv_ht : ∀ s ∈ Icc h₀ β, HasDerivAt (Z x₀) (A x₀ s (Z x₀ s)) s :=
        fun s hs => hZx₀_deriv_Icc s ⟨le_trans hα_le_h₀ hs.1, hs.2⟩
      have hZ₂_deriv_ht : ∀ s ∈ Icc h₀ β, HasDerivAt (Z x) (A x s (Z x s)) s :=
        fun s hs => hZx_deriv_Icc s ⟨le_trans hα_le_h₀ hs.1, hs.2⟩
      have hAx₀_bd_ht : ∀ s ∈ Icc h₀ β, ‖A x₀ s‖ ≤ K :=
        fun s hs => hAx₀_bd s ⟨le_trans hα_le_h₀ hs.1, hs.2⟩
      have hdiff_bd_ht : ∀ s ∈ Icc h₀ β, ‖(A x s - A x₀ s) (Z x s)‖ ≤ η_target :=
        fun s hs => hdiff_bd_full s ⟨le_trans hα_le_h₀ hs.1, hs.2⟩
      have hres := linearODE_gronwall_forward (A₁ := A x₀) (A₂ := A x) (Z₁ := Z x₀) (Z₂ := Z x)
        hh₀_le_β hK_nn hZ₁_cont_ht hZ₂_cont_ht hZ₁_deriv_ht hZ₂_deriv_ht
        hAx₀_bd_ht hdiff_bd_ht t ⟨hh₀_le_t, ht.2⟩
      have h_init_eq : ‖Z x₀ h₀ - Z x h₀‖ = ‖Z₀ x - Z₀ x₀‖ := by
        rw [hZ_init x, hZ_init x₀]
        rw [← norm_neg]; congr 1; abel
      rw [h_init_eq] at hres
      have h_lhs_eq : ‖Z x t - Z x₀ t‖ = ‖Z x₀ t - Z x t‖ := by
        rw [← norm_neg]; congr 1; abel
      rw [h_lhs_eq]
      have h_abs : |t - h₀| = t - h₀ := abs_of_nonneg (by linarith)
      rw [h_abs]
      exact hres
    · have ht_le_h₀ : t ≤ h₀ := hth
      have hZ₁_cont_th : ContinuousOn (Z x₀) (Icc α h₀) := by
        intro s hs
        exact (hZx₀_cont s ⟨hs.1, le_trans hs.2 hh₀_le_β⟩).mono
          (fun u hu => ⟨hu.1, le_trans hu.2 hh₀_le_β⟩)
      have hZ₂_cont_th : ContinuousOn (Z x) (Icc α h₀) := by
        intro s hs
        exact (hZx_cont s ⟨hs.1, le_trans hs.2 hh₀_le_β⟩).mono
          (fun u hu => ⟨hu.1, le_trans hu.2 hh₀_le_β⟩)
      have hZ₁_deriv_th : ∀ s ∈ Icc α h₀, HasDerivAt (Z x₀) (A x₀ s (Z x₀ s)) s :=
        fun s hs => hZx₀_deriv_Icc s ⟨hs.1, le_trans hs.2 hh₀_le_β⟩
      have hZ₂_deriv_th : ∀ s ∈ Icc α h₀, HasDerivAt (Z x) (A x s (Z x s)) s :=
        fun s hs => hZx_deriv_Icc s ⟨hs.1, le_trans hs.2 hh₀_le_β⟩
      have hAx₀_bd_th : ∀ s ∈ Icc α h₀, ‖A x₀ s‖ ≤ K :=
        fun s hs => hAx₀_bd s ⟨hs.1, le_trans hs.2 hh₀_le_β⟩
      have hdiff_bd_th : ∀ s ∈ Icc α h₀, ‖(A x s - A x₀ s) (Z x s)‖ ≤ η_target :=
        fun s hs => hdiff_bd_full s ⟨hs.1, le_trans hs.2 hh₀_le_β⟩
      have hres := linearODE_gronwall_backward (A₁ := A x₀) (A₂ := A x) (Z₁ := Z x₀) (Z₂ := Z x)
        hα_le_h₀ hK_nn hZ₁_cont_th hZ₂_cont_th hZ₁_deriv_th hZ₂_deriv_th
        hAx₀_bd_th hdiff_bd_th t ⟨ht.1, ht_le_h₀⟩
      have h_init_eq : ‖Z x₀ h₀ - Z x h₀‖ = ‖Z₀ x - Z₀ x₀‖ := by
        rw [hZ_init x, hZ_init x₀]
        rw [← norm_neg]; congr 1; abel
      rw [h_init_eq] at hres
      have h_lhs_eq : ‖Z x t - Z x₀ t‖ = ‖Z x₀ t - Z x t‖ := by
        rw [← norm_neg]; congr 1; abel
      rw [h_lhs_eq]
      have h_abs : |t - h₀| = h₀ - t := by
        rw [abs_of_nonpos (by linarith)]; ring
      rw [h_abs]
      exact hres
  have hZx₀_cont_Ioo : ContinuousOn (Z x₀) (Ioo a b) := hZ_cont_t x₀ hx₀U
  have hZx₀_cont_at : ContinuousAt (Z x₀) t₀ :=
    (hZx₀_cont_Ioo t₀ ht₀).continuousAt (isOpen_Ioo.mem_nhds ht₀)
  have hZx₀_tendsto : Tendsto (Z x₀) (𝓝 t₀) (𝓝 (Z x₀ t₀)) := hZx₀_cont_at
  rw [Metric.tendsto_nhds] at hZx₀_tendsto
  obtain ⟨δ_t, hδ_t_pos, hδ_t_bd⟩ :=
    Metric.mem_nhds_iff.mp (hZx₀_tendsto (ε / 2) (by linarith))
  obtain ⟨ρ_param, hρ_param_pos, hρ_param_sub⟩ :=
    Metric.isOpen_iff.mp hWparam_open x₀ hx₀_Wparam
  set δ_time : ℝ := min δ_t (min (β - t₀) (t₀ - α)) with hδ_time_def
  have hδ_time_pos : 0 < δ_time := by
    rw [hδ_time_def]
    refine lt_min hδ_t_pos (lt_min ?_ ?_)
    · linarith [lt_of_le_of_lt (le_max_left _ _) hmax_lt_β]
    · linarith [lt_of_lt_of_le hα_lt_min (min_le_left _ _)]
  set δ_final : ℝ := min ρ_param δ_time with hδ_final_def
  have hδ_final_pos : 0 < δ_final :=
    lt_min hρ_param_pos hδ_time_pos
  use δ_final
  refine ⟨hδ_final_pos, ?_⟩
  intro p hp
  obtain ⟨x, t⟩ := p
  rw [Prod.dist_eq] at hp
  have hdx : dist x x₀ < δ_final := lt_of_le_of_lt (le_max_left _ _) hp
  have hdt : dist t t₀ < δ_final := lt_of_le_of_lt (le_max_right _ _) hp
  have hx_param : x ∈ Wparam := hρ_param_sub
    (Metric.mem_ball.mpr (lt_of_lt_of_le hdx (min_le_left _ _)))
  have hdt_t : dist t t₀ < δ_t :=
    lt_of_lt_of_le hdt (le_trans (min_le_right _ _) (min_le_left _ _))
  have hdt_β : dist t t₀ < β - t₀ :=
    lt_of_lt_of_le hdt (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hdt_α : dist t t₀ < t₀ - α :=
    lt_of_lt_of_le hdt (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have ht_Icc : t ∈ Icc α β := by
    rw [Real.dist_eq] at hdt_β hdt_α
    refine ⟨?_, ?_⟩
    · have := abs_lt.mp hdt_α
      linarith [this.1]
    · have := abs_lt.mp hdt_β
      linarith [this.2]
  have h_triangle : ‖Z x t - Z x₀ t₀‖ ≤ ‖Z x t - Z x₀ t‖ + ‖Z x₀ t - Z x₀ t₀‖ := by
    have h_eq : Z x t - Z x₀ t₀ = (Z x t - Z x₀ t) + (Z x₀ t - Z x₀ t₀) := by abel
    rw [h_eq]
    exact norm_add_le _ _
  have h_t_piece : ‖Z x₀ t - Z x₀ t₀‖ < ε / 2 := by
    have hd := hδ_t_bd (Metric.mem_ball.mpr hdt_t)
    simp only [Set.mem_setOf_eq] at hd
    rw [dist_eq_norm] at hd
    exact hd
  have hbd := hbd_diff x hx_param t ht_Icc
  have h_init_bd : ‖Z₀ x - Z₀ x₀‖ < δ_target := hWparam_diff_lt x hx_param
  have h_t_h0_le_T : |t - h₀| ≤ T := by
    rw [hT_def]
    rcases le_total h₀ t with hht | hth
    · rw [abs_of_nonneg (by linarith)]; linarith [ht_Icc.2, hh₀_mem_Icc.1]
    · rw [abs_of_nonpos (by linarith)]; linarith [ht_Icc.1, hh₀_mem_Icc.2]
  have h_t_h0_nn : 0 ≤ |t - h₀| := abs_nonneg _
  have h_init_nn : 0 ≤ ‖Z₀ x - Z₀ x₀‖ := norm_nonneg _
  have h_eta_nn : 0 ≤ η_target := le_of_lt hη_target_pos
  have h_gb_mono := gronwallBound_mono h_init_nn h_eta_nn hK_nn h_t_h0_le_T
  have hbd' : ‖Z x t - Z x₀ t‖ ≤ gronwallBound ‖Z₀ x - Z₀ x₀‖ K η_target T :=
    le_trans hbd h_gb_mono
  have h_param_piece : ‖Z x t - Z x₀ t‖ < ε / 2 := by
    have h_gb_lt : gronwallBound ‖Z₀ x - Z₀ x₀‖ K η_target T < ε / 2 := by
      have h_gb_mono_eps : gronwallBound ‖Z₀ x - Z₀ x₀‖ K η_target T ≤
          gronwallBound δ_target K η_target T := by
        simp only [gronwallBound_of_K_ne_0 hK_ne]
        have h_exp_pos : 0 < Real.exp (K * T) := Real.exp_pos _
        have h_init_le : ‖Z₀ x - Z₀ x₀‖ ≤ δ_target := le_of_lt h_init_bd
        have h_mul_le : ‖Z₀ x - Z₀ x₀‖ * Real.exp (K * T) ≤ δ_target * Real.exp (K * T) :=
          mul_le_mul_of_nonneg_right h_init_le h_exp_pos.le
        linarith
      have h_inner_lt : gronwallBound δ_target K η_target T < ε / 2 := by
        have h_pair_in_ball : (δ_target, η_target) ∈ Metric.ball ((0 : ℝ), (0 : ℝ)) ρ := by
          rw [Metric.mem_ball, Prod.dist_eq]
          have h1 : dist δ_target 0 < ρ := by
            rw [Real.dist_0_eq_abs, abs_of_nonneg (le_of_lt hδ_target_pos)]
            rw [hδ_target_def]; linarith
          have h2 : dist η_target 0 < ρ := by
            rw [Real.dist_0_eq_abs, abs_of_nonneg (le_of_lt hη_target_pos)]
            rw [hη_target_def]; linarith
          exact max_lt h1 h2
        have hd := hρ_bd h_pair_in_ball
        simp only [Set.mem_setOf_eq] at hd
        rw [Real.dist_0_eq_abs] at hd
        exact lt_of_le_of_lt (le_abs_self _) hd
      exact lt_of_le_of_lt h_gb_mono_eps h_inner_lt
    exact lt_of_le_of_lt hbd' h_gb_lt
  have h_dist_eq : dist (Z x t) (Z x₀ t₀) = ‖Z x t - Z x₀ t₀‖ := dist_eq_norm _ _
  change dist (Z x t) (Z x₀ t₀) < ε
  rw [h_dist_eq]
  calc ‖Z x t - Z x₀ t₀‖
      ≤ ‖Z x t - Z x₀ t‖ + ‖Z x₀ t - Z x₀ t₀‖ := h_triangle
    _ < ε / 2 + ε / 2 := add_lt_add h_param_piece h_t_piece
    _ = ε := by ring

end JointContinuity

section Inhomogeneous

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- **Augmented coefficient** of an inhomogeneous linear ODE.

For `A : F → ℝ → (G →L[ℝ] G)` and `b : F → ℝ → G`, this is the continuous
linear map `AHat(x, t) : (G × ℝ) →L[ℝ] (G × ℝ)` sending `(g, c)` to
`(A(x, t) g + c • b(x, t), 0)`.  Its first component combines the linear part
on `G` with the inhomogeneity scaled by the auxiliary scalar component; its
second component is identically zero, so the auxiliary scalar component of any
solution of the associated homogeneous system has zero derivative. -/
noncomputable def inhomogAugmentedCoeff
    (A : F → ℝ → (G →L[ℝ] G)) (b : F → ℝ → G) (x : F) (t : ℝ) :
    (G × ℝ) →L[ℝ] (G × ℝ) :=
  (((A x t).comp (ContinuousLinearMap.fst ℝ G ℝ)) +
    ((ContinuousLinearMap.snd ℝ G ℝ).smulRight (b x t))).prod 0

@[simp] lemma inhomogAugmentedCoeff_apply
    (A : F → ℝ → (G →L[ℝ] G)) (b : F → ℝ → G) (x : F) (t : ℝ) (gc : G × ℝ) :
    inhomogAugmentedCoeff A b x t gc = (A x t gc.1 + gc.2 • b x t, 0) := by
  simp [inhomogAugmentedCoeff]

private lemma inhomogAugmentedCoeff_continuousOn
    {A : F → ℝ → (G →L[ℝ] G)} {b : F → ℝ → G}
    {U : Set F} {a b' : ℝ}
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hb_cont : ContinuousOn (Function.uncurry b) (U ×ˢ Set.Ioo a b')) :
    ContinuousOn (Function.uncurry (inhomogAugmentedCoeff A b))
      (U ×ˢ Set.Ioo a b') := by
  have h_first : ContinuousOn
      (fun p : F × ℝ => (A p.1 p.2).comp (ContinuousLinearMap.fst ℝ G ℝ))
      (U ×ˢ Set.Ioo a b') := by
    exact hA_cont.clm_comp (continuousOn_const)
  have h_second : ContinuousOn
      (fun p : F × ℝ =>
        (ContinuousLinearMap.snd ℝ G ℝ).smulRight (b p.1 p.2))
      (U ×ˢ Set.Ioo a b') := by
    have h_smul_cont :
        Continuous (fun y : G => (ContinuousLinearMap.snd ℝ G ℝ).smulRight y) :=
      (ContinuousLinearMap.smulRightL ℝ (G × ℝ) G
        (ContinuousLinearMap.snd ℝ G ℝ)).continuous
    exact h_smul_cont.comp_continuousOn hb_cont
  have h_sum : ContinuousOn
      (fun p : F × ℝ =>
        ((A p.1 p.2).comp (ContinuousLinearMap.fst ℝ G ℝ)) +
          ((ContinuousLinearMap.snd ℝ G ℝ).smulRight (b p.1 p.2)))
      (U ×ˢ Set.Ioo a b') := h_first.add h_second
  have h_prodL_cont :
      Continuous (fun q : ((G × ℝ) →L[ℝ] G) × ((G × ℝ) →L[ℝ] ℝ) =>
        q.1.prod q.2) :=
    (ContinuousLinearMap.prodL (𝕜 := ℝ) (E := G × ℝ) (F := G) (G := ℝ)
      ℝ).continuous
  have h_pair : ContinuousOn
      (fun p : F × ℝ =>
        (((A p.1 p.2).comp (ContinuousLinearMap.fst ℝ G ℝ)) +
          ((ContinuousLinearMap.snd ℝ G ℝ).smulRight (b p.1 p.2)),
        (0 : (G × ℝ) →L[ℝ] ℝ)))
      (U ×ˢ Set.Ioo a b') := h_sum.prodMk continuousOn_const
  have hcomp : ContinuousOn
      ((fun q : ((G × ℝ) →L[ℝ] G) × ((G × ℝ) →L[ℝ] ℝ) => q.1.prod q.2) ∘
        (fun p : F × ℝ =>
          (((A p.1 p.2).comp (ContinuousLinearMap.fst ℝ G ℝ)) +
            ((ContinuousLinearMap.snd ℝ G ℝ).smulRight (b p.1 p.2)),
          (0 : (G × ℝ) →L[ℝ] ℝ))))
      (U ×ˢ Set.Ioo a b') :=
    h_prodL_cont.comp_continuousOn h_pair
  exact hcomp

/-- **Per-parameter existence predicate** for the inhomogeneous linear ODE.
`HasInhomogLinearODESolution A b a b' h₀ Z₀ x` asserts that for the fixed
parameter `x : F`, there exists a curve `Z : ℝ → G` with `Z h₀ = Z₀ x` and
`HasDerivAt Z (A x t (Z t) + b x t) t` for every `t ∈ Ioo a b'`. -/
def HasInhomogLinearODESolution
    (A : F → ℝ → (G →L[ℝ] G)) (b : F → ℝ → G)
    (a b' h₀ : ℝ) (Z₀ : F → G) (x : F) : Prop :=
  ∃ Z : ℝ → G, Z h₀ = Z₀ x ∧
    ∀ t ∈ Set.Ioo a b', HasDerivAt Z (A x t (Z t) + b x t) t

/-- **Parametric solution of the inhomogeneous linear ODE**
`Z'(t) = A(x, t) Z(t) + b(x, t)` with initial condition `Z(x, h₀) = Z₀ x` on
the open interval `Ioo a b'`.

Defined as the first component of the augmented-system solution
`linearODESolution (inhomogAugmentedCoeff A b) a b' h₀ (fun x => (Z₀ x, 1)) x t`.
This is total: when joint continuity of `A` and `b` holds, it satisfies both
the initial-condition and ODE clauses; otherwise it falls back via the
underlying `linearODESolution` fallback. -/
noncomputable def inhomogLinearODESolution
    (A : F → ℝ → (G →L[ℝ] G)) (b : F → ℝ → G)
    (a b' h₀ : ℝ) (Z₀ : F → G) : F → ℝ → G :=
  fun x t =>
    (linearODESolution (inhomogAugmentedCoeff A b) a b' h₀
      (fun y => (Z₀ y, (1 : ℝ))) x t).1

/-- **Initial condition** for `inhomogLinearODESolution`.  At `t = h₀`, the
parametric solution equals the initial datum `Z₀ x`. -/
theorem inhomogLinearODESolution_init
    (A : F → ℝ → (G →L[ℝ] G)) (b : F → ℝ → G)
    (a b' h₀ : ℝ) (Z₀ : F → G) (x : F) :
    inhomogLinearODESolution A b a b' h₀ Z₀ x h₀ = Z₀ x := by
  unfold inhomogLinearODESolution
  rw [linearODESolution_init]

/-- **Auxiliary scalar component stays at one**.

If the augmented coefficient is continuous on `U ×ˢ Ioo a b'`, then the second
component of the augmented solution is identically `1` on `Ioo a b'`.  Its
derivative is `0` (second component of `AHat`) and its value at `h₀` is `1`. -/
private theorem inhomogLinearODESolution_second_eq_one
    {A : F → ℝ → (G →L[ℝ] G)} {b : F → ℝ → G}
    {a b' h₀ : ℝ} {Z₀ : F → G}
    (hab_lt : a < b') (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hb_cont : ContinuousOn (Function.uncurry b) (U ×ˢ Set.Ioo a b'))
    {x : F} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Set.Ioo a b') :
    (linearODESolution (inhomogAugmentedCoeff A b) a b' h₀
        (fun y => (Z₀ y, (1 : ℝ))) x t).2 = 1 := by
  set AHat : F → ℝ → (G × ℝ) →L[ℝ] (G × ℝ) := inhomogAugmentedCoeff A b with hAHat_def
  set ZHat : ℝ → G × ℝ := fun s =>
    linearODESolution AHat a b' h₀ (fun y => (Z₀ y, (1 : ℝ))) x s with hZHat_def
  have hAHat_cont : ContinuousOn (Function.uncurry AHat) (U ×ˢ Set.Ioo a b') :=
    inhomogAugmentedCoeff_continuousOn hA_cont hb_cont
  have hZHat_deriv : ∀ s ∈ Set.Ioo a b',
      HasDerivAt ZHat (AHat x s (ZHat s)) s :=
    fun s hs => linearODESolution_hasDerivAt hab_lt h₀_mem hU hAHat_cont hx hs
  have hZHat_init : ZHat h₀ = (Z₀ x, (1 : ℝ)) := linearODESolution_init _ _ _ _ _ _
  set w : ℝ → ℝ := fun s => (ZHat s).2 with hw_def
  have hw_init : w h₀ = 1 := by
    change (ZHat h₀).2 = 1
    rw [hZHat_init]
  have hw_deriv : ∀ s ∈ Set.Ioo a b', HasDerivAt w 0 s := by
    intro s hs
    have hd : HasDerivAt ZHat (AHat x s (ZHat s)) s := hZHat_deriv s hs
    have h_snd_eq : (AHat x s (ZHat s)).2 = 0 := by
      simp [hAHat_def, inhomogAugmentedCoeff_apply]
    have h_fderiv_snd : HasFDerivAt (Prod.snd : G × ℝ → ℝ)
        (ContinuousLinearMap.snd ℝ G ℝ) (ZHat s) := hasFDerivAt_snd
    have h_comp := h_fderiv_snd.comp_hasDerivAt s hd
    have h_eq_w : (Prod.snd : G × ℝ → ℝ) ∘ ZHat = w := rfl
    rw [h_eq_w] at h_comp
    have h_eq_val :
        (ContinuousLinearMap.snd ℝ G ℝ) (AHat x s (ZHat s)) = (AHat x s (ZHat s)).2 := rfl
    rw [h_eq_val, h_snd_eq] at h_comp
    exact h_comp
  have h_diff : DifferentiableOn ℝ w (Set.Ioo a b') := by
    intro s hs
    exact ((hw_deriv s hs).differentiableAt).differentiableWithinAt
  have h_deriv_zero : Set.EqOn (deriv w) 0 (Set.Ioo a b') := by
    intro s hs
    have hd : HasDerivAt w 0 s := hw_deriv s hs
    simp [hd.deriv]
  have h_open : IsOpen (Set.Ioo a b' : Set ℝ) := isOpen_Ioo
  have h_preconn : IsPreconnected (Set.Ioo a b' : Set ℝ) := isPreconnected_Ioo
  have h_const := h_open.is_const_of_deriv_eq_zero h_preconn h_diff h_deriv_zero ht h₀_mem
  change w t = 1
  rw [h_const, hw_init]

/-- **ODE clause** for `inhomogLinearODESolution` under joint continuity.

When `A` and `b` are jointly continuous on `U ×ˢ Ioo a b'`, the parametric
solution at any `x ∈ U` satisfies the inhomogeneous linear ODE pointwise on
`Ioo a b'`. -/
theorem inhomogLinearODESolution_hasDerivAt
    {A : F → ℝ → (G →L[ℝ] G)} {b : F → ℝ → G}
    {a b' h₀ : ℝ} {Z₀ : F → G}
    (hab_lt : a < b') (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hb_cont : ContinuousOn (Function.uncurry b) (U ×ˢ Set.Ioo a b'))
    {x : F} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Set.Ioo a b') :
    HasDerivAt (inhomogLinearODESolution A b a b' h₀ Z₀ x ·)
      (A x t (inhomogLinearODESolution A b a b' h₀ Z₀ x t) + b x t) t := by
  set AHat : F → ℝ → (G × ℝ) →L[ℝ] (G × ℝ) := inhomogAugmentedCoeff A b with hAHat_def
  set ZHat : ℝ → G × ℝ := fun s =>
    linearODESolution AHat a b' h₀ (fun y => (Z₀ y, (1 : ℝ))) x s with hZHat_def
  have hAHat_cont : ContinuousOn (Function.uncurry AHat) (U ×ˢ Set.Ioo a b') :=
    inhomogAugmentedCoeff_continuousOn hA_cont hb_cont
  have hZHat_deriv : HasDerivAt ZHat (AHat x t (ZHat t)) t :=
    linearODESolution_hasDerivAt hab_lt h₀_mem hU hAHat_cont hx ht
  have h_snd_one : (ZHat t).2 = 1 :=
    inhomogLinearODESolution_second_eq_one
      hab_lt h₀_mem hU hA_cont hb_cont hx ht
  have h_fst_eq : (AHat x t (ZHat t)).1 = A x t (ZHat t).1 + (ZHat t).2 • b x t := by
    simp [hAHat_def, inhomogAugmentedCoeff_apply]
  have h_fderiv_fst : HasFDerivAt (Prod.fst : G × ℝ → G)
      (ContinuousLinearMap.fst ℝ G ℝ) (ZHat t) := hasFDerivAt_fst
  have h_comp := h_fderiv_fst.comp_hasDerivAt t hZHat_deriv
  have h_proj : (Prod.fst : G × ℝ → G) ∘ ZHat =
      (inhomogLinearODESolution A b a b' h₀ Z₀ x ·) := by
    funext s
    rfl
  rw [h_proj] at h_comp
  have h_fst_val :
      (ContinuousLinearMap.fst ℝ G ℝ) (AHat x t (ZHat t)) = (AHat x t (ZHat t)).1 := rfl
  rw [h_fst_val, h_fst_eq, h_snd_one, one_smul] at h_comp
  have h_ZHat_fst : (ZHat t).1 = inhomogLinearODESolution A b a b' h₀ Z₀ x t := rfl
  rw [h_ZHat_fst] at h_comp
  exact h_comp

/-- **Joint continuity of `inhomogLinearODESolution` in `(x, t)`**.

If `A` and `b` are jointly continuous on `U × Ioo a b'` and `Z₀` is continuous
on `U`, then the parametric solution
`(x, t) ↦ inhomogLinearODESolution A b a b' h₀ Z₀ x t` is jointly continuous on
`U × Ioo a b'`. -/
theorem inhomogLinearODESolution_continuousOn
    {A : F → ℝ → (G →L[ℝ] G)} {b : F → ℝ → G}
    {a b' h₀ : ℝ} {Z₀ : F → G}
    (hab_lt : a < b') (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hb_cont : ContinuousOn (Function.uncurry b) (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U) :
    ContinuousOn
      (Function.uncurry (inhomogLinearODESolution A b a b' h₀ Z₀))
      (U ×ˢ Set.Ioo a b') := by
  set AHat : F → ℝ → (G × ℝ) →L[ℝ] (G × ℝ) := inhomogAugmentedCoeff A b with hAHat_def
  have hAHat_cont : ContinuousOn (Function.uncurry AHat) (U ×ˢ Set.Ioo a b') :=
    inhomogAugmentedCoeff_continuousOn hA_cont hb_cont
  have hZHat₀_cont : ContinuousOn (fun y => (Z₀ y, (1 : ℝ))) U :=
    hZ₀_cont.prodMk continuousOn_const
  have h_aug_cont : ContinuousOn
      (Function.uncurry
        (linearODESolution AHat a b' h₀ (fun y => (Z₀ y, (1 : ℝ)))))
      (U ×ˢ Set.Ioo a b') :=
    linearODESolution_continuousOn hab_lt h₀_mem hU hAHat_cont hZHat₀_cont
  have h_eq : Function.uncurry (inhomogLinearODESolution A b a b' h₀ Z₀) =
      Prod.fst ∘
        Function.uncurry
          (linearODESolution AHat a b' h₀ (fun y => (Z₀ y, (1 : ℝ)))) := by
    funext p
    rfl
  rw [h_eq]
  exact continuous_fst.comp_continuousOn h_aug_cont

end Inhomogeneous

section VariationalSolution

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- **Forcing term** of the variational equation.

`variationalForcing A a b' h₀ Z₀ x v t :=
  (fderiv ℝ (fun y => A y t) x) v (linearODESolution A a b' h₀ Z₀ x t)`.

This is the inhomogeneous term in the variational equation derived by formally
differentiating `Z'(t) = A(x, t) Z(t)` with respect to the parameter `x` in
the direction `v`. -/
noncomputable def variationalForcing
    (A : F → ℝ → (G →L[ℝ] G)) (a b' h₀ : ℝ) (Z₀ : F → G)
    (x : F) (v : F) (t : ℝ) : G :=
  (fderiv ℝ (fun y => A y t) x) v (linearODESolution A a b' h₀ Z₀ x t)

/-- **Per-parameter, per-direction variational solution** `W(x, t, v)` of the
parametric linear ODE.

For fixed parameter `x : F` and test direction `v : F`, this is the candidate
function on `ℝ` satisfying the variational equation

`W'(t) = (fderiv (fun y => A y t) x) v · linearODESolution A a b' h₀ Z₀ x t
        + A(x, t) · W(t),
W(h₀) = (fderiv ℝ Z₀ x) v`.

Defined as `inhomogLinearODESolution` applied to coefficient `A`, forcing
`variationalForcing A a b' h₀ Z₀ x v`, and initial datum `fun y => (fderiv ℝ Z₀ y) v`.
-/
noncomputable def variationalW
    (A : F → ℝ → (G →L[ℝ] G)) (a b' h₀ : ℝ) (Z₀ : F → G)
    (x : F) (v : F) : ℝ → G :=
  inhomogLinearODESolution A (fun y t => variationalForcing A a b' h₀ Z₀ y v t)
    a b' h₀ (fun y => (fderiv ℝ Z₀ y) v) x

/-- **Initial condition** for `variationalW`.  At `t = h₀`, the variational
solution equals `(fderiv ℝ Z₀ x) v`. -/
theorem variationalW_init
    (A : F → ℝ → (G →L[ℝ] G)) (a b' h₀ : ℝ) (Z₀ : F → G) (x : F) (v : F) :
    variationalW A a b' h₀ Z₀ x v h₀ = (fderiv ℝ Z₀ x) v := by
  unfold variationalW
  exact inhomogLinearODESolution_init _ _ _ _ _ _ _

/-- **Joint continuity of the variational forcing**.

If `A` is jointly continuous and `(x, t) ↦ fderiv (fun y => A y t) x` is jointly
continuous on `U ×ˢ Ioo a b'`, and `Z₀` is continuous on `U`, then the forcing
`variationalForcing A a b' h₀ Z₀ · v ·` is jointly continuous on `U ×ˢ Ioo a b'`.
-/
theorem variationalForcing_continuousOn
    {A : F → ℝ → (G →L[ℝ] G)} {a b' h₀ : ℝ} {Z₀ : F → G}
    (hab_lt : a < b') (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U) (v : F) :
    ContinuousOn (Function.uncurry (fun x t => variationalForcing A a b' h₀ Z₀ x v t))
      (U ×ˢ Set.Ioo a b') := by
  have hZ_cont : ContinuousOn (Function.uncurry (linearODESolution A a b' h₀ Z₀))
      (U ×ˢ Set.Ioo a b') :=
    linearODESolution_continuousOn hab_lt h₀_mem hU hA_cont hZ₀_cont
  have happ : ContinuousOn
      (Function.uncurry fun x t => (fderiv ℝ (fun y => A y t) x) v)
      (U ×ˢ Set.Ioo a b') := by
    exact ContinuousOn.clm_apply hDA_cont continuousOn_const
  have hgoal : ContinuousOn
      (fun p : F × ℝ =>
        ((fderiv ℝ (fun y => A y p.2) p.1) v)
          (linearODESolution A a b' h₀ Z₀ p.1 p.2))
      (U ×ˢ Set.Ioo a b') :=
    ContinuousOn.clm_apply happ hZ_cont
  convert hgoal using 1

/-- **ODE clause** for `variationalW` under joint continuity hypotheses.

When `A`, `(x, t) ↦ fderiv (fun y => A y t) x` are jointly continuous on
`U ×ˢ Ioo a b'` and `Z₀` is continuous on `U`, the variational solution at any
`x ∈ U` and any test direction `v : F` satisfies the variational equation
pointwise on `Ioo a b'`. -/
theorem variationalW_hasDerivAt
    {A : F → ℝ → (G →L[ℝ] G)} {a b' h₀ : ℝ} {Z₀ : F → G}
    (hab_lt : a < b') (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U)
    {x : F} (hx : x ∈ U) (v : F) {t : ℝ} (ht : t ∈ Set.Ioo a b') :
    HasDerivAt (variationalW A a b' h₀ Z₀ x v ·)
      ((fderiv ℝ (fun y => A y t) x) v (linearODESolution A a b' h₀ Z₀ x t)
        + A x t (variationalW A a b' h₀ Z₀ x v t)) t := by
  have hb_cont : ContinuousOn
      (Function.uncurry (fun x t => variationalForcing A a b' h₀ Z₀ x v t))
      (U ×ˢ Set.Ioo a b') :=
    variationalForcing_continuousOn hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont v
  have hderiv : HasDerivAt
      (inhomogLinearODESolution A
        (fun y t => variationalForcing A a b' h₀ Z₀ y v t) a b' h₀
        (fun y => (fderiv ℝ Z₀ y) v) x ·)
      (A x t (inhomogLinearODESolution A
          (fun y t => variationalForcing A a b' h₀ Z₀ y v t) a b' h₀
          (fun y => (fderiv ℝ Z₀ y) v) x t)
        + variationalForcing A a b' h₀ Z₀ x v t) t :=
    inhomogLinearODESolution_hasDerivAt hab_lt h₀_mem hU hA_cont hb_cont hx ht
  have hderiv' : HasDerivAt
      (inhomogLinearODESolution A
        (fun y t => variationalForcing A a b' h₀ Z₀ y v t) a b' h₀
        (fun y => (fderiv ℝ Z₀ y) v) x ·)
      (variationalForcing A a b' h₀ Z₀ x v t
        + A x t (inhomogLinearODESolution A
          (fun y t => variationalForcing A a b' h₀ Z₀ y v t) a b' h₀
          (fun y => (fderiv ℝ Z₀ y) v) x t)) t := by
    have := hderiv
    rwa [add_comm] at this
  exact hderiv'

/-- **Joint continuity** of `variationalW` in `(x, t)` for a fixed direction `v`.

Under the same regularity hypotheses as `variationalW_hasDerivAt`, the map
`(x, t) ↦ variationalW A a b' h₀ Z₀ x v t` is jointly continuous on
`U ×ˢ Ioo a b'`.  Continuity of the initial datum `x ↦ (fderiv ℝ Z₀ x) v` on
`U` is supplied as a separate hypothesis (it is the natural regularity input
on `Z₀` for this clause). -/
theorem variationalW_continuousOn
    {A : F → ℝ → (G →L[ℝ] G)} {a b' h₀ : ℝ} {Z₀ : F → G}
    (hab_lt : a < b') (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U)
    (v : F)
    (hZ₀'_cont : ContinuousOn (fun x => (fderiv ℝ Z₀ x) v) U) :
    ContinuousOn
      (Function.uncurry (fun x t => variationalW A a b' h₀ Z₀ x v t))
      (U ×ˢ Set.Ioo a b') := by
  have hb_cont : ContinuousOn
      (Function.uncurry (fun x t => variationalForcing A a b' h₀ Z₀ x v t))
      (U ×ˢ Set.Ioo a b') :=
    variationalForcing_continuousOn hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont v
  exact inhomogLinearODESolution_continuousOn (Z₀ := fun y => (fderiv ℝ Z₀ y) v)
    hab_lt h₀_mem hU hA_cont hb_cont hZ₀'_cont

/-- **Uniqueness for the inhomogeneous linear ODE on an open interval `Ioo a b`**.

Two solutions of `Z' = A Z + b` sharing the initial value at `h₀ ∈ Ioo a b` agree
on `Ioo a b`. The proof reduces to the homogeneous-uniqueness statement
`linearODE_unique_on_Ioo` applied to the difference `Z₁ - Z₂`. -/
theorem inhomogLinearODE_unique_on_Ioo
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {A : ℝ → (G →L[ℝ] G)} {b : ℝ → G} {a b' h₀ : ℝ}
    (ht₀ : h₀ ∈ Set.Ioo a b')
    (hA_cont : ContinuousOn A (Set.Ioo a b'))
    {Z₁ Z₂ : ℝ → G}
    (hZ₁ : ∀ t ∈ Set.Ioo a b', HasDerivAt Z₁ (A t (Z₁ t) + b t) t)
    (hZ₂ : ∀ t ∈ Set.Ioo a b', HasDerivAt Z₂ (A t (Z₂ t) + b t) t)
    (heq : Z₁ h₀ = Z₂ h₀) :
    Set.EqOn Z₁ Z₂ (Set.Ioo a b') := by
  set D : ℝ → G := fun t => Z₁ t - Z₂ t with hD_def
  have hD_deriv : ∀ t ∈ Set.Ioo a b', HasDerivAt D (A t (D t)) t := by
    intro t ht
    have h₁ : HasDerivAt Z₁ (A t (Z₁ t) + b t) t := hZ₁ t ht
    have h₂ : HasDerivAt Z₂ (A t (Z₂ t) + b t) t := hZ₂ t ht
    have hsub : HasDerivAt D ((A t (Z₁ t) + b t) - (A t (Z₂ t) + b t)) t := h₁.sub h₂
    have h_eq : (A t (Z₁ t) + b t) - (A t (Z₂ t) + b t) = A t (D t) := by
      have hD_t : D t = Z₁ t - Z₂ t := rfl
      rw [hD_t, ContinuousLinearMap.map_sub]
      abel
    rw [h_eq] at hsub
    exact hsub
  have h0_deriv : ∀ t ∈ Set.Ioo a b', HasDerivAt (fun _ : ℝ => (0 : G)) (A t ((fun _ => 0) t)) t := by
    intro t _
    have h0 : HasDerivAt (fun _ : ℝ => (0 : G)) 0 t := hasDerivAt_const _ _
    have h_eq : (A t ((fun _ : ℝ => (0 : G)) t)) = 0 := by
      change A t 0 = 0
      rw [ContinuousLinearMap.map_zero]
    rw [h_eq]
    exact h0
  have hD_init : D h₀ = (fun _ : ℝ => (0 : G)) h₀ := by
    change Z₁ h₀ - Z₂ h₀ = 0
    rw [heq, sub_self]
  have hD_eq_zero : Set.EqOn D (fun _ : ℝ => (0 : G)) (Set.Ioo a b') :=
    linearODE_unique_on_Ioo ht₀ hA_cont hD_deriv h0_deriv hD_init
  intro t ht
  have h : D t = 0 := hD_eq_zero ht
  have h' : Z₁ t - Z₂ t = 0 := h
  exact sub_eq_zero.mp h'

/-- **Additivity of `variationalW` in the test direction `v`** at `t ∈ Ioo a b'`. -/
theorem variationalW_add_in_v
    {A : F → ℝ → (G →L[ℝ] G)} {a b' h₀ : ℝ} {Z₀ : F → G}
    (hab_lt : a < b') (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U)
    {x : F} (hx : x ∈ U) (v₁ v₂ : F) {t : ℝ} (ht : t ∈ Set.Ioo a b') :
    variationalW A a b' h₀ Z₀ x (v₁ + v₂) t =
      variationalW A a b' h₀ Z₀ x v₁ t + variationalW A a b' h₀ Z₀ x v₂ t := by
  set Z₁ : ℝ → G := fun s => variationalW A a b' h₀ Z₀ x (v₁ + v₂) s with hZ₁_def
  set Z₂ : ℝ → G := fun s =>
    variationalW A a b' h₀ Z₀ x v₁ s + variationalW A a b' h₀ Z₀ x v₂ s with hZ₂_def
  set b : F → ℝ → G := fun y s => variationalForcing A a b' h₀ Z₀ y (v₁ + v₂) s with hb_def
  have hZ₁_deriv : ∀ s ∈ Set.Ioo a b', HasDerivAt Z₁
      ((fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
          (linearODESolution A a b' h₀ Z₀ x s)
        + A x s (Z₁ s)) s := by
    intro s hs
    have := variationalW_hasDerivAt hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont
      hx (v₁ + v₂) hs
    exact this
  have hZ₂_deriv : ∀ s ∈ Set.Ioo a b', HasDerivAt Z₂
      ((fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
          (linearODESolution A a b' h₀ Z₀ x s)
        + A x s (Z₂ s)) s := by
    intro s hs
    have h1 := variationalW_hasDerivAt hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont
      hx v₁ hs
    have h2 := variationalW_hasDerivAt hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont
      hx v₂ hs
    have hsum := h1.add h2
    have h_eq :
        (fderiv ℝ (fun y => A y s) x) v₁ (linearODESolution A a b' h₀ Z₀ x s)
            + A x s (variationalW A a b' h₀ Z₀ x v₁ s)
          + ((fderiv ℝ (fun y => A y s) x) v₂ (linearODESolution A a b' h₀ Z₀ x s)
            + A x s (variationalW A a b' h₀ Z₀ x v₂ s))
        = (fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
            (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (Z₂ s) := by
      have hfderiv_add :
          (fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
            = (fderiv ℝ (fun y => A y s) x) v₁ + (fderiv ℝ (fun y => A y s) x) v₂ :=
        ContinuousLinearMap.map_add _ _ _
      rw [hfderiv_add]
      change
        (fderiv ℝ (fun y => A y s) x) v₁ (linearODESolution A a b' h₀ Z₀ x s)
            + A x s (variationalW A a b' h₀ Z₀ x v₁ s)
          + ((fderiv ℝ (fun y => A y s) x) v₂ (linearODESolution A a b' h₀ Z₀ x s)
            + A x s (variationalW A a b' h₀ Z₀ x v₂ s))
        = ((fderiv ℝ (fun y => A y s) x) v₁ + (fderiv ℝ (fun y => A y s) x) v₂)
              (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (variationalW A a b' h₀ Z₀ x v₁ s
              + variationalW A a b' h₀ Z₀ x v₂ s)
      rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.map_add]
      abel
    rw [← h_eq]
    exact hsum
  set Ax : ℝ → (G →L[ℝ] G) := fun s => A x s with hAx_def
  have hAx_cont : ContinuousOn Ax (Set.Ioo a b') := by
    intro s hs
    have h : ContinuousAt (fun p : F × ℝ => A p.1 p.2) (x, s) := by
      have : (x, s) ∈ U ×ˢ Set.Ioo a b' := ⟨hx, hs⟩
      have hopen : IsOpen (U ×ˢ Set.Ioo a b') := hU.prod isOpen_Ioo
      exact (hA_cont.continuousAt (hopen.mem_nhds this))
    have hAx_at : ContinuousAt Ax s := by
      have hcurve : ContinuousAt (fun s' : ℝ => ((x, s') : F × ℝ)) s :=
        Continuous.continuousAt (by continuity)
      exact h.comp hcurve
    exact hAx_at.continuousWithinAt
  set bs : ℝ → G := fun s =>
    (fderiv ℝ (fun y => A y s) x) (v₁ + v₂) (linearODESolution A a b' h₀ Z₀ x s)
    with hbs_def
  have hZ₁_deriv' : ∀ s ∈ Set.Ioo a b', HasDerivAt Z₁ (Ax s (Z₁ s) + bs s) s := by
    intro s hs
    have h := hZ₁_deriv s hs
    have h_eq :
        (fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
            (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (Z₁ s)
        = Ax s (Z₁ s) + bs s := by
      change
        (fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
            (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (Z₁ s)
        = A x s (Z₁ s)
          + (fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
              (linearODESolution A a b' h₀ Z₀ x s)
      abel
    rw [h_eq] at h
    exact h
  have hZ₂_deriv' : ∀ s ∈ Set.Ioo a b', HasDerivAt Z₂ (Ax s (Z₂ s) + bs s) s := by
    intro s hs
    have h := hZ₂_deriv s hs
    have h_eq :
        (fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
            (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (Z₂ s)
        = Ax s (Z₂ s) + bs s := by
      change
        (fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
            (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (Z₂ s)
        = A x s (Z₂ s)
          + (fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
              (linearODESolution A a b' h₀ Z₀ x s)
      abel
    rw [h_eq] at h
    exact h
  have hZ₁_init : Z₁ h₀ = (fderiv ℝ Z₀ x) (v₁ + v₂) :=
    variationalW_init A a b' h₀ Z₀ x (v₁ + v₂)
  have hZ₂_init : Z₂ h₀ = (fderiv ℝ Z₀ x) v₁ + (fderiv ℝ Z₀ x) v₂ := by
    change variationalW A a b' h₀ Z₀ x v₁ h₀ + variationalW A a b' h₀ Z₀ x v₂ h₀
      = (fderiv ℝ Z₀ x) v₁ + (fderiv ℝ Z₀ x) v₂
    rw [variationalW_init, variationalW_init]
  have hinit_eq : Z₁ h₀ = Z₂ h₀ := by
    rw [hZ₁_init, hZ₂_init, ContinuousLinearMap.map_add]
  have heq := inhomogLinearODE_unique_on_Ioo h₀_mem hAx_cont hZ₁_deriv' hZ₂_deriv' hinit_eq
  exact heq ht

/-- **Homogeneity of `variationalW` in the test direction `v`** at `t ∈ Ioo a b'`. -/
theorem variationalW_smul_in_v
    {A : F → ℝ → (G →L[ℝ] G)} {a b' h₀ : ℝ} {Z₀ : F → G}
    (hab_lt : a < b') (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U)
    {x : F} (hx : x ∈ U) (c : ℝ) (v : F) {t : ℝ} (ht : t ∈ Set.Ioo a b') :
    variationalW A a b' h₀ Z₀ x (c • v) t = c • variationalW A a b' h₀ Z₀ x v t := by
  set Z₁ : ℝ → G := fun s => variationalW A a b' h₀ Z₀ x (c • v) s with hZ₁_def
  set Z₂ : ℝ → G := fun s => c • variationalW A a b' h₀ Z₀ x v s with hZ₂_def
  set Ax : ℝ → (G →L[ℝ] G) := fun s => A x s with hAx_def
  have hAx_cont : ContinuousOn Ax (Set.Ioo a b') := by
    intro s hs
    have h : ContinuousAt (fun p : F × ℝ => A p.1 p.2) (x, s) := by
      have : (x, s) ∈ U ×ˢ Set.Ioo a b' := ⟨hx, hs⟩
      have hopen : IsOpen (U ×ˢ Set.Ioo a b') := hU.prod isOpen_Ioo
      exact (hA_cont.continuousAt (hopen.mem_nhds this))
    have hAx_at : ContinuousAt Ax s := by
      have hcurve : ContinuousAt (fun s' : ℝ => ((x, s') : F × ℝ)) s :=
        Continuous.continuousAt (by continuity)
      exact h.comp hcurve
    exact hAx_at.continuousWithinAt
  set bs : ℝ → G := fun s =>
    (fderiv ℝ (fun y => A y s) x) (c • v) (linearODESolution A a b' h₀ Z₀ x s)
    with hbs_def
  have hZ₁_deriv : ∀ s ∈ Set.Ioo a b', HasDerivAt Z₁ (Ax s (Z₁ s) + bs s) s := by
    intro s hs
    have h := variationalW_hasDerivAt hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont
      hx (c • v) hs
    have h_eq :
        (fderiv ℝ (fun y => A y s) x) (c • v)
            (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (Z₁ s)
        = Ax s (Z₁ s) + bs s := by
      change
        (fderiv ℝ (fun y => A y s) x) (c • v)
            (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (Z₁ s)
        = A x s (Z₁ s)
          + (fderiv ℝ (fun y => A y s) x) (c • v)
              (linearODESolution A a b' h₀ Z₀ x s)
      abel
    rw [h_eq] at h
    exact h
  have hZ₂_deriv : ∀ s ∈ Set.Ioo a b', HasDerivAt Z₂ (Ax s (Z₂ s) + bs s) s := by
    intro s hs
    have h := variationalW_hasDerivAt hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont
      hx v hs
    have hsmul : HasDerivAt (fun s' => c • variationalW A a b' h₀ Z₀ x v s')
        (c • ((fderiv ℝ (fun y => A y s) x) v (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (variationalW A a b' h₀ Z₀ x v s))) s := h.const_smul c
    have h_eq :
        c • ((fderiv ℝ (fun y => A y s) x) v (linearODESolution A a b' h₀ Z₀ x s)
              + A x s (variationalW A a b' h₀ Z₀ x v s))
        = Ax s (Z₂ s) + bs s := by
      have hL :
          (fderiv ℝ (fun y => A y s) x) (c • v)
            = c • (fderiv ℝ (fun y => A y s) x) v :=
        ContinuousLinearMap.map_smul _ _ _
      change
        c • ((fderiv ℝ (fun y => A y s) x) v (linearODESolution A a b' h₀ Z₀ x s)
              + A x s (variationalW A a b' h₀ Z₀ x v s))
        = A x s (c • variationalW A a b' h₀ Z₀ x v s)
          + (fderiv ℝ (fun y => A y s) x) (c • v)
              (linearODESolution A a b' h₀ Z₀ x s)
      rw [hL, ContinuousLinearMap.smul_apply, ContinuousLinearMap.map_smul, smul_add]
      abel
    rw [← h_eq]
    exact hsmul
  have hZ₁_init : Z₁ h₀ = (fderiv ℝ Z₀ x) (c • v) :=
    variationalW_init A a b' h₀ Z₀ x (c • v)
  have hZ₂_init : Z₂ h₀ = c • (fderiv ℝ Z₀ x) v := by
    change c • variationalW A a b' h₀ Z₀ x v h₀ = c • (fderiv ℝ Z₀ x) v
    rw [variationalW_init]
  have hinit_eq : Z₁ h₀ = Z₂ h₀ := by
    rw [hZ₁_init, hZ₂_init, ContinuousLinearMap.map_smul]
  have heq := inhomogLinearODE_unique_on_Ioo h₀_mem hAx_cont hZ₁_deriv hZ₂_deriv hinit_eq
  exact heq ht

/-- **Linearity in the test direction `v`** of the variational solution, packaged as
the conjunction of additivity and homogeneity, at any `t ∈ Ioo a b'`. -/
theorem variationalW_linear_in_v
    {A : F → ℝ → (G →L[ℝ] G)} {a b' h₀ : ℝ} {Z₀ : F → G}
    (hab_lt : a < b') (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U)
    {x : F} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Set.Ioo a b') :
    (∀ v₁ v₂ : F, variationalW A a b' h₀ Z₀ x (v₁ + v₂) t =
        variationalW A a b' h₀ Z₀ x v₁ t + variationalW A a b' h₀ Z₀ x v₂ t) ∧
    (∀ (c : ℝ) (v : F), variationalW A a b' h₀ Z₀ x (c • v) t =
        c • variationalW A a b' h₀ Z₀ x v t) :=
  ⟨fun v₁ v₂ => variationalW_add_in_v hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont hx v₁ v₂ ht,
   fun c v => variationalW_smul_in_v hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont hx c v ht⟩

/-- **Apriori bound for `variationalW` on a closed sub-interval, linear in `‖v‖`**.

If `[α, β] ⊂ Ioo a b'` contains both `h₀` and `t`, and `M` bounds `‖A x ·‖`,
`P` bounds `‖fderiv (A · s) x‖`, `Q` bounds `‖linearODESolution A … x ·‖` on
`Icc α β`, and `R` bounds `‖fderiv Z₀ x‖` (as an operator norm in `v`),
then for every `v : F` and every `t ∈ Icc α β`:
`‖variationalW A a b' h₀ Z₀ x v t‖
  ≤ gronwallBound R M (P · Q) (β - α) · ‖v‖`. -/
private theorem variationalW_norm_bound_on_Icc
    {A : F → ℝ → (G →L[ℝ] G)} {a b' h₀ : ℝ} {Z₀ : F → G}
    (hab_lt : a < b') (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U)
    {x : F} (hx : x ∈ U)
    {α β : ℝ} (_hαβ : α ≤ β) (hα_lt : a < α) (hβ_lt : β < b')
    (hh₀_mem : h₀ ∈ Set.Icc α β)
    (M P Q R : ℝ) (hM_nn : 0 ≤ M) (hP_nn : 0 ≤ P) (hQ_nn : 0 ≤ Q) (hR_nn : 0 ≤ R)
    (hA_bd : ∀ s ∈ Set.Icc α β, ‖A x s‖ ≤ M)
    (hDA_bd : ∀ s ∈ Set.Icc α β, ‖fderiv ℝ (fun y => A y s) x‖ ≤ P)
    (hZ_bd : ∀ s ∈ Set.Icc α β, ‖linearODESolution A a b' h₀ Z₀ x s‖ ≤ Q)
    (hZ₀'_bd : ‖fderiv ℝ Z₀ x‖ ≤ R)
    (v : F) (t : ℝ) (ht : t ∈ Set.Icc α β) :
    ‖variationalW A a b' h₀ Z₀ x v t‖
      ≤ gronwallBound R M (P * Q) (β - α) * ‖v‖ := by
  set W : ℝ → G := variationalW A a b' h₀ Z₀ x v with hW_def
  have hsub_open : Set.Icc α β ⊆ Set.Ioo a b' := fun s hs =>
    ⟨lt_of_lt_of_le hα_lt hs.1, lt_of_le_of_lt hs.2 hβ_lt⟩
  have hW_deriv : ∀ s ∈ Set.Icc α β,
      HasDerivAt W
        ((fderiv ℝ (fun y => A y s) x) v (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (W s)) s := fun s hs =>
    variationalW_hasDerivAt hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont
      hx v (hsub_open hs)
  have hW_cont : ContinuousOn W (Set.Icc α β) := fun s hs =>
    ((hW_deriv s hs).continuousAt).continuousWithinAt
  have hW_init : W h₀ = (fderiv ℝ Z₀ x) v := variationalW_init A a b' h₀ Z₀ x v
  set bv : ℝ → G := fun s =>
    (fderiv ℝ (fun y => A y s) x) v (linearODESolution A a b' h₀ Z₀ x s) with hbv_def
  have hbv_bd : ∀ s ∈ Set.Icc α β, ‖bv s‖ ≤ P * Q * ‖v‖ := by
    intro s hs
    have h1 : ‖(fderiv ℝ (fun y => A y s) x) v‖
        ≤ ‖fderiv ℝ (fun y => A y s) x‖ * ‖v‖ :=
      (fderiv ℝ (fun y => A y s) x).le_opNorm v
    have h2 : ‖(fderiv ℝ (fun y => A y s) x) v (linearODESolution A a b' h₀ Z₀ x s)‖
        ≤ ‖(fderiv ℝ (fun y => A y s) x) v‖ * ‖linearODESolution A a b' h₀ Z₀ x s‖ :=
      ((fderiv ℝ (fun y => A y s) x) v).le_opNorm _
    have h3 : ‖(fderiv ℝ (fun y => A y s) x) v‖ * ‖linearODESolution A a b' h₀ Z₀ x s‖
        ≤ (‖fderiv ℝ (fun y => A y s) x‖ * ‖v‖)
            * ‖linearODESolution A a b' h₀ Z₀ x s‖ :=
      mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have h4 : (‖fderiv ℝ (fun y => A y s) x‖ * ‖v‖)
            * ‖linearODESolution A a b' h₀ Z₀ x s‖
        ≤ (P * ‖v‖) * Q :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hDA_bd s hs) (norm_nonneg _))
        (hZ_bd s hs) (norm_nonneg _) (by positivity)
    calc ‖bv s‖ ≤ ‖(fderiv ℝ (fun y => A y s) x) v‖
                  * ‖linearODESolution A a b' h₀ Z₀ x s‖ := h2
      _ ≤ (‖fderiv ℝ (fun y => A y s) x‖ * ‖v‖)
            * ‖linearODESolution A a b' h₀ Z₀ x s‖ := h3
      _ ≤ (P * ‖v‖) * Q := h4
      _ = P * Q * ‖v‖ := by ring
  have h_h₀_le_β : h₀ ≤ β := hh₀_mem.2
  have h_α_le_h₀ : α ≤ h₀ := hh₀_mem.1
  have hIcc_fwd_sub : Set.Icc h₀ β ⊆ Set.Icc α β := fun s hs =>
    ⟨le_trans h_α_le_h₀ hs.1, hs.2⟩
  have hIcc_bwd_sub : Set.Icc α h₀ ⊆ Set.Icc α β := fun s hs =>
    ⟨hs.1, le_trans hs.2 h_h₀_le_β⟩
  have hW'_bound : ∀ s ∈ Set.Icc α β,
      ‖(fderiv ℝ (fun y => A y s) x) v (linearODESolution A a b' h₀ Z₀ x s)
        + A x s (W s)‖ ≤ M * ‖W s‖ + P * Q * ‖v‖ := by
    intro s hs
    have ha : ‖A x s (W s)‖ ≤ M * ‖W s‖ := by
      have h1 : ‖A x s (W s)‖ ≤ ‖A x s‖ * ‖W s‖ := (A x s).le_opNorm (W s)
      have h2 : ‖A x s‖ * ‖W s‖ ≤ M * ‖W s‖ :=
        mul_le_mul_of_nonneg_right (hA_bd s hs) (norm_nonneg _)
      linarith
    have hb : ‖bv s‖ ≤ P * Q * ‖v‖ := hbv_bd s hs
    have h_tri := norm_add_le (bv s) (A x s (W s))
    calc ‖bv s + A x s (W s)‖
        ≤ ‖bv s‖ + ‖A x s (W s)‖ := h_tri
      _ ≤ P * Q * ‖v‖ + M * ‖W s‖ := by linarith
      _ = M * ‖W s‖ + P * Q * ‖v‖ := by ring
  have hW_init_bd : ‖W h₀‖ ≤ R * ‖v‖ := by
    rw [hW_init]
    calc ‖(fderiv ℝ Z₀ x) v‖
        ≤ ‖fderiv ℝ Z₀ x‖ * ‖v‖ := (fderiv ℝ Z₀ x).le_opNorm v
      _ ≤ R * ‖v‖ := mul_le_mul_of_nonneg_right hZ₀'_bd (norm_nonneg _)
  have hv_nn : 0 ≤ ‖v‖ := norm_nonneg _
  have hPQ_nn : 0 ≤ P * Q := mul_nonneg hP_nn hQ_nn
  have h_gb_scale : ∀ y : ℝ,
      gronwallBound (R * ‖v‖) M (P * Q * ‖v‖) y
        = gronwallBound R M (P * Q) y * ‖v‖ := by
    intro y
    by_cases hM_eq : M = 0
    · simp only [gronwallBound_K0, hM_eq]
      ring
    · simp only [gronwallBound_of_K_ne_0 hM_eq]
      field_simp
  have h_gb_mono : ∀ y₁ y₂ : ℝ, y₁ ≤ y₂ →
      gronwallBound R M (P * Q) y₁ ≤ gronwallBound R M (P * Q) y₂ :=
    fun y₁ y₂ hy => gronwallBound_mono hR_nn hPQ_nn hM_nn hy
  rcases le_total h₀ t with hh₀t | hth₀
  · have ht' : t ∈ Set.Icc h₀ β := ⟨hh₀t, ht.2⟩
    have hW_cont_fwd : ContinuousOn W (Set.Icc h₀ β) := hW_cont.mono hIcc_fwd_sub
    have hW_deriv_right : ∀ s ∈ Set.Ico h₀ β, HasDerivWithinAt W
        ((fderiv ℝ (fun y => A y s) x) v (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (W s)) (Set.Ici s) s := fun s hs =>
      (hW_deriv s (hIcc_fwd_sub (Set.Ico_subset_Icc_self hs))).hasDerivWithinAt
    have hbound_fwd : ∀ s ∈ Set.Ico h₀ β,
        ‖(fderiv ℝ (fun y => A y s) x) v (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (W s)‖ ≤ M * ‖W s‖ + P * Q * ‖v‖ := fun s hs =>
      hW'_bound s (hIcc_fwd_sub (Set.Ico_subset_Icc_self hs))
    have hgw := norm_le_gronwallBound_of_norm_deriv_right_le
      hW_cont_fwd hW_deriv_right hW_init_bd hbound_fwd t ht'
    rw [h_gb_scale (t - h₀)] at hgw
    have h_t_sub_le : t - h₀ ≤ β - α := by linarith [ht.2, h_α_le_h₀]
    have h_step : gronwallBound R M (P * Q) (t - h₀) ≤ gronwallBound R M (P * Q) (β - α) :=
      h_gb_mono _ _ h_t_sub_le
    calc ‖W t‖
        ≤ gronwallBound R M (P * Q) (t - h₀) * ‖v‖ := hgw
      _ ≤ gronwallBound R M (P * Q) (β - α) * ‖v‖ :=
          mul_le_mul_of_nonneg_right h_step hv_nn
  · have ht' : t ∈ Set.Icc α h₀ := ⟨ht.1, hth₀⟩
    set Wb : ℝ → G := fun s => W (2 * h₀ - s) with hWb_def
    have h_h₀_le_2h₀mt : h₀ ≤ 2 * h₀ - t := by linarith
    have h_dom_swap : ∀ s ∈ Set.Icc h₀ (2 * h₀ - t), 2 * h₀ - s ∈ Set.Icc α h₀ := by
      intro s hs
      refine ⟨?_, ?_⟩
      · linarith [hs.2, ht'.1]
      · linarith [hs.1]
    have hWb_cont : ContinuousOn Wb (Set.Icc h₀ (2 * h₀ - t)) := by
      apply ContinuousOn.comp (hW_cont.mono hIcc_bwd_sub) (s := Set.Icc h₀ (2 * h₀ - t))
        (t := Set.Icc α h₀) (f := fun s => 2 * h₀ - s)
      · exact (continuous_const.sub continuous_id).continuousOn
      · exact h_dom_swap
    have hWb_deriv : ∀ s ∈ Set.Icc h₀ (2 * h₀ - t),
        HasDerivAt Wb (-((fderiv ℝ (fun y => A y (2 * h₀ - s)) x) v
              (linearODESolution A a b' h₀ Z₀ x (2 * h₀ - s))
            + A x (2 * h₀ - s) (W (2 * h₀ - s)))) s := by
      intro s hs
      have hd : HasDerivAt W
          ((fderiv ℝ (fun y => A y (2 * h₀ - s)) x) v
            (linearODESolution A a b' h₀ Z₀ x (2 * h₀ - s))
          + A x (2 * h₀ - s) (W (2 * h₀ - s))) (2 * h₀ - s) :=
        hW_deriv (2 * h₀ - s) (hIcc_bwd_sub (h_dom_swap s hs))
      have h_chain : HasDerivAt (fun r : ℝ => 2 * h₀ - r) (-1 : ℝ) s := by
        simpa using ((hasDerivAt_const s (2 * h₀)).sub (hasDerivAt_id s))
      have hd' := hd.scomp s h_chain
      have h_eq_smul :
          (-1 : ℝ) • ((fderiv ℝ (fun y => A y (2 * h₀ - s)) x) v
              (linearODESolution A a b' h₀ Z₀ x (2 * h₀ - s))
            + A x (2 * h₀ - s) (W (2 * h₀ - s)))
          = -((fderiv ℝ (fun y => A y (2 * h₀ - s)) x) v
              (linearODESolution A a b' h₀ Z₀ x (2 * h₀ - s))
            + A x (2 * h₀ - s) (W (2 * h₀ - s))) :=
        neg_one_smul ℝ _
      rw [h_eq_smul] at hd'
      exact hd'
    have hWb_init : Wb h₀ = W h₀ := by
      change W (2 * h₀ - h₀) = W h₀
      have : 2 * h₀ - h₀ = h₀ := by ring
      rw [this]
    have hWb'_bound : ∀ s ∈ Set.Icc h₀ (2 * h₀ - t),
        ‖-((fderiv ℝ (fun y => A y (2 * h₀ - s)) x) v
              (linearODESolution A a b' h₀ Z₀ x (2 * h₀ - s))
            + A x (2 * h₀ - s) (W (2 * h₀ - s)))‖
          ≤ M * ‖Wb s‖ + P * Q * ‖v‖ := by
      intro s hs
      have h_in : 2 * h₀ - s ∈ Set.Icc α β := hIcc_bwd_sub (h_dom_swap s hs)
      have h := hW'_bound (2 * h₀ - s) h_in
      have hWbs_eq : Wb s = W (2 * h₀ - s) := rfl
      rw [norm_neg, hWbs_eq]
      exact h
    have hWb_init_bd : ‖Wb h₀‖ ≤ R * ‖v‖ := by
      rw [hWb_init]; exact hW_init_bd
    have hWb_deriv_right : ∀ s ∈ Set.Ico h₀ (2 * h₀ - t),
        HasDerivWithinAt Wb (-((fderiv ℝ (fun y => A y (2 * h₀ - s)) x) v
            (linearODESolution A a b' h₀ Z₀ x (2 * h₀ - s))
          + A x (2 * h₀ - s) (W (2 * h₀ - s)))) (Set.Ici s) s := fun s hs =>
      (hWb_deriv s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt
    have hbound_bwd : ∀ s ∈ Set.Ico h₀ (2 * h₀ - t),
        ‖-((fderiv ℝ (fun y => A y (2 * h₀ - s)) x) v
              (linearODESolution A a b' h₀ Z₀ x (2 * h₀ - s))
            + A x (2 * h₀ - s) (W (2 * h₀ - s)))‖
          ≤ M * ‖Wb s‖ + P * Q * ‖v‖ := fun s hs =>
      hWb'_bound s (Set.Ico_subset_Icc_self hs)
    have hgw_bwd := norm_le_gronwallBound_of_norm_deriv_right_le
      hWb_cont hWb_deriv_right hWb_init_bd hbound_bwd
      (2 * h₀ - t) (right_mem_Icc.mpr h_h₀_le_2h₀mt)
    have hWb_t : Wb (2 * h₀ - t) = W t := by
      change W (2 * h₀ - (2 * h₀ - t)) = W t
      have : 2 * h₀ - (2 * h₀ - t) = t := by ring
      rw [this]
    rw [hWb_t] at hgw_bwd
    have h_time : 2 * h₀ - t - h₀ = h₀ - t := by ring
    rw [h_time] at hgw_bwd
    rw [h_gb_scale (h₀ - t)] at hgw_bwd
    have h_h₀mt_le : h₀ - t ≤ β - α := by linarith [ht.1, h_h₀_le_β]
    have h_step : gronwallBound R M (P * Q) (h₀ - t) ≤ gronwallBound R M (P * Q) (β - α) :=
      h_gb_mono _ _ h_h₀mt_le
    calc ‖W t‖
        ≤ gronwallBound R M (P * Q) (h₀ - t) * ‖v‖ := hgw_bwd
      _ ≤ gronwallBound R M (P * Q) (β - α) * ‖v‖ :=
          mul_le_mul_of_nonneg_right h_step hv_nn

/-- **Packaging `v ↦ variationalW A a b' h₀ Z₀ x v t` as a continuous linear map**
`F →L[ℝ] G`, for any `t ∈ Ioo a b'`.

The underlying linear map is `v ↦ variationalW A a b' h₀ Z₀ x v t`, whose linearity
is `variationalW_linear_in_v`.  The operator-norm bound is obtained by applying
`variationalW_norm_bound_on_Icc` to any closed sub-interval `[α, β] ⊂ Ioo a b'`
containing both `h₀` and `t`. -/
noncomputable def variationalW_clm
    {A : F → ℝ → (G →L[ℝ] G)} {a b' : ℝ} (hab_lt : a < b')
    {h₀ : ℝ} (h₀_mem : h₀ ∈ Set.Ioo a b')
    {Z₀ : F → G}
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U)
    {x : F} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Set.Ioo a b') :
    F →L[ℝ] G :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun v => variationalW A a b' h₀ Z₀ x v t
      map_add' := fun v₁ v₂ =>
        variationalW_add_in_v hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont hx v₁ v₂ ht
      map_smul' := fun c v => by
        have h := variationalW_smul_in_v hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont
          hx c v ht
        simpa using h }
    (by
      classical
      set α := (a + min t h₀) / 2 with hα_def
      set β := (b' + max t h₀) / 2 with hβ_def
      have hmin_lt : a < min t h₀ := lt_min ht.1 h₀_mem.1
      have hmax_lt : max t h₀ < b' := max_lt ht.2 h₀_mem.2
      have hmin_le_t : min t h₀ ≤ t := min_le_left _ _
      have hmin_le_t₀ : min t h₀ ≤ h₀ := min_le_right _ _
      have ht_le_max : t ≤ max t h₀ := le_max_left _ _
      have ht₀_le_max : h₀ ≤ max t h₀ := le_max_right _ _
      have hα_lt_min : α < min t h₀ := by rw [hα_def]; linarith
      have ha_lt_α : a < α := by rw [hα_def]; linarith
      have hmax_lt_β : max t h₀ < β := by rw [hβ_def]; linarith
      have hβ_lt_b' : β < b' := by rw [hβ_def]; linarith
      have hα_le_β : α ≤ β := by linarith
      have hh₀_mem : h₀ ∈ Set.Icc α β :=
        ⟨le_of_lt (lt_of_lt_of_le hα_lt_min hmin_le_t₀),
         le_of_lt (lt_of_le_of_lt ht₀_le_max hmax_lt_β)⟩
      have h_t_Icc : t ∈ Set.Icc α β :=
        ⟨le_of_lt (lt_of_lt_of_le hα_lt_min hmin_le_t),
         le_of_lt (lt_of_le_of_lt ht_le_max hmax_lt_β)⟩
      have hIcc_sub : Set.Icc α β ⊆ Set.Ioo a b' := fun s hs =>
        ⟨lt_of_lt_of_le ha_lt_α hs.1, lt_of_le_of_lt hs.2 hβ_lt_b'⟩
      have hIcc_cpt : IsCompact (Set.Icc α β) := isCompact_Icc
      have hIcc_ne : (Set.Icc α β).Nonempty := ⟨α, left_mem_Icc.mpr hα_le_β⟩
      have hAx_cont_Icc : ContinuousOn (fun s => A x s) (Set.Icc α β) := by
        intro s hs
        have h : ContinuousAt (fun p : F × ℝ => A p.1 p.2) (x, s) := by
          have hxs : (x, s) ∈ U ×ˢ Set.Ioo a b' := ⟨hx, hIcc_sub hs⟩
          have hopen : IsOpen (U ×ˢ Set.Ioo a b') := hU.prod isOpen_Ioo
          exact hA_cont.continuousAt (hopen.mem_nhds hxs)
        have hcurve : ContinuousAt (fun s' : ℝ => ((x, s') : F × ℝ)) s :=
          Continuous.continuousAt (by continuity)
        exact (h.comp hcurve).continuousWithinAt
      have h_normA_cont : ContinuousOn (fun s => ‖A x s‖) (Set.Icc α β) :=
        continuous_norm.comp_continuousOn hAx_cont_Icc
      obtain ⟨σM, _, hM_bd⟩ := hIcc_cpt.exists_isMaxOn hIcc_ne h_normA_cont
      let Mv : ℝ := ‖A x σM‖
      have hMv_nn : 0 ≤ Mv := norm_nonneg _
      have hMv_bd : ∀ s ∈ Set.Icc α β, ‖A x s‖ ≤ Mv := fun s hs => hM_bd hs
      have hDAx_cont_Icc : ContinuousOn (fun s => fderiv ℝ (fun y => A y s) x)
          (Set.Icc α β) := by
        intro s hs
        have h : ContinuousAt (Function.uncurry fun x' t' => fderiv ℝ (fun y => A y t') x')
            (x, s) := by
          have hxs : (x, s) ∈ U ×ˢ Set.Ioo a b' := ⟨hx, hIcc_sub hs⟩
          have hopen : IsOpen (U ×ˢ Set.Ioo a b') := hU.prod isOpen_Ioo
          exact hDA_cont.continuousAt (hopen.mem_nhds hxs)
        have hcurve : ContinuousAt (fun s' : ℝ => ((x, s') : F × ℝ)) s :=
          Continuous.continuousAt (by continuity)
        exact (h.comp hcurve).continuousWithinAt
      have h_normDA_cont : ContinuousOn (fun s => ‖fderiv ℝ (fun y => A y s) x‖)
          (Set.Icc α β) := continuous_norm.comp_continuousOn hDAx_cont_Icc
      obtain ⟨σP, _, hP_bd⟩ := hIcc_cpt.exists_isMaxOn hIcc_ne h_normDA_cont
      let Pv : ℝ := ‖fderiv ℝ (fun y => A y σP) x‖
      have hPv_nn : 0 ≤ Pv := norm_nonneg _
      have hPv_bd : ∀ s ∈ Set.Icc α β, ‖fderiv ℝ (fun y => A y s) x‖ ≤ Pv :=
        fun s hs => hP_bd hs
      have hZ_cont_full : ContinuousOn (Function.uncurry (linearODESolution A a b' h₀ Z₀))
          (U ×ˢ Set.Ioo a b') :=
        linearODESolution_continuousOn hab_lt h₀_mem hU hA_cont hZ₀_cont
      have hZx_cont_Icc : ContinuousOn (linearODESolution A a b' h₀ Z₀ x) (Set.Icc α β) := by
        intro s hs
        have h : ContinuousAt (Function.uncurry (linearODESolution A a b' h₀ Z₀)) (x, s) := by
          have hxs : (x, s) ∈ U ×ˢ Set.Ioo a b' := ⟨hx, hIcc_sub hs⟩
          have hopen : IsOpen (U ×ˢ Set.Ioo a b') := hU.prod isOpen_Ioo
          exact hZ_cont_full.continuousAt (hopen.mem_nhds hxs)
        have hcurve : ContinuousAt (fun s' : ℝ => ((x, s') : F × ℝ)) s :=
          Continuous.continuousAt (by continuity)
        exact (h.comp hcurve).continuousWithinAt
      have h_normZ_cont : ContinuousOn (fun s => ‖linearODESolution A a b' h₀ Z₀ x s‖)
          (Set.Icc α β) := continuous_norm.comp_continuousOn hZx_cont_Icc
      obtain ⟨σQ, _, hQ_bd⟩ := hIcc_cpt.exists_isMaxOn hIcc_ne h_normZ_cont
      let Qv : ℝ := ‖linearODESolution A a b' h₀ Z₀ x σQ‖
      have hQv_nn : 0 ≤ Qv := norm_nonneg _
      have hQv_bd : ∀ s ∈ Set.Icc α β, ‖linearODESolution A a b' h₀ Z₀ x s‖ ≤ Qv :=
        fun s hs => hQ_bd hs
      let Rv : ℝ := ‖fderiv ℝ Z₀ x‖
      have hRv_nn : 0 ≤ Rv := norm_nonneg _
      refine ⟨gronwallBound Rv Mv (Pv * Qv) (β - α), fun v => ?_⟩
      have h := variationalW_norm_bound_on_Icc hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont
        hx hα_le_β ha_lt_α hβ_lt_b' hh₀_mem Mv Pv Qv Rv hMv_nn hPv_nn hQv_nn hRv_nn
        hMv_bd hPv_bd hQv_bd le_rfl v t h_t_Icc
      simpa using h)

/-- **`variationalW_clm` agrees with `variationalW`** pointwise. -/
theorem variationalW_clm_apply
    {A : F → ℝ → (G →L[ℝ] G)} {a b' : ℝ} (hab_lt : a < b')
    {h₀ : ℝ} (h₀_mem : h₀ ∈ Set.Ioo a b')
    {Z₀ : F → G}
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U)
    {x : F} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Set.Ioo a b') (v : F) :
    variationalW_clm hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht v
      = variationalW A a b' h₀ Z₀ x v t := rfl

/-- **Parametric stability for the linear ODE** on a closed sub-interval.

Given `Icc α β ⊂ Ioo a b'` containing `h₀`, two parameters `x₁, x₂ ∈ U`, an
operator-norm bound `K` for `A x₁` on the interval, and a forcing bound `η`
for `‖(A x₂ s - A x₁ s) (Z(x₂, s))‖`, the difference between the two
parametric solutions at any `t ∈ Icc α β` is bounded by

`gronwallBound ‖Z₀(x₁) - Z₀(x₂)‖ K η |t - h₀|`.

This is a public wrapper around the forward / backward Grönwall comparison
specialised to the (jointly continuous) parametric solution `linearODESolution`. -/
theorem linearODESolution_dist_le
    {A : F → ℝ → (G →L[ℝ] G)} {a b' h₀ : ℝ} {Z₀ : F → G}
    (hab_lt : a < b') (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    {x₁ x₂ : F} (hx₁ : x₁ ∈ U) (hx₂ : x₂ ∈ U)
    {α β : ℝ} (_hαβ : α ≤ β) (hα_lt : a < α) (hβ_lt : β < b')
    (hh₀_mem : h₀ ∈ Set.Icc α β)
    {K η : ℝ} (hK_nn : 0 ≤ K)
    (hA₁_bd : ∀ s ∈ Set.Icc α β, ‖A x₁ s‖ ≤ K)
    (hdiff_bd : ∀ s ∈ Set.Icc α β,
      ‖(A x₂ s - A x₁ s) (linearODESolution A a b' h₀ Z₀ x₂ s)‖ ≤ η)
    {t : ℝ} (ht : t ∈ Set.Icc α β) :
    ‖linearODESolution A a b' h₀ Z₀ x₁ t - linearODESolution A a b' h₀ Z₀ x₂ t‖
      ≤ gronwallBound ‖Z₀ x₁ - Z₀ x₂‖ K η |t - h₀| := by
  set Z : F → ℝ → G := linearODESolution A a b' h₀ Z₀ with hZ_def
  have hZ_deriv₁ : ∀ s ∈ Set.Ioo a b', HasDerivAt (Z x₁) (A x₁ s (Z x₁ s)) s :=
    fun s hs => linearODESolution_hasDerivAt hab_lt h₀_mem hU hA_cont hx₁ hs
  have hZ_deriv₂ : ∀ s ∈ Set.Ioo a b', HasDerivAt (Z x₂) (A x₂ s (Z x₂ s)) s :=
    fun s hs => linearODESolution_hasDerivAt hab_lt h₀_mem hU hA_cont hx₂ hs
  have hZ_init₁ : Z x₁ h₀ = Z₀ x₁ := linearODESolution_init A a b' h₀ Z₀ x₁
  have hZ_init₂ : Z x₂ h₀ = Z₀ x₂ := linearODESolution_init A a b' h₀ Z₀ x₂
  have hIcc_sub_Ioo : Set.Icc α β ⊆ Set.Ioo a b' := fun s hs =>
    ⟨lt_of_lt_of_le hα_lt hs.1, lt_of_le_of_lt hs.2 hβ_lt⟩
  have hZ_cont₁ : ContinuousOn (Z x₁) (Set.Icc α β) := fun s hs =>
    ((hZ_deriv₁ s (hIcc_sub_Ioo hs)).continuousAt).continuousWithinAt
  have hZ_cont₂ : ContinuousOn (Z x₂) (Set.Icc α β) := fun s hs =>
    ((hZ_deriv₂ s (hIcc_sub_Ioo hs)).continuousAt).continuousWithinAt
  have hα_le_h₀ : α ≤ h₀ := hh₀_mem.1
  have hh₀_le_β : h₀ ≤ β := hh₀_mem.2
  rcases le_total h₀ t with hht | hth
  · have hIcc_fwd_sub : Set.Icc h₀ β ⊆ Set.Icc α β := fun s hs =>
      ⟨le_trans hα_le_h₀ hs.1, hs.2⟩
    have hZ₁_cont_fwd : ContinuousOn (Z x₁) (Set.Icc h₀ β) := hZ_cont₁.mono hIcc_fwd_sub
    have hZ₂_cont_fwd : ContinuousOn (Z x₂) (Set.Icc h₀ β) := hZ_cont₂.mono hIcc_fwd_sub
    have hZ₁_deriv_fwd : ∀ s ∈ Set.Icc h₀ β, HasDerivAt (Z x₁) (A x₁ s (Z x₁ s)) s :=
      fun s hs => hZ_deriv₁ s (hIcc_sub_Ioo (hIcc_fwd_sub hs))
    have hZ₂_deriv_fwd : ∀ s ∈ Set.Icc h₀ β, HasDerivAt (Z x₂) (A x₂ s (Z x₂ s)) s :=
      fun s hs => hZ_deriv₂ s (hIcc_sub_Ioo (hIcc_fwd_sub hs))
    have hA₁_bd_fwd : ∀ s ∈ Set.Icc h₀ β, ‖A x₁ s‖ ≤ K := fun s hs =>
      hA₁_bd s (hIcc_fwd_sub hs)
    have hdiff_bd_fwd : ∀ s ∈ Set.Icc h₀ β,
        ‖(A x₂ s - A x₁ s) (Z x₂ s)‖ ≤ η := fun s hs =>
      hdiff_bd s (hIcc_fwd_sub hs)
    have hres := linearODE_gronwall_forward (A₁ := A x₁) (A₂ := A x₂)
      (Z₁ := Z x₁) (Z₂ := Z x₂) (h₀ := h₀) (β := β) (K := K) (η := η)
      hh₀_le_β hK_nn hZ₁_cont_fwd hZ₂_cont_fwd hZ₁_deriv_fwd hZ₂_deriv_fwd
      hA₁_bd_fwd hdiff_bd_fwd t ⟨hht, ht.2⟩
    have h_init_eq : ‖Z x₁ h₀ - Z x₂ h₀‖ = ‖Z₀ x₁ - Z₀ x₂‖ := by
      rw [hZ_init₁, hZ_init₂]
    rw [h_init_eq] at hres
    have h_abs : |t - h₀| = t - h₀ := abs_of_nonneg (by linarith)
    rw [h_abs]
    exact hres
  · have hIcc_bwd_sub : Set.Icc α h₀ ⊆ Set.Icc α β := fun s hs =>
      ⟨hs.1, le_trans hs.2 hh₀_le_β⟩
    have hZ₁_cont_bwd : ContinuousOn (Z x₁) (Set.Icc α h₀) := hZ_cont₁.mono hIcc_bwd_sub
    have hZ₂_cont_bwd : ContinuousOn (Z x₂) (Set.Icc α h₀) := hZ_cont₂.mono hIcc_bwd_sub
    have hZ₁_deriv_bwd : ∀ s ∈ Set.Icc α h₀, HasDerivAt (Z x₁) (A x₁ s (Z x₁ s)) s :=
      fun s hs => hZ_deriv₁ s (hIcc_sub_Ioo (hIcc_bwd_sub hs))
    have hZ₂_deriv_bwd : ∀ s ∈ Set.Icc α h₀, HasDerivAt (Z x₂) (A x₂ s (Z x₂ s)) s :=
      fun s hs => hZ_deriv₂ s (hIcc_sub_Ioo (hIcc_bwd_sub hs))
    have hA₁_bd_bwd : ∀ s ∈ Set.Icc α h₀, ‖A x₁ s‖ ≤ K := fun s hs =>
      hA₁_bd s (hIcc_bwd_sub hs)
    have hdiff_bd_bwd : ∀ s ∈ Set.Icc α h₀,
        ‖(A x₂ s - A x₁ s) (Z x₂ s)‖ ≤ η := fun s hs =>
      hdiff_bd s (hIcc_bwd_sub hs)
    have hres := linearODE_gronwall_backward (A₁ := A x₁) (A₂ := A x₂)
      (Z₁ := Z x₁) (Z₂ := Z x₂) (α := α) (h₀ := h₀) (K := K) (η := η)
      hα_le_h₀ hK_nn hZ₁_cont_bwd hZ₂_cont_bwd hZ₁_deriv_bwd hZ₂_deriv_bwd
      hA₁_bd_bwd hdiff_bd_bwd t ⟨ht.1, hth⟩
    have h_init_eq : ‖Z x₁ h₀ - Z x₂ h₀‖ = ‖Z₀ x₁ - Z₀ x₂‖ := by
      rw [hZ_init₁, hZ_init₂]
    rw [h_init_eq] at hres
    have h_abs : |t - h₀| = h₀ - t := by
      rw [abs_of_nonpos (by linarith)]; ring
    rw [h_abs]
    exact hres

set_option maxHeartbeats 1600000 in
/-- **Differentiability in the parameter** of the linear ODE solution.

For `A` and `Z₀` of class `C^1` in `x` (with jointly continuous coefficient
and derivative), the parametric solution `x ↦ linearODESolution A a b' h₀ Z₀
x t` is Fréchet differentiable at any `x ∈ U` with derivative
`variationalW_clm … x t : F →L[ℝ] G`, the CLM packaging of the variational
solution `v ↦ variationalW A a b' h₀ Z₀ x v t`. -/
theorem linearODESolution_hasFDerivAt_param
    [FiniteDimensional ℝ F]
    {A : F → ℝ → (G →L[ℝ] G)} {Z₀ : F → G}
    {a b' : ℝ} (hab_lt : a < b') {h₀ : ℝ} (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hA_diff : ∀ y ∈ U, ∀ s ∈ Set.Ioo a b',
      HasFDerivAt (fun z => A z s) (fderiv ℝ (fun z => A z s) y) y)
    (hZ₀_cont : ContinuousOn Z₀ U)
    (hDZ₀_cont : ContinuousOn (fun x => fderiv ℝ Z₀ x) U)
    (hZ₀_diff : ∀ y ∈ U, HasFDerivAt Z₀ (fderiv ℝ Z₀ y) y)
    {x : F} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Set.Ioo a b') :
    HasFDerivAt (fun y => linearODESolution A a b' h₀ Z₀ y t)
      (variationalW_clm hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht) x := by
  classical
  set Z : F → ℝ → G := linearODESolution A a b' h₀ Z₀ with hZ_def
  set α := (a + min t h₀) / 2 with hα_def
  set β := (b' + max t h₀) / 2 with hβ_def
  have hmin_lt_a : a < min t h₀ := lt_min ht.1 h₀_mem.1
  have hmax_lt_b' : max t h₀ < b' := max_lt ht.2 h₀_mem.2
  have hmin_le_t : min t h₀ ≤ t := min_le_left _ _
  have hmin_le_h₀ : min t h₀ ≤ h₀ := min_le_right _ _
  have ht_le_max : t ≤ max t h₀ := le_max_left _ _
  have hh₀_le_max : h₀ ≤ max t h₀ := le_max_right _ _
  have hα_lt_min : α < min t h₀ := by rw [hα_def]; linarith
  have ha_lt_α : a < α := by rw [hα_def]; linarith
  have hmax_lt_β : max t h₀ < β := by rw [hβ_def]; linarith
  have hβ_lt_b' : β < b' := by rw [hβ_def]; linarith
  have hα_le_β : α ≤ β := by linarith
  have hh₀_mem_Icc : h₀ ∈ Set.Icc α β :=
    ⟨le_of_lt (lt_of_lt_of_le hα_lt_min hmin_le_h₀),
     le_of_lt (lt_of_le_of_lt hh₀_le_max hmax_lt_β)⟩
  have ht_mem_Icc : t ∈ Set.Icc α β :=
    ⟨le_of_lt (lt_of_lt_of_le hα_lt_min hmin_le_t),
     le_of_lt (lt_of_le_of_lt ht_le_max hmax_lt_β)⟩
  have hIcc_sub : Set.Icc α β ⊆ Set.Ioo a b' := fun s hs =>
    ⟨lt_of_lt_of_le ha_lt_α hs.1, lt_of_le_of_lt hs.2 hβ_lt_b'⟩
  have hIcc_cpt : IsCompact (Set.Icc α β) := isCompact_Icc
  have hIcc_ne : (Set.Icc α β).Nonempty := ⟨α, left_mem_Icc.mpr hα_le_β⟩
  obtain ⟨ε_open, hε_open_pos, hball_sub⟩ :=
    Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  set δ₀ : ℝ := ε_open / 2 with hδ₀_def
  have hδ₀_pos : 0 < δ₀ := by positivity
  have hδ₀_lt : δ₀ < ε_open := by rw [hδ₀_def]; linarith
  have hclosedBall_sub : Metric.closedBall x δ₀ ⊆ U := fun y hy =>
    hball_sub (Metric.closedBall_subset_ball hδ₀_lt hy)
  have hclosedBall_cpt : IsCompact (Metric.closedBall x δ₀) :=
    isCompact_closedBall x δ₀
  set K : Set (F × ℝ) := Metric.closedBall x δ₀ ×ˢ Set.Icc α β with hK_def
  have hK_cpt : IsCompact K := hclosedBall_cpt.prod hIcc_cpt
  have hK_sub : K ⊆ U ×ˢ Set.Ioo a b' := fun p hp =>
    ⟨hclosedBall_sub hp.1, hIcc_sub hp.2⟩
  have hx_ball : x ∈ Metric.closedBall x δ₀ := Metric.mem_closedBall_self hδ₀_pos.le
  have hK_ne : K.Nonempty :=
    ⟨(x, α), hx_ball, left_mem_Icc.mpr hα_le_β⟩
  have hA_cont_K : ContinuousOn (Function.uncurry A) K := hA_cont.mono hK_sub
  have hAnorm_cont_K : ContinuousOn (fun p : F × ℝ => ‖A p.1 p.2‖) K :=
    continuous_norm.comp_continuousOn hA_cont_K
  obtain ⟨pM, _, hM_bd⟩ := hK_cpt.exists_isMaxOn hK_ne hAnorm_cont_K
  set M : ℝ := ‖A pM.1 pM.2‖ with hM_def
  have hM_nn : 0 ≤ M := norm_nonneg _
  have hM_bd' : ∀ p ∈ K, ‖A p.1 p.2‖ ≤ M := fun p hp => hM_bd hp
  have hDA_cont_K : ContinuousOn
      (Function.uncurry fun y s => fderiv ℝ (fun z => A z s) y) K :=
    hDA_cont.mono hK_sub
  have hDAnorm_cont_K : ContinuousOn
      (fun p : F × ℝ => ‖fderiv ℝ (fun z => A z p.2) p.1‖) K :=
    continuous_norm.comp_continuousOn hDA_cont_K
  obtain ⟨pP, _, hP_bd⟩ := hK_cpt.exists_isMaxOn hK_ne hDAnorm_cont_K
  set P : ℝ := ‖fderiv ℝ (fun z => A z pP.2) pP.1‖ with hP_def
  have hP_nn : 0 ≤ P := norm_nonneg _
  have hP_bd' : ∀ p ∈ K, ‖fderiv ℝ (fun z => A z p.2) p.1‖ ≤ P :=
    fun p hp => hP_bd hp
  have hZ_cont_K : ContinuousOn (Function.uncurry Z) K :=
    (linearODESolution_continuousOn hab_lt h₀_mem hU hA_cont hZ₀_cont).mono hK_sub
  have hZnorm_cont_K : ContinuousOn (fun p : F × ℝ => ‖Z p.1 p.2‖) K :=
    continuous_norm.comp_continuousOn hZ_cont_K
  obtain ⟨pQ, _, hQ_bd⟩ := hK_cpt.exists_isMaxOn hK_ne hZnorm_cont_K
  set Q : ℝ := ‖Z pQ.1 pQ.2‖ with hQ_def
  have hQ_nn : 0 ≤ Q := norm_nonneg _
  have hQ_bd' : ∀ p ∈ K, ‖Z p.1 p.2‖ ≤ Q := fun p hp => hQ_bd hp
  have hDZ₀_cont_ball : ContinuousOn (fun y => fderiv ℝ Z₀ y)
      (Metric.closedBall x δ₀) := hDZ₀_cont.mono hclosedBall_sub
  have hDZ₀norm_cont_ball : ContinuousOn (fun y => ‖fderiv ℝ Z₀ y‖)
      (Metric.closedBall x δ₀) :=
    continuous_norm.comp_continuousOn hDZ₀_cont_ball
  obtain ⟨pL, _, hL_bd⟩ := hclosedBall_cpt.exists_isMaxOn
    ⟨x, hx_ball⟩ hDZ₀norm_cont_ball
  set L : ℝ := ‖fderiv ℝ Z₀ pL‖ with hL_def
  have hL_nn : 0 ≤ L := norm_nonneg _
  have hL_bd' : ∀ y ∈ Metric.closedBall x δ₀, ‖fderiv ℝ Z₀ y‖ ≤ L :=
    fun y hy => hL_bd hy
  have hAx_bd : ∀ s ∈ Set.Icc α β, ‖A x s‖ ≤ M := fun s hs =>
    hM_bd' (x, s) ⟨hx_ball, hs⟩
  have hDAx_bd : ∀ s ∈ Set.Icc α β, ‖fderiv ℝ (fun z => A z s) x‖ ≤ P :=
    fun s hs => hP_bd' (x, s) ⟨hx_ball, hs⟩
  have hZx_bd : ∀ s ∈ Set.Icc α β, ‖Z x s‖ ≤ Q := fun s hs =>
    hQ_bd' (x, s) ⟨hx_ball, hs⟩
  have hZ₀x_bd : ‖fderiv ℝ Z₀ x‖ ≤ L := hL_bd' x hx_ball
  set C_stab : ℝ := gronwallBound L M (P * Q) (β - α) with hC_stab_def
  have hPQ_nn : 0 ≤ P * Q := mul_nonneg hP_nn hQ_nn
  have hβα_nn : 0 ≤ β - α := by linarith
  have hC_stab_nn : 0 ≤ C_stab := by
    rw [hC_stab_def]
    have h0 : gronwallBound L M (P * Q) 0 = L := gronwallBound_x0 _ _ _
    have hmono : gronwallBound L M (P * Q) 0 ≤ gronwallBound L M (P * Q) (β - α) :=
      gronwallBound_mono hL_nn hPQ_nn hM_nn hβα_nn
    linarith
  have h_gb_scale : ∀ (c y : ℝ),
      gronwallBound (L * c) M (P * Q * c) y = c * gronwallBound L M (P * Q) y := by
    intro c y
    by_cases hMeq : M = 0
    · rw [hMeq]
      simp only [gronwallBound_K0]; ring
    · simp only [gronwallBound_of_K_ne_0 hMeq]
      field_simp
  have h_stab : ∀ h : F, ‖h‖ ≤ δ₀ → ∀ s ∈ Set.Icc α β,
      ‖Z (x + h) s - Z x s‖ ≤ C_stab * ‖h‖ := by
    intro h hh_bd s hs
    have hdist_xh_x : dist (x + h) x = ‖h‖ := by
      rw [dist_eq_norm]; congr 1; abel
    have hxh_ball : x + h ∈ Metric.closedBall x δ₀ := by
      rw [Metric.mem_closedBall, hdist_xh_x]; exact hh_bd
    have hxh_U : x + h ∈ U := hclosedBall_sub hxh_ball
    have hConv : Convex ℝ (Metric.closedBall x δ₀) := convex_closedBall _ _
    have hZ₀_lip : ‖Z₀ (x + h) - Z₀ x‖ ≤ L * ‖h‖ := by
      have hdiff : ∀ y ∈ Metric.closedBall x δ₀, DifferentiableAt ℝ Z₀ y :=
        fun y hy => (hZ₀_diff y (hclosedBall_sub hy)).differentiableAt
      have hres := hConv.norm_image_sub_le_of_norm_fderiv_le hdiff hL_bd' hx_ball hxh_ball
      have hsub_eq : x + h - x = h := by abel
      rw [hsub_eq] at hres; exact hres
    have h_force : ∀ s' ∈ Set.Icc α β,
        ‖(A (x + h) s' - A x s') (Z (x + h) s')‖ ≤ (P * Q) * ‖h‖ := by
      intro s' hs'
      have hZxh_bd : ‖Z (x + h) s'‖ ≤ Q := hQ_bd' (x + h, s') ⟨hxh_ball, hs'⟩
      have hAdiff_bd : ‖A (x + h) s' - A x s'‖ ≤ P * ‖h‖ := by
        have hbd : ∀ y ∈ Metric.closedBall x δ₀,
            ‖fderiv ℝ (fun z => A z s') y‖ ≤ P :=
          fun y hy => hP_bd' (y, s') ⟨hy, hs'⟩
        have hdiff : ∀ y ∈ Metric.closedBall x δ₀,
            DifferentiableAt ℝ (fun z => A z s') y := fun y hy =>
          (hA_diff y (hclosedBall_sub hy) s' (hIcc_sub hs')).differentiableAt
        have hres := hConv.norm_image_sub_le_of_norm_fderiv_le hdiff hbd hx_ball hxh_ball
        have hsub_eq : x + h - x = h := by abel
        rw [hsub_eq] at hres; exact hres
      have h1 : ‖(A (x + h) s' - A x s') (Z (x + h) s')‖
          ≤ ‖A (x + h) s' - A x s'‖ * ‖Z (x + h) s'‖ :=
        (A (x + h) s' - A x s').le_opNorm _
      have h2 : ‖A (x + h) s' - A x s'‖ * ‖Z (x + h) s'‖ ≤ (P * ‖h‖) * Q :=
        mul_le_mul hAdiff_bd hZxh_bd (norm_nonneg _) (by positivity)
      calc ‖(A (x + h) s' - A x s') (Z (x + h) s')‖
          ≤ ‖A (x + h) s' - A x s'‖ * ‖Z (x + h) s'‖ := h1
        _ ≤ (P * ‖h‖) * Q := h2
        _ = P * Q * ‖h‖ := by ring
    have hgw := linearODESolution_dist_le (A := A) (Z₀ := Z₀)
      hab_lt h₀_mem hU hA_cont hx hxh_U hα_le_β ha_lt_α hβ_lt_b' hh₀_mem_Icc
      hM_nn hAx_bd h_force hs
    have h_init_bd : ‖Z₀ x - Z₀ (x + h)‖ ≤ L * ‖h‖ := by
      rw [show Z₀ x - Z₀ (x + h) = -(Z₀ (x + h) - Z₀ x) by abel, norm_neg]
      exact hZ₀_lip
    have h_abs_le : |s - h₀| ≤ β - α := by
      rcases le_total h₀ s with h | h
      · rw [abs_of_nonneg (by linarith)]; linarith [hh₀_mem_Icc.1, hs.2]
      · rw [abs_of_nonpos (by linarith)]; linarith [hs.1, hh₀_mem_Icc.2]
    rw [show Z x s - Z (x + h) s = -(Z (x + h) s - Z x s) by abel, norm_neg] at hgw
    have h_gb_mono_δ : gronwallBound ‖Z₀ x - Z₀ (x + h)‖ M (P * Q * ‖h‖) |s - h₀|
        ≤ gronwallBound (L * ‖h‖) M (P * Q * ‖h‖) |s - h₀| := by
      by_cases hMeq : M = 0
      · simp only [gronwallBound_K0, hMeq]; linarith
      · simp only [gronwallBound_of_K_ne_0 hMeq]
        have hexp_nn : 0 ≤ Real.exp (M * |s - h₀|) := (Real.exp_pos _).le
        have : ‖Z₀ x - Z₀ (x + h)‖ * Real.exp (M * |s - h₀|)
            ≤ (L * ‖h‖) * Real.exp (M * |s - h₀|) :=
          mul_le_mul_of_nonneg_right h_init_bd hexp_nn
        linarith
    have h_abs_nn : 0 ≤ |s - h₀| := abs_nonneg _
    have h_gb_mono_x : gronwallBound (L * ‖h‖) M (P * Q * ‖h‖) |s - h₀|
        ≤ gronwallBound (L * ‖h‖) M (P * Q * ‖h‖) (β - α) :=
      gronwallBound_mono (mul_nonneg hL_nn (norm_nonneg _))
        (mul_nonneg hPQ_nn (norm_nonneg _)) hM_nn h_abs_le
    have hbd_final :
        gronwallBound (L * ‖h‖) M (P * Q * ‖h‖) (β - α) = C_stab * ‖h‖ := by
      rw [hC_stab_def, h_gb_scale ‖h‖ (β - α)]; ring
    calc ‖Z (x + h) s - Z x s‖
        ≤ gronwallBound ‖Z₀ x - Z₀ (x + h)‖ M (P * Q * ‖h‖) |s - h₀| := hgw
      _ ≤ gronwallBound (L * ‖h‖) M (P * Q * ‖h‖) |s - h₀| := h_gb_mono_δ
      _ ≤ gronwallBound (L * ‖h‖) M (P * Q * ‖h‖) (β - α) := h_gb_mono_x
      _ = C_stab * ‖h‖ := hbd_final
  have hUC : UniformContinuousOn
      (fun p : F × ℝ => fderiv ℝ (fun z => A z p.2) p.1) K :=
    hK_cpt.uniformContinuousOn_of_continuous hDA_cont_K
  have h_taylor : ∀ ε > (0 : ℝ), ∃ δ_ε > (0 : ℝ), δ_ε ≤ δ₀ ∧
      ∀ h : F, ‖h‖ ≤ δ_ε → ∀ s ∈ Set.Icc α β,
        ‖A (x + h) s - A x s - (fderiv ℝ (fun z => A z s) x) h‖ ≤ ε * ‖h‖ := by
    intro ε hε
    rw [Metric.uniformContinuousOn_iff_le] at hUC
    obtain ⟨δ', hδ'_pos, hδ'_unif⟩ := hUC ε hε
    refine ⟨min δ₀ δ', lt_min hδ₀_pos hδ'_pos, min_le_left _ _, ?_⟩
    intro h hh_bd s hs
    have hh_le_δ₀ : ‖h‖ ≤ δ₀ := le_trans hh_bd (min_le_left _ _)
    have hh_le_δ' : ‖h‖ ≤ δ' := le_trans hh_bd (min_le_right _ _)
    have hball_sub_K : ∀ y ∈ Metric.closedBall x ‖h‖, y ∈ Metric.closedBall x δ₀ :=
      fun y hy => Metric.closedBall_subset_closedBall hh_le_δ₀ hy
    have hConv_h : Convex ℝ (Metric.closedBall x ‖h‖) := convex_closedBall _ _
    have hx_in_h : x ∈ Metric.closedBall x ‖h‖ :=
      Metric.mem_closedBall_self (norm_nonneg _)
    have hxh_in_h : x + h ∈ Metric.closedBall x ‖h‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have : x + h - x = h := by abel
      rw [this]
    have h_pt_bd : ∀ y ∈ Metric.closedBall x ‖h‖,
        ‖fderiv ℝ (fun z => A z s) y - fderiv ℝ (fun z => A z s) x‖ ≤ ε := by
      intro y hy
      have hy_K : (y, s) ∈ K := ⟨hball_sub_K y hy, hs⟩
      have hx_K : (x, s) ∈ K := ⟨hx_ball, hs⟩
      have hdist_le : dist (y, s) (x, s) ≤ δ' := by
        rw [Prod.dist_eq]
        have : dist s s = 0 := dist_self _
        rw [this]
        have hys_dist : dist y x ≤ ‖h‖ := hy
        exact max_le (le_trans hys_dist hh_le_δ') (le_of_lt hδ'_pos)
      have hunif := hδ'_unif (y, s) hy_K (x, s) hx_K hdist_le
      rw [dist_eq_norm] at hunif
      exact hunif
    have hHasFDeriv : ∀ y ∈ Metric.closedBall x ‖h‖,
        HasFDerivWithinAt (fun z => A z s) (fderiv ℝ (fun z => A z s) y)
          (Metric.closedBall x ‖h‖) y := fun y hy =>
      (hA_diff y (hclosedBall_sub (hball_sub_K y hy)) s (hIcc_sub hs)).hasFDerivWithinAt
    have hres := hConv_h.norm_image_sub_le_of_norm_hasFDerivWithin_le'
      hHasFDeriv h_pt_bd hx_in_h hxh_in_h
    have hsub_eq : x + h - x = h := by abel
    rw [hsub_eq] at hres
    exact hres
  have hW_deriv : ∀ h : F, ∀ s ∈ Set.Ioo a b',
      HasDerivAt (variationalW A a b' h₀ Z₀ x h ·)
        ((fderiv ℝ (fun y => A y s) x) h (Z x s)
          + A x s (variationalW A a b' h₀ Z₀ x h s)) s := fun h s hs =>
    variationalW_hasDerivAt hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont hx h hs
  have hW_init_eq : ∀ h : F,
      variationalW A a b' h₀ Z₀ x h h₀ = (fderiv ℝ Z₀ x) h := fun h =>
    variationalW_init A a b' h₀ Z₀ x h
  have hZ_deriv : ∀ y ∈ U, ∀ s ∈ Set.Ioo a b',
      HasDerivAt (Z y ·) (A y s (Z y s)) s := fun y hy s hs =>
    linearODESolution_hasDerivAt hab_lt h₀_mem hU hA_cont hy hs
  have hZ_init_eq : ∀ y : F, Z y h₀ = Z₀ y := fun y =>
    linearODESolution_init A a b' h₀ Z₀ y
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  set E_T : ℝ := if M = 0 then β - α else (Real.exp (M * (β - α)) - 1) / M
    with hET_def
  set E_δ : ℝ := if M = 0 then 1 else Real.exp (M * (β - α)) with hEδ_def
  have hgb_eq : ∀ δ ε : ℝ,
      gronwallBound δ M ε (β - α) = δ * E_δ + ε * E_T := by
    intro δ ε
    by_cases hMeq : M = 0
    · have hEδ_val : E_δ = 1 := by rw [hEδ_def, if_pos hMeq]
      have hET_val : E_T = β - α := by rw [hET_def, if_pos hMeq]
      rw [hMeq, hEδ_val, hET_val, gronwallBound_K0]; ring
    · have hEδ_val : E_δ = Real.exp (M * (β - α)) := by
        rw [hEδ_def, if_neg hMeq]
      have hET_val : E_T = (Real.exp (M * (β - α)) - 1) / M := by
        rw [hET_def, if_neg hMeq]
      rw [hEδ_val, hET_val, gronwallBound_of_K_ne_0 hMeq]
      field_simp
  have hET_nn : 0 ≤ E_T := by
    by_cases hMeq : M = 0
    · have : E_T = β - α := by rw [hET_def, if_pos hMeq]
      rw [this]; linarith
    · have : E_T = (Real.exp (M * (β - α)) - 1) / M := by
        rw [hET_def, if_neg hMeq]
      rw [this]
      have hexp_ge : 1 ≤ Real.exp (M * (β - α)) :=
        Real.one_le_exp (mul_nonneg hM_nn hβα_nn)
      have : 0 ≤ Real.exp (M * (β - α)) - 1 := by linarith
      exact div_nonneg this hM_nn
  have hEδ_pos : 0 < E_δ := by
    by_cases hMeq : M = 0
    · have : E_δ = 1 := by rw [hEδ_def, if_pos hMeq]
      rw [this]; norm_num
    · have : E_δ = Real.exp (M * (β - α)) := by rw [hEδ_def, if_neg hMeq]
      rw [this]; exact Real.exp_pos _
  have hEδ_nn : 0 ≤ E_δ := hEδ_pos.le
  set c₁ : ℝ := c / (2 * E_δ) with hc₁_def
  have hc₁_pos : 0 < c₁ := by
    rw [hc₁_def]; positivity
  set c₂ : ℝ := c / (2 * (E_T + 1)) with hc₂_def
  have hET_inc : 0 < E_T + 1 := by linarith
  have hc₂_pos : 0 < c₂ := by
    rw [hc₂_def]; positivity
  have hEδ_ne : E_δ ≠ 0 := ne_of_gt hEδ_pos
  have hET_inc_ne : (E_T + 1 : ℝ) ≠ 0 := ne_of_gt hET_inc
  have h_bound_compose : c₁ * E_δ + c₂ * E_T ≤ c := by
    have h1 : c₁ * E_δ = c / 2 := by
      rw [hc₁_def, div_mul_eq_mul_div, mul_div_assoc]
      have : E_δ / (2 * E_δ) = 1 / 2 := by
        rw [div_eq_iff (by positivity)]; ring
      rw [this]; ring
    have h2 : c₂ * E_T ≤ c / 2 := by
      rw [hc₂_def]
      have hET_le : E_T ≤ E_T + 1 := by linarith
      have hstep : c / (2 * (E_T + 1)) * E_T ≤ c / (2 * (E_T + 1)) * (E_T + 1) :=
        mul_le_mul_of_nonneg_left hET_le (by positivity)
      have hfinal : c / (2 * (E_T + 1)) * (E_T + 1) = c / 2 := by
        rw [div_mul_eq_mul_div, mul_div_assoc]
        have : (E_T + 1) / (2 * (E_T + 1)) = 1 / 2 := by
          rw [div_eq_iff (by positivity)]; ring
        rw [this]; ring
      linarith
    linarith
  have hZ₀_at : HasFDerivAt Z₀ (fderiv ℝ Z₀ x) x := hZ₀_diff x hx
  have hZ₀_lit : (fun h : F => Z₀ (x + h) - Z₀ x - (fderiv ℝ Z₀ x) h) =o[𝓝 0]
      (fun h : F => h) :=
    hasFDerivAt_iff_isLittleO_nhds_zero.mp hZ₀_at
  have hZ₀_bd_event : ∀ᶠ h : F in 𝓝 0,
      ‖Z₀ (x + h) - Z₀ x - (fderiv ℝ Z₀ x) h‖ ≤ c₁ * ‖h‖ :=
    (Asymptotics.isLittleO_iff.mp hZ₀_lit) hc₁_pos
  set ε₁ : ℝ := c₂ / (2 * (Q + 1)) with hε₁_def
  have hQ_inc : 0 < Q + 1 := by linarith
  have hε₁_pos : 0 < ε₁ := by rw [hε₁_def]; positivity
  obtain ⟨δ_tay, hδ_tay_pos, hδ_tay_le_δ₀, h_tay_bd⟩ := h_taylor ε₁ hε₁_pos
  set δ_pcs : ℝ := c₂ / (2 * (P * C_stab + 1)) with hδ_pcs_def
  have hPCS_inc : 0 < P * C_stab + 1 := by
    have : 0 ≤ P * C_stab := mul_nonneg hP_nn hC_stab_nn
    linarith
  have hδ_pcs_pos : 0 < δ_pcs := by rw [hδ_pcs_def]; positivity
  set δ_force : ℝ := min δ_tay δ_pcs with hδ_force_def
  have hδ_force_pos : 0 < δ_force :=
    lt_min hδ_tay_pos hδ_pcs_pos
  have hδ_force_le_δ_tay : δ_force ≤ δ_tay := min_le_left _ _
  have hδ_force_le_δ_pcs : δ_force ≤ δ_pcs := min_le_right _ _
  have h_force_total : ∀ h : F, ‖h‖ ≤ δ_force →
      ε₁ * Q + P * C_stab * ‖h‖ ≤ c₂ := by
    intro h hh_le
    have h1 : ε₁ * Q ≤ c₂ / 2 := by
      rw [hε₁_def]
      have hQ_le : Q ≤ Q + 1 := by linarith
      have hQ1_pos : (0 : ℝ) < Q + 1 := hQ_inc
      have hstep : c₂ / (2 * (Q + 1)) * Q ≤ c₂ / (2 * (Q + 1)) * (Q + 1) :=
        mul_le_mul_of_nonneg_left hQ_le (by positivity)
      have hfinal : c₂ / (2 * (Q + 1)) * (Q + 1) = c₂ / 2 := by
        rw [div_mul_eq_mul_div, mul_div_assoc]
        field_simp
      linarith
    have h2 : P * C_stab * ‖h‖ ≤ c₂ / 2 := by
      have hh_le_δ_pcs : ‖h‖ ≤ δ_pcs := le_trans hh_le hδ_force_le_δ_pcs
      have hpcs_nn : 0 ≤ P * C_stab := mul_nonneg hP_nn hC_stab_nn
      have : P * C_stab * ‖h‖ ≤ P * C_stab * δ_pcs :=
        mul_le_mul_of_nonneg_left hh_le_δ_pcs hpcs_nn
      have h_step2 : P * C_stab * δ_pcs ≤ c₂ / 2 := by
        rw [hδ_pcs_def]
        have hPCS_le : P * C_stab ≤ P * C_stab + 1 := by linarith
        have hPCS_pos : (0 : ℝ) < P * C_stab + 1 := hPCS_inc
        have hPCS_ne : (P * C_stab + 1 : ℝ) ≠ 0 := ne_of_gt hPCS_inc
        have hstep1 : P * C_stab * (c₂ / (2 * (P * C_stab + 1)))
            ≤ (P * C_stab + 1) * (c₂ / (2 * (P * C_stab + 1))) :=
          mul_le_mul_of_nonneg_right hPCS_le (by positivity)
        have hfinal : (P * C_stab + 1) * (c₂ / (2 * (P * C_stab + 1))) = c₂ / 2 := by
          rw [mul_div_assoc']
          field_simp
        linarith
      linarith
    linarith
  rw [Metric.eventually_nhds_iff]
  rw [Metric.eventually_nhds_iff] at hZ₀_bd_event
  obtain ⟨δ_init, hδ_init_pos, hδ_init_bd⟩ := hZ₀_bd_event
  set δ_final : ℝ := min δ_force δ_init with hδ_final_def
  have hδ_final_pos : 0 < δ_final := lt_min hδ_force_pos hδ_init_pos
  refine ⟨δ_final, hδ_final_pos, ?_⟩
  intro h hh_lt
  rw [dist_zero_right] at hh_lt
  have hh_le_force : ‖h‖ ≤ δ_force := le_of_lt (lt_of_lt_of_le hh_lt (min_le_left _ _))
  have hh_lt_init : dist h 0 < δ_init :=
    lt_of_lt_of_le (by rw [dist_zero_right]; exact hh_lt) (min_le_right _ _)
  have hh_le_δ₀ : ‖h‖ ≤ δ₀ :=
    le_trans (le_trans hh_le_force hδ_force_le_δ_tay) hδ_tay_le_δ₀
  have hh_le_δ_tay : ‖h‖ ≤ δ_tay := le_trans hh_le_force hδ_force_le_δ_tay
  have hdist_xh_x : dist (x + h) x = ‖h‖ := by
    rw [dist_eq_norm]; congr 1; abel
  have hxh_ball : x + h ∈ Metric.closedBall x δ₀ := by
    rw [Metric.mem_closedBall, hdist_xh_x]; exact hh_le_δ₀
  have hxh_U : x + h ∈ U := hclosedBall_sub hxh_ball
  set R : ℝ → G := fun s => Z (x + h) s - Z x s - variationalW A a b' h₀ Z₀ x h s
    with hR_def
  set Force : ℝ → G := fun s =>
    (A (x + h) s - A x s - (fderiv ℝ (fun z => A z s) x) h) (Z (x + h) s)
      + (fderiv ℝ (fun z => A z s) x) h (Z (x + h) s - Z x s)
    with hForce_def
  set Rderiv : ℝ → G := fun s => A x s (R s) + Force s with hRderiv_def
  have hR_deriv : ∀ s ∈ Set.Ioo a b', HasDerivAt R (Rderiv s) s := by
    intro s hs
    have h1 := hZ_deriv (x + h) hxh_U s hs
    have h2 := hZ_deriv x hx s hs
    have h3 := hW_deriv h s hs
    have hRderiv := (h1.sub h2).sub h3
    have h_eq :
        A (x + h) s (Z (x + h) s) - A x s (Z x s)
            - ((fderiv ℝ (fun y => A y s) x) h (Z x s)
              + A x s (variationalW A a b' h₀ Z₀ x h s))
        = Rderiv s := by
      change _ = A x s (R s) + Force s
      have hRs : R s = Z (x + h) s - Z x s - variationalW A a b' h₀ Z₀ x h s := rfl
      have hForce_val : Force s
          = (A (x + h) s - A x s - (fderiv ℝ (fun z => A z s) x) h) (Z (x + h) s)
            + (fderiv ℝ (fun z => A z s) x) h (Z (x + h) s - Z x s) := rfl
      rw [hRs, hForce_val]
      rw [show Z (x + h) s - Z x s - variationalW A a b' h₀ Z₀ x h s
          = (Z (x + h) s - Z x s) + (-variationalW A a b' h₀ Z₀ x h s) by abel,
        ContinuousLinearMap.map_add, ContinuousLinearMap.map_sub,
        ContinuousLinearMap.map_neg]
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.map_sub]
      abel
    rw [h_eq] at hRderiv
    exact hRderiv
  have hR_init : R h₀ = Z₀ (x + h) - Z₀ x - (fderiv ℝ Z₀ x) h := by
    change Z (x + h) h₀ - Z x h₀ - variationalW A a b' h₀ Z₀ x h h₀ = _
    rw [hZ_init_eq (x + h), hZ_init_eq x, hW_init_eq h]
  have hR_init_bd : ‖R h₀‖ ≤ c₁ * ‖h‖ := by
    rw [hR_init]; exact hδ_init_bd hh_lt_init
  have h_force_bd : ∀ s ∈ Set.Icc α β,
      ‖Force s‖ ≤ (ε₁ * Q + P * C_stab * ‖h‖) * ‖h‖ := by
    intro s hs
    have h_tay := h_tay_bd h hh_le_δ_tay s hs
    have hZxh_bd : ‖Z (x + h) s‖ ≤ Q := hQ_bd' (x + h, s) ⟨hxh_ball, hs⟩
    have h_stab_s := h_stab h hh_le_δ₀ s hs
    have hP_s_bd : ‖fderiv ℝ (fun z => A z s) x‖ ≤ P := hDAx_bd s hs
    let diffA : G →L[ℝ] G :=
      A (x + h) s - A x s - (fderiv ℝ (fun z => A z s) x) h
    let dxA : F →L[ℝ] (G →L[ℝ] G) := fderiv ℝ (fun z => A z s) x
    let piece1 : G := diffA (Z (x + h) s)
    let piece2 : G := dxA h (Z (x + h) s - Z x s)
    have hp1 : ‖piece1‖ ≤ (ε₁ * Q) * ‖h‖ := by
      change ‖diffA (Z (x + h) s)‖ ≤ _
      have hop : ‖diffA (Z (x + h) s)‖ ≤ ‖diffA‖ * ‖Z (x + h) s‖ := diffA.le_opNorm _
      have hbd : ‖diffA‖ * ‖Z (x + h) s‖ ≤ (ε₁ * ‖h‖) * Q :=
        mul_le_mul h_tay hZxh_bd (norm_nonneg _) (by positivity)
      calc ‖diffA (Z (x + h) s)‖
          ≤ ‖diffA‖ * ‖Z (x + h) s‖ := hop
        _ ≤ (ε₁ * ‖h‖) * Q := hbd
        _ = (ε₁ * Q) * ‖h‖ := by ring
    have hp2 : ‖piece2‖ ≤ (P * C_stab * ‖h‖) * ‖h‖ := by
      change ‖dxA h (Z (x + h) s - Z x s)‖ ≤ _
      have hop1 : ‖dxA h (Z (x + h) s - Z x s)‖
          ≤ ‖dxA h‖ * ‖Z (x + h) s - Z x s‖ := (dxA h).le_opNorm _
      have hop2 : ‖dxA h‖ ≤ ‖dxA‖ * ‖h‖ := dxA.le_opNorm h
      have h2 : ‖dxA h‖ ≤ P * ‖h‖ :=
        le_trans hop2 (mul_le_mul_of_nonneg_right hP_s_bd (norm_nonneg _))
      have h3 : ‖dxA h‖ * ‖Z (x + h) s - Z x s‖ ≤ (P * ‖h‖) * (C_stab * ‖h‖) :=
        mul_le_mul h2 h_stab_s (norm_nonneg _) (by positivity)
      calc ‖dxA h (Z (x + h) s - Z x s)‖
          ≤ ‖dxA h‖ * ‖Z (x + h) s - Z x s‖ := hop1
        _ ≤ (P * ‖h‖) * (C_stab * ‖h‖) := h3
        _ = (P * C_stab * ‖h‖) * ‖h‖ := by ring
    change ‖piece1 + piece2‖ ≤ _
    calc ‖piece1 + piece2‖
        ≤ ‖piece1‖ + ‖piece2‖ := norm_add_le _ _
      _ ≤ (ε₁ * Q) * ‖h‖ + (P * C_stab * ‖h‖) * ‖h‖ := by linarith
      _ = (ε₁ * Q + P * C_stab * ‖h‖) * ‖h‖ := by ring
  set ε_total : ℝ := ε₁ * Q + P * C_stab * ‖h‖ with hε_total_def
  have hε_total_nn : 0 ≤ ε_total := by
    rw [hε_total_def]
    have h1 : 0 ≤ ε₁ * Q := mul_nonneg hε₁_pos.le hQ_nn
    have h2 : 0 ≤ P * C_stab * ‖h‖ :=
      mul_nonneg (mul_nonneg hP_nn hC_stab_nn) (norm_nonneg _)
    linarith
  have hε_total_le_c₂ : ε_total ≤ c₂ := h_force_total h hh_le_force
  have hR_deriv_norm_bd : ∀ s ∈ Set.Icc α β,
      ‖Rderiv s‖ ≤ M * ‖R s‖ + ε_total * ‖h‖ := by
    intro s hs
    have hAR : ‖A x s (R s)‖ ≤ M * ‖R s‖ := by
      have h1 : ‖A x s (R s)‖ ≤ ‖A x s‖ * ‖R s‖ := (A x s).le_opNorm _
      have h2 : ‖A x s‖ * ‖R s‖ ≤ M * ‖R s‖ :=
        mul_le_mul_of_nonneg_right (hAx_bd s hs) (norm_nonneg _)
      linarith
    have hFB : ‖Force s‖ ≤ ε_total * ‖h‖ := h_force_bd s hs
    have hR_val : Rderiv s = A x s (R s) + Force s := rfl
    rw [hR_val]
    calc ‖A x s (R s) + Force s‖
        ≤ ‖A x s (R s)‖ + ‖Force s‖ := norm_add_le _ _
      _ ≤ M * ‖R s‖ + ε_total * ‖h‖ := by linarith
  have hR_cont : ContinuousOn R (Set.Icc α β) := fun s hs =>
    ((hR_deriv s (hIcc_sub hs)).continuousAt).continuousWithinAt
  have h_α_le_h₀ : α ≤ h₀ := hh₀_mem_Icc.1
  have h_h₀_le_β : h₀ ≤ β := hh₀_mem_Icc.2
  have hRt_bd : ‖R t‖ ≤ gronwallBound (c₁ * ‖h‖) M (ε_total * ‖h‖) (β - α) := by
    rcases le_total h₀ t with hht | hth
    · have ht_fwd : t ∈ Set.Icc h₀ β := ⟨hht, ht_mem_Icc.2⟩
      have hIcc_fwd_sub : Set.Icc h₀ β ⊆ Set.Icc α β := fun s hs =>
        ⟨le_trans h_α_le_h₀ hs.1, hs.2⟩
      have hR_cont_fwd : ContinuousOn R (Set.Icc h₀ β) := hR_cont.mono hIcc_fwd_sub
      have hR_deriv_within_right : ∀ s ∈ Set.Ico h₀ β,
          HasDerivWithinAt R (Rderiv s) (Set.Ici s) s := fun s hs =>
        (hR_deriv s (hIcc_sub (hIcc_fwd_sub (Set.Ico_subset_Icc_self hs)))).hasDerivWithinAt
      have h_init_le : ‖R h₀‖ ≤ c₁ * ‖h‖ := hR_init_bd
      have h_bound_fwd : ∀ s ∈ Set.Ico h₀ β,
          ‖Rderiv s‖ ≤ M * ‖R s‖ + ε_total * ‖h‖ := fun s hs =>
        hR_deriv_norm_bd s (hIcc_fwd_sub (Set.Ico_subset_Icc_self hs))
      have hgw := norm_le_gronwallBound_of_norm_deriv_right_le
        hR_cont_fwd hR_deriv_within_right h_init_le h_bound_fwd t ht_fwd
      have h_t_sub_le : t - h₀ ≤ β - α := by linarith [ht_mem_Icc.2, h_α_le_h₀]
      have hε_total_h_nn : 0 ≤ ε_total * ‖h‖ :=
        mul_nonneg hε_total_nn (norm_nonneg _)
      have hc₁_h_nn : 0 ≤ c₁ * ‖h‖ := mul_nonneg hc₁_pos.le (norm_nonneg _)
      have h_mono : gronwallBound (c₁ * ‖h‖) M (ε_total * ‖h‖) (t - h₀)
          ≤ gronwallBound (c₁ * ‖h‖) M (ε_total * ‖h‖) (β - α) :=
        gronwallBound_mono hc₁_h_nn hε_total_h_nn hM_nn h_t_sub_le
      linarith
    · have ht_bwd : t ∈ Set.Icc α h₀ := ⟨ht_mem_Icc.1, hth⟩
      have hIcc_bwd_sub : Set.Icc α h₀ ⊆ Set.Icc α β := fun s hs =>
        ⟨hs.1, le_trans hs.2 h_h₀_le_β⟩
      set Rb : ℝ → G := fun s => R (2 * h₀ - s) with hRb_def
      have h_h₀_le_2h₀_t : h₀ ≤ 2 * h₀ - t := by linarith
      have h_dom_swap : ∀ s ∈ Set.Icc h₀ (2 * h₀ - t), 2 * h₀ - s ∈ Set.Icc α h₀ := by
        intro s hs; refine ⟨?_, ?_⟩ <;> linarith [hs.1, hs.2, ht_bwd.1]
      have hRb_cont : ContinuousOn Rb (Set.Icc h₀ (2 * h₀ - t)) := by
        apply ContinuousOn.comp (hR_cont.mono hIcc_bwd_sub)
          (s := Set.Icc h₀ (2 * h₀ - t)) (t := Set.Icc α h₀) (f := fun s => 2 * h₀ - s)
        · exact (continuous_const.sub continuous_id).continuousOn
        · exact h_dom_swap
      have hRb_deriv : ∀ s ∈ Set.Icc h₀ (2 * h₀ - t),
          HasDerivAt Rb (-(Rderiv (2 * h₀ - s))) s := by
        intro s hs
        have hs_in : 2 * h₀ - s ∈ Set.Ioo a b' :=
          hIcc_sub (hIcc_bwd_sub (h_dom_swap s hs))
        have hd := hR_deriv (2 * h₀ - s) hs_in
        have hchain : HasDerivAt (fun r : ℝ => 2 * h₀ - r) (-1 : ℝ) s := by
          simpa using (hasDerivAt_const s (2 * h₀)).sub (hasDerivAt_id s)
        have hd' := hd.scomp s hchain
        have h_smul : ((-1 : ℝ) • Rderiv (2 * h₀ - s) : G)
            = -(Rderiv (2 * h₀ - s)) := neg_one_smul ℝ _
        rw [h_smul] at hd'
        exact hd'
      have hRb_deriv_within_right : ∀ s ∈ Set.Ico h₀ (2 * h₀ - t),
          HasDerivWithinAt Rb (-(Rderiv (2 * h₀ - s))) (Set.Ici s) s :=
        fun s hs => (hRb_deriv s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt
      have hRb_init : Rb h₀ = R h₀ := by
        change R (2 * h₀ - h₀) = R h₀
        congr 1; ring
      have hRb_init_bd : ‖Rb h₀‖ ≤ c₁ * ‖h‖ := by rw [hRb_init]; exact hR_init_bd
      have hRb_bd : ∀ s ∈ Set.Ico h₀ (2 * h₀ - t),
          ‖-(Rderiv (2 * h₀ - s))‖ ≤ M * ‖Rb s‖ + ε_total * ‖h‖ := by
        intro s hs
        have hin : 2 * h₀ - s ∈ Set.Icc α β :=
          hIcc_bwd_sub (h_dom_swap s (Set.Ico_subset_Icc_self hs))
        have h := hR_deriv_norm_bd (2 * h₀ - s) hin
        have hRbs_eq : Rb s = R (2 * h₀ - s) := rfl
        rw [norm_neg, hRbs_eq]
        exact h
      have hgw_bwd := norm_le_gronwallBound_of_norm_deriv_right_le
        hRb_cont hRb_deriv_within_right hRb_init_bd hRb_bd (2 * h₀ - t)
        (right_mem_Icc.mpr h_h₀_le_2h₀_t)
      have hRb_t : Rb (2 * h₀ - t) = R t := by
        change R (2 * h₀ - (2 * h₀ - t)) = R t
        congr 1; ring
      rw [hRb_t] at hgw_bwd
      have h_time : 2 * h₀ - t - h₀ = h₀ - t := by ring
      rw [h_time] at hgw_bwd
      have h_h₀_sub_t_le : h₀ - t ≤ β - α := by linarith [ht_bwd.1, h_h₀_le_β]
      have hε_total_h_nn : 0 ≤ ε_total * ‖h‖ :=
        mul_nonneg hε_total_nn (norm_nonneg _)
      have hc₁_h_nn : 0 ≤ c₁ * ‖h‖ := mul_nonneg hc₁_pos.le (norm_nonneg _)
      have h_mono : gronwallBound (c₁ * ‖h‖) M (ε_total * ‖h‖) (h₀ - t)
          ≤ gronwallBound (c₁ * ‖h‖) M (ε_total * ‖h‖) (β - α) :=
        gronwallBound_mono hc₁_h_nn hε_total_h_nn hM_nn h_h₀_sub_t_le
      linarith
  have h_final : ‖R t‖ ≤ c * ‖h‖ := by
    have hgb_evald : gronwallBound (c₁ * ‖h‖) M (ε_total * ‖h‖) (β - α)
        = (c₁ * ‖h‖) * E_δ + (ε_total * ‖h‖) * E_T := hgb_eq _ _
    have h_step :
        (c₁ * ‖h‖) * E_δ + (ε_total * ‖h‖) * E_T
          = ‖h‖ * (c₁ * E_δ + ε_total * E_T) := by ring
    have h_ε_le : ε_total * E_T ≤ c₂ * E_T :=
      mul_le_mul_of_nonneg_right hε_total_le_c₂ hET_nn
    have h_combo :
        c₁ * E_δ + ε_total * E_T ≤ c₁ * E_δ + c₂ * E_T := by linarith
    have h_bound_final :
        ‖h‖ * (c₁ * E_δ + ε_total * E_T) ≤ ‖h‖ * c := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      linarith
    calc ‖R t‖
        ≤ gronwallBound (c₁ * ‖h‖) M (ε_total * ‖h‖) (β - α) := hRt_bd
      _ = (c₁ * ‖h‖) * E_δ + (ε_total * ‖h‖) * E_T := hgb_evald
      _ = ‖h‖ * (c₁ * E_δ + ε_total * E_T) := h_step
      _ ≤ ‖h‖ * c := h_bound_final
      _ = c * ‖h‖ := by ring
  have h_clm_apply :
      (variationalW_clm hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht) h
        = variationalW A a b' h₀ Z₀ x h t :=
    variationalW_clm_apply hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht h
  change ‖linearODESolution A a b' h₀ Z₀ (x + h) t
        - linearODESolution A a b' h₀ Z₀ x t
        - (variationalW_clm hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht) h‖
      ≤ c * ‖h‖
  rw [h_clm_apply]
  change ‖R t‖ ≤ c * ‖h‖
  exact h_final

/-- **Joint continuity of the time-partial derivative** of the parametric
linear ODE solution. The function `(x, t) ↦ A(x, t) (Z(x, t))`, where
`Z = linearODESolution A a b' h₀ Z₀`, is jointly continuous on
`U ×ˢ Ioo a b'`. -/
private theorem linearODESolution_partial_t_continuousOn
    {A : F → ℝ → (G →L[ℝ] G)} {a b' h₀ : ℝ} {Z₀ : F → G}
    (hab_lt : a < b') (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U) :
    ContinuousOn
      (fun p : F × ℝ => A p.1 p.2 (linearODESolution A a b' h₀ Z₀ p.1 p.2))
      (U ×ˢ Set.Ioo a b') := by
  have hZ_cont : ContinuousOn
      (Function.uncurry (linearODESolution A a b' h₀ Z₀)) (U ×ˢ Set.Ioo a b') :=
    linearODESolution_continuousOn hab_lt h₀_mem hU hA_cont hZ₀_cont
  have h_app_cont : Continuous fun q : (G →L[ℝ] G) × G => q.1 q.2 :=
    isBoundedBilinearMap_apply.continuous
  have h_pair_cont : ContinuousOn
      (fun p : F × ℝ => (A p.1 p.2, linearODESolution A a b' h₀ Z₀ p.1 p.2))
      (U ×ˢ Set.Ioo a b') :=
    ContinuousOn.prodMk hA_cont hZ_cont
  exact h_app_cont.comp_continuousOn h_pair_cont

open Classical in
set_option linter.style.setOption false in
set_option maxHeartbeats 800000 in
/-- Joint continuity of the CLM-valued x-partial in the operator-norm topology. -/
private theorem variationalW_clm_continuousOn
    [FiniteDimensional ℝ F]
    {A : F → ℝ → (G →L[ℝ] G)} {a b' : ℝ} (hab_lt : a < b')
    {h₀ : ℝ} (h₀_mem : h₀ ∈ Set.Ioo a b')
    {Z₀ : F → G}
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U)
    (hDZ₀_cont : ContinuousOn (fun x => fderiv ℝ Z₀ x) U) :
    ContinuousOn
      (fun p : F × ℝ =>
        if hx : p.1 ∈ U then
          if ht : p.2 ∈ Set.Ioo a b' then
            variationalW_clm hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht
          else 0
        else 0)
      (U ×ˢ Set.Ioo a b') := by
  rw [continuousOn_clm_apply]
  intro v
  have h_eq : ∀ p ∈ U ×ˢ Set.Ioo a b',
      (if hx : p.1 ∈ U then
        if ht : p.2 ∈ Set.Ioo a b' then
          variationalW_clm hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht
        else 0
      else 0) v =
      variationalW A a b' h₀ Z₀ p.1 v p.2 := by
    intro ⟨x, t⟩ ⟨hxU, htI⟩
    change (if hx : x ∈ U then if ht : t ∈ Set.Ioo a b' then
            variationalW_clm hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht
          else 0 else 0) v = _
    rw [dif_pos hxU, dif_pos htI]
    exact variationalW_clm_apply hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont hxU htI v
  refine ContinuousOn.congr ?_ h_eq
  have hZ₀'_cont : ContinuousOn (fun x => (fderiv ℝ Z₀ x) v) U :=
    (ContinuousLinearMap.apply ℝ G v).continuous.comp_continuousOn hDZ₀_cont
  exact variationalW_continuousOn hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont v hZ₀'_cont

set_option maxHeartbeats 1600000 in
/-- **Total Frechet derivative** of the joint map `(x, t) |-> Z(x, t)`.

At every `(x0, t0) in U xs Ioo a b'`, the map
`Function.uncurry (linearODESolution A a b' h0 Z0)` has Frechet derivative
`(variationalW_clm ...).coprod (toSpanSingleton R (A x0 t0 (Z x0 t0)))`,
i.e. the linear map `(h, s) |-> L_x(h) + s . A(x0, t0)(Z(x0, t0))`.

The proof decomposes the remainder as
`[Z(x0+h, t0+s) - Z(x0+h, t0) - s . v0] + [Z(x0+h, t0) - Z(x0, t0) - L_x(h)]`
and bounds each piece as `o(||(h,s)||)` using the mean-value theorem (for the
time piece) and `linearODESolution_hasFDerivAt_param` (for the parameter piece).
-/
private theorem linearODESolution_hasFDerivAt_joint
    [FiniteDimensional ℝ F]
    {A : F → ℝ → (G →L[ℝ] G)} {Z₀ : F → G}
    {a b' : ℝ} (hab_lt : a < b') {h₀ : ℝ} (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hA_diff : ∀ y ∈ U, ∀ s ∈ Set.Ioo a b',
      HasFDerivAt (fun z => A z s) (fderiv ℝ (fun z => A z s) y) y)
    (hZ₀_cont : ContinuousOn Z₀ U)
    (hDZ₀_cont : ContinuousOn (fun x => fderiv ℝ Z₀ x) U)
    (hZ₀_diff : ∀ y ∈ U, HasFDerivAt Z₀ (fderiv ℝ Z₀ y) y)
    {x₀ : F} (hx₀ : x₀ ∈ U) {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo a b') :
    HasFDerivAt (Function.uncurry (linearODESolution A a b' h₀ Z₀))
      ((variationalW_clm hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont hx₀ ht₀).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ
          (A x₀ t₀ (linearODESolution A a b' h₀ Z₀ x₀ t₀))))
      (x₀, t₀) := by
  set Z := linearODESolution A a b' h₀ Z₀ with hZ_def
  set v₀ := A x₀ t₀ (Z x₀ t₀) with hv₀_def
  set L_x := variationalW_clm hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont hx₀ ht₀
  set L := L_x.coprod (ContinuousLinearMap.toSpanSingleton ℝ v₀)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro c hc
  have hx_param := linearODESolution_hasFDerivAt_param hab_lt h₀_mem hU hA_cont hDA_cont
    hA_diff hZ₀_cont hDZ₀_cont hZ₀_diff hx₀ ht₀
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hx_param
  have hx_param_bd := hx_param.bound (show (0 : ℝ) < c / 2 by linarith)
  obtain ⟨δ_x, hδ_x_pos, hδ_x_bd⟩ := Metric.eventually_nhds_iff.mp hx_param_bd
  have ht_partial_cont :
      ContinuousOn (fun p : F × ℝ => A p.1 p.2 (Z p.1 p.2)) (U ×ˢ Set.Ioo a b') :=
    linearODESolution_partial_t_continuousOn hab_lt h₀_mem hU hA_cont hZ₀_cont
  have hS_open : IsOpen (U ×ˢ Set.Ioo a b' : Set (F × ℝ)) := hU.prod isOpen_Ioo
  have hx₀t₀_mem : (x₀, t₀) ∈ U ×ˢ Set.Ioo a b' := ⟨hx₀, ht₀⟩
  have ht_partial_cont_at : ContinuousAt
      (fun p : F × ℝ => A p.1 p.2 (Z p.1 p.2)) (x₀, t₀) :=
    (ht_partial_cont (x₀, t₀) hx₀t₀_mem).continuousAt (hS_open.mem_nhds hx₀t₀_mem)
  rw [Metric.continuousAt_iff] at ht_partial_cont_at
  obtain ⟨δ_t, hδ_t_pos, hδ_t_bd⟩ := ht_partial_cont_at (c / 2) (by linarith)
  have h_add_nhds : ∀ᶠ p : F × ℝ in 𝓝 (0, 0),
      x₀ + p.1 ∈ U ∧ t₀ + p.2 ∈ Set.Ioo a b' := by
    have h1 : ∀ᶠ q : F in 𝓝 0, x₀ + q ∈ U := by
      have : Continuous (fun q : F => x₀ + q) := continuous_const.add continuous_id
      exact this.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hx₀)
    have h2 : ∀ᶠ r : ℝ in 𝓝 0, t₀ + r ∈ Set.Ioo a b' := by
      have : Continuous (fun r : ℝ => t₀ + r) := continuous_const.add continuous_id
      exact this.continuousAt.preimage_mem_nhds (by simpa using isOpen_Ioo.mem_nhds ht₀)
    rw [nhds_prod_eq]
    exact h1.prod_mk h2
  obtain ⟨δ₀, hδ₀_pos, hδ₀_bd⟩ := Metric.eventually_nhds_iff.mp h_add_nhds
  set δ := min δ₀ (min δ_x δ_t) with hδ_def
  have hδ_pos : 0 < δ := lt_min hδ₀_pos (lt_min hδ_x_pos hδ_t_pos)
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ_pos, fun ⟨h, s⟩ h_dist => ?_⟩
  simp only [dist_zero_right] at h_dist
  have hh_lt : ‖h‖ < δ := lt_of_le_of_lt (le_max_left _ _) h_dist
  have hs_lt : ‖s‖ < δ := lt_of_le_of_lt (le_max_right _ _) h_dist
  have hh_lt_δ₀ : ‖h‖ < δ₀ := lt_of_lt_of_le hh_lt (min_le_left _ _)
  have hs_lt_δ₀ : ‖s‖ < δ₀ := lt_of_lt_of_le hs_lt (min_le_left _ _)
  have hh_lt_δx : ‖h‖ < δ_x :=
    lt_of_lt_of_le hh_lt ((min_le_right _ _).trans (min_le_left _ _))
  have hhs_lt_δt : max ‖h‖ ‖s‖ < δ_t :=
    lt_of_lt_of_le h_dist ((min_le_right _ _).trans (min_le_right _ _))
  have hprod_mem : x₀ + h ∈ U ∧ t₀ + s ∈ Set.Ioo a b' := by
    have h_dist_pair : dist (h, s) (0, 0) < δ₀ := by
      rw [Prod.dist_eq, dist_zero_right, dist_zero_right]
      exact max_lt hh_lt_δ₀ hs_lt_δ₀
    exact hδ₀_bd h_dist_pair
  obtain ⟨hxh_U, hts_Ioo⟩ := hprod_mem
  change ‖uncurry Z ((x₀, t₀) + (h, s)) - uncurry Z (x₀, t₀) - L (h, s)‖ ≤ c * ‖(h, s)‖
  simp only [uncurry, Prod.mk_add_mk]
  have hL_eq : L (h, s) = L_x h + s • v₀ := by
    simp [L, ContinuousLinearMap.coprod_apply, ContinuousLinearMap.toSpanSingleton_apply]
  rw [hL_eq]
  have h_split :
      Z (x₀ + h) (t₀ + s) - Z x₀ t₀ - (L_x h + s • v₀)
        = (Z (x₀ + h) (t₀ + s) - Z (x₀ + h) t₀ - s • v₀)
          + (Z (x₀ + h) t₀ - Z x₀ t₀ - L_x h) := by abel
  rw [h_split]
  calc ‖(Z (x₀ + h) (t₀ + s) - Z (x₀ + h) t₀ - s • v₀)
        + (Z (x₀ + h) t₀ - Z x₀ t₀ - L_x h)‖
      ≤ ‖Z (x₀ + h) (t₀ + s) - Z (x₀ + h) t₀ - s • v₀‖
        + ‖Z (x₀ + h) t₀ - Z x₀ t₀ - L_x h‖ := norm_add_le _ _
    _ ≤ c / 2 * ‖(h, s)‖ + c / 2 * ‖(h, s)‖ := by
        apply add_le_add
        · have hZ_deriv_at : ∀ r ∈ Set.Ioo a b',
              HasDerivAt (Z (x₀ + h) ·) (A (x₀ + h) r (Z (x₀ + h) r)) r :=
            fun r hr => linearODESolution_hasDerivAt hab_lt h₀_mem hU hA_cont hxh_U hr
          set χ : ℝ → G := fun r => Z (x₀ + h) r - (r - t₀) • v₀ with hχ_def
          have hχ_diff : ∀ r ∈ Set.Ioo a b', DifferentiableAt ℝ χ r := by
            intro r hr
            exact (hZ_deriv_at r hr).differentiableAt.sub
              (((hasDerivAt_id r).sub (hasDerivAt_const r t₀)).smul_const v₀).differentiableAt
          have hχ_deriv : ∀ r ∈ Set.Ioo a b',
              deriv χ r = A (x₀ + h) r (Z (x₀ + h) r) - v₀ := by
            intro r hr
            have hd : HasDerivAt χ (A (x₀ + h) r (Z (x₀ + h) r) - v₀) r := by
              have hd1 := hZ_deriv_at r hr
              have hd2 : HasDerivAt (fun r => (r - t₀) • v₀) v₀ r := by
                have h_base := ((hasDerivAt_id r).sub (hasDerivAt_const r t₀)).smul_const v₀
                convert h_base using 1
                simp
              exact hd1.sub hd2
            exact hd.deriv
          have h_uIcc_sub : Set.uIcc t₀ (t₀ + s) ⊆ Set.Ioo a b' := by
            intro r hr
            rw [Set.mem_uIcc] at hr
            constructor
            · rcases hr with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith [ht₀.1, hts_Ioo.1]
            · rcases hr with ⟨_, h2⟩ | ⟨_, h2⟩ <;> linarith [ht₀.2, hts_Ioo.2]
          have hχ_deriv_bd : ∀ r ∈ Set.uIcc t₀ (t₀ + s), ‖deriv χ r‖ ≤ c / 2 := by
            intro r hr
            rw [hχ_deriv r (h_uIcc_sub hr)]
            have h_r_bound : ‖r - t₀‖ ≤ ‖s‖ := by
              rw [Set.mem_uIcc] at hr
              rw [Real.norm_eq_abs, Real.norm_eq_abs]
              rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
              · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
            have h_dist_prod : dist (x₀ + h, r) (x₀, t₀) < δ_t := by
              rw [Prod.dist_eq, dist_eq_norm, show x₀ + h - x₀ = h from add_sub_cancel_left _ _,
                dist_eq_norm]
              exact lt_of_le_of_lt (max_le_max le_rfl h_r_bound) hhs_lt_δt
            have := hδ_t_bd h_dist_prod
            rw [dist_eq_norm] at this
            exact le_of_lt this
          have hχ_diff_uI : ∀ r ∈ Set.uIcc t₀ (t₀ + s),
              DifferentiableAt ℝ χ r :=
            fun r hr => hχ_diff r (h_uIcc_sub hr)
          have h_mvt := Convex.norm_image_sub_le_of_norm_deriv_le
            (𝕜 := ℝ)
            hχ_diff_uI
            hχ_deriv_bd
            (convex_uIcc t₀ (t₀ + s))
            (Set.left_mem_uIcc) (Set.right_mem_uIcc)
          have hχ_diff_eq :
              χ (t₀ + s) - χ t₀
                = Z (x₀ + h) (t₀ + s) - Z (x₀ + h) t₀ - s • v₀ := by
            simp [hχ_def]; ring_nf; abel
          rw [← hχ_diff_eq]
          have hs_eq : ‖t₀ + s - t₀‖ = ‖s‖ := by rw [add_sub_cancel_left]
          rw [hs_eq] at h_mvt
          calc ‖χ (t₀ + s) - χ t₀‖
              ≤ c / 2 * ‖s‖ := h_mvt
            _ ≤ c / 2 * ‖(h, s)‖ :=
                mul_le_mul_of_nonneg_left (norm_snd_le (h, s)) (by linarith)
        · have h_param_bd : ‖Z (x₀ + h) t₀ - Z x₀ t₀ - L_x h‖ ≤ c / 2 * ‖h‖ := by
            have := hδ_x_bd (show dist h 0 < δ_x by rwa [dist_zero_right])
            simpa [hZ_def] using this
          calc ‖Z (x₀ + h) t₀ - Z x₀ t₀ - L_x h‖
              ≤ c / 2 * ‖h‖ := h_param_bd
            _ ≤ c / 2 * ‖(h, s)‖ :=
                mul_le_mul_of_nonneg_left (norm_fst_le (h, s)) (by linarith)
    _ = c * ‖(h, s)‖ := by ring

set_option maxHeartbeats 800000 in
/-- **C^1 regularity** of the joint map `(x, t) |-> linearODESolution A a b' h0 Z0 x t`
on the open set `U xs Ioo a b'`. -/
private theorem linearODESolution_contDiffOn_one
    [FiniteDimensional ℝ F]
    {A : F → ℝ → (G →L[ℝ] G)} {Z₀ : F → G}
    {a b' : ℝ} (hab_lt : a < b') {h₀ : ℝ} (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hA_diff : ∀ y ∈ U, ∀ s ∈ Set.Ioo a b',
      HasFDerivAt (fun z => A z s) (fderiv ℝ (fun z => A z s) y) y)
    (hZ₀_cont : ContinuousOn Z₀ U)
    (hDZ₀_cont : ContinuousOn (fun x => fderiv ℝ Z₀ x) U)
    (hZ₀_diff : ∀ y ∈ U, HasFDerivAt Z₀ (fderiv ℝ Z₀ y) y) :
    ContDiffOn ℝ 1
      (Function.uncurry (linearODESolution A a b' h₀ Z₀))
      (U ×ˢ Set.Ioo a b') := by
  classical
  set Z := linearODESolution A a b' h₀ Z₀ with hZ_def
  have hS_open : IsOpen (U ×ˢ Set.Ioo a b' : Set (F × ℝ)) := hU.prod isOpen_Ioo
  change ContDiffOn ℝ ((0 : WithTop ℕ∞) + 1) _ _
  rw [contDiffOn_succ_iff_fderiv_of_isOpen hS_open]
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨x, t⟩ ⟨hx, ht⟩
    exact (linearODESolution_hasFDerivAt_joint hab_lt h₀_mem hU hA_cont hDA_cont hA_diff
      hZ₀_cont hDZ₀_cont hZ₀_diff hx ht).differentiableAt.differentiableWithinAt
  · intro h_absurd; exact absurd h_absurd (by simp)
  · rw [contDiffOn_zero]
    have h_coprod_bilin : Continuous
        (fun (p : (F →L[ℝ] G) × (ℝ →L[ℝ] G)) => p.1.coprod p.2) :=
      (ContinuousLinearMap.coprodEquivL ℝ).continuous
    have h_clm_cont : ContinuousOn
        (fun p : F × ℝ =>
          if hx : p.1 ∈ U then
            if ht : p.2 ∈ Set.Ioo a b' then
              variationalW_clm hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht
            else 0
          else 0)
        (U ×ˢ Set.Ioo a b') :=
      variationalW_clm_continuousOn hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont hDZ₀_cont
    have h_toSpan_cont : ContinuousOn
        (fun p : F × ℝ => ContinuousLinearMap.toSpanSingleton ℝ
          (A p.1 p.2 (Z p.1 p.2)))
        (U ×ˢ Set.Ioo a b') :=
      (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := G)).continuous.comp_continuousOn
        (linearODESolution_partial_t_continuousOn hab_lt h₀_mem hU hA_cont hZ₀_cont)
    have h_formula_cont : ContinuousOn
        (fun p : F × ℝ =>
          (if hx : p.1 ∈ U then
            if ht : p.2 ∈ Set.Ioo a b' then
              variationalW_clm hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht
            else 0
          else 0).coprod
            (ContinuousLinearMap.toSpanSingleton ℝ (A p.1 p.2 (Z p.1 p.2))))
        (U ×ˢ Set.Ioo a b') :=
      h_coprod_bilin.comp_continuousOn (h_clm_cont.prodMk h_toSpan_cont)
    apply h_formula_cont.congr
    intro p hp
    obtain ⟨hx, ht⟩ := Set.mem_prod.mp hp
    have h_eq : (if hx' : p.1 ∈ U then
        if ht' : p.2 ∈ Set.Ioo a b' then
          variationalW_clm hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont hx' ht'
        else 0
      else 0) = variationalW_clm hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht := by
      rw [dif_pos hx, dif_pos ht]
    change fderiv ℝ (uncurry Z) p
        = ((if hx' : p.1 ∈ U then
              if ht' : p.2 ∈ Set.Ioo a b' then
                variationalW_clm hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont hx' ht'
              else 0
            else 0).coprod
            (ContinuousLinearMap.toSpanSingleton ℝ (A p.1 p.2 (Z p.1 p.2))))
    rw [h_eq, hZ_def]
    conv_lhs => rw [show p = (p.1, p.2) from Prod.mk.eta.symm]
    exact (linearODESolution_hasFDerivAt_joint hab_lt h₀_mem hU hA_cont hDA_cont
      hA_diff hZ₀_cont hDZ₀_cont hZ₀_diff hx ht).fderiv

/-- **C^n regularity of the augmented coefficient**.

If `A : F → ℝ → (G →L[ℝ] G)` and `b : F → ℝ → G` are both `C^n` jointly on
`U ×ˢ Ioo a b'`, then the augmented coefficient `inhomogAugmentedCoeff A b`
is `C^n` jointly.  This extends `inhomogAugmentedCoeff_continuousOn` to
general regularity order. -/
private theorem inhomogAugmentedCoeff_contDiffOn
    {n : ℕ∞}
    {A : F → ℝ → (G →L[ℝ] G)} {b : F → ℝ → G}
    {U : Set F} {a b' : ℝ}
    (hA : ContDiffOn ℝ n (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hb : ContDiffOn ℝ n (Function.uncurry b) (U ×ˢ Set.Ioo a b')) :
    ContDiffOn ℝ n (Function.uncurry (inhomogAugmentedCoeff A b))
      (U ×ˢ Set.Ioo a b') := by
  have h_first : ContDiffOn ℝ n
      (fun p : F × ℝ => (A p.1 p.2).comp (ContinuousLinearMap.fst ℝ G ℝ))
      (U ×ˢ Set.Ioo a b') :=
    hA.clm_comp contDiffOn_const
  have h_second : ContDiffOn ℝ n
      (fun p : F × ℝ =>
        (ContinuousLinearMap.snd ℝ G ℝ).smulRight (b p.1 p.2))
      (U ×ˢ Set.Ioo a b') := by
    have h_smul_cont : ContDiff ℝ n
        (fun y : G => (ContinuousLinearMap.snd ℝ G ℝ).smulRight y) :=
      (ContinuousLinearMap.smulRightL ℝ (G × ℝ) G
        (ContinuousLinearMap.snd ℝ G ℝ)).contDiff
    exact h_smul_cont.comp_contDiffOn hb
  have h_sum : ContDiffOn ℝ n
      (fun p : F × ℝ =>
        ((A p.1 p.2).comp (ContinuousLinearMap.fst ℝ G ℝ)) +
          ((ContinuousLinearMap.snd ℝ G ℝ).smulRight (b p.1 p.2)))
      (U ×ˢ Set.Ioo a b') := h_first.add h_second
  have h_prodL : ContDiff ℝ n
      (fun q : ((G × ℝ) →L[ℝ] G) × ((G × ℝ) →L[ℝ] ℝ) => q.1.prod q.2) :=
    (ContinuousLinearMap.prodL (𝕜 := ℝ) (E := G × ℝ) (F := G) (G := ℝ) ℝ).contDiff
  have h_pair : ContDiffOn ℝ n
      (fun p : F × ℝ =>
        (((A p.1 p.2).comp (ContinuousLinearMap.fst ℝ G ℝ)) +
          ((ContinuousLinearMap.snd ℝ G ℝ).smulRight (b p.1 p.2)),
        (0 : (G × ℝ) →L[ℝ] ℝ)))
      (U ×ˢ Set.Ioo a b') := h_sum.prodMk contDiffOn_const
  exact h_prodL.comp_contDiffOn h_pair

/-- Extract the six hypotheses of `linearODESolution_contDiffOn_one` from
`ContDiffOn ℝ (↑(n + 1)) (uncurry A)` and `ContDiffOn ℝ (↑(n + 1)) Z₀`,
plus openness of `U`.

Returns:
1. `ContinuousOn (uncurry A) (U ×ˢ Ioo a b')`
2. `ContinuousOn (uncurry (fun x t => fderiv ℝ (fun y => A y t) x)) (U ×ˢ Ioo a b')`
3. `∀ y ∈ U, ∀ s ∈ Ioo a b', HasFDerivAt (fun z => A z s) (fderiv ℝ (·) y) y`
4. `ContinuousOn Z₀ U`
5. `ContinuousOn (fun x => fderiv ℝ Z₀ x) U`
6. `∀ y ∈ U, HasFDerivAt Z₀ (fderiv ℝ Z₀ y) y`
-/
private theorem extract_C1_hypotheses
    {A : F → ℝ → (G →L[ℝ] G)} {Z₀ : F → G}
    {a b' : ℝ} {n : ℕ}
    {U : Set F} (hU : IsOpen U)
    (hA : ContDiffOn ℝ (↑(n + 1) : ℕ∞) (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hZ₀ : ContDiffOn ℝ (↑(n + 1) : ℕ∞) Z₀ U) :
    ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b') ∧
    ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b') ∧
    (∀ y ∈ U, ∀ s ∈ Set.Ioo a b',
      HasFDerivAt (fun z => A z s) (fderiv ℝ (fun z => A z s) y) y) ∧
    ContinuousOn Z₀ U ∧
    ContinuousOn (fun x => fderiv ℝ Z₀ x) U ∧
    (∀ y ∈ U, HasFDerivAt Z₀ (fderiv ℝ Z₀ y) y) := by
  have hS_open : IsOpen (U ×ˢ Set.Ioo a b' : Set (F × ℝ)) := hU.prod isOpen_Ioo
  have hA_ge1 : ContDiffOn ℝ 1 (Function.uncurry A) (U ×ˢ Set.Ioo a b') :=
    hA.of_le (by norm_cast; omega)
  have hZ₀_ge1 : ContDiffOn ℝ 1 Z₀ U := hZ₀.of_le (by norm_cast; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hA_ge1.continuousOn
  · have h_fderiv_cont : ContinuousOn (fderiv ℝ (Function.uncurry A))
        (U ×ˢ Set.Ioo a b') :=
      hA_ge1.continuousOn_fderiv_of_isOpen hS_open le_rfl
    have h_eq : ∀ p : F × ℝ, p ∈ U ×ˢ Set.Ioo a b' →
        fderiv ℝ (fun y => A y p.2) p.1
          = (fderiv ℝ (Function.uncurry A) p).comp (ContinuousLinearMap.inl ℝ F ℝ) := by
      intro ⟨x, t⟩ ⟨hx, ht⟩
      have h_eq_comp : (fun y => A y t) = Function.uncurry A ∘ (fun y => (y, t)) := by
        ext y; simp [Function.uncurry]
      have h_diffA : DifferentiableAt ℝ (Function.uncurry A) (x, t) := by
        apply (hA_ge1.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
          (x, t) (Set.mem_prod.mpr ⟨hx, ht⟩)).differentiableAt
        exact hS_open.mem_nhds (Set.mem_prod.mpr ⟨hx, ht⟩)
      rw [h_eq_comp]
      rw [fderiv_comp x h_diffA (hasFDerivAt_prodMk_left x t).differentiableAt]
      simp [hasFDerivAt_prodMk_left x t |>.fderiv]
    refine (h_fderiv_cont.clm_comp continuousOn_const).congr h_eq
  · intro y hy s hs
    have h_diffA : DifferentiableAt ℝ (Function.uncurry A) (y, s) := by
      apply (hA_ge1.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
        (y, s) (Set.mem_prod.mpr ⟨hy, hs⟩)).differentiableAt
      exact hS_open.mem_nhds (Set.mem_prod.mpr ⟨hy, hs⟩)
    have h_diff_partial : DifferentiableAt ℝ (fun z => A z s) y := by
      have : (fun z => A z s) = Function.uncurry A ∘ (fun z => (z, s)) := by
        ext z; simp [Function.uncurry]
      rw [this]
      exact h_diffA.comp y (hasFDerivAt_prodMk_left y s).differentiableAt
    exact h_diff_partial.hasFDerivAt
  · exact hZ₀_ge1.continuousOn
  · exact hZ₀_ge1.continuousOn_fderiv_of_isOpen hU le_rfl
  · intro y hy
    exact ((hZ₀_ge1.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0) y hy).differentiableAt
      (hU.mem_nhds hy)).hasFDerivAt

/-- **C^n regularity of the variational forcing**.

If `A` is `C^{n+1}` jointly and `Z` (the linearODESolution) is `C^n` (by IH), then the
variational forcing `(x,t) ↦ variationalForcing A a b' h₀ Z₀ x v t` is `C^n`. -/
private theorem variationalForcing_contDiffOn_of_Z_contDiffOn
    {n : ℕ∞}
    {A : F → ℝ → (G →L[ℝ] G)} {a b' : ℝ} {h₀ : ℝ} {Z₀ : F → G}
    {U : Set F} (hU : IsOpen U)
    (hA : ContDiffOn ℝ (n + 1) (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hZ : ContDiffOn ℝ n (Function.uncurry (linearODESolution A a b' h₀ Z₀))
      (U ×ˢ Set.Ioo a b'))
    (v : F) :
    ContDiffOn ℝ n
      (Function.uncurry (fun x t => variationalForcing A a b' h₀ Z₀ x v t))
      (U ×ˢ Set.Ioo a b') := by
  have hS_open : IsOpen (U ×ˢ Set.Ioo a b' : Set (F × ℝ)) := hU.prod isOpen_Ioo
  have h_fderivA : ContDiffOn ℝ n (fderiv ℝ (Function.uncurry A))
      (U ×ˢ Set.Ioo a b') :=
    hA.fderiv_of_isOpen hS_open le_rfl
  have h_partial : ContDiffOn ℝ n
      (fun p : F × ℝ => (fderiv ℝ (Function.uncurry A) p).comp
        (ContinuousLinearMap.inl ℝ F ℝ))
      (U ×ˢ Set.Ioo a b') :=
    h_fderivA.clm_comp contDiffOn_const
  have h_eval_v : ContDiffOn ℝ n
      (fun p : F × ℝ =>
        ((fderiv ℝ (Function.uncurry A) p).comp (ContinuousLinearMap.inl ℝ F ℝ)) v)
      (U ×ˢ Set.Ioo a b') :=
    h_partial.clm_apply contDiffOn_const
  have h_agree : ∀ p : F × ℝ, p ∈ U ×ˢ Set.Ioo a b' →
      (fderiv ℝ (fun y => A y p.2) p.1)
        = (fderiv ℝ (Function.uncurry A) p).comp (ContinuousLinearMap.inl ℝ F ℝ) := by
    intro ⟨x, t⟩ ⟨hx, ht⟩
    have hA_ge1 : ContDiffOn ℝ 1 (Function.uncurry A) (U ×ˢ Set.Ioo a b') :=
      hA.of_le (by simp)
    have h_diffA : DifferentiableAt ℝ (Function.uncurry A) (x, t) := by
      exact ((hA_ge1.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0))
        (x, t) (Set.mem_prod.mpr ⟨hx, ht⟩)).differentiableAt
        (hS_open.mem_nhds (Set.mem_prod.mpr ⟨hx, ht⟩))
    have h_eq_comp : (fun y => A y t) = Function.uncurry A ∘ (fun y => (y, t)) := by
      ext y; simp [Function.uncurry]
    rw [h_eq_comp, fderiv_comp x h_diffA (hasFDerivAt_prodMk_left x t).differentiableAt]
    simp [hasFDerivAt_prodMk_left x t |>.fderiv]
  have h_forcing_eq : ∀ p : F × ℝ, p ∈ U ×ˢ Set.Ioo a b' →
      Function.uncurry (fun x t => variationalForcing A a b' h₀ Z₀ x v t) p
        = ((fderiv ℝ (Function.uncurry A) p).comp (ContinuousLinearMap.inl ℝ F ℝ)) v
            (linearODESolution A a b' h₀ Z₀ p.1 p.2) := by
    intro ⟨x, t⟩ hp
    simp only [Function.uncurry, variationalForcing]
    rw [h_agree (x, t) hp]
  exact (h_eval_v.clm_apply hZ).congr h_forcing_eq

end VariationalSolution

set_option maxHeartbeats 1600000 in
/-- **C^n regularity of the parametric linear ODE solution operator**.

If `A : F → ℝ → (G →L[ℝ] G)` is `C^n` jointly on `U ×ˢ Ioo a b'` and
`Z₀ : F → G` is `C^n` on `U`, then the parametric solution
`(x, t) ↦ linearODESolution A a b' h₀ Z₀ x t` is `C^n` jointly on
`U ×ˢ Ioo a b'`.

The proof is by induction on `n`:
- `n = 0`: joint continuity (`linearODESolution_continuousOn`).
- `n → n + 1`: reduce to `C^n` of the Fréchet derivative via
  `contDiffOn_succ_iff_fderiv_of_isOpen`.  The derivative is the coprod
  of `variationalW_clm` (x-partial) and `toSpanSingleton(A(x,t)(Z(x,t)))`
  (t-partial).  Both components inherit `C^n` from the inductive hypothesis
  applied to the original system (for the t-partial) and to the augmented
  variational system (for the x-partial via `contDiffOn_clm_apply`). -/
theorem linearODESolution_contDiffOn
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    [FiniteDimensional ℝ F]
    {A : F → ℝ → (G →L[ℝ] G)} {Z₀ : F → G}
    {a b' : ℝ} (hab_lt : a < b') {h₀ : ℝ} (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (n : ℕ)
    (hA : ContDiffOn ℝ (n : ℕ∞) (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hZ₀ : ContDiffOn ℝ (n : ℕ∞) Z₀ U) :
    ContDiffOn ℝ (n : ℕ∞)
      (Function.uncurry (linearODESolution A a b' h₀ Z₀))
      (U ×ˢ Set.Ioo a b') := by
  classical
  induction n generalizing G with
  | zero =>
    exact (contDiffOn_zero.mpr
      (linearODESolution_continuousOn hab_lt h₀_mem hU hA.continuousOn hZ₀.continuousOn))
  | succ n ih =>
    have hA_n : ContDiffOn ℝ (n : ℕ∞) (Function.uncurry A) (U ×ˢ Set.Ioo a b') :=
      hA.of_le (by norm_cast; omega)
    have hZ₀_n : ContDiffOn ℝ (n : ℕ∞) Z₀ U := hZ₀.of_le (by norm_cast; omega)
    have hZ_n : ContDiffOn ℝ (n : ℕ∞)
        (Function.uncurry (linearODESolution A a b' h₀ Z₀)) (U ×ˢ Set.Ioo a b') :=
      ih hA_n hZ₀_n
    have ⟨hA_cont, hDA_cont, hA_diff, hZ₀_cont, hDZ₀_cont, hZ₀_diff⟩ :=
      extract_C1_hypotheses hU hA hZ₀
    set Z := linearODESolution A a b' h₀ Z₀ with hZ_def
    set S := (U ×ˢ Set.Ioo a b' : Set (F × ℝ)) with hS_def
    have hS_open : IsOpen S := hU.prod isOpen_Ioo
    suffices h_goal : ContDiffOn ℝ ((↑(↑n : ℕ∞) : WithTop ℕ∞) + 1) (Function.uncurry Z) S by
      exact_mod_cast h_goal
    rw [contDiffOn_succ_iff_fderiv_of_isOpen hS_open]
    refine ⟨?_, ?_, ?_⟩
    · intro ⟨x, t⟩ ⟨hx, ht⟩
      exact (linearODESolution_hasFDerivAt_joint hab_lt h₀_mem hU hA_cont hDA_cont hA_diff
        hZ₀_cont hDZ₀_cont hZ₀_diff hx ht).differentiableAt.differentiableWithinAt
    · intro h_absurd
      exact absurd h_absurd WithTop.coe_ne_top
    · have h_AZ_n : ContDiffOn ℝ (↑n : ℕ∞)
          (fun p : F × ℝ => A p.1 p.2 (Z p.1 p.2)) S :=
        hA_n.clm_apply hZ_n
      have h_toSpan_n : ContDiffOn ℝ (↑n : ℕ∞)
          (fun p : F × ℝ => ContinuousLinearMap.toSpanSingleton ℝ
            (A p.1 p.2 (Z p.1 p.2))) S :=
        (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := G)).contDiff.comp_contDiffOn
          h_AZ_n
      have h_varW_v_n : ∀ v : F, ContDiffOn ℝ (↑n : ℕ∞)
          (fun p : F × ℝ => variationalW A a b' h₀ Z₀ p.1 v p.2) S := by
        intro v
        have h_forcing_n : ContDiffOn ℝ (↑n : ℕ∞)
            (Function.uncurry (fun x t => variationalForcing A a b' h₀ Z₀ x v t))
            S :=
          variationalForcing_contDiffOn_of_Z_contDiffOn hU (by exact_mod_cast hA) hZ_n v
        have hZ₀_fderiv_n : ContDiffOn ℝ (↑n : ℕ∞) (fderiv ℝ Z₀) U :=
          hZ₀.fderiv_of_isOpen hU (by norm_cast)
        have h_augIC_n : ContDiffOn ℝ (↑n : ℕ∞)
            (fun y => ((fderiv ℝ Z₀ y) v, (1 : ℝ))) U :=
          (hZ₀_fderiv_n.clm_apply contDiffOn_const).prodMk contDiffOn_const
        have h_Ahat_n : ContDiffOn ℝ (↑n : ℕ∞)
            (Function.uncurry (inhomogAugmentedCoeff A
              (fun y t => variationalForcing A a b' h₀ Z₀ y v t))) S :=
          inhomogAugmentedCoeff_contDiffOn hA_n h_forcing_n
        have h_aug_sol_n : ContDiffOn ℝ (↑n : ℕ∞)
            (Function.uncurry (linearODESolution
              (inhomogAugmentedCoeff A (fun y t => variationalForcing A a b' h₀ Z₀ y v t))
              a b' h₀ (fun y => ((fderiv ℝ Z₀ y) v, (1 : ℝ))))) S :=
          ih (G := G × ℝ) h_Ahat_n h_augIC_n
        have h_fst_n : ContDiffOn ℝ (↑n : ℕ∞)
            (fun p : F × ℝ =>
              (linearODESolution
                (inhomogAugmentedCoeff A (fun y t => variationalForcing A a b' h₀ Z₀ y v t))
                a b' h₀ (fun y => ((fderiv ℝ Z₀ y) v, (1 : ℝ))) p.1 p.2).1) S :=
          contDiff_fst.comp_contDiffOn h_aug_sol_n
        exact h_fst_n.congr (fun _ _ => rfl)
      have h_clm_n : ContDiffOn ℝ (↑n : ℕ∞)
          (fun p : F × ℝ =>
            if hx : p.1 ∈ U then
              if ht : p.2 ∈ Set.Ioo a b' then
                variationalW_clm hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht
              else 0
            else 0)
          S := by
        rw [contDiffOn_clm_apply]
        intro v'
        refine (h_varW_v_n v').congr (fun p hp => ?_)
        obtain ⟨hx, ht⟩ := Set.mem_prod.mp hp
        simp only [dif_pos hx, dif_pos ht]
        exact (variationalW_clm_apply hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont
          hx ht v').symm
      have h_coprod_n : ContDiffOn ℝ (↑n : ℕ∞)
          (fun p : F × ℝ =>
            (if hx : p.1 ∈ U then
              if ht : p.2 ∈ Set.Ioo a b' then
                variationalW_clm hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht
              else 0
            else 0).coprod
              (ContinuousLinearMap.toSpanSingleton ℝ (A p.1 p.2 (Z p.1 p.2))))
          S := by
        exact (ContinuousLinearMap.coprodEquivL ℝ
          (E := F) (F := ℝ) (G := G)).contDiff.comp_contDiffOn
          (h_clm_n.prodMk h_toSpan_n)
      refine h_coprod_n.congr (fun p hp => ?_)
      obtain ⟨hx, ht⟩ := Set.mem_prod.mp hp
      have h_eq : (if hx' : p.1 ∈ U then
          if ht' : p.2 ∈ Set.Ioo a b' then
            variationalW_clm hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont hx' ht'
          else 0
        else 0) = variationalW_clm hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht := by
        rw [dif_pos hx, dif_pos ht]
      change fderiv ℝ (Function.uncurry Z) p
          = ((if hx' : p.1 ∈ U then
                if ht' : p.2 ∈ Set.Ioo a b' then
                  variationalW_clm hab_lt h₀_mem hU hA_cont hDA_cont hZ₀_cont hx' ht'
                else 0
              else 0).coprod
              (ContinuousLinearMap.toSpanSingleton ℝ (A p.1 p.2 (Z p.1 p.2))))
      rw [h_eq, hZ_def]
      conv_lhs => rw [show p = (p.1, p.2) from Prod.mk.eta.symm]
      exact (linearODESolution_hasFDerivAt_joint hab_lt h₀_mem hU hA_cont hDA_cont
        hA_diff hZ₀_cont hDZ₀_cont hZ₀_diff hx ht).fderiv

section CInfinityRegularity

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- **C^∞ regularity of the parametric linear ODE solution operator**.

If `A : F → ℝ → (G →L[ℝ] G)` is `C^∞` jointly on `U ×ˢ Ioo a b'` and
`Z₀ : F → G` is `C^∞` on `U`, then the parametric solution
`(x, t) ↦ linearODESolution A a b' h₀ Z₀ x t` is `C^∞` jointly on
`U ×ˢ Ioo a b'`. -/
theorem linearODESolution_contDiffOn_top
    [FiniteDimensional ℝ F]
    {A : F → ℝ → (G →L[ℝ] G)} {Z₀ : F → G}
    {a b' : ℝ} (hab_lt : a < b') {h₀ : ℝ} (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hZ₀ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Z₀ U) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry (linearODESolution A a b' h₀ Z₀))
      (U ×ˢ Set.Ioo a b') := by
  rw [contDiffOn_infty]
  intro k
  exact linearODESolution_contDiffOn hab_lt h₀_mem hU k
    (hA.of_le (by exact_mod_cast le_top)) (hZ₀.of_le (by exact_mod_cast le_top))

end CInfinityRegularity

end Flow
end ODE
end Analysis
end DifferentialGeometry

end
