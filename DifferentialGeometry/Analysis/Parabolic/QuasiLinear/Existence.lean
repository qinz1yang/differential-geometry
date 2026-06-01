import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.Contraction
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Short-time existence and uniqueness of the mild solution

For a real Banach space `X`, a `BoundedC0Semigroup S` with generator `A`,
an initial datum `u₀ : X`, and a globally Lipschitz lower-order
nonlinearity `N : X → X`, this file proves **short-time existence and
uniqueness** of a mild solution of the semilinear evolution equation

  `∂_t u = A u + N(u)`,  `u(0) = u₀`,

i.e. a continuous path `u : [0, T] → X` solving the Duhamel integral
equation

  `u(t) = S t u₀ + ∫₀ᵗ S (t - τ) (N (u τ)) dτ`.

The construction is the classical Banach fixed-point argument. On the
complete metric space `C(↑(Set.Icc 0 T), X)` of continuous maps from the
compact time interval, the nonlinear Duhamel map `duhamelCM` is a
self-map; the contraction estimate `nlDuhamel_dist_le` shows that for `T`
small enough that `(L : ℝ) * T < 1` it is a contraction with constant
`(L : ℝ) * T`. Mathlib's `ContractingWith.fixedPoint` then supplies a
unique fixed point, which is the mild solution.

Choosing `T := 1 / (L + 1)` makes `(L : ℝ) * T = L / (L + 1) < 1`
unconditionally, so a positive existence time always exists.

## Main definitions

* `duhamelCM S u₀ hN hT0` — the nonlinear Duhamel map realised as a
  self-map of `C(↑(Set.Icc 0 T), X)`.

## Main results

* `duhamelCM_contractingWith` — `duhamelCM` is a contraction whenever
  `(L : ℝ) * T < 1`.
* `semilinear_mild_solution_existence` — existence of a positive time `T` and
  a continuous mild solution on `[0, T]`.
* `semilinear_mild_solution_unique` — two continuous mild solutions on the
  same interval `[0, T]` (with `(L : ℝ) * T < 1`) coincide.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [CompleteSpace X]

/-- The space of continuous maps from the compact interval
`↑(Set.Icc 0 T)` to a Banach space `X` is complete. -/
instance instCompleteSpaceContinuousMapIcc {T : ℝ} :
    CompleteSpace C(↑(Set.Icc (0 : ℝ) T), X) :=
  (ContinuousMap.isometryEquivBoundedOfCompact
    (↑(Set.Icc (0 : ℝ) T)) X).completeSpace

/-- The forcing path obtained from a continuous map on the time interval
by clamping the argument into `[0, T]`. -/
private def pathOfCM {T : ℝ} (hT0 : (0 : ℝ) ≤ T)
    (u : C(↑(Set.Icc (0 : ℝ) T), X)) : ℝ → X :=
  Set.IccExtend hT0 u

private theorem continuous_pathOfCM {T : ℝ} (hT0 : (0 : ℝ) ≤ T)
    (u : C(↑(Set.Icc (0 : ℝ) T), X)) : Continuous (pathOfCM hT0 u) :=
  Continuous.Icc_extend' u.continuous

/-- On the time interval `[0, T]` the clamped forcing path agrees with
the original continuous map. -/
private theorem pathOfCM_apply_mem {T : ℝ} (hT0 : (0 : ℝ) ≤ T)
    (u : C(↑(Set.Icc (0 : ℝ) T), X)) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) T) :
    pathOfCM hT0 u τ = u ⟨τ, hτ⟩ :=
  Set.IccExtend_of_mem hT0 u hτ

/-- The nonlinear Duhamel map realised as a self-map of the space of
continuous paths `C(↑(Set.Icc 0 T), X)`.

A continuous path `u` is first clamped to a forcing function on all of
`ℝ` via `pathOfCM`, then mapped through the nonlinear Duhamel map
`nlDuhamel`; the result, restricted to the compact interval, is again a
continuous map. Continuity on `[0, T]` follows from
`nlDuhamel_continuousOn` (which needs the nonlinearity `N` to be
Lipschitz) since `Set.Icc 0 T ⊆ Set.Ici 0`. -/
def duhamelCM (S : BoundedC0Semigroup X) (u₀ : X) {N : X → X} {L : ℝ≥0}
    (hN : LipschitzWith L N) {T : ℝ} (hT0 : (0 : ℝ) ≤ T) :
    C(↑(Set.Icc (0 : ℝ) T), X) → C(↑(Set.Icc (0 : ℝ) T), X) :=
  fun u =>
    ⟨fun t => nlDuhamel S u₀ N (pathOfCM hT0 u) t,
      by
        have h_on : ContinuousOn
            (nlDuhamel S u₀ N (pathOfCM hT0 u)) (Set.Ici 0) :=
          nlDuhamel_continuousOn S u₀ hN (continuous_pathOfCM hT0 u)
        have h_sub : Set.Icc (0 : ℝ) T ⊆ Set.Ici (0 : ℝ) :=
          Set.Icc_subset_Ici_self
        exact (h_on.mono h_sub).restrict⟩

@[simp]
theorem duhamelCM_apply (S : BoundedC0Semigroup X) (u₀ : X) {N : X → X}
    {L : ℝ≥0} (hN : LipschitzWith L N) {T : ℝ} (hT0 : (0 : ℝ) ≤ T)
    (u : C(↑(Set.Icc (0 : ℝ) T), X)) (t : ↑(Set.Icc (0 : ℝ) T)) :
    duhamelCM S u₀ hN hT0 u t =
      nlDuhamel S u₀ N (pathOfCM hT0 u) (t : ℝ) :=
  rfl

/-- Pointwise `dist` bound for the Duhamel self-map: for any two
continuous paths the distance of the Duhamel images at a time
`t ∈ [0, T]` is bounded by `(L : ℝ) * T * dist u v`. -/
private theorem duhamelCM_dist_apply_le (S : BoundedC0Semigroup X)
    (u₀ : X) {N : X → X} {L : ℝ≥0} (hN : LipschitzWith L N) {T : ℝ}
    (hT0 : (0 : ℝ) ≤ T) (u v : C(↑(Set.Icc (0 : ℝ) T), X))
    (t : ↑(Set.Icc (0 : ℝ) T)) :
    dist (duhamelCM S u₀ hN hT0 u t) (duhamelCM S u₀ hN hT0 v t) ≤
      (L : ℝ) * T * dist u v := by
  obtain ⟨t, ht⟩ := t
  obtain ⟨ht0, htT⟩ := ht
  have h_forcing_bound : ∀ τ ∈ Set.Icc (0 : ℝ) t,
      ‖pathOfCM hT0 u τ - pathOfCM hT0 v τ‖ ≤ dist u v := by
    intro τ hτ
    have hτT : τ ∈ Set.Icc (0 : ℝ) T :=
      ⟨hτ.1, le_trans hτ.2 htT⟩
    rw [pathOfCM_apply_mem hT0 u hτT, pathOfCM_apply_mem hT0 v hτT,
      ← dist_eq_norm]
    exact ContinuousMap.dist_apply_le_dist _
  have h_t_le :
      ‖nlDuhamel S u₀ N (pathOfCM hT0 u) t -
          nlDuhamel S u₀ N (pathOfCM hT0 v) t‖ ≤
        (L : ℝ) * t * dist u v :=
    nlDuhamel_dist_le S u₀ hN (continuous_pathOfCM hT0 u)
      (continuous_pathOfCM hT0 v) ht0 h_forcing_bound
  have h_dist_nn : (0 : ℝ) ≤ dist u v := dist_nonneg
  have hL_nn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  have h_mono : (L : ℝ) * t * dist u v ≤ (L : ℝ) * T * dist u v := by
    have : (L : ℝ) * t ≤ (L : ℝ) * T :=
      mul_le_mul_of_nonneg_left htT hL_nn
    exact mul_le_mul_of_nonneg_right this h_dist_nn
  calc dist (duhamelCM S u₀ hN hT0 u ⟨t, _⟩)
        (duhamelCM S u₀ hN hT0 v ⟨t, _⟩)
      = ‖nlDuhamel S u₀ N (pathOfCM hT0 u) t -
          nlDuhamel S u₀ N (pathOfCM hT0 v) t‖ := by
        rw [duhamelCM_apply, duhamelCM_apply, dist_eq_norm]
    _ ≤ (L : ℝ) * t * dist u v := h_t_le
    _ ≤ (L : ℝ) * T * dist u v := h_mono

/-- Global `dist` bound for the Duhamel self-map:
`dist (duhamelCM … u) (duhamelCM … v) ≤ ((L : ℝ) * T) * dist u v`. -/
private theorem duhamelCM_dist_le (S : BoundedC0Semigroup X) (u₀ : X)
    {N : X → X} {L : ℝ≥0} (hN : LipschitzWith L N) {T : ℝ}
    (hT0 : (0 : ℝ) ≤ T) (hTL_nn : (0 : ℝ) ≤ (L : ℝ) * T)
    (u v : C(↑(Set.Icc (0 : ℝ) T), X)) :
    dist (duhamelCM S u₀ hN hT0 u) (duhamelCM S u₀ hN hT0 v) ≤
      ((L : ℝ) * T) * dist u v := by
  refine (ContinuousMap.dist_le ?_).mpr ?_
  · exact mul_nonneg hTL_nn dist_nonneg
  · intro t
    exact duhamelCM_dist_apply_le S u₀ hN hT0 u v t

/-- The Duhamel self-map is a contraction whenever `(L : ℝ) * T < 1`.

The contraction constant is `(L : ℝ) * T`, packaged as an element of
`ℝ≥0` via the non-negativity of `(L : ℝ) * T`; the `LipschitzWith`
property follows from the global `dist` bound `duhamelCM_dist_le`. -/
theorem duhamelCM_contractingWith (S : BoundedC0Semigroup X) (u₀ : X)
    {N : X → X} {L : ℝ≥0} (hN : LipschitzWith L N) {T : ℝ}
    (hT0 : (0 : ℝ) ≤ T) (hTL : (L : ℝ) * T < 1) :
    ContractingWith ⟨(L : ℝ) * T, mul_nonneg L.coe_nonneg hT0⟩
      (duhamelCM S u₀ hN hT0) := by
  have hTL_nn : (0 : ℝ) ≤ (L : ℝ) * T := mul_nonneg L.coe_nonneg hT0
  refine ⟨?_, ?_⟩
  · rw [← NNReal.coe_lt_coe]
    simpa using hTL
  · refine LipschitzWith.of_dist_le_mul ?_
    intro u v
    have h := duhamelCM_dist_le S u₀ hN hT0 hTL_nn u v
    simpa using h

/-- **Short-time existence of a mild solution.**

For a bounded `C₀`-semigroup `S` on a Banach space `X`, any initial
datum `u₀`, and a globally Lipschitz nonlinearity `N`, there is a
positive existence time `T` and a continuous path `u : [0, T] → X`
solving the semilinear Duhamel integral equation
`u(t) = S t u₀ + ∫₀ᵗ S (t - τ) (N (u τ)) dτ` with `u(0) = u₀`.

The existence time `T := 1 / (L + 1)` is positive and makes the
nonlinear Duhamel map a contraction on the path space; its unique fixed
point, extended off `[0, T]` by `Set.IccExtend`, is the mild
solution. -/
theorem semilinear_mild_solution_existence (S : BoundedC0Semigroup X)
    (u₀ : X) {N : X → X} {L : ℝ≥0} (hN : LipschitzWith L N) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → X,
      ContinuousOn u (Set.Icc 0 T) ∧
      u 0 = u₀ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        u t = S t u₀ + ∫ τ in (0 : ℝ)..t, S (t - τ) (N (u τ)) := by
  set T : ℝ := 1 / ((L : ℝ) + 1) with hT_def
  have hLp1_pos : (0 : ℝ) < (L : ℝ) + 1 :=
    add_pos_of_nonneg_of_pos L.coe_nonneg one_pos
  have hT_pos : 0 < T := by
    rw [hT_def]
    positivity
  have hT0 : (0 : ℝ) ≤ T := le_of_lt hT_pos
  have hTL : (L : ℝ) * T < 1 := by
    rw [hT_def, mul_one_div, div_lt_one hLp1_pos]
    linarith
  have h_contr := duhamelCM_contractingWith S u₀ hN hT0 hTL
  haveI : Nonempty (↑(Set.Icc (0 : ℝ) T)) :=
    ⟨⟨0, Set.left_mem_Icc.mpr hT0⟩⟩
  set uStar : C(↑(Set.Icc (0 : ℝ) T), X) :=
    ContractingWith.fixedPoint (duhamelCM S u₀ hN hT0) h_contr
      with huStar_def
  have huStar_fix : duhamelCM S u₀ hN hT0 uStar = uStar :=
    (ContractingWith.fixedPoint_isFixedPt h_contr)
  refine ⟨T, hT_pos, pathOfCM hT0 uStar, ?_, ?_, ?_⟩
  · exact (continuous_pathOfCM hT0 uStar).continuousOn
  · have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T :=
      Set.left_mem_Icc.mpr hT0
    rw [pathOfCM_apply_mem hT0 uStar h0_mem]
    have h_fix0 :
        (duhamelCM S u₀ hN hT0 uStar) ⟨0, h0_mem⟩ =
          uStar ⟨0, h0_mem⟩ := by
      rw [huStar_fix]
    rw [← h_fix0, duhamelCM_apply]
    exact nlDuhamel_zero S u₀ N (pathOfCM hT0 uStar)
  · intro t ht
    rw [pathOfCM_apply_mem hT0 uStar ht]
    have h_fixt :
        (duhamelCM S u₀ hN hT0 uStar) ⟨t, ht⟩ = uStar ⟨t, ht⟩ := by
      rw [huStar_fix]
    rw [← h_fixt, duhamelCM_apply]
    unfold nlDuhamel duhamel
    rfl

/-- The linear Duhamel value at time `t` depends on the forcing term `F`
only through its values on `[0, t]`: if `F₁` and `F₂` agree on
`Set.Icc 0 t` and `0 ≤ t`, then `duhamel S u₀ F₁ t = duhamel S u₀ F₂ t`.

Only the interval integral `∫ τ in 0..t` is forcing-dependent, and it
sees `F` only on `uIcc 0 t = Icc 0 t`. -/
private theorem duhamel_congr (S : BoundedC0Semigroup X) (u₀ : X)
    {F₁ F₂ : ℝ → X} {t : ℝ} (ht : 0 ≤ t)
    (hF : Set.EqOn F₁ F₂ (Set.Icc 0 t)) :
    duhamel S u₀ F₁ t = duhamel S u₀ F₂ t := by
  unfold duhamel
  congr 1
  refine intervalIntegral.integral_congr ?_
  intro τ hτ
  rw [Set.uIcc_of_le ht] at hτ
  change S (t - τ) (F₁ τ) = S (t - τ) (F₂ τ)
  rw [hF hτ]

/-- The nonlinear Duhamel value at time `t` depends on the forcing path
`u` only through its values on `[0, t]`. -/
private theorem nlDuhamel_congr (S : BoundedC0Semigroup X) (u₀ : X)
    (N : X → X) {u₁ u₂ : ℝ → X} {t : ℝ} (ht : 0 ≤ t)
    (hu : Set.EqOn u₁ u₂ (Set.Icc 0 t)) :
    nlDuhamel S u₀ N u₁ t = nlDuhamel S u₀ N u₂ t := by
  unfold nlDuhamel
  refine duhamel_congr S u₀ ht ?_
  intro τ hτ
  change N (u₁ τ) = N (u₂ τ)
  rw [hu hτ]

/-- A continuous path `u` on `[0, T]` solving the Duhamel integral
equation restricts to a fixed point of the Duhamel self-map `duhamelCM`.

The clamped forcing `pathOfCM hT0 u_restricted` agrees with `u` on
`[0, T]`, so by `nlDuhamel_congr` the nonlinear Duhamel value at any
`t ∈ [0, T]` is unchanged when the forcing is replaced by `u` itself;
the Duhamel equation then identifies it with `u t`. -/
private theorem isFixedPt_of_duhamel_solution (S : BoundedC0Semigroup X)
    (u₀ : X) {N : X → X} {L : ℝ≥0} (hN : LipschitzWith L N) {T : ℝ}
    (hT0 : (0 : ℝ) ≤ T) {u : ℝ → X}
    (hu : ContinuousOn u (Set.Icc 0 T))
    (hu_eq : ∀ t ∈ Set.Icc (0 : ℝ) T,
      u t = S t u₀ + ∫ τ in (0 : ℝ)..t, S (t - τ) (N (u τ))) :
    duhamelCM S u₀ hN hT0 ⟨_, hu.restrict⟩ = ⟨_, hu.restrict⟩ := by
  ext t
  obtain ⟨t, ht⟩ := t
  have h_eqOn : Set.EqOn
      (pathOfCM hT0 (⟨_, hu.restrict⟩ : C(↑(Set.Icc (0 : ℝ) T), X)))
      u (Set.Icc 0 t) := by
    intro τ hτ
    have hτT : τ ∈ Set.Icc (0 : ℝ) T :=
      ⟨hτ.1, le_trans hτ.2 ht.2⟩
    rw [pathOfCM_apply_mem hT0 _ hτT]
    rfl
  rw [duhamelCM_apply]
  have h_congr :
      nlDuhamel S u₀ N
          (pathOfCM hT0 (⟨_, hu.restrict⟩ : C(↑(Set.Icc (0 : ℝ) T), X)))
          t =
        nlDuhamel S u₀ N u t :=
    nlDuhamel_congr S u₀ N ht.1 h_eqOn
  rw [h_congr]
  change nlDuhamel S u₀ N u t = u t
  unfold nlDuhamel duhamel
  rw [hu_eq t ht]

/-- **Uniqueness of the mild solution.**

Any two continuous paths `u, v : [0, T] → X` solving the same semilinear
Duhamel integral equation with the same initial datum `u₀` coincide on
`[0, T]`, provided `(L : ℝ) * T < 1`.

Each solution restricts to a fixed point of the contracting Duhamel
self-map `duhamelCM`; uniqueness of the Banach fixed point forces the
two restrictions — hence the two paths on `[0, T]` — to be equal. -/
theorem semilinear_mild_solution_unique (S : BoundedC0Semigroup X) (u₀ : X)
    {N : X → X} {L : ℝ≥0} (hN : LipschitzWith L N) {T : ℝ} (hT : 0 < T)
    (hTL : (L : ℝ) * T < 1) {u v : ℝ → X}
    (hu : ContinuousOn u (Set.Icc 0 T)) (hv : ContinuousOn v (Set.Icc 0 T))
    (hu_eq : ∀ t ∈ Set.Icc (0 : ℝ) T,
      u t = S t u₀ + ∫ τ in (0 : ℝ)..t, S (t - τ) (N (u τ)))
    (hv_eq : ∀ t ∈ Set.Icc (0 : ℝ) T,
      v t = S t u₀ + ∫ τ in (0 : ℝ)..t, S (t - τ) (N (v τ))) :
    Set.EqOn u v (Set.Icc 0 T) := by
  have hT0 : (0 : ℝ) ≤ T := le_of_lt hT
  have h_contr := duhamelCM_contractingWith S u₀ hN hT0 hTL
  haveI : Nonempty (↑(Set.Icc (0 : ℝ) T)) :=
    ⟨⟨0, Set.left_mem_Icc.mpr hT0⟩⟩
  have hu_fix :
      duhamelCM S u₀ hN hT0 ⟨_, hu.restrict⟩ = ⟨_, hu.restrict⟩ :=
    isFixedPt_of_duhamel_solution S u₀ hN hT0 hu hu_eq
  have hv_fix :
      duhamelCM S u₀ hN hT0 ⟨_, hv.restrict⟩ = ⟨_, hv.restrict⟩ :=
    isFixedPt_of_duhamel_solution S u₀ hN hT0 hv hv_eq
  have h_eq :
      (⟨_, hu.restrict⟩ : C(↑(Set.Icc (0 : ℝ) T), X)) =
        ⟨_, hv.restrict⟩ := by
    rw [ContractingWith.fixedPoint_unique h_contr hu_fix,
      ContractingWith.fixedPoint_unique h_contr hv_fix]
  intro t ht
  have h_ap := ContinuousMap.congr_fun h_eq ⟨t, ht⟩
  simpa using h_ap

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
