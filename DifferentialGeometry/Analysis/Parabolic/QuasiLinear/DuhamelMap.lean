import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.AbstractSemigroup
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Abstract Duhamel mild-solution map

For a real Banach space `X`, a `BoundedC0Semigroup S` on `X`, an initial
datum `u₀ : X`, and a forcing term `F : ℝ → X`, the **Duhamel mild
solution** of the linear evolution equation `u' = A u + F(t)`, `u(0) = u₀`
(where `A` is the generator of `S`) is

  `duhamel S u₀ F t = S t u₀ + ∫₀ᵗ S (t - τ) (F τ) dτ`,

the second summand being a Bochner-valued interval integral on `[0, t]`.

This file defines `duhamel` and establishes that it is well posed: the
Duhamel integrand is interval-integrable for continuous `F`, the map is
continuous on `[0, ∞)`, and it recovers `u₀` at `t = 0`.

## Main definitions

* `duhamel S u₀ F t` — the abstract Duhamel formula.

## Main results

* `duhamel_zero` — `duhamel S u₀ F 0 = u₀`.
* `duhamel_integrable` — the integrand `τ ↦ S (t - τ) (F τ)` is
  interval-integrable on `[0, t]` for continuous `F` and `t ≥ 0`.
* `duhamel_continuousOn` — `duhamel S u₀ F` is continuous on `[0, ∞)`.
-/

noncomputable section

open Set Filter Topology MeasureTheory

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [CompleteSpace X]

/-- The abstract Duhamel mild solution of `u' = A u + F(t)`, `u(0) = u₀`,
for a bounded `C₀`-semigroup `S` (with generator `A`):
`duhamel S u₀ F t = S t u₀ + ∫₀ᵗ S (t - τ) (F τ) dτ`. -/
noncomputable def duhamel (S : BoundedC0Semigroup X) (u₀ : X)
    (F : ℝ → X) (t : ℝ) : X :=
  S t u₀ + ∫ τ in (0 : ℝ)..t, S (t - τ) (F τ)

/-- The clipped Duhamel kernel `S (max 0 (t - τ)) (F τ)`. Jointly
continuous in `(t, τ)`, and equal to the Duhamel integrand on
`τ ∈ [0, t]` for `t ≥ 0`. -/
private noncomputable def duhamelKernelClipped (S : BoundedC0Semigroup X)
    (F : ℝ → X) (t τ : ℝ) : X :=
  S (max 0 (t - τ)) (F τ)

/-- Joint continuity of the clipped Duhamel kernel: the map
`(t, τ) ↦ (max 0 (t - τ), F τ)` is continuous into `[0, ∞) × X`, and the
semigroup action is jointly continuous there. -/
private lemma continuous_duhamelKernelClipped (S : BoundedC0Semigroup X)
    {F : ℝ → X} (hF : Continuous F) :
    Continuous (Function.uncurry (duhamelKernelClipped S F)) := by
  have h_inner : Continuous
      (fun p : ℝ × ℝ => (max 0 (p.1 - p.2), F p.2)) := by
    refine Continuous.prodMk ?_ (hF.comp continuous_snd)
    exact continuous_const.max (continuous_fst.sub continuous_snd)
  have h_maps : ∀ p : ℝ × ℝ,
      (max 0 (p.1 - p.2), F p.2) ∈ Set.Ici (0 : ℝ) ×ˢ Set.univ := by
    intro p
    exact ⟨Set.mem_Ici.mpr (le_max_left _ _), Set.mem_univ _⟩
  have h_comp :=
    (S.continuousOn_uncurry).comp_continuous h_inner h_maps
  exact h_comp

/-- At `t = 0` the Duhamel mild solution recovers the initial datum:
`duhamel S u₀ F 0 = u₀`. -/
theorem duhamel_zero (S : BoundedC0Semigroup X) (u₀ : X) (F : ℝ → X) :
    duhamel S u₀ F 0 = u₀ := by
  unfold duhamel
  rw [intervalIntegral.integral_same, add_zero]
  rw [S.apply_zero]
  rfl

/-- The Duhamel integrand `τ ↦ S (t - τ) (F τ)` is interval-integrable on
`[0, t]` whenever `F` is continuous and `t ≥ 0`.

On `Set.uIoc 0 t = (0, t]` the raw integrand agrees with the clipped
kernel `duhamelKernelClipped S F t`, which is continuous, hence
interval-integrable; the conclusion transfers across that agreement. -/
theorem duhamel_integrable (S : BoundedC0Semigroup X) {F : ℝ → X}
    (hF : Continuous F) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun τ => S (t - τ) (F τ))
      MeasureTheory.volume 0 t := by
  have h_clip_cont :
      Continuous (fun τ : ℝ => duhamelKernelClipped S F t τ) :=
    (continuous_duhamelKernelClipped S hF).comp
      (continuous_const.prodMk continuous_id)
  have h_clip_ii :
      IntervalIntegrable (fun τ : ℝ => duhamelKernelClipped S F t τ)
        MeasureTheory.volume 0 t :=
    h_clip_cont.intervalIntegrable 0 t
  refine h_clip_ii.congr ?_
  intro τ hτ
  rw [Set.uIoc_of_le ht] at hτ
  have h_nn : 0 ≤ t - τ := sub_nonneg.mpr hτ.2
  change duhamelKernelClipped S F t τ = S (t - τ) (F τ)
  unfold duhamelKernelClipped
  rw [max_eq_right h_nn]

/-- The Duhamel mild solution `duhamel S u₀ F` is continuous on
`[0, ∞)`.

The homogeneous term `t ↦ S t u₀` is continuous on `[0, ∞)` by strong
continuity of the semigroup. The Duhamel integral term equals, for
`t ≥ 0`, the parametric integral of the jointly continuous clipped
kernel, which is continuous; the two facts combine after replacing the
raw map by the clipped one on a neighbourhood within `[0, ∞)`. -/
theorem duhamel_continuousOn (S : BoundedC0Semigroup X) (u₀ : X)
    {F : ℝ → X} (hF : Continuous F) :
    ContinuousOn (duhamel S u₀ F) (Set.Ici 0) := by
  have h_first_cont : ContinuousOn (fun t : ℝ => S t u₀) (Set.Ici 0) :=
    S.continuousOn_apply u₀
  have h_clip_eq : ∀ t : ℝ, 0 ≤ t →
      duhamel S u₀ F t =
        S t u₀ +
          ∫ τ in (0 : ℝ)..t, duhamelKernelClipped S F t τ := by
    intro t ht
    unfold duhamel
    congr 1
    refine intervalIntegral.integral_congr ?_
    intro τ hτ
    rw [Set.uIcc_of_le ht] at hτ
    have h_nn : 0 ≤ t - τ := sub_nonneg.mpr hτ.2
    change S (t - τ) (F τ) = duhamelKernelClipped S F t τ
    unfold duhamelKernelClipped
    rw [max_eq_right h_nn]
  have h_int_cont :
      Continuous (fun t : ℝ =>
        ∫ τ in (0 : ℝ)..t, duhamelKernelClipped S F t τ) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := MeasureTheory.volume) (a₀ := (0 : ℝ))
      (continuous_duhamelKernelClipped S hF) continuous_id
  intro t₀ ht₀
  have h_t₀_nn : 0 ≤ t₀ := Set.mem_Ici.mp ht₀
  have h_clipped_cont : ContinuousWithinAt
      (fun t : ℝ =>
        S t u₀ +
          ∫ τ in (0 : ℝ)..t, duhamelKernelClipped S F t τ)
      (Set.Ici 0) t₀ := by
    have h1 := h_first_cont t₀ ht₀
    have h2 : ContinuousWithinAt
        (fun t : ℝ =>
          ∫ τ in (0 : ℝ)..t, duhamelKernelClipped S F t τ)
        (Set.Ici 0) t₀ :=
      h_int_cont.continuousWithinAt
    exact h1.add h2
  apply h_clipped_cont.congr_of_eventuallyEq
  · rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ici (0 : ℝ), self_mem_nhdsWithin, ?_⟩
    intro t ht
    exact h_clip_eq t (Set.mem_Ici.mp ht)
  · exact h_clip_eq t₀ h_t₀_nn

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
