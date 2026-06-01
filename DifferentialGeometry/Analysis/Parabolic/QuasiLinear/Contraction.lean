import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.DuhamelMap

/-!
# Nonlinear Duhamel map and the contraction estimate

For a real Banach space `X`, a `BoundedC0Semigroup S`, an initial datum
`u₀ : X`, and a globally Lipschitz lower-order nonlinearity `N : X → X`,
the **nonlinear Duhamel map** sends a path `u : ℝ → X` to

  `nlDuhamel S u₀ N u t = S t u₀ + ∫₀ᵗ S (t - τ) (N (u τ)) dτ`,

i.e. the linear `duhamel` map fed with the forcing term `F = N ∘ u`.

The central result is the **contraction estimate**: for two paths
`u, v` whose pointwise distance on `[0, t]` is bounded by `C`, the
nonlinear Duhamel images satisfy

  `‖nlDuhamel S u₀ N u t - nlDuhamel S u₀ N v t‖ ≤ L * t * C`,

where `L` is the Lipschitz constant of `N`. For small `t` the factor
`L * t < 1`, which is exactly what turns the nonlinear Duhamel map into a
contraction and yields a mild solution via the Banach fixed point
theorem.

## Main definitions

* `nlDuhamel S u₀ N u t` — the nonlinear Duhamel map.

## Main results

* `nlDuhamel_zero` — `nlDuhamel S u₀ N u 0 = u₀`.
* `nlDuhamel_continuousOn` — `nlDuhamel S u₀ N u` is continuous on
  `[0, ∞)` for continuous `u` and Lipschitz `N`.
* `nlDuhamel_dist_le` — the contraction estimate
  `‖nlDuhamel S u₀ N u t - nlDuhamel S u₀ N v t‖ ≤ L * t * C`.
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

/-- The nonlinear Duhamel map: the linear Duhamel mild solution `duhamel`
with the forcing term given by the lower-order nonlinearity `N` evaluated
along the path `u`. Explicitly,
`nlDuhamel S u₀ N u t = S t u₀ + ∫₀ᵗ S (t - τ) (N (u τ)) dτ`. -/
noncomputable def nlDuhamel (S : BoundedC0Semigroup X) (u₀ : X)
    (N : X → X) (u : ℝ → X) (t : ℝ) : X :=
  duhamel S u₀ (fun τ => N (u τ)) t

/-- At `t = 0` the nonlinear Duhamel map recovers the initial datum:
`nlDuhamel S u₀ N u 0 = u₀`. -/
theorem nlDuhamel_zero (S : BoundedC0Semigroup X) (u₀ : X) (N : X → X)
    (u : ℝ → X) : nlDuhamel S u₀ N u 0 = u₀ := by
  unfold nlDuhamel
  exact duhamel_zero S u₀ (fun τ => N (u τ))

/-- The nonlinear Duhamel map `nlDuhamel S u₀ N u` is continuous on
`[0, ∞)` whenever the path `u` is continuous and the nonlinearity `N` is
Lipschitz.

A Lipschitz map is continuous, so the forcing term `τ ↦ N (u τ)` is the
composition of two continuous maps; continuity of the Duhamel map then
follows from `duhamel_continuousOn`. -/
theorem nlDuhamel_continuousOn (S : BoundedC0Semigroup X) (u₀ : X)
    {N : X → X} {L : ℝ≥0} (hN : LipschitzWith L N) {u : ℝ → X}
    (hu : Continuous u) :
    ContinuousOn (nlDuhamel S u₀ N u) (Set.Ici 0) := by
  unfold nlDuhamel
  exact duhamel_continuousOn S u₀ (hN.continuous.comp hu)

/-- Continuity on `uIcc 0 t` of the map `τ ↦ S (t - τ) (w τ)` for a
continuous `w`. This is the building block for the interval-integrability
of the integrands appearing in the contraction estimate.

The map `τ ↦ (max 0 (t - τ), w τ)` is continuous into the domain
`[0, ∞) × X` of joint continuity of the semigroup action, and on
`uIcc 0 t` (with `t ≥ 0`) the clipped time `max 0 (t - τ)` equals
`t - τ`. -/
private lemma continuousOn_semigroup_apply (S : BoundedC0Semigroup X)
    {w : ℝ → X} (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousOn (fun τ : ℝ => S (t - τ) (w τ)) (Set.uIcc 0 t) := by
  have h_inner : Continuous
      (fun τ : ℝ => (max 0 (t - τ), w τ)) := by
    refine Continuous.prodMk ?_ hw
    exact continuous_const.max (continuous_const.sub continuous_id)
  have h_maps : ∀ τ : ℝ,
      (max 0 (t - τ), w τ) ∈ Set.Ici (0 : ℝ) ×ˢ Set.univ := by
    intro τ
    exact ⟨Set.mem_Ici.mpr (le_max_left _ _), Set.mem_univ _⟩
  have h_clip_cont : Continuous
      (fun τ : ℝ => S (max 0 (t - τ)) (w τ)) :=
    (S.continuousOn_uncurry).comp_continuous h_inner h_maps
  refine (h_clip_cont.continuousOn).congr ?_
  intro τ hτ
  rw [Set.uIcc_of_le ht] at hτ
  have h_nn : 0 ≤ t - τ := sub_nonneg.mpr hτ.2
  change S (t - τ) (w τ) = S (max 0 (t - τ)) (w τ)
  rw [max_eq_right h_nn]

/-- Interval-integrability on `[0, t]` of the map `τ ↦ S (t - τ) (w τ)`
for a continuous `w` and `t ≥ 0`, obtained from its continuity on
`uIcc 0 t`. -/
private lemma intervalIntegrable_semigroup_apply (S : BoundedC0Semigroup X)
    {w : ℝ → X} (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun τ => S (t - τ) (w τ))
      MeasureTheory.volume 0 t :=
  (continuousOn_semigroup_apply S hw ht).intervalIntegrable

/-- The contraction estimate for the nonlinear Duhamel map.

Let `N` be `L`-Lipschitz and let `u, v` be continuous paths whose
pointwise distance on `[0, t]` is bounded by `C`. Then the difference of
the nonlinear Duhamel images at time `t ≥ 0` is bounded by `L * t * C`:

  `‖nlDuhamel S u₀ N u t - nlDuhamel S u₀ N v t‖ ≤ L * t * C`.

The homogeneous terms `S t u₀` cancel; the remaining difference of
interval integrals is combined into a single integral whose integrand,
`S (t - τ) (N (u τ) - N (v τ))`, is bounded in norm by
`‖N (u τ) - N (v τ)‖ ≤ L * ‖u τ - v τ‖ ≤ L * C` using the contraction
bound of `S` and the Lipschitz bound of `N`. Integrating the constant
`L * C` over `[0, t]` gives `L * C * t = L * t * C`. -/
theorem nlDuhamel_dist_le (S : BoundedC0Semigroup X) (u₀ : X)
    {N : X → X} {L : ℝ≥0} (hN : LipschitzWith L N) {u v : ℝ → X}
    (hu : Continuous u) (hv : Continuous v) {t : ℝ} (ht : 0 ≤ t)
    {C : ℝ} (hC : ∀ τ ∈ Set.Icc (0 : ℝ) t, ‖u τ - v τ‖ ≤ C) :
    ‖nlDuhamel S u₀ N u t - nlDuhamel S u₀ N v t‖ ≤ (L : ℝ) * t * C := by
  have hNu : Continuous (fun τ => N (u τ)) := hN.continuous.comp hu
  have hNv : Continuous (fun τ => N (v τ)) := hN.continuous.comp hv
  have h_diff_eq :
      nlDuhamel S u₀ N u t - nlDuhamel S u₀ N v t =
        (∫ τ in (0 : ℝ)..t, S (t - τ) (N (u τ))) -
          ∫ τ in (0 : ℝ)..t, S (t - τ) (N (v τ)) := by
    unfold nlDuhamel duhamel
    abel
  have hI_u : IntervalIntegrable (fun τ => S (t - τ) (N (u τ)))
      MeasureTheory.volume 0 t :=
    duhamel_integrable S hNu ht
  have hI_v : IntervalIntegrable (fun τ => S (t - τ) (N (v τ)))
      MeasureTheory.volume 0 t :=
    duhamel_integrable S hNv ht
  have h_one_integral :
      (∫ τ in (0 : ℝ)..t, S (t - τ) (N (u τ))) -
          (∫ τ in (0 : ℝ)..t, S (t - τ) (N (v τ))) =
        ∫ τ in (0 : ℝ)..t,
          (S (t - τ) (N (u τ)) - S (t - τ) (N (v τ))) :=
    (intervalIntegral.integral_sub hI_u hI_v).symm
  have h_integrand_eq :
      (∫ τ in (0 : ℝ)..t,
          (S (t - τ) (N (u τ)) - S (t - τ) (N (v τ)))) =
        ∫ τ in (0 : ℝ)..t, S (t - τ) (N (u τ) - N (v τ)) := by
    refine intervalIntegral.integral_congr ?_
    intro τ _
    change S (t - τ) (N (u τ)) - S (t - τ) (N (v τ)) =
      S (t - τ) (N (u τ) - N (v τ))
    rw [(S (t - τ)).map_sub]
  have hw_cont : Continuous (fun τ => N (u τ) - N (v τ)) :=
    hNu.sub hNv
  have h_norm_le :
      ‖∫ τ in (0 : ℝ)..t, S (t - τ) (N (u τ) - N (v τ))‖ ≤
        ∫ τ in (0 : ℝ)..t, ‖S (t - τ) (N (u τ) - N (v τ))‖ :=
    intervalIntegral.norm_integral_le_integral_norm ht
  have h_cont_integrand :
      ContinuousOn (fun τ : ℝ => S (t - τ) (N (u τ) - N (v τ)))
        (Set.uIcc 0 t) :=
    continuousOn_semigroup_apply S hw_cont ht
  have hI_norm : IntervalIntegrable
      (fun τ => ‖S (t - τ) (N (u τ) - N (v τ))‖)
      MeasureTheory.volume 0 t :=
    h_cont_integrand.norm.intervalIntegrable
  have hI_const : IntervalIntegrable (fun _ : ℝ => (L : ℝ) * C)
      MeasureTheory.volume 0 t :=
    intervalIntegrable_const
  have h_pointwise : ∀ τ ∈ Set.Icc (0 : ℝ) t,
      ‖S (t - τ) (N (u τ) - N (v τ))‖ ≤ (L : ℝ) * C := by
    intro τ hτ
    obtain ⟨hτ0, hτt⟩ := hτ
    have h_t_sub_nn : 0 ≤ t - τ := sub_nonneg.mpr hτt
    have h_sg : ‖S (t - τ) (N (u τ) - N (v τ))‖ ≤
        ‖N (u τ) - N (v τ)‖ :=
      S.norm_apply_le h_t_sub_nn (N (u τ) - N (v τ))
    have h_lip : ‖N (u τ) - N (v τ)‖ ≤ (L : ℝ) * ‖u τ - v τ‖ := by
      have h_dist : dist (N (u τ)) (N (v τ)) ≤
          (L : ℝ) * dist (u τ) (v τ) := hN.dist_le_mul (u τ) (v τ)
      rwa [dist_eq_norm, dist_eq_norm] at h_dist
    have h_C : ‖u τ - v τ‖ ≤ C := hC τ ⟨hτ0, hτt⟩
    have hL_nn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
    calc ‖S (t - τ) (N (u τ) - N (v τ))‖
        ≤ ‖N (u τ) - N (v τ)‖ := h_sg
      _ ≤ (L : ℝ) * ‖u τ - v τ‖ := h_lip
      _ ≤ (L : ℝ) * C := by
          exact mul_le_mul_of_nonneg_left h_C hL_nn
  have h_int_mono :
      (∫ τ in (0 : ℝ)..t, ‖S (t - τ) (N (u τ) - N (v τ))‖) ≤
        ∫ _ in (0 : ℝ)..t, (L : ℝ) * C :=
    intervalIntegral.integral_mono_on ht hI_norm hI_const h_pointwise
  have h_const_eval :
      (∫ _ in (0 : ℝ)..t, (L : ℝ) * C) = (L : ℝ) * C * t := by
    rw [intervalIntegral.integral_const]
    rw [sub_zero, smul_eq_mul, mul_comm]
  calc ‖nlDuhamel S u₀ N u t - nlDuhamel S u₀ N v t‖
      = ‖∫ τ in (0 : ℝ)..t, S (t - τ) (N (u τ) - N (v τ))‖ := by
        rw [h_diff_eq, h_one_integral, h_integrand_eq]
    _ ≤ ∫ τ in (0 : ℝ)..t, ‖S (t - τ) (N (u τ) - N (v τ))‖ :=
        h_norm_le
    _ ≤ ∫ _ in (0 : ℝ)..t, (L : ℝ) * C := h_int_mono
    _ = (L : ℝ) * C * t := h_const_eval
    _ = (L : ℝ) * t * C := by ring

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
