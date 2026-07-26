import DifferentialGeometry.Geometry.Exponential.ChartFlow.RescaledLift
import DifferentialGeometry.Geometry.Exponential.ChartFlow.UniformExistence
import DifferentialGeometry.Geometry.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Geodesic.MaximalRescaling

set_option linter.unusedSectionVars false

/-!
# Side-condition-free small-velocity geodesic rescaling

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete inner-product space `E`, this file produces the
**uniform small-velocity** form of the classical geodesic rescaling
identity

```
maximalGeodesic g p (t • v) 1 = maximalGeodesic g p v t   (t ∈ [0, 1])
```

with the *only* hypothesis being that the initial velocity `v` is small
(`‖v‖ < ρ` for an explicit `ρ > 0` depending on `g` and `p`).

The earlier `Geodesic/MaximalRescaling.lean` rescaling at time `1` carries
a chart-coordinate-agreement side condition (`h1_in_agreement`) that is
only known near `0`. Here we sidestep that side condition entirely by
routing both sides of the identity through the **same** chart-pushed flow
orbit `Φ` provided by `Exponential/UniformExistence.lean`.

## Strategy

Fix the uniform chart-pushed flow `(ρ, T, Φ)` of
`exists_uniform_existence_interval`, and pick the working scale
`t' := T / 2 ∈ (0, T)`, so the rescaled interval `Ioo (-T/t') (T/t')`
equals `Ioo (-2) 2 ⊇ [0, 1]`. For a small velocity `v` with
`‖v‖ < t' * ρ`, set `v_base := (1/t') • v`, so `‖v_base‖ < ρ` and
`t' • v_base = v`.

The rescaled manifold lift `chartFlowOrbitLiftRescaled Φ p · v_base` then
identifies, on `Ioo (-T/t') (T/t')`, the maximal geodesic with the orbit
projection (`chartFlowOrbitLiftRescaled_proj_eq_maximalGeodesic_on_Ioo`).
Because the orbit projection only depends on the orbit's *first*
component (`chartFlowOrbitLiftRescaled_proj`), which the time-rescaling
leaves untouched, both `maximalGeodesic g p (t • v) 1` (rescaling factor
`t * t'`) and `maximalGeodesic g p v t` (rescaling factor `t'`) reduce to
the **single** value `(extChartAt I p).symm (Φ ((x₀, v_base), t * t')).1`,
yielding the identity without any chart-coordinate-agreement input.

## Main results

* `foot_in_source_throughout` — there is `ρ > 0` such that for every
  `v` with `‖v‖ < ρ`, the geodesic arc `t ↦ maximalGeodesic g p v t`
  stays in `(chartAt H p).source` for all `t ∈ [0, 1]`.
* `maximalGeodesic_rescale_at_one_of_small` — the uniform small-velocity
  rescaling identity at time `1`.
-/

noncomputable section

open Set Function Filter Metric Bundle Manifold
open scoped Topology NNReal Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure

section UniformSmallRescaling

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Orbit-projection value of the rescaled geodesic.** For the uniform
chart-pushed flow data `Φ` and a base velocity `v` in the uniform ball,
the maximal geodesic at the rescaled velocity `t' • v` evaluated at any
`s ∈ Ioo (-T/t') (T/t')` equals the inverse extended chart of the
orbit's first component at time `t' * s`. -/
private theorem maximalGeodesic_rescaled_eq_orbit_proj
    (g : SmoothRiemannianMetric I M) (p : M) (v : E)
    {T t' : ℝ} (ht'_pos : 0 < t')
    {Φ : (E × E) × ℝ → E × E}
    (hΦ_init : Φ (((extChartAt I p p, v) : E × E), 0) =
      ((extChartAt I p p, v) : E × E))
    (hΦ_target : ∀ s ∈ Set.Icc (-T) T,
      Φ (((extChartAt I p p, v) : E × E), s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E))
    (hΦ_phase : ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
        (chartPhaseVF (I := I) g p
          (Φ (((extChartAt I p p, v) : E × E), s))) s)
    {s : ℝ} (hs : s ∈ Set.Ioo (-T / t') (T / t')) :
    maximalGeodesic (I := I) g p (t' • v) s =
      (extChartAt I p).symm
        (Φ (((extChartAt I p p, v) : E × E), t' * s)).1 := by
  have h_proj_eq :=
    chartFlowOrbitLiftRescaled_proj_eq_maximalGeodesic_on_Ioo (I := I)
      (g := g) (p := p) (v := v) (T := T) (t' := t') ht'_pos
      (Φ := Φ) hΦ_init hΦ_target hΦ_phase hs
  have hts_Ioo : t' * s ∈ Set.Ioo (-T) T :=
    mul_mem_Ioo_of_pos_of_lt ht'_pos hs
  have hΦ_target_ts := hΦ_target (t' * s) (Set.Ioo_subset_Icc_self hts_Ioo)
  have h_proj :=
    chartFlowOrbitLiftRescaled_proj (I := I) p v t' (Φ := Φ) s hΦ_target_ts
  rw [← h_proj_eq, h_proj]

/-- **Foot-in-source throughout `[0, 1]` for small velocity.** There
exists `ρ > 0` such that for every initial velocity `v` with `‖v‖ < ρ`
the entire geodesic arc `t ↦ maximalGeodesic g p v t`, `t ∈ [0, 1]`,
stays in the home chart's source `(chartAt H p).source`.

The radius `ρ = (T / 2) * ρ₀`, where `(ρ₀, T, Φ)` is the uniform
chart-pushed flow of `exists_uniform_existence_interval`. Writing
`v = t' • v_base` with `t' = T / 2 < T` and `v_base = (1/t') • v ∈
ball 0 ρ₀`, the geodesic on `[0, 1] ⊆ Ioo (-T/t') (T/t')` is the
projection of the rescaled manifold lift, which is confined to the
chart source. -/
theorem foot_in_source_throughout
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ {v : TangentSpace I p}, ‖(v : E)‖ < ρ →
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          maximalGeodesic (I := I) g p v t ∈ (chartAt H p).source := by
  classical
  obtain ⟨ρ₀, T, Φ, hρ₀_pos, hT_pos, hΦ_init, hΦ_target, hΦ_phase, _hF⟩ :=
    exists_uniform_existence_interval (I := I) (g := g) (p := p)
  set t' : ℝ := T / 2 with ht'_def
  have ht'_pos : 0 < t' := by rw [ht'_def]; linarith
  have ht'_lt_T : t' < T := by rw [ht'_def]; linarith
  refine ⟨t' * ρ₀, mul_pos ht'_pos hρ₀_pos, ?_⟩
  intro v hv t ht
  set w : E := (v : E) with hw_def
  have ht'_ne : t' ≠ 0 := ne_of_gt ht'_pos
  obtain ⟨vb, hvb_def⟩ : ∃ vb : E, vb = (1 / t') • w := ⟨_, rfl⟩
  have hvb_resc : t' • vb = (v : E) := by
    rw [hvb_def, smul_smul, mul_one_div, div_self ht'_ne, one_smul, hw_def]
  have hw_norm : ‖w‖ < t' * ρ₀ := by rw [hw_def]; exact hv
  have hvb_ball : vb ∈ Metric.ball (0 : E) ρ₀ := by
    rw [Metric.mem_ball, dist_zero_right, hvb_def, norm_smul]
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / t')]
    rw [one_div, ← div_eq_inv_mul]
    rw [div_lt_iff₀ ht'_pos]
    linarith [hw_norm, mul_comm t' ρ₀]
  have hT_div : T / t' = 2 := by
    rw [ht'_def]; field_simp
  have ht_Ioo : t ∈ Set.Ioo (-T / t') (T / t') := by
    rw [neg_div, hT_div]
    obtain ⟨ht0, ht1⟩ := ht
    exact ⟨by linarith, by linarith⟩
  have hmem_v : (v : E) = t' • vb := hvb_resc.symm
  have h_eq :
      maximalGeodesic (I := I) g p v t =
        (extChartAt I p).symm
          (Φ (((extChartAt I p p, vb) : E × E), t' * t)).1 := by
    have h := maximalGeodesic_rescaled_eq_orbit_proj (I := I) (g := g) (p := p)
      (v := vb) (T := T) (t' := t') ht'_pos
      (hΦ_init vb hvb_ball) (hΦ_target vb hvb_ball) (hΦ_phase vb hvb_ball)
      (s := t) ht_Ioo
    rw [show (t' • vb : TangentSpace I p) = v from hvb_resc] at h
    exact h
  rw [h_eq]
  have hts_Icc : t' * t ∈ Set.Icc (-T) T := by
    obtain ⟨ht0, ht1⟩ := ht
    refine ⟨?_, ?_⟩
    · nlinarith [ht'_pos.le, hT_pos.le]
    · nlinarith [ht'_lt_T.le, ht'_pos.le]
  have hΦ_target_tt := hΦ_target vb hvb_ball (t' * t) hts_Icc
  have hsrc :=
    chartFlowOrbitLiftRescaled_proj_mem_chartAt_source (I := I) p vb t' t
      hΦ_target_tt
  rw [chartFlowOrbitLiftRescaled_proj (I := I) p vb t' t hΦ_target_tt] at hsrc
  exact hsrc

/-- **Continuity of the maximal geodesic arc on `[0, 1]` for small velocity.**
There is `ρ > 0` such that for every initial velocity `v₀` with `‖v₀‖ < ρ`,
the geodesic arc `t ↦ maximalGeodesic g p v₀ t` is continuous on `[0, 1]`.

For small `v₀` the arc stays in the home chart and equals the projection of the
uniform chart-pushed flow orbit `t ↦ (extChartAt I p).symm (Φ((x₀, v_base),
t'·t)).1`, which is continuous in `t`: the orbit is differentiable in time
(`hΦ_phase`), hence continuous, its first component lands in
`interior (extChartAt I p).target` (`hΦ_target`), and `(extChartAt I p).symm`
is continuous there.  (No analogue holds for large `v₀`, whose geodesic leaves
the chart and for which `maximalGeodesic` reverts to its junk value.) -/
theorem maximalGeodesic_continuousOn_Icc_of_norm_lt
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ {v₀ : TangentSpace I p}, ‖(v₀ : E)‖ < ρ →
        ContinuousOn (maximalGeodesic (I := I) g p v₀) (Set.Icc (0 : ℝ) 1) := by
  classical
  obtain ⟨ρ₀, T, Φ, hρ₀_pos, hT_pos, hΦ_init, hΦ_target, hΦ_phase, _hF⟩ :=
    exists_uniform_existence_interval (I := I) (g := g) (p := p)
  set t' : ℝ := T / 2 with ht'_def
  have ht'_pos : 0 < t' := by rw [ht'_def]; linarith
  have ht'_lt_T : t' < T := by rw [ht'_def]; linarith
  refine ⟨t' * ρ₀, mul_pos ht'_pos hρ₀_pos, ?_⟩
  intro v₀ hv₀
  set w : E := (v₀ : E) with hw_def
  have ht'_ne : t' ≠ 0 := ne_of_gt ht'_pos
  set vb : E := (1 / t') • w with hvb_def
  have hvb_resc : t' • vb = (v₀ : E) := by
    rw [hvb_def, smul_smul, mul_one_div, div_self ht'_ne, one_smul, hw_def]
  have hw_norm : ‖w‖ < t' * ρ₀ := by rw [hw_def]; exact hv₀
  have hvb_ball : vb ∈ Metric.ball (0 : E) ρ₀ := by
    rw [Metric.mem_ball, dist_zero_right, hvb_def, norm_smul]
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / t')]
    rw [one_div, ← div_eq_inv_mul, div_lt_iff₀ ht'_pos]
    linarith [hw_norm, mul_comm t' ρ₀]
  have hT_div : T / t' = 2 := by rw [ht'_def]; field_simp
  -- The maximal geodesic equals the chart-pushed orbit projection on `[0, 1]`.
  have h_eqOn : Set.EqOn (maximalGeodesic (I := I) g p v₀)
      (fun t => (extChartAt I p).symm
        (Φ (((extChartAt I p p, vb) : E × E), t' * t)).1)
      (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    have ht_Ioo : t ∈ Set.Ioo (-T / t') (T / t') := by
      rw [neg_div, hT_div]
      obtain ⟨ht0, ht1⟩ := ht
      exact ⟨by linarith, by linarith⟩
    have h := maximalGeodesic_rescaled_eq_orbit_proj (I := I) (g := g) (p := p)
      (v := vb) (T := T) (t' := t') ht'_pos
      (hΦ_init vb hvb_ball) (hΦ_target vb hvb_ball) (hΦ_phase vb hvb_ball)
      (s := t) ht_Ioo
    rw [show (t' • vb : TangentSpace I p) = v₀ from hvb_resc] at h
    exact h
  -- Continuity of the orbit-projection representative on `[0, 1]`.
  have hφ_contOn : ContinuousOn
      (fun s : ℝ => Φ (((extChartAt I p p, vb) : E × E), s)) (Set.Ioo (-T) T) := by
    intro s hs
    exact ((hΦ_phase vb hvb_ball s hs).differentiableAt).continuousAt.continuousWithinAt
  have hmap : Set.MapsTo (fun t : ℝ => t' * t) (Set.Icc (0 : ℝ) 1) (Set.Ioo (-T) T) := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    have h_nonneg : 0 ≤ t' * t := mul_nonneg ht'_pos.le ht0
    have h_le : t' * t ≤ t' := by
      calc t' * t ≤ t' * 1 := mul_le_mul_of_nonneg_left ht1 ht'_pos.le
        _ = t' := mul_one t'
    exact ⟨by linarith, by linarith [ht'_lt_T]⟩
  have h_orbit_cont : ContinuousOn
      (fun t : ℝ => Φ (((extChartAt I p p, vb) : E × E), t' * t)) (Set.Icc (0 : ℝ) 1) :=
    hφ_contOn.comp ((continuous_const.mul continuous_id).continuousOn) hmap
  have h_fst : ContinuousOn
      (fun t : ℝ => (Φ (((extChartAt I p p, vb) : E × E), t' * t)).1)
      (Set.Icc (0 : ℝ) 1) :=
    continuous_fst.comp_continuousOn h_orbit_cont
  have hmaps_target : Set.MapsTo
      (fun t : ℝ => (Φ (((extChartAt I p p, vb) : E × E), t' * t)).1)
      (Set.Icc (0 : ℝ) 1) (extChartAt I p).target := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    have h_nonneg : 0 ≤ t' * t := mul_nonneg ht'_pos.le ht0
    have h_le : t' * t ≤ t' := by
      calc t' * t ≤ t' * 1 := mul_le_mul_of_nonneg_left ht1 ht'_pos.le
        _ = t' := mul_one t'
    have hts : t' * t ∈ Set.Icc (-T) T := ⟨by linarith, by linarith [ht'_lt_T.le]⟩
    exact interior_subset (hΦ_target vb hvb_ball (t' * t) hts).1
  have hF_cont : ContinuousOn
      (fun t => (extChartAt I p).symm
        (Φ (((extChartAt I p p, vb) : E × E), t' * t)).1)
      (Set.Icc (0 : ℝ) 1) :=
    (continuousOn_extChartAt_symm (I := I) p).comp h_fst hmaps_target
  exact hF_cont.congr h_eqOn

/-- **Uniform small-velocity geodesic rescaling at time `1`.** There is
an explicit `ρ > 0` (namely `(T / 2) * ρ₀` for the uniform flow radii
`(ρ₀, T)` of `exists_uniform_existence_interval`) such that for every
initial velocity `v` with `‖v‖ < ρ` and every `t ∈ [0, 1]`,

```
maximalGeodesic g p (t • v) 1 = maximalGeodesic g p v t.
```

Unlike `Geodesic.maximalGeodesic_rescale_at_one`, this carries **no**
chart-coordinate-agreement side condition: both sides are reduced to the
same chart-pushed flow orbit value `(extChartAt I p).symm
(Φ ((x₀, v_base), t * t')).1`. -/
theorem maximalGeodesic_rescale_at_one_of_small
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ {v : TangentSpace I p}, ‖(v : E)‖ < ρ →
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          maximalGeodesic (I := I) g p (t • v) 1 =
            maximalGeodesic (I := I) g p v t := by
  classical
  obtain ⟨ρ₀, T, Φ, hρ₀_pos, hT_pos, hΦ_init, hΦ_target, hΦ_phase, _hF⟩ :=
    exists_uniform_existence_interval (I := I) (g := g) (p := p)
  set t' : ℝ := T / 2 with ht'_def
  have ht'_pos : 0 < t' := by rw [ht'_def]; linarith
  have ht'_lt_T : t' < T := by rw [ht'_def]; linarith
  refine ⟨t' * ρ₀, mul_pos ht'_pos hρ₀_pos, ?_⟩
  intro v hv t ht
  obtain ⟨ht0, ht1⟩ := ht
  set w : E := (v : E) with hw_def
  have ht'_ne : t' ≠ 0 := ne_of_gt ht'_pos
  obtain ⟨vb, hvb_def⟩ : ∃ vb : E, vb = (1 / t') • w := ⟨_, rfl⟩
  have hvb_resc : t' • vb = (v : E) := by
    rw [hvb_def, smul_smul, mul_one_div, div_self ht'_ne, one_smul, hw_def]
  have hw_norm : ‖w‖ < t' * ρ₀ := by rw [hw_def]; exact hv
  have hvb_ball : vb ∈ Metric.ball (0 : E) ρ₀ := by
    rw [Metric.mem_ball, dist_zero_right, hvb_def, norm_smul]
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / t')]
    rw [one_div, ← div_eq_inv_mul]
    rw [div_lt_iff₀ ht'_pos]
    linarith [hw_norm, mul_comm t' ρ₀]
  have hT_div : T / t' = 2 := by rw [ht'_def]; field_simp
  rcases eq_or_lt_of_le ht0 with ht_zero | ht_pos
  · subst ht_zero
    rw [zero_smul, maximalGeodesic_zero (I := I) g p v]
    have h1 : (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p
        (0 : TangentSpace I p) :=
      maximalGeodesicWitness_zero_all_times (I := I) g p 1
    rw [maximalGeodesic_of_mem (I := I) (g := g) (p := p)
      (v := (0 : TangentSpace I p)) h1]
    obtain ⟨J, hJ_open, hJ_conn, h0J, h1J, hγ⟩ :=
      maximalGeodesicChosenCurve_spec (I := I) g p (0 : TangentSpace I p) h1
    exact maximalGeodesicWitness_zero_curve_eq_p (I := I)
      hJ_open hJ_conn h0J hγ 1 h1J
  · have ht_Ioo : t ∈ Set.Ioo (-T / t') (T / t') := by
      rw [neg_div, hT_div]; exact ⟨by linarith, by linarith⟩
    have h_rhs :
        maximalGeodesic (I := I) g p v t =
          (extChartAt I p).symm
            (Φ (((extChartAt I p p, vb) : E × E), t' * t)).1 := by
      have h := maximalGeodesic_rescaled_eq_orbit_proj (I := I) (g := g) (p := p)
        (v := vb) (T := T) (t' := t') ht'_pos
        (hΦ_init vb hvb_ball) (hΦ_target vb hvb_ball) (hΦ_phase vb hvb_ball)
        (s := t) ht_Ioo
      rw [show (t' • vb : TangentSpace I p) = v from hvb_resc] at h
      exact h
    set t'' : ℝ := t * t' with ht''_def
    have ht''_pos : 0 < t'' := by rw [ht''_def]; exact mul_pos ht_pos ht'_pos
    have ht''_lt_T : t'' < T := by
      rw [ht''_def]; nlinarith [ht'_pos.le, ht'_lt_T]
    have htvb : (t'' • vb : E) = t • w := by
      rw [ht''_def, ← smul_smul, hvb_resc, hw_def]
    have h_tv : (t • v : TangentSpace I p) = t'' • vb := htvb.symm
    have hone_Ioo : (1 : ℝ) ∈ Set.Ioo (-T / t'') (T / t'') := by
      have hlt : 1 < T / t'' := (one_lt_div ht''_pos).mpr ht''_lt_T
      have hneg : -T / t'' < 0 := by
        rw [neg_div]; exact neg_lt_zero.mpr (div_pos hT_pos ht''_pos)
      exact ⟨by linarith, hlt⟩
    have h_lhs :
        maximalGeodesic (I := I) g p (t • v) 1 =
          (extChartAt I p).symm
            (Φ (((extChartAt I p p, vb) : E × E), t'' * 1)).1 := by
      have h := maximalGeodesic_rescaled_eq_orbit_proj (I := I) (g := g) (p := p)
        (v := vb) (T := T) (t' := t'') ht''_pos
        (hΦ_init vb hvb_ball) (hΦ_target vb hvb_ball) (hΦ_phase vb hvb_ball)
        (s := (1 : ℝ)) hone_Ioo
      rw [show (t'' • vb : TangentSpace I p) = t • v from h_tv.symm] at h
      exact h
    rw [h_lhs, h_rhs]
    congr 2
    rw [ht''_def, mul_one, mul_comm]

end UniformSmallRescaling

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
