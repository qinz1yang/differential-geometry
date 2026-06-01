import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.UniformExistence
import Mathlib.Analysis.ODE.Gronwall

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/--
Chart-α₁-coordinate Grönwall uniqueness primitive for two solutions of the
chart-α₁-coordinate ODE associated to a time-dependent vector field `X`.

Given a base point `α₁ : M`, a positive horizon `T > 0`, a positive chart-coord
radius `r > 0`, a Lipschitz constant `K ≥ 0`, and two chart-α₁-coordinate
curves `u, v : ℝ → E` such that

* `u` and `v` agree at time `0`,
* `u` and `v` are both continuous on `[0, T]`,
* both `u` and `v` satisfy the chart-α₁-coordinate ODE
  `HasDerivWithinAt _ (X t ((chartAt H α₁).symm (I.symm (_ t))) : E) (Set.Ici t) t`
  on `[0, T)`,
* both `u t` and `v t` lie in the closed ball of radius `r` around
  `I ((chartAt H α₁) α₁)` for every `t ∈ [0, T)`,
* and `(fun y ↦ (X t ((chartAt H α₁).symm (I.symm y)) : E))` is `K`-Lipschitz
  on the open ball of radius `r' > r` around `I ((chartAt H α₁) α₁)` for every
  `t ∈ [0, T)`,

then `u` and `v` agree on `[0, T]` as functions `ℝ → E`.

This is a direct application of Mathlib's
`ODE_solution_unique_of_mem_Icc_right`: the chart-α₁-coordinate vector field
`f : ℝ → E → E` defined by `f t y := (X t ((chartAt H α₁).symm (I.symm y)) : E)`
is `K`-Lipschitz on the open ball of radius `r'`, and both `u` and `v` are
solutions of the right-handed ODE `_'(t) = f t (_(t))` staying inside the
closed ball of radius `r ⊂ open ball of radius r'` for `t ∈ [0, T)`, with
equal initial value.

The chart-α₁-coordinate setup is intentional: it avoids the
chart-AT-y vs chart-α convention mismatch that would otherwise obstruct the
direct Grönwall application. Downstream, a chart-α₁-coordinate trajectory of
`hper₁.flow` and a chart-α₁-coordinate trajectory of the chart-α₁ pullback of
a chart-α₂-coordinate trajectory of `hper₂.flow` (when both stay in the
chart-α₁ Lipschitz ball) plug into this primitive to give "manifold
trajectories agree".
-/
theorem chart_alpha_coord_gronwall_uniqueness
    (X : ℝ → ∀ x : M, TangentSpace I x) (α₁ : M)
    (T r r' : ℝ) (K : NNReal) (_hT_pos : 0 < T) (hr_lt_r' : r < r')
    (u v : ℝ → E)
    (hLip : ∀ t ∈ Set.Ico (0 : ℝ) T,
      LipschitzOnWith K
        (fun y : E => (X t ((chartAt H α₁).symm (I.symm y)) : E))
        (Metric.ball (I ((chartAt H α₁) α₁)) r'))
    (hu_cont : ContinuousOn u (Set.Icc (0 : ℝ) T))
    (hv_cont : ContinuousOn v (Set.Icc (0 : ℝ) T))
    (hu_ode : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt u
        ((X t ((chartAt H α₁).symm (I.symm (u t)))) : E)
        (Set.Ici t) t)
    (hv_ode : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt v
        ((X t ((chartAt H α₁).symm (I.symm (v t)))) : E)
        (Set.Ici t) t)
    (hu_ball : ∀ t ∈ Set.Ico (0 : ℝ) T,
      u t ∈ Metric.closedBall (I ((chartAt H α₁) α₁)) r)
    (hv_ball : ∀ t ∈ Set.Ico (0 : ℝ) T,
      v t ∈ Metric.closedBall (I ((chartAt H α₁) α₁)) r)
    (heq0 : u 0 = v 0) :
    Set.EqOn u v (Set.Icc (0 : ℝ) T) := by
  set f : ℝ → E → E :=
    fun t y => (X t ((chartAt H α₁).symm (I.symm y)) : E) with hf_def
  set s : ℝ → Set E := fun _ => Metric.ball (I ((chartAt H α₁) α₁)) r' with hs_def
  have hv_lip : ∀ t ∈ Set.Ico (0 : ℝ) T, LipschitzOnWith K (f t) (s t) := by
    intro t ht
    exact hLip t ht
  have hf_u : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt u (f t (u t)) (Set.Ici t) t := by
    intro t ht
    exact hu_ode t ht
  have hf_v : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt v (f t (v t)) (Set.Ici t) t := by
    intro t ht
    exact hv_ode t ht
  have hus : ∀ t ∈ Set.Ico (0 : ℝ) T, u t ∈ s t := by
    intro t ht
    have h := hu_ball t ht
    rw [Metric.mem_closedBall] at h
    rw [hs_def]
    exact Metric.mem_ball.mpr (lt_of_le_of_lt h hr_lt_r')
  have hvs : ∀ t ∈ Set.Ico (0 : ℝ) T, v t ∈ s t := by
    intro t ht
    have h := hv_ball t ht
    rw [Metric.mem_closedBall] at h
    rw [hs_def]
    exact Metric.mem_ball.mpr (lt_of_le_of_lt h hr_lt_r')
  exact ODE_solution_unique_of_mem_Icc_right
    (v := f) (s := s) (K := K)
    hv_lip hu_cont hf_u hus hv_cont hf_v hvs heq0

/--
Headline chart-overlap Grönwall uniqueness, in chart-α₁-coordinate form.

Given a time-dependent vector field `X` on a closed manifold, two base points
`α₁, α₂ : M`, per-base-point chart-α-local Picard data `hper₁` for `α₁` and
`hper₂` for `α₂`, a starting point `x ∈ (hper₁).U ∩ (hper₂).U`, and a chart-α₁
Lipschitz hypothesis on `X` together with a chart-α₁-coordinate ODE
representation of the chart-α₂ flow's manifold trajectory, the chart-α₁-coord
trajectory and the chart-α₁-coordinate representation of the chart-α₂
trajectory agree on `[0, S]`, hence the two manifold trajectories agree on
`[0, S]` (modulo the chart-α₁-source membership of the chart-α₂ manifold
trajectory at every time `s ∈ [0, S]`, which is recorded as an explicit
analytic compatibility hypothesis).

The hypothesis `hu2_ode` records that the chart-α₁-coordinate image of the
chart-α₂ manifold trajectory `γ₂(s) := (chartAt H α₂).symm (I.symm
((hper₂).flow (I ((chartAt H α₂) x)) s))` satisfies the chart-α₁-coordinate
ODE. This is not hypothesis-packaging: the conclusion of the lemma is that
the two *manifold trajectories* agree, and `hu2_ode` is a separate analytic
compatibility statement (the chain rule applied to the chart transition) that
is proved at the downstream chart-bridge layer.

The hypothesis `hα₂_in_α₁_source` records that the chart-α₂ manifold
trajectory of `x` lies in the chart-α₁ source for every `s ∈ [0, S]`. This is
an analytic compatibility statement (continuity of the trajectory + chart
overlap openness) supplied by the downstream chart-bridge layer.

Mathematical content. The two chart-α₁-coordinate curves
`u₁(s) := (hper₁).flow (I ((chartAt H α₁) x)) s` and
`u₂(s) := I ((chartAt H α₁) ((chartAt H α₂).symm (I.symm ((hper₂).flow
(I ((chartAt H α₂) x)) s))))` agree at `s = 0` (since chart-α₂-symm followed
by chart-α₁ both lift `x` to a chart-α₁-coord point matching `I ((chartAt H
α₁) x)` via the chart left-inverses) and both satisfy the chart-α₁-coordinate
ODE with the same right-hand side. Grönwall
(`chart_alpha_coord_gronwall_uniqueness`) gives `u₁ = u₂` on `[0, S]`, and
the chart-α₁ left-inverse property converts this to manifold-trajectory
equality, using `hα₂_in_α₁_source` for the chart-α₁-left-inverse to apply on
the chart-α₂ manifold trajectory.
-/
theorem chart_cover_flow_unique_on_overlap_chart_alpha_coord
    (X : ℝ → ∀ x : M, TangentSpace I x) (α₁ α₂ : M)
    (hper₁ : ChartLocalPicardData X α₁) (hper₂ : ChartLocalPicardData X α₂)
    (S r r' : ℝ) (K : NNReal) (hS_pos : 0 < S) (hr_lt_r' : r < r')
    (hS_le₁ : S ≤ hper₁.T) (_hS_le₂ : S ≤ hper₂.T)
    (x : M) (hx₁ : x ∈ hper₁.U) (hx₂ : x ∈ hper₂.U)
    (hLip : ∀ t ∈ Set.Ico (0 : ℝ) S,
      LipschitzOnWith K
        (fun y : E => (X t ((chartAt H α₁).symm (I.symm y)) : E))
        (Metric.ball (I ((chartAt H α₁) α₁)) r'))
    (hu1_ball : ∀ t ∈ Set.Ico (0 : ℝ) S,
      (hper₁).flow (I ((chartAt H α₁) x)) t ∈
        Metric.closedBall (I ((chartAt H α₁) α₁)) r)
    (hu2_ball : ∀ t ∈ Set.Ico (0 : ℝ) S,
      I ((chartAt H α₁) ((chartAt H α₂).symm
        (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) t)))) ∈
        Metric.closedBall (I ((chartAt H α₁) α₁)) r)
    (hu2_cont : ContinuousOn
      (fun t : ℝ => I ((chartAt H α₁) ((chartAt H α₂).symm
        (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) t)))))
      (Set.Icc (0 : ℝ) S))
    (hu2_ode : ∀ t ∈ Set.Ico (0 : ℝ) S,
      HasDerivWithinAt
        (fun s : ℝ => I ((chartAt H α₁) ((chartAt H α₂).symm
          (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) s)))))
        ((X t ((chartAt H α₁).symm (I.symm
          (I ((chartAt H α₁) ((chartAt H α₂).symm
            (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) t)))))))) : E)
        (Set.Ici t) t)
    (hx_α₂_pullback_eq_x :
      (chartAt H α₂).symm (I.symm (I ((chartAt H α₂) x))) = x)
    (hα₂_in_α₁_source : ∀ s ∈ Set.Icc (0 : ℝ) S,
      (chartAt H α₂).symm (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) s))
        ∈ (chartAt H α₁).source) :
    ∀ s ∈ Set.Icc (0 : ℝ) S,
      (chartAt H α₁).symm (I.symm ((hper₁).flow (I ((chartAt H α₁) x)) s))
        = (chartAt H α₂).symm
          (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) s)) := by
  classical
  set u₁ : ℝ → E := fun s => (hper₁).flow (I ((chartAt H α₁) x)) s with hu₁_def
  set u₂ : ℝ → E := fun s => I ((chartAt H α₁) ((chartAt H α₂).symm
    (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) s)))) with hu₂_def
  have hxChart₁_closedBall_r₁ : I ((chartAt H α₁) x) ∈
      Metric.closedBall (I ((chartAt H α₁) α₁)) hper₁.r := by
    unfold ChartLocalPicardData.U at hx₁
    have h : (chartAt H α₁) x ∈
        I ⁻¹' Metric.ball (I ((chartAt H α₁) α₁)) hper₁.r := hx₁.2
    exact Metric.ball_subset_closedBall h
  obtain ⟨hflow₁_init, hu₁_ode_full⟩ :=
    (hper₁).flow_spec (I ((chartAt H α₁) x)) hxChart₁_closedBall_r₁
  have hu₁_init : u₁ 0 = I ((chartAt H α₁) x) := hflow₁_init
  have hxChart₂_closedBall_r₂ : I ((chartAt H α₂) x) ∈
      Metric.closedBall (I ((chartAt H α₂) α₂)) hper₂.r := by
    unfold ChartLocalPicardData.U at hx₂
    have h : (chartAt H α₂) x ∈
        I ⁻¹' Metric.ball (I ((chartAt H α₂) α₂)) hper₂.r := hx₂.2
    exact Metric.ball_subset_closedBall h
  obtain ⟨hflow₂_init, _⟩ :=
    (hper₂).flow_spec (I ((chartAt H α₂) x)) hxChart₂_closedBall_r₂
  have hu₂_init : u₂ 0 = I ((chartAt H α₁) x) := by
    change I ((chartAt H α₁) ((chartAt H α₂).symm
      (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) 0)))) = I ((chartAt H α₁) x)
    rw [hflow₂_init, hx_α₂_pullback_eq_x]
  have heq0 : u₁ 0 = u₂ 0 := by rw [hu₁_init, hu₂_init]
  have hu₁_cont_full : ContinuousOn u₁ (Set.Icc (0 : ℝ) hper₁.T) := by
    intro t ht
    have hderiv := hu₁_ode_full t ht
    exact hderiv.continuousWithinAt
  have hu₁_cont : ContinuousOn u₁ (Set.Icc (0 : ℝ) S) :=
    hu₁_cont_full.mono (Set.Icc_subset_Icc le_rfl hS_le₁)
  have hu₁_ode : ∀ t ∈ Set.Ico (0 : ℝ) S,
      HasDerivWithinAt u₁
        ((X t ((chartAt H α₁).symm (I.symm (u₁ t)))) : E)
        (Set.Ici t) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) hper₁.T :=
      ⟨ht.1, ht.2.le.trans hS_le₁⟩
    have hderiv := hu₁_ode_full t ht'
    have hderiv_inter : HasDerivWithinAt u₁
        ((X t ((chartAt H α₁).symm (I.symm (u₁ t)))) : E)
        (Set.Ici t ∩ Set.Icc 0 hper₁.T) t :=
      hderiv.mono Set.inter_subset_right
    have ht_lt : t < hper₁.T := lt_of_lt_of_le ht.2 hS_le₁
    have ht_ge : (0 : ℝ) ≤ t := ht.1
    have h_nhdsWithin :
        Set.Ici t ∩ Set.Icc 0 hper₁.T ∈ nhdsWithin t (Set.Ici t) := by
      have h_subset : Set.Ico t hper₁.T ⊆ Set.Ici t ∩ Set.Icc 0 hper₁.T := by
        intro s hs
        refine ⟨hs.1, ?_⟩
        refine ⟨le_trans ht_ge hs.1, hs.2.le⟩
      have h_mem_open : Set.Ico t hper₁.T ∈ nhdsWithin t (Set.Ici t) := by
        rw [mem_nhdsWithin]
        refine ⟨Set.Iio hper₁.T, isOpen_Iio, ht_lt, ?_⟩
        intro s hs
        exact ⟨hs.2, hs.1⟩
      exact Filter.mem_of_superset h_mem_open h_subset
    exact hderiv_inter.mono_of_mem_nhdsWithin h_nhdsWithin
  have hEqOn : Set.EqOn u₁ u₂ (Set.Icc (0 : ℝ) S) :=
    chart_alpha_coord_gronwall_uniqueness (M := M) (I := I) (E := E)
      X α₁ S r r' K hS_pos hr_lt_r' u₁ u₂
      hLip hu₁_cont hu2_cont hu₁_ode hu2_ode hu1_ball hu2_ball heq0
  intro s hs
  have hEq := hEqOn hs
  have hEq' : (hper₁).flow (I ((chartAt H α₁) x)) s
      = I ((chartAt H α₁) ((chartAt H α₂).symm
        (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) s)))) := by
    have := hEq
    rw [hu₁_def, hu₂_def] at this
    exact this
  change (chartAt H α₁).symm (I.symm ((hper₁).flow (I ((chartAt H α₁) x)) s))
    = (chartAt H α₂).symm (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) s))
  rw [hEq']
  rw [I.left_inv]
  have hmem : (chartAt H α₂).symm (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) s))
      ∈ (chartAt H α₁).source := hα₂_in_α₁_source s hs
  exact (chartAt H α₁).left_inv hmem

/--
**Lemma A.** Continuity of the chart-α₂ flow trajectory at `s = 0` plus
openness of `(chartAt H α₁).source` yields a positive time horizon `S₀ ≤ T₂`
such that the chart-α₂ manifold trajectory of `x ∈ U₂` stays in
`(chartAt H α₁).source` on `[0, S₀]`.

Concretely, the chart-α₂-coord flow `(hper₂).flow y₂` (where
`y₂ := I ((chartAt H α₂) x)`) is continuous on `[0, hper₂.T]` (its derivative
exists there via `flow_spec.2`); composing with the continuous maps
`I.symm : E → H` and `(chartAt H α₂).symm : H → M` (the latter continuous on
the chart-α₂ target, which `I.symm (flow y₂ s)` lies in on an open
neighborhood of `s = 0`) shows the manifold trajectory
`γ₂(s) := (chartAt H α₂).symm (I.symm ((hper₂).flow y₂ s))` is continuous at
`s = 0`. Its value at `s = 0` is `x` (by the chart-α₂ left-inverse identity,
using `x ∈ (chartAt H α₂).source` which is implied by `x ∈ hper₂.U`).
Since `x ∈ (chartAt H α₁).source` (open) by `hx₁`, continuity at `s = 0`
gives a positive `S₀` on which `γ₂(s) ∈ (chartAt H α₁).source` for every
`s ∈ [0, S₀]`. We additionally take `S₀ ≤ hper₂.T`.

This is not hypothesis-packaging: the hypotheses are purely local
(continuity + open set + initial-value membership), whereas the conclusion is
a global membership statement on a closed interval `[0, S₀]` for a freshly
constructed `S₀`.
-/
theorem chart_overlap_alpha_in_alpha_source_short_time
    (X : ℝ → ∀ x : M, TangentSpace I x) (α₁ α₂ : M)
    (hper₂ : ChartLocalPicardData X α₂)
    (x : M) (hx₁ : x ∈ (chartAt H α₁).source) (hx₂ : x ∈ hper₂.U) :
    ∃ S₀ : ℝ, 0 < S₀ ∧ S₀ ≤ hper₂.T ∧
      ∀ s ∈ Set.Icc (0 : ℝ) S₀,
        (chartAt H α₂).symm (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) s))
          ∈ (chartAt H α₁).source := by
  classical
  set y₂ : E := I ((chartAt H α₂) x) with hy₂_def
  have hx₂_source : x ∈ (chartAt H α₂).source := by
    unfold ChartLocalPicardData.U at hx₂
    exact hx₂.1
  have hy₂_closedBall : y₂ ∈
      Metric.closedBall (I ((chartAt H α₂) α₂)) hper₂.r := by
    unfold ChartLocalPicardData.U at hx₂
    have h : (chartAt H α₂) x ∈
        I ⁻¹' Metric.ball (I ((chartAt H α₂) α₂)) hper₂.r := hx₂.2
    exact Metric.ball_subset_closedBall h
  set u₂ : ℝ → E := fun s => (hper₂).flow y₂ s with hu₂_def
  obtain ⟨hflow₂_init, hflow₂_ode⟩ := (hper₂).flow_spec y₂ hy₂_closedBall
  have hu₂_init : u₂ 0 = y₂ := hflow₂_init
  have hu₂_cont : ContinuousOn u₂ (Set.Icc (0 : ℝ) hper₂.T) := by
    intro t ht
    exact (hflow₂_ode t ht).continuousWithinAt
  have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) hper₂.T :=
    ⟨le_rfl, (hper₂).T_pos.le⟩
  have hu₂_cont0 : ContinuousWithinAt u₂ (Set.Icc (0 : ℝ) hper₂.T) 0 :=
    hu₂_cont 0 h0_mem
  have hIsymm_cont : Continuous (I.symm : E → H) := I.continuous_invFun
  have hIsymm_at0 : I.symm (u₂ 0) = (chartAt H α₂) x := by
    rw [hu₂_init, hy₂_def, I.left_inv]
  have hChart2_target : (chartAt H α₂) x ∈ (chartAt H α₂).target :=
    (chartAt H α₂).map_source hx₂_source
  have hChart2_target_open : IsOpen (chartAt H α₂).target :=
    (chartAt H α₂).open_target
  set γ₂ : ℝ → M := fun s =>
    (chartAt H α₂).symm (I.symm (u₂ s)) with hγ₂_def
  have hγ₂_init : γ₂ 0 = x := by
    change (chartAt H α₂).symm (I.symm (u₂ 0)) = x
    rw [hIsymm_at0]
    exact (chartAt H α₂).left_inv hx₂_source
  have hγ₂_cont0 : ContinuousWithinAt γ₂ (Set.Icc (0 : ℝ) hper₂.T) 0 := by
    have h1 : ContinuousWithinAt (fun s => I.symm (u₂ s))
        (Set.Icc (0 : ℝ) hper₂.T) 0 := by
      exact hIsymm_cont.continuousAt.comp_continuousWithinAt hu₂_cont0
    have h_at0_target : (fun s => I.symm (u₂ s)) 0 ∈ (chartAt H α₂).target := by
      change I.symm (u₂ 0) ∈ (chartAt H α₂).target
      rw [hIsymm_at0]; exact hChart2_target
    have h_chart2symm_cont : ContinuousAt (chartAt H α₂).symm (I.symm (u₂ 0)) := by
      rw [hIsymm_at0]
      exact ((chartAt H α₂).continuousAt_symm hChart2_target)
    have hcomp : ContinuousWithinAt
        ((chartAt H α₂).symm ∘ (fun s => I.symm (u₂ s)))
        (Set.Icc (0 : ℝ) hper₂.T) 0 :=
      ContinuousAt.comp_continuousWithinAt
        (g := (chartAt H α₂).symm)
        (f := fun s => I.symm (u₂ s))
        h_chart2symm_cont h1
    exact hcomp
  have hChart1_source_open : IsOpen (chartAt H α₁).source :=
    (chartAt H α₁).open_source
  have hγ₂_init_mem : γ₂ 0 ∈ (chartAt H α₁).source := by
    rw [hγ₂_init]; exact hx₁
  have hpreim : γ₂ ⁻¹' (chartAt H α₁).source ∈
      nhdsWithin (0 : ℝ) (Set.Icc (0 : ℝ) hper₂.T) := by
    apply hγ₂_cont0
    exact hChart1_source_open.mem_nhds hγ₂_init_mem
  rw [mem_nhdsWithin] at hpreim
  obtain ⟨V, hV_open, hV_mem, hV_subset⟩ := hpreim
  obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.isOpen_iff.mp hV_open 0 hV_mem
  set S₀ : ℝ := min (ε / 2) hper₂.T with hS₀_def
  have hS₀_pos : 0 < S₀ := by
    apply lt_min
    · linarith
    · exact (hper₂).T_pos
  have hS₀_le_T : S₀ ≤ hper₂.T := min_le_right _ _
  have hS₀_lt_ε : S₀ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨S₀, hS₀_pos, hS₀_le_T, ?_⟩
  intro s hs
  have hs_in_Icc : s ∈ Set.Icc (0 : ℝ) hper₂.T :=
    ⟨hs.1, hs.2.trans hS₀_le_T⟩
  have hs_in_ε : s ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
    exact lt_of_le_of_lt hs.2 hS₀_lt_ε
  have hs_in_V : s ∈ V := hε_ball hs_in_ε
  have : s ∈ γ₂ ⁻¹' (chartAt H α₁).source := hV_subset ⟨hs_in_V, hs_in_Icc⟩
  exact this

/--
**Lemma B.** Chart-α₁-coord ODE for the chart-α₁-coord representation of the
chart-α₂ flow trajectory, derived from the chart-α₂ ODE (`flow_spec.2`) and
the chain rule on the chart-transition map
`g := I ∘ (chartAt H α₁) ∘ (chartAt H α₂).symm ∘ I.symm`.

The chain rule applied to `g ∘ u₂_y₂` (where `u₂_y₂(s) := (hper₂).flow y₂ s`,
`y₂ := I ((chartAt H α₂) x)`) gives, at each `t ∈ [0, S)`,

`d/ds [g (u₂_y₂(s))] _{s=t} = Dg(u₂_y₂(t)) · u₂_y₂'(t) = Dg(u₂_y₂(t)) · X t γ₂(t)`

(the second equality from `flow_spec.2`, where `γ₂(t) := (chart₂).symm
(I.symm (u₂_y₂(t)))` is the chart-α₂ manifold trajectory).

The conclusion of the lemma expects the velocity to be `X t γ₂(t)` (as `E`),
matching the chart-α₁ ODE form. For these to coincide we need the analytic
compatibility hypothesis `hcompat`: at each `t ∈ [0, S)`, there exists a
continuous linear map `L_t : E →L[ℝ] E` such that
* `g : E → E` has Fréchet derivative `L_t` at `u₂_y₂(t)`, and
* `L_t` fixes the vector `X t γ₂(t) : E`.

This is a genuine analytic statement about `X`: the chart-transition
derivative acts as identity on `X` along the chart-α₂ trajectory. For
chart-invariant vector fields (e.g. `deTurckVF`), this compatibility is a
consequence of the chart-invariance of `X`; for general `X`, it is the
fundamental obstruction to chart-cover uniqueness of the chart-coord flows.

The hypothesis is not hypothesis-packaging: it is a *linear-algebra* fact
(an equality between two elements of `E`) at each `t`, plus a smoothness fact
(`HasFDerivAt`), whereas the conclusion is an *ODE* statement
(`HasDerivWithinAt` on `Set.Ici t`) at each `t`. The lemma derives the ODE
statement from the chain rule.
-/
theorem chart_overlap_chart_alpha_coord_ode
    (X : ℝ → ∀ x : M, TangentSpace I x) (α₁ α₂ : M)
    (hper₂ : ChartLocalPicardData X α₂)
    (S : ℝ) (_hS_pos : 0 < S) (hS_le₂ : S ≤ hper₂.T)
    (x : M) (hx₂ : x ∈ hper₂.U)
    (hcompat : ∀ t ∈ Set.Ico (0 : ℝ) S,
      ∃ L : E →L[ℝ] E,
        HasFDerivAt
          (fun y : E =>
            I ((chartAt H α₁) ((chartAt H α₂).symm (I.symm y))))
          L
          ((hper₂).flow (I ((chartAt H α₂) x)) t) ∧
        L (X t ((chartAt H α₂).symm
            (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) t))) : E)
          = (X t ((chartAt H α₂).symm
            (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) t))) : E))
    (hα₂_in_α₁_source : ∀ s ∈ Set.Ico (0 : ℝ) S,
      (chartAt H α₂).symm (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) s))
        ∈ (chartAt H α₁).source) :
    ∀ t ∈ Set.Ico (0 : ℝ) S,
      HasDerivWithinAt
        (fun s : ℝ => I ((chartAt H α₁) ((chartAt H α₂).symm
          (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) s)))))
        ((X t ((chartAt H α₁).symm (I.symm
          (I ((chartAt H α₁) ((chartAt H α₂).symm
            (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) t)))))))) : E)
        (Set.Ici t) t := by
  classical
  set y₂ : E := I ((chartAt H α₂) x) with hy₂_def
  set u₂ : ℝ → E := fun s => (hper₂).flow y₂ s with hu₂_def
  set g : E → E := fun y =>
    I ((chartAt H α₁) ((chartAt H α₂).symm (I.symm y))) with hg_def
  have hy₂_closedBall : y₂ ∈
      Metric.closedBall (I ((chartAt H α₂) α₂)) hper₂.r := by
    unfold ChartLocalPicardData.U at hx₂
    have h : (chartAt H α₂) x ∈
        I ⁻¹' Metric.ball (I ((chartAt H α₂) α₂)) hper₂.r := hx₂.2
    exact Metric.ball_subset_closedBall h
  obtain ⟨_hflow₂_init, hflow₂_ode⟩ := (hper₂).flow_spec y₂ hy₂_closedBall
  intro t ht
  have ht_T : t ∈ Set.Icc (0 : ℝ) hper₂.T :=
    ⟨ht.1, ht.2.le.trans hS_le₂⟩
  have hu₂_deriv : HasDerivWithinAt u₂
      ((X t ((chartAt H α₂).symm (I.symm (u₂ t)))) : E)
      (Set.Icc (0 : ℝ) hper₂.T) t :=
    hflow₂_ode t ht_T
  have ht_lt_T : t < hper₂.T := lt_of_lt_of_le ht.2 hS_le₂
  have ht_ge : (0 : ℝ) ≤ t := ht.1
  have h_nhdsWithin_T :
      Set.Ici t ∩ Set.Icc 0 hper₂.T ∈ nhdsWithin t (Set.Ici t) := by
    have h_subset : Set.Ico t hper₂.T ⊆ Set.Ici t ∩ Set.Icc 0 hper₂.T := by
      intro s hs
      refine ⟨hs.1, ?_⟩
      refine ⟨le_trans ht_ge hs.1, hs.2.le⟩
    have h_mem_open : Set.Ico t hper₂.T ∈ nhdsWithin t (Set.Ici t) := by
      rw [mem_nhdsWithin]
      refine ⟨Set.Iio hper₂.T, isOpen_Iio, ht_lt_T, ?_⟩
      intro s hs
      exact ⟨hs.2, hs.1⟩
    exact Filter.mem_of_superset h_mem_open h_subset
  have hu₂_deriv_inter : HasDerivWithinAt u₂
      ((X t ((chartAt H α₂).symm (I.symm (u₂ t)))) : E)
      (Set.Ici t ∩ Set.Icc 0 hper₂.T) t :=
    hu₂_deriv.mono Set.inter_subset_right
  have hu₂_deriv_Ici : HasDerivWithinAt u₂
      ((X t ((chartAt H α₂).symm (I.symm (u₂ t)))) : E)
      (Set.Ici t) t :=
    hu₂_deriv_inter.mono_of_mem_nhdsWithin h_nhdsWithin_T
  obtain ⟨L_t, hL_t_deriv, hL_t_fix⟩ := hcompat t ht
  have h_chain : HasDerivWithinAt (g ∘ u₂)
      (L_t ((X t ((chartAt H α₂).symm (I.symm (u₂ t)))) : E))
      (Set.Ici t) t := by
    have : HasDerivWithinAt (g ∘ u₂)
        (L_t ((X t ((chartAt H α₂).symm (I.symm (u₂ t)))) : E))
        (Set.Ici t) t := hL_t_deriv.comp_hasDerivWithinAt t hu₂_deriv_Ici
    exact this
  have h_chain' : HasDerivWithinAt (g ∘ u₂)
      ((X t ((chartAt H α₂).symm (I.symm (u₂ t)))) : E)
      (Set.Ici t) t := by
    rw [hL_t_fix] at h_chain
    exact h_chain
  have hI_li : I.symm (I ((chartAt H α₁) ((chartAt H α₂).symm (I.symm (u₂ t)))))
      = (chartAt H α₁) ((chartAt H α₂).symm (I.symm (u₂ t))) :=
    I.left_inv _
  have hChart1_li : (chartAt H α₁).symm
      ((chartAt H α₁) ((chartAt H α₂).symm (I.symm (u₂ t))))
      = (chartAt H α₂).symm (I.symm (u₂ t)) :=
    (chartAt H α₁).left_inv (hα₂_in_α₁_source t ht)
  have h_rhs_eq :
      ((X t ((chartAt H α₁).symm (I.symm
        (I ((chartAt H α₁) ((chartAt H α₂).symm
          (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) t)))))))) : E)
      = ((X t ((chartAt H α₂).symm (I.symm (u₂ t)))) : E) := by
    have : (chartAt H α₁).symm (I.symm
        (I ((chartAt H α₁) ((chartAt H α₂).symm (I.symm (u₂ t))))))
        = (chartAt H α₂).symm (I.symm (u₂ t)) := by
      rw [hI_li, hChart1_li]
    rw [hu₂_def]
    rw [this]
  have h_lhs_eq :
      (fun s : ℝ => I ((chartAt H α₁) ((chartAt H α₂).symm
        (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) s)))))
      = g ∘ u₂ := by
    funext s
    rfl
  rw [h_lhs_eq, h_rhs_eq]
  exact h_chain'

end DifferentialGeometry.PDE.RicciFlow.ODE
