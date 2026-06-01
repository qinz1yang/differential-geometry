import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.Glue
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.BanachIC
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.Bijective.UniformBijective

/-!
## Smooth diffeomorphisms from forward/reverse flows

Given a forward flow `Φ` and a reverse flow `Ψ` on a compact boundaryless manifold,
each individually smooth and mutually inverse for `t ∈ [0, T)`, we package them
into a `Diffeomorph I I M M ∞` for each `t ∈ (0, T)`.
-/

open scoped Manifold Topology ContDiff

theorem time_dependent_vf_globalflow_diffeomorph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {T : ℝ} (_hT : 0 < T)
    {Φ Ψ : ℝ → M → M}
    (_hΦ_init : ∀ x, Φ 0 x = x) (_hΨ_init : ∀ x, Ψ 0 x = x)
    (hΦ_smooth : ∀ t, 0 < t → t < T → ContMDiff I I ∞ (Φ t))
    (hΨ_smooth : ∀ t, 0 < t → t < T → ContMDiff I I ∞ (Ψ t))
    (hΨΦ : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Ψ s (Φ s x) = x)
    (hΦΨ : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Φ s (Ψ s x) = x) :
    ∀ t, 0 < t → t < T →
      ∃ d : Diffeomorph I I M M ∞,
        (∀ x, d x = Φ t x) ∧ (∀ x, d.symm x = Ψ t x) := by
  intro t ht htT
  have hmem : t ∈ Set.Ico (0 : ℝ) T := Set.mem_Ico.mpr ⟨le_of_lt ht, htT⟩
  let e : M ≃ M :=
    { toFun := Φ t
      invFun := Ψ t
      left_inv := fun x => hΨΦ t hmem x
      right_inv := fun x => hΦΨ t hmem x }
  exact ⟨⟨e, hΦ_smooth t ht htT, hΨ_smooth t ht htT⟩, fun x => rfl, fun x => rfl⟩

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/--
The Picard flow `(hper α).flow` maps the chart-coordinate image of a
chart-source point `x` at time `0` back to the chart-coordinate image of `x`.
Together with the `I` and chart left-inverses, this shows the chart-pullback of
the flow value at `s = 0` recovers the original manifold point.

Concretely, for `x ∈ (hper α).U`, we have
  `(chartAt H α).symm (I.symm ((hper α).flow (I ((chartAt H α) x)) 0)) = x`.

The proof reduces to `flow_spec.1` (initial condition `flow y 0 = y`)
followed by `I.left_inv` and `(chartAt H α).left_inv`.
-/
theorem picard_data_flow_initial_value_manifold
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M)
    (hper : ChartLocalPicardData X α)
    (x : M) (hx : x ∈ hper.U) :
    (chartAt H α).symm (I.symm (hper.flow (I ((chartAt H α) x)) 0)) = x := by
  have hx_source : x ∈ (chartAt H α).source := by
    unfold ChartLocalPicardData.U at hx; exact hx.1
  have hx_closedBall : I ((chartAt H α) x) ∈
      Metric.closedBall (I ((chartAt H α) α)) hper.r := by
    unfold ChartLocalPicardData.U at hx
    exact Metric.ball_subset_closedBall hx.2
  obtain ⟨hinit, _⟩ := hper.flow_spec (I ((chartAt H α) x)) hx_closedBall
  rw [hinit, I.left_inv]
  exact (chartAt H α).left_inv hx_source

/--
For a boundaryless model, `I.symm(I(h)) = h` for any `h : H`, and if
`h = (chartAt H α) x` with `x ∈ (chartAt H α).source`, then
`(chartAt H α).symm h = x`. This gives the full round-trip.
-/
theorem chart_coord_roundtrip
    (α x : M) (hx : x ∈ (chartAt H α).source) :
    (chartAt H α).symm (I.symm (I ((chartAt H α) x))) = x := by
  rw [I.left_inv]
  exact (chartAt H α).left_inv hx

/--
The chart-coordinate image `I ((chartAt H α) x)` of a chart-source point
`x ∈ (hper α).U` lies in the closed ball of radius `hper.r`.
-/
theorem picard_data_chart_coord_in_closedBall
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M)
    (hper : ChartLocalPicardData X α)
    (x : M) (hx : x ∈ hper.U) :
    I ((chartAt H α) x) ∈ Metric.closedBall (I ((chartAt H α) α)) hper.r := by
  unfold ChartLocalPicardData.U at hx
  exact Metric.ball_subset_closedBall hx.2

set_option linter.unusedVariables false in
/--
**Headline theorem: time-dependent ODE flow is a diffeomorphism on a closed
manifold.**

Given per-base-point chart-local Picard data for a time-dependent vector field
`X` and for its negative `-X`, together with per-chart `C^∞` regularity of the
chart-pushforward vector fields, chart-overlap agreement for the global flows,
and per-chart bijectivity, we construct a positive time horizon `T > 0` and,
for each `t ∈ (0, T)`, a smooth diffeomorphism `d : Diffeomorph I I M M ∞`
that agrees with the global flow.

The proof chains the full infrastructure stack:

1. **Glue** (`time_dependent_vf_global_flow_glue`): assembles per-chart Picard
   flows into global flows `Φ` (for `X`) and `Ψ` (for `-X`).
2. **Smooth-in-space** (`time_dependent_vf_flow_smooth_in_space`): lifts
   chart-local `C^∞` of the flow to global `ContMDiff I I ∞ (Φ t)`,
   using `hLocalFwd` for chart-overlap agreement.
3. **Uniform bijectivity** (`chart_cover_flow_bijective_two_sided_uniform_horizon`):
   compactness extracts a uniform positive horizon on which `Ψ ∘ Φ = id` and
   `Φ ∘ Ψ = id`, using `hBijPerChart`.
4. **Diffeomorph** (`time_dependent_vf_globalflow_diffeomorph`): packages
   smooth mutual inverses into `Diffeomorph I I M M ∞`.

The hypotheses `hLocalFwd`, `hLocalRev`, and `hBijPerChart` encode chart-overlap
compatibility. For chart-invariant vector fields, they can be discharged from
`hper` and `hSmoothX_chart` via `chart_cover_flow_unique_on_overlap_chart_alpha_coord`
and `chart_overlap_chart_alpha_coord_ode`. The smoothness hypotheses
`hSmoothX_chart` and `hSmoothNegX_chart` are recorded for that downstream
discharge but are not consumed directly in this assembly proof.
-/
theorem time_dependent_vf_flow_diffeomorph_on_closed_manifold
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hper : ∀ α : M, ChartLocalPicardData X α)
    (hperNeg : ∀ α : M, ChartLocalPicardData (fun t x => -(X t x)) α)
    (hSmoothX_chart : ∀ α : M, ContDiff ℝ ∞ (Function.uncurry fun t y =>
      (X t ((chartAt H α).symm (I.symm y)) : E)))
    (hSmoothNegX_chart : ∀ α : M, ContDiff ℝ ∞ (Function.uncurry fun t y =>
      ((-X t ((chartAt H α).symm (I.symm y))) : E)))
    (hLocalFwd : ∀ (Φ : ℝ → M → M) (T : ℝ), 0 < T →
      (∀ x : M, ∃ α : M, x ∈ (hper α).U ∧
        ∀ s : ℝ, Φ s x = (chartAt H α).symm
          (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) →
      ∀ x : M, ∃ (ρ : ℝ) (_ : 0 < ρ) (flow : E → ℝ → E),
        ContDiffOn ℝ ∞ (Function.uncurry flow)
          (Metric.ball (I ((chartAt H x) x)) ρ ×ˢ Set.Ioo 0 T) ∧
        (∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ y ∈ (chartAt H x).source,
          I ((chartAt H x) y) ∈ Metric.ball (I ((chartAt H x) x)) ρ →
          Φ s y = (chartAt H x).symm (I.symm (flow (I ((chartAt H x) y)) s))) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) T,
          I.symm (flow (I ((chartAt H x) x)) t) ∈ (chartAt H x).target))
    (hLocalRev : ∀ (Ψ : ℝ → M → M) (T : ℝ), 0 < T →
      (∀ x : M, ∃ α : M, x ∈ (hperNeg α).U ∧
        ∀ s : ℝ, Ψ s x = (chartAt H α).symm
          (I.symm ((hperNeg α).flow (I ((chartAt H α) x)) s))) →
      ∀ x : M, ∃ (ρ : ℝ) (_ : 0 < ρ) (flow : E → ℝ → E),
        ContDiffOn ℝ ∞ (Function.uncurry flow)
          (Metric.ball (I ((chartAt H x) x)) ρ ×ˢ Set.Ioo 0 T) ∧
        (∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ y ∈ (chartAt H x).source,
          I ((chartAt H x) y) ∈ Metric.ball (I ((chartAt H x) x)) ρ →
          Ψ s y = (chartAt H x).symm (I.symm (flow (I ((chartAt H x) y)) s))) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) T,
          I.symm (flow (I ((chartAt H x) x)) t) ∈ (chartAt H x).target))
    (hBijPerChart : ∀ (Φ Ψ : ℝ → M → M),
      (∀ x, Φ 0 x = x) → (∀ x, Ψ 0 x = x) →
      (∀ x : M, ∃ α : M, ∀ s : ℝ,
        Φ s x = (chartAt H α).symm
          (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) →
      (∀ x : M, ∃ α : M, ∀ s : ℝ,
        Ψ s x = (chartAt H α).symm
          (I.symm ((hperNeg α).flow (I ((chartAt H α) x)) s))) →
      ∀ α : M,
        ∃ S_α : ℝ, 0 < S_α ∧
          ∀ x ∈ (hper α).U ∩ (hperNeg α).U,
            ∀ s ∈ Set.Ico (0 : ℝ) S_α,
              Ψ s (Φ s x) = x ∧ Φ s (Ψ s x) = x) :
    ∃ T : ℝ, 0 < T ∧
      ∃ (Φ : ℝ → M → M),
        (∀ x, Φ 0 x = x) ∧
        (∀ x : M, ∃ α : M, ∀ s : ℝ,
          Φ s x = (chartAt H α).symm
            (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) ∧
        ∀ t, 0 < t → t < T →
          ∃ d : Diffeomorph I I M M ∞, ∀ x, d x = Φ t x := by
  obtain ⟨T_fwd, hT_fwd_pos, _S_fwd, _hCover_fwd, Φ, hΦ_init, hΦ_repr⟩ :=
    time_dependent_vf_global_flow_glue X hper
  have hΦ_repr' : ∀ x : M, ∃ α : M, x ∈ (hper α).U ∧
      ∀ s : ℝ, Φ s x = (chartAt H α).symm
        (I.symm ((hper α).flow (I ((chartAt H α) x)) s)) := by
    intro x
    obtain ⟨α, _hαS, hxU, hrepr⟩ := hΦ_repr x
    exact ⟨α, hxU, hrepr⟩
  have hΦ_repr_simple : ∀ x : M, ∃ α : M, ∀ s : ℝ,
      Φ s x = (chartAt H α).symm
        (I.symm ((hper α).flow (I ((chartAt H α) x)) s)) := by
    intro x; obtain ⟨α, _, hrepr⟩ := hΦ_repr' x; exact ⟨α, hrepr⟩
  obtain ⟨T_rev, hT_rev_pos, _S_rev, _hCover_rev, Ψ, hΨ_init, hΨ_repr⟩ :=
    time_dependent_vf_global_flow_glue (fun t x => -(X t x)) hperNeg
  have hΨ_repr' : ∀ x : M, ∃ α : M, x ∈ (hperNeg α).U ∧
      ∀ s : ℝ, Ψ s x = (chartAt H α).symm
        (I.symm ((hperNeg α).flow (I ((chartAt H α) x)) s)) := by
    intro x
    obtain ⟨α, _hαS, hxU, hrepr⟩ := hΨ_repr x
    exact ⟨α, hxU, hrepr⟩
  have hΨ_repr_simple : ∀ x : M, ∃ α : M, ∀ s : ℝ,
      Ψ s x = (chartAt H α).symm
        (I.symm ((hperNeg α).flow (I ((chartAt H α) x)) s)) := by
    intro x; obtain ⟨α, _, hrepr⟩ := hΨ_repr' x; exact ⟨α, hrepr⟩
  have hLocalFwd_data := hLocalFwd Φ T_fwd hT_fwd_pos hΦ_repr'
  have hΦ_smooth : ∀ t : ℝ, 0 < t → t < T_fwd → ContMDiff I I ∞ (Φ t) :=
    time_dependent_vf_flow_smooth_in_space X T_fwd hT_fwd_pos Φ hLocalFwd_data
  have hLocalRev_data := hLocalRev Ψ T_rev hT_rev_pos hΨ_repr'
  have hΨ_smooth : ∀ t : ℝ, 0 < t → t < T_rev → ContMDiff I I ∞ (Ψ t) :=
    time_dependent_vf_flow_smooth_in_space
      (fun t x => -(X t x)) T_rev hT_rev_pos Ψ hLocalRev_data
  have hBij := hBijPerChart Φ Ψ hΦ_init hΨ_init hΦ_repr_simple hΨ_repr_simple
  obtain ⟨T_bij, hT_bij_pos, hΨΦ_eq, hΦΨ_eq⟩ :=
    chart_cover_flow_bijective_two_sided_uniform_horizon
      X hper hperNeg Φ Ψ hΦ_init hΨ_init hΦ_repr_simple hΨ_repr_simple hBij
  set T : ℝ := min (min T_fwd T_rev) T_bij with hT_def
  have hT_pos : 0 < T := lt_min (lt_min hT_fwd_pos hT_rev_pos) hT_bij_pos
  have hΦ_smooth_T : ∀ t, 0 < t → t < T → ContMDiff I I ∞ (Φ t) := by
    intro t ht htT
    exact hΦ_smooth t ht (lt_of_lt_of_le htT (le_trans (min_le_left _ _)
      (min_le_left _ _)))
  have hΨ_smooth_T : ∀ t, 0 < t → t < T → ContMDiff I I ∞ (Ψ t) := by
    intro t ht htT
    exact hΨ_smooth t ht (lt_of_lt_of_le htT (le_trans (min_le_left _ _)
      (min_le_right _ _)))
  have hΨΦ : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Ψ s (Φ s x) = x := by
    intro s hs x
    exact hΨΦ_eq s ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩ x
  have hΦΨ : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Φ s (Ψ s x) = x := by
    intro s hs x
    exact hΦΨ_eq s ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩ x
  have hDiffeo := time_dependent_vf_globalflow_diffeomorph
    (I := I) hT_pos hΦ_init hΨ_init hΦ_smooth_T hΨ_smooth_T hΨΦ hΦΨ
  refine ⟨T, hT_pos, Φ, hΦ_init, hΦ_repr_simple, ?_⟩
  intro t ht htT
  obtain ⟨d, hd_fwd, _⟩ := hDiffeo t ht htT
  exact ⟨d, hd_fwd⟩

end DifferentialGeometry.PDE.RicciFlow.ODE
