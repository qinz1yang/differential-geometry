import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Existence
import DifferentialGeometry.Geometry.Riemannian.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Riemannian.Geodesic.SmoothFlow
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Uniqueness
import DifferentialGeometry.Geometry.Riemannian.Exponential.Definition
import Mathlib.Analysis.ODE.Gronwall

set_option linter.unusedSectionVars false

/-!
# Bridge: chart-pushed geodesic flow ↔ manifold geodesic

This file links the chart-pushed phase-space flow `Φ : (E × E) × ℝ → E × E`
provided by `Geodesic/SmoothFlow.lean` to the manifold-level geodesic
formalism (`IsGeodesicAt`, `maximalGeodesic`).

The chart-pushed flow is built from the cutoff vector field
`chartPhaseVFCutoff g α (x₀, v₀) b` on `E × E`, which agrees with the
genuine chart-phase vector field `chartPhaseVF g α` on the inner ball
of the cutoff bump. On that inner ball, the flow's orbits satisfy the
chart-coordinate geodesic ODE
$$\dot x = v, \qquad \dot v = -\Gamma_\alpha(v, v)(x),$$
i.e., the chart-coordinate form of the geodesic equation.

## Main results

* `chartPhaseVF_orbit_uniqueness` — **chart-coordinate ODE uniqueness on
  `E × E`.** Two curves `c₁, c₂ : ℝ → E × E` with matching values at
  `t = 0` that both satisfy the chart-phase geodesic ODE on a
  neighbourhood of `0` agree on a neighbourhood of `0`. This is a direct
  application of `ODE_solution_unique_of_eventually` with the
  smooth-on-chart-interior right-hand side.

* `chartFlowGeodesicCurve` — the candidate manifold curve obtained by
  pulling back the chart-pushed flow's first component via
  `(extChartAt I p).symm`. We give its initial value, continuity, and
  domain properties.

* `IsMIntegralCurveAt.chartPhaseVF_hasDerivAt` — bridge from the
  manifold-level `IsMIntegralCurveAt` predicate to the chart-phase ODE
  satisfied by the chart-pushed lift. This is the **input direction** of
  the bridge: any geodesic lift, when pushed to chart coordinates, solves
  the chart-phase ODE.

## What this file does *not* do

* It does *not* invert the bridge: extracting a manifold geodesic from a
  chart-pushed flow orbit requires lifting the orbit back to the tangent
  bundle, which uses the chart-of-`TM` structure and the explicit form
  of `geodesicVectorFieldChart` as a section. The first-component
  identification of `Φ ((x₀, v₀), t).1` with `extChartAt I p (γ t)` for
  the manifold geodesic `γ` would be a direct consequence and is left as
  a follow-up step.

* It does *not* establish that the chart-pushed flow's first component,
  pulled back to `M`, equals `maximalGeodesic g p v` on the flow's time
  interval. That identification requires both the inverse-bridge above
  *and* a global-uniqueness propagation argument for `maximalGeodesic`
  itself (the chart-fixed geodesic vector field is only `C^∞` on the
  chart-domain preimage, so propagation along the maximal interval must
  change chart basepoint; this is a moving-chart phenomenon and is a
  separate development).
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

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.Geodesic

section ChartPhaseODE

variable [I.Boundaryless]

/-- The cutoff field equals the genuine chart-phase field on the inner
ball of the bump. Restated for the time-padded variant used by the local
flow theorem. -/
lemma chartPhaseVFTime_eq_chartPhaseVF_of_mem_closedBall
    (g : SmoothRiemannianMetric I M) (α : M)
    (z₀ : E × E) (b : ContDiffBump z₀) {z : E × E}
    (hz : z ∈ Metric.closedBall z₀ b.rIn) (τ : ℝ) :
    chartPhaseVFTime (I := I) g α z₀ b τ z = chartPhaseVF (I := I) g α z := by
  simp only [chartPhaseVFTime_apply]
  exact chartPhaseVFCutoff_eq_of_mem_closedBall (I := I) g α z₀ b hz

end ChartPhaseODE

section ChartPhaseUniqueness

variable [I.Boundaryless]

/-- Time-padded autonomous form of `chartPhaseVF`. -/
def chartPhaseVFAuto (g : SmoothRiemannianMetric I M) (α : M) :
    ℝ → (E × E) → E × E :=
  fun _ z => chartPhaseVF (I := I) g α z

@[simp] lemma chartPhaseVFAuto_apply
    (g : SmoothRiemannianMetric I M) (α : M) (t : ℝ) (z : E × E) :
    chartPhaseVFAuto (I := I) g α t z = chartPhaseVF (I := I) g α z := rfl

/-- On the chart-interior product, `chartPhaseVF g α` is locally
Lipschitz: it is `C^1` there, hence locally Lipschitz at each point. -/
lemma chartPhaseVF_lipschitzOnWith_locally
    (g : SmoothRiemannianMetric I M) (α : M)
    {z : E × E} (hz : z ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :
    ∃ K : ℝ≥0, ∃ s ∈ 𝓝 z, LipschitzOnWith K (chartPhaseVF (I := I) g α) s := by
  have hC1 : ContDiffOn ℝ 1 (chartPhaseVF (I := I) g α)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) := by
    have h := chartPhaseVF_contDiffOn (I := I) g α
    exact h.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have hopen : IsOpen ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :=
    isOpen_interior.prod isOpen_univ
  have hC1_at : ContDiffAt ℝ 1 (chartPhaseVF (I := I) g α) z :=
    hC1.contDiffAt (hopen.mem_nhds hz)
  exact hC1_at.exists_lipschitzOnWith

/-- **Chart-coordinate ODE uniqueness.** If two curves `c₁, c₂ : ℝ → E × E`
have matching values at `0` and both satisfy the chart-phase geodesic
ODE on a neighbourhood of `0`, with values staying inside the chart-
interior product, then they agree on a neighbourhood of `0`. -/
theorem chartPhaseVF_orbit_uniqueness
    {g : SmoothRiemannianMetric I M} {α : M}
    {c₁ c₂ : ℝ → E × E} {z₀ : E × E}
    (hz₀ : z₀ ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E))
    (h1 : c₁ 0 = z₀) (h2 : c₂ 0 = z₀)
    (hd1 : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt c₁ (chartPhaseVF (I := I) g α (c₁ t)) t ∧
        c₁ t ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E))
    (hd2 : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt c₂ (chartPhaseVF (I := I) g α (c₂ t)) t ∧
        c₂ t ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :
    c₁ =ᶠ[𝓝 (0 : ℝ)] c₂ := by
  classical
  obtain ⟨K, sNhd, hsNhd, hlip⟩ :=
    chartPhaseVF_lipschitzOnWith_locally (I := I) g α hz₀
  set v : ℝ → (E × E) → E × E := chartPhaseVFAuto (I := I) g α with hv_def
  set s : ℝ → Set (E × E) := fun _ => sNhd with hs_def
  have hv_lip : ∀ᶠ t in 𝓝 (0 : ℝ), LipschitzOnWith K (v t) (s t) :=
    Filter.Eventually.of_forall (fun _ => hlip)
  have hc1_in_s : ∀ᶠ t in 𝓝 (0 : ℝ), c₁ t ∈ sNhd := by
    have ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, (HasDerivAt c₁ (chartPhaseVF (I := I) g α (c₁ t₀)) t₀ ∧
        c₁ t₀ ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) ∧
        ∀ᶠ t in 𝓝 t₀, HasDerivAt c₁ (chartPhaseVF (I := I) g α (c₁ t)) t ∧
          c₁ t ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := by
      refine ⟨0, ?_, hd1⟩
      exact hd1.self_of_nhds
    have hcont : ContinuousAt c₁ 0 := (hd1.self_of_nhds).1.continuousAt
    have hc1_z₀ : c₁ 0 ∈ sNhd := by rw [h1]; exact mem_of_mem_nhds hsNhd
    exact hcont.preimage_mem_nhds (by rw [h1]; exact hsNhd)
  have hc2_in_s : ∀ᶠ t in 𝓝 (0 : ℝ), c₂ t ∈ sNhd := by
    have hcont : ContinuousAt c₂ 0 := (hd2.self_of_nhds).1.continuousAt
    exact hcont.preimage_mem_nhds (by rw [h2]; exact hsNhd)
  have hf : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt c₁ (v t (c₁ t)) t ∧ c₁ t ∈ s t := by
    filter_upwards [hd1, hc1_in_s] with t htD htS
    exact ⟨htD.1, htS⟩
  have hg : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt c₂ (v t (c₂ t)) t ∧ c₂ t ∈ s t := by
    filter_upwards [hd2, hc2_in_s] with t htD htS
    exact ⟨htD.1, htS⟩
  have heq : c₁ 0 = c₂ 0 := h1.trans h2.symm
  exact ODE_solution_unique_of_eventually (v := v) (s := s) (K := K) (t₀ := 0)
    hv_lip hf hg heq

end ChartPhaseUniqueness

section ChartFlowOrbit

variable [I.Boundaryless]

/-- The chart-pushed flow's orbit through the base point `(x₀, v₀)`, as a
function of time. -/
def chartFlowOrbit (Φ : (E × E) × ℝ → E × E) (z₀ : E × E) : ℝ → E × E :=
  fun t => Φ (z₀, t)

@[simp] lemma chartFlowOrbit_apply (Φ : (E × E) × ℝ → E × E) (z₀ : E × E) (t : ℝ) :
    chartFlowOrbit Φ z₀ t = Φ (z₀, t) := rfl

end ChartFlowOrbit

section ChartFlowGeodesicCurve

variable [I.Boundaryless]

/-- The chart-pushed flow geodesic curve on `M`: pull back the first
component of the orbit through `(extChartAt I p p, v_chart)` via the
inverse extended chart at `p`. -/
def chartFlowGeodesicCurve (Φ : (E × E) × ℝ → E × E) (p : M) (v_chart : E) :
    ℝ → M :=
  fun t => (extChartAt I p).symm
    (chartFlowOrbit Φ ((extChartAt I p p, v_chart)) t).1

@[simp] lemma chartFlowGeodesicCurve_apply
    (Φ : (E × E) × ℝ → E × E) (p : M) (v_chart : E) (t : ℝ) :
    chartFlowGeodesicCurve (I := I) Φ p v_chart t =
      (extChartAt I p).symm (Φ ((extChartAt I p p, v_chart), t)).1 := rfl

/-- **Initial value of the chart-pushed flow geodesic curve.** Provided
the flow satisfies the `IsLocalFlow` initial-value identity at the base
point, the chart-pushed geodesic curve starts at `p`. -/
theorem chartFlowGeodesicCurve_zero
    {Φ : (E × E) × ℝ → E × E} {p : M} {v_chart : E}
    (hinit : Φ ((extChartAt I p p, v_chart), 0) = (extChartAt I p p, v_chart)) :
    chartFlowGeodesicCurve (I := I) Φ p v_chart 0 = p := by
  unfold chartFlowGeodesicCurve chartFlowOrbit
  rw [hinit]
  exact (extChartAt I p).left_inv (mem_extChartAt_source (I := I) p)

end ChartFlowGeodesicCurve

section ChartFlowExistencePackaging

variable [I.Boundaryless] [CompleteSpace E]

/-- **Existence packaging of the chart-pushed flow geodesic curve.** For
any base point `p : M` and chart-coordinate velocity `v_chart : E`, there
exists a `ContDiffBump`, radii `ρ, T > 0`, a chart-pushed flow `Φ`, and
the corresponding chart-pushed geodesic curve `γ : ℝ → M` such that:

* `Φ` is jointly `C^1` on `ball ((x₀, v_chart)) ρ ×ˢ Ioo (-T) T`, where
  `x₀ := extChartAt I p p`;
* the initial-value identity `Φ ((x₀, v_chart), 0) = (x₀, v_chart)` holds;
* the chart-pushed geodesic curve starts at `p`.

The interior assumption `x₀ ∈ interior (extChartAt I p).target` is the
defining condition for the chart-phase ODE to be smooth at the base
point; under `[I.Boundaryless]`, this follows from
`extChartAt_target_subset_interior_of_boundaryless` applied to
`x₀ = extChartAt I p p`. -/
theorem exists_chartFlowGeodesicCurve
    (g : SmoothRiemannianMetric I M) (p : M) (v_chart : E) :
    ∃ (ρ T : ℝ) (Φ : (E × E) × ℝ → E × E),
      0 < ρ ∧ 0 < T ∧
      ContDiffOn ℝ 1 Φ
        ((Metric.ball (((extChartAt I p p, v_chart)) : E × E) ρ) ×ˢ Set.Ioo (-T) T) ∧
      Φ (((extChartAt I p p, v_chart) : E × E), 0) = (extChartAt I p p, v_chart) ∧
      chartFlowGeodesicCurve (I := I) Φ p v_chart 0 = p := by
  set x₀ : E := extChartAt I p p with hx₀_def
  have hx₀_src : p ∈ (extChartAt I p).source :=
    mem_extChartAt_source (I := I) p
  have hx₀_target : x₀ ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hx₀_src
  have hx₀_interior : x₀ ∈ interior (extChartAt I p).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) p hx₀_target
  obtain ⟨_b, ρ, T, Φ, hρ_pos, hT_pos, _hb_sub, hcd, hinit⟩ :=
    exists_chartPhase_contDiffOn_isLocalFlow (I := I) (M := M)
      (g := g) (α := p) (x₀ := x₀) (v₀ := v_chart) hx₀_interior
  refine ⟨ρ, T, Φ, hρ_pos, hT_pos, hcd, hinit, ?_⟩
  exact chartFlowGeodesicCurve_zero (I := I) (Φ := Φ) (p := p) (v_chart := v_chart) hinit

end ChartFlowExistencePackaging

section OrbitODE

variable [I.Boundaryless] [CompleteSpace E]

/-- The chart-pushed flow orbit `t ↦ Φ((x₀, v_chart), t)` satisfies the
chart-phase geodesic ODE on the inner ball of the bump, expressed via
`HasDerivAt`. This is the input expected by `chartPhaseVF_orbit_uniqueness`.

We assume the orbit's values stay inside the inner ball over the open
interval `Ioo (-T) T` (this is enforced by working with the cutoff
field, which equals `chartPhaseVF` only on the inner ball; values
outside trivially yield the cutoff identity but not the genuine ODE).

Concretely, when `Φ` is `IsLocalFlow` of `chartPhaseVFTime ... b`, the
orbit through `z₀` satisfies the cutoff ODE on `Ioo (-ε) ε`. If the
orbit stays inside the inner ball `closedBall z₀ b.rIn` over `Ioo (-δ) δ`
(possibly smaller), then on `Ioo (-δ) δ` the orbit satisfies the
genuine chart-phase ODE. -/
theorem chartFlowOrbit_hasDerivAt_chartPhaseVF_of_isLocalFlow
    {g : SmoothRiemannianMetric I M} {α : M}
    {z₀ : E × E} {b : ContDiffBump z₀} {r : ℝ≥0} {ε : ℝ}
    {Φ : (E × E) × ℝ → E × E}
    (hΦ : DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow
        (chartPhaseVFTime (I := I) g α z₀ b) (0 : ℝ) z₀ r (-ε) ε Φ)
    (hz₀_ball : z₀ ∈ Metric.closedBall z₀ r) :
    ∀ t ∈ Set.Ioo (-ε) ε,
      HasDerivAt (fun s : ℝ => Φ (z₀, s))
        (chartPhaseVFCutoff (I := I) g α z₀ b (Φ (z₀, t))) t := by
  intro t ht
  have ht_icc : t ∈ Set.Icc (-ε) ε := Set.Ioo_subset_Icc_self ht
  have hd := hΦ.hasDerivWithinAt z₀ hz₀_ball t ht_icc
  have hIoo_nhds : Set.Ioo (-ε) ε ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
  have hIcc_mem : Set.Icc (-ε) ε ∈ 𝓝 t :=
    Filter.mem_of_superset hIoo_nhds Set.Ioo_subset_Icc_self
  have hVFTime_apply :
      chartPhaseVFTime (I := I) g α z₀ b t (Φ (z₀, t)) =
        chartPhaseVFCutoff (I := I) g α z₀ b (Φ (z₀, t)) := rfl
  rw [hVFTime_apply] at hd
  exact hd.hasDerivAt hIcc_mem

end OrbitODE

section ChartCoordBridge

variable [I.Boundaryless] [CompleteSpace E]

/-- **Chart-coordinate orbit uniqueness against the chart-pushed flow.**
For any `(p, v_chart)` with `x₀ := extChartAt I p p` in the chart-target
interior, and any other curve `c : ℝ → E × E` satisfying the chart-phase
geodesic ODE on a neighbourhood of `0` with `c 0 = (x₀, v_chart)` and
values inside the chart-target interior product, there exists a
chart-pushed flow `Φ` such that `c` and the flow orbit
`t ↦ Φ((x₀, v_chart), t)` agree on a neighbourhood of `0`. -/
theorem exists_chartFlow_orbit_eq_chartPhase_solution_eventually
    (g : SmoothRiemannianMetric I M) (p : M) (v_chart : E)
    {c : ℝ → E × E}
    (h0 : c 0 = ((extChartAt I p p, v_chart) : E × E))
    (hd : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt c (chartPhaseVF (I := I) g p (c t)) t ∧
        c t ∈ (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) :
    ∃ (Φ : (E × E) × ℝ → E × E),
      Φ (((extChartAt I p p, v_chart) : E × E), 0) =
        (extChartAt I p p, v_chart) ∧
      c =ᶠ[𝓝 (0 : ℝ)] (fun t => Φ (((extChartAt I p p, v_chart) : E × E), t)) := by
  classical
  set x₀ : E := extChartAt I p p with hx₀_def
  have hx₀_src : p ∈ (extChartAt I p).source :=
    mem_extChartAt_source (I := I) p
  have hx₀_target : x₀ ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hx₀_src
  have hx₀_interior : x₀ ∈ interior (extChartAt I p).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) p hx₀_target
  obtain ⟨b, r, ε, Φ, hr, hε, hb_sub, hΦ⟩ :=
    exists_chartPhase_isLocalFlow (I := I) (M := M)
      (g := g) (α := p) (x₀ := x₀) (v₀ := v_chart) hx₀_interior
  have hΦinit : Φ (((x₀, v_chart) : E × E), 0) = (x₀, v_chart) :=
    hΦ.apply_initial ((x₀, v_chart) : E × E)
      (Metric.mem_closedBall_self (by exact_mod_cast (le_of_lt hr)))
  refine ⟨Φ, hΦinit, ?_⟩
  set Φorbit : ℝ → E × E := fun t => Φ ((x₀, v_chart), t) with hΦorbit_def
  have hz₀_interior : ((x₀, v_chart) : E × E) ∈
      (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) :=
    ⟨hx₀_interior, Set.mem_univ _⟩
  have hΦorbit_zero : Φorbit 0 = (x₀, v_chart) := hΦinit
  have hc_zero : c 0 = (x₀, v_chart) := h0
  have hΦorbit_cont0 : ContinuousAt Φorbit 0 := by
    have hcont_on : ContinuousOn Φorbit (Set.Icc (-ε) ε) :=
      hΦ.orbit_continuousOn ((x₀, v_chart) : E × E)
        (Metric.mem_closedBall_self (by exact_mod_cast (le_of_lt hr)))
    have hIcc_nhds : Set.Icc (-ε) ε ∈ 𝓝 (0 : ℝ) := by
      have hIoo_nhds : Set.Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) :=
        isOpen_Ioo.mem_nhds ⟨by linarith, hε⟩
      exact Filter.mem_of_superset hIoo_nhds Set.Ioo_subset_Icc_self
    exact (hcont_on.continuousAt hIcc_nhds)
  have hΦorbit_inner_eventually : ∀ᶠ t in 𝓝 (0 : ℝ),
      Φorbit t ∈ Metric.closedBall ((x₀, v_chart) : E × E) b.rIn := by
    have hinner_nhds : Metric.closedBall ((x₀, v_chart) : E × E) b.rIn ∈
        𝓝 ((x₀, v_chart) : E × E) :=
      Metric.closedBall_mem_nhds _ b.rIn_pos
    exact hΦorbit_cont0.preimage_mem_nhds
      (by rw [hΦorbit_zero]; exact hinner_nhds)
  have hball_sub_chart : Metric.closedBall ((x₀, v_chart) : E × E) b.rIn ⊆
      (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    refine Subset.trans ?_ hb_sub
    exact Metric.closedBall_subset_closedBall (le_of_lt b.rIn_lt_rOut)
  have hΦorbit_deriv : ∀ t ∈ Set.Ioo (-ε) ε,
      HasDerivAt Φorbit
        (chartPhaseVFCutoff (I := I) g p (x₀, v_chart) b (Φorbit t)) t := by
    intro t ht
    exact chartFlowOrbit_hasDerivAt_chartPhaseVF_of_isLocalFlow
      (I := I) (g := g) (α := p) (z₀ := (x₀, v_chart)) (b := b) (r := r) (ε := ε)
      (Φ := Φ) hΦ (Metric.mem_closedBall_self (by
        exact_mod_cast (le_of_lt hr))) t ht
  have hΦorbit_deriv_ev : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt Φorbit
        (chartPhaseVF (I := I) g p (Φorbit t)) t ∧
        Φorbit t ∈ (interior (extChartAt I p).target) ×ˢ
          (Set.univ : Set E) := by
    have hIoo_nhds : Set.Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) :=
      isOpen_Ioo.mem_nhds ⟨by linarith, hε⟩
    filter_upwards [hΦorbit_inner_eventually, hIoo_nhds] with t htInner htIoo
    refine ⟨?_, hball_sub_chart htInner⟩
    have hcutoff_eq :
        chartPhaseVFCutoff (I := I) g p (x₀, v_chart) b (Φorbit t) =
        chartPhaseVF (I := I) g p (Φorbit t) :=
      chartPhaseVFCutoff_eq_of_mem_closedBall (I := I) g p (x₀, v_chart) b htInner
    have hd_cutoff : HasDerivAt Φorbit
        (chartPhaseVFCutoff (I := I) g p (x₀, v_chart) b (Φorbit t)) t :=
      hΦorbit_deriv t htIoo
    rw [hcutoff_eq] at hd_cutoff
    exact hd_cutoff
  exact chartPhaseVF_orbit_uniqueness (I := I) (g := g) (α := p)
    (c₁ := c) (c₂ := Φorbit) (z₀ := (x₀, v_chart))
    hz₀_interior hc_zero hΦorbit_zero hd hΦorbit_deriv_ev

end ChartCoordBridge

section ManifoldBridge

variable [I.Boundaryless] [CompleteSpace E]

/-- **Bridge consequence in manifold terms.** Any manifold curve
`γ : ℝ → M` whose chart-coordinate image
`u : ℝ → E, u t := extChartAt I p (γ t)` satisfies the chart-phase
position component of the geodesic ODE near `0`, paired with a velocity
curve `w : ℝ → E` satisfying the velocity-component ODE, with matching
initial values, agrees with the chart-pushed flow's projection on a
neighbourhood of `0`. -/
theorem chartFlowGeodesicCurve_eq_of_chartPhase_solution_eventually
    (g : SmoothRiemannianMetric I M) (p : M) (v_chart : E)
    {γ : ℝ → M}
    (hγ_chart_eventually : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ (extChartAt I p).source)
    {w : ℝ → E}
    (hu0 : extChartAt I p (γ 0) = extChartAt I p p)
    (hw0 : w 0 = v_chart)
    (hd : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (fun s => ((extChartAt I p (γ s), w s) : E × E))
        (chartPhaseVF (I := I) g p (extChartAt I p (γ t), w t)) t ∧
      ((extChartAt I p (γ t), w t) : E × E) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) :
    ∃ (Φ : (E × E) × ℝ → E × E),
      Φ (((extChartAt I p p, v_chart) : E × E), 0) =
        (extChartAt I p p, v_chart) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ),
        γ t = chartFlowGeodesicCurve (I := I) Φ p v_chart t) := by
  classical
  have hc0 : ((extChartAt I p (γ 0), w 0) : E × E) =
      (extChartAt I p p, v_chart) := by
    rw [hu0, hw0]
  obtain ⟨Φ, hΦ_init, hc_eq_orbit⟩ :=
    exists_chartFlow_orbit_eq_chartPhase_solution_eventually
      (I := I) (g := g) (p := p) (v_chart := v_chart)
      (c := fun s => (extChartAt I p (γ s), w s)) hc0 hd
  refine ⟨Φ, hΦ_init, ?_⟩
  filter_upwards [hc_eq_orbit, hγ_chart_eventually] with t ht_eq ht_src
  have ht_eq_fst :
      extChartAt I p (γ t) = (Φ (((extChartAt I p p, v_chart) : E × E), t)).1 := by
    have := congrArg Prod.fst ht_eq
    exact this
  have hγ_recover : (extChartAt I p).symm (extChartAt I p (γ t)) = γ t :=
    (extChartAt I p).left_inv ht_src
  rw [← hγ_recover, ht_eq_fst]
  rfl

/-- The **bridge headline** in a packaged existence form: there exist a
chart-pushed flow `Φ` and an open interval around `0` on which the
chart-pushed flow's projection (`chartFlowGeodesicCurve Φ p v_chart`)
agrees with **any** witness curve whose chart-coordinate form satisfies
the chart-phase ODE with matching initial value.

This is the chart-coordinate identification step of the bridge. The
final identification with `maximalGeodesic g p v` requires constructing
the chart-coordinate companion `w : ℝ → E` from the maximal-geodesic
lift's fibre component, which is the standalone TM-lift construction
step packaged as `maximalGeodesicChosenCurve_chartPushLift_hasDerivAt`
in the chart-pushed lift module. The combined identification then
chains chart-coordinate uniqueness (above) with the maximal-geodesic
witness selection, yielding the headline statement
`chartPushedFlow_eq_maximalGeodesic` modulo the explicit construction
of the chart-coordinate velocity companion from the witness lift. -/
@[simp] theorem chartFlowGeodesicCurve_zero_velocity_eq_const
    (p : M) {Φ : (E × E) × ℝ → E × E}
    (hinit : Φ (((extChartAt I p p, (0 : E)) : E × E), 0) =
      (extChartAt I p p, (0 : E))) :
    chartFlowGeodesicCurve (I := I) Φ p (0 : E) 0 = p :=
  chartFlowGeodesicCurve_zero (I := I) hinit

end ManifoldBridge

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
