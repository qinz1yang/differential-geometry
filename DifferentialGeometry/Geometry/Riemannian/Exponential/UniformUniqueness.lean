import DifferentialGeometry.Geometry.Riemannian.Exponential.Bridge
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

set_option linter.unusedSectionVars false

/-!
# Uniform-in-parameter chart-coordinate ODE uniqueness on `Ioo (-T) T`

The eventually-equal form `chartPhaseVF_orbit_uniqueness` (from `Bridge.lean`)
gives ODE uniqueness on a neighbourhood of `0` whose size depends on the
input curves. For a uniform-in-parameter statement — agreement on a
**fixed** open interval `Ioo (-T) T` — we need an explicit Lipschitz
constant for the chart-coordinate phase-space vector field on a compact
spatial set `K`, then a single application of Mathlib's
`ODE_solution_unique_of_mem_Ioo`.

## Strategy

1. `chartPhaseVF g α` is `C^∞` on the open product
   `interior (extChartAt I α).target ×ˢ univ` (from
   `chartPhaseVF_contDiffOn`), hence locally Lipschitz at every point of
   that open product.

2. For any compact `K` contained in that open product, `chartPhaseVF g α`
   is locally Lipschitz on `K`. By
   `LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`, there is a
   global Lipschitz constant `L` such that
   `LipschitzOnWith L (chartPhaseVF g α) K`.

3. Apply `ODE_solution_unique_of_mem_Ioo` with that constant, the
   constant set function `s t := K`, and the constant vector field
   `v t := chartPhaseVF g α`.

## Main result

* `chartPhaseVF_orbit_uniqueness_uniform_Ioo` — if two parameterised
  chart-phase ODE solutions agree at `0` and both stay in a compact set
  `K ⊆ interior (extChartAt I α).target ×ˢ univ` throughout
  `Ioo (-T) T`, then they agree on all of `Ioo (-T) T`.

## Supporting lemmas

* `chartPhaseVF_locallyLipschitzOn_of_compact` — `chartPhaseVF g α` is
  locally Lipschitz on any compact subset of the chart-target interior
  product.

* `chartPhaseVF_lipschitzOnWith_of_compact` — `chartPhaseVF g α` is
  globally Lipschitz on any such compact subset, with an existential
  Lipschitz constant.
-/

noncomputable section

open Set Function Filter Metric
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
open DifferentialGeometry.Geometry.Riemannian.Geodesic

section LipschitzOnCompact

variable [I.Boundaryless]

/-- **Local Lipschitz property at a point of the chart-target interior product.**
At any point `z` of `interior (extChartAt I α).target ×ˢ univ`, the chart-
phase vector field `chartPhaseVF g α` is Lipschitz on a (full) neighbourhood
of `z`. This is a direct consequence of `ContDiffAt.exists_lipschitzOnWith`
applied to the `C^∞` regularity provided by `chartPhaseVF_contDiffOn`. -/
lemma chartPhaseVF_exists_lipschitzOnWith_at
    (g : SmoothRiemannianMetric I M) (α : M)
    {z : E × E} (hz : z ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :
    ∃ L : ℝ≥0, ∃ t ∈ 𝓝 z, LipschitzOnWith L (chartPhaseVF (I := I) g α) t := by
  have hC1 : ContDiffOn ℝ 1 (chartPhaseVF (I := I) g α)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :=
    (chartPhaseVF_contDiffOn (I := I) g α).of_le
      (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have hopen : IsOpen ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :=
    isOpen_interior.prod isOpen_univ
  have hC1_at : ContDiffAt ℝ 1 (chartPhaseVF (I := I) g α) z :=
    hC1.contDiffAt (hopen.mem_nhds hz)
  exact hC1_at.exists_lipschitzOnWith

/-- **Local Lipschitz property on a compact subset of the chart-target interior
product.** If `K` is contained in the open set
`interior (extChartAt I α).target ×ˢ univ`, then `chartPhaseVF g α`
is locally Lipschitz on `K` (in the sense of
`LocallyLipschitzOn`). The neighbourhoods produced are full
neighbourhoods (not within `K`), which trivially induce within-`K`
neighbourhoods. -/
lemma chartPhaseVF_locallyLipschitzOn_of_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set (E × E)}
    (hK_subset : K ⊆ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :
    LocallyLipschitzOn K (chartPhaseVF (I := I) g α) := by
  intro z hz
  obtain ⟨L, t, ht, hL⟩ :=
    chartPhaseVF_exists_lipschitzOnWith_at (I := I) g α (hK_subset hz)
  refine ⟨L, t, ?_, hL⟩
  exact mem_nhdsWithin_of_mem_nhds ht

/-- **Existence of a global Lipschitz constant on a compact spatial set.**
If `K ⊆ interior (extChartAt I α).target ×ˢ univ` is compact, then there
exists a single Lipschitz constant `L` such that `chartPhaseVF g α` is
`L`-Lipschitz on `K`. -/
theorem chartPhaseVF_lipschitzOnWith_of_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set (E × E)}
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :
    ∃ L : ℝ≥0, LipschitzOnWith L (chartPhaseVF (I := I) g α) K :=
  (chartPhaseVF_locallyLipschitzOn_of_compact (I := I) g α
    hK_subset).exists_lipschitzOnWith_of_compact hK_compact

end LipschitzOnCompact

section UniformUniqueness

variable [I.Boundaryless]

/-- **Uniform-in-parameter chart-coordinate ODE uniqueness on
`Ioo (-T) T`.** If two curves `c₁, c₂ : ℝ → E × E` satisfy the chart-phase
geodesic ODE on the open interval `Ioo (-T) T`, take values inside a
compact set `K ⊆ interior (extChartAt I α).target ×ˢ univ`, and agree at
`0`, then they agree on the **entire** open interval `Ioo (-T) T`.

This is the **uniform** form needed for parameter families: the
agreement interval `Ioo (-T) T` is fixed independently of the curves,
and depends only on the compact set `K` and the time horizon `T`. -/
theorem chartPhaseVF_orbit_uniqueness_uniform_Ioo
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set (E × E)}
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E))
    {T : ℝ} (hT_pos : 0 < T)
    {c₁ c₂ : ℝ → E × E}
    (hc₁_hasDeriv : ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt c₁ (chartPhaseVF (I := I) g α (c₁ s)) s)
    (hc₂_hasDeriv : ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt c₂ (chartPhaseVF (I := I) g α (c₂ s)) s)
    (hc₁_in_K : ∀ s ∈ Set.Ioo (-T) T, c₁ s ∈ K)
    (hc₂_in_K : ∀ s ∈ Set.Ioo (-T) T, c₂ s ∈ K)
    (h_eq_at_zero : c₁ 0 = c₂ 0) :
    ∀ s ∈ Set.Ioo (-T) T, c₁ s = c₂ s := by
  obtain ⟨L, hLip⟩ :=
    chartPhaseVF_lipschitzOnWith_of_compact (I := I) g α hK_compact hK_subset
  set v : ℝ → (E × E) → E × E := fun _ z => chartPhaseVF (I := I) g α z with hv_def
  set sSet : ℝ → Set (E × E) := fun _ => K with hsSet_def
  have hv_lip : ∀ t ∈ Set.Ioo (-T) T, LipschitzOnWith L (v t) (sSet t) := by
    intro t _
    exact hLip
  have h0_in : (0 : ℝ) ∈ Set.Ioo (-T) T :=
    ⟨by linarith, hT_pos⟩
  have hf : ∀ t ∈ Set.Ioo (-T) T,
      HasDerivAt c₁ (v t (c₁ t)) t ∧ c₁ t ∈ sSet t := by
    intro t ht
    exact ⟨hc₁_hasDeriv t ht, hc₁_in_K t ht⟩
  have hg : ∀ t ∈ Set.Ioo (-T) T,
      HasDerivAt c₂ (v t (c₂ t)) t ∧ c₂ t ∈ sSet t := by
    intro t ht
    exact ⟨hc₂_hasDeriv t ht, hc₂_in_K t ht⟩
  have hEqOn : Set.EqOn c₁ c₂ (Set.Ioo (-T) T) :=
    ODE_solution_unique_of_mem_Ioo (v := v) (s := sSet) (K := L) (t₀ := 0)
      (a := -T) (b := T) hv_lip h0_in hf hg h_eq_at_zero
  intro s hs
  exact hEqOn hs

end UniformUniqueness

section UniformAgainstFlow

variable [I.Boundaryless]

/-- **Uniform agreement of a chart-phase solution with the chart-pushed
flow orbit on `Ioo (-T) T`.** If `c : ℝ → E × E` and the orbit
`t ↦ Φ((x₀, v_chart), t)` both satisfy the chart-phase ODE on
`Ioo (-T) T`, match at `0`, and stay in a compact set `K` contained in
the chart-target interior product, then they agree on `Ioo (-T) T`. -/
theorem chartPhaseVF_solution_eq_chartFlowOrbit_on_Ioo
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set (E × E)}
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E))
    {T : ℝ} (hT_pos : 0 < T)
    {c : ℝ → E × E} {Φ : (E × E) × ℝ → E × E} {z₀ : E × E}
    (hc_hasDeriv : ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt c (chartPhaseVF (I := I) g α (c s)) s)
    (hΦ_hasDeriv : ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt (fun τ => Φ (z₀, τ))
        (chartPhaseVF (I := I) g α (Φ (z₀, s))) s)
    (hc_in_K : ∀ s ∈ Set.Ioo (-T) T, c s ∈ K)
    (hΦ_in_K : ∀ s ∈ Set.Ioo (-T) T, Φ (z₀, s) ∈ K)
    (h_eq_at_zero : c 0 = Φ (z₀, 0)) :
    ∀ s ∈ Set.Ioo (-T) T, c s = Φ (z₀, s) := by
  exact chartPhaseVF_orbit_uniqueness_uniform_Ioo (I := I) g α
    hK_compact hK_subset hT_pos
    (c₁ := c) (c₂ := fun τ => Φ (z₀, τ))
    hc_hasDeriv hΦ_hasDeriv hc_in_K hΦ_in_K h_eq_at_zero

end UniformAgainstFlow

section UniformOnClosedBall

variable [I.Boundaryless]

/-- **Uniform-in-parameter ODE uniqueness on a closed ball.** Specialised
form of `chartPhaseVF_orbit_uniqueness_uniform_Ioo` with `K` taken to be
a closed metric ball around a base point `z₀` whose closed ball is
contained in the chart-target interior product. -/
theorem chartPhaseVF_orbit_uniqueness_uniform_Ioo_closedBall
    (g : SmoothRiemannianMetric I M) (α : M)
    {z₀ : E × E} {r : ℝ}
    (hr_subset : Metric.closedBall z₀ r ⊆
      (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E))
    {T : ℝ} (hT_pos : 0 < T)
    {c₁ c₂ : ℝ → E × E}
    (hc₁_hasDeriv : ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt c₁ (chartPhaseVF (I := I) g α (c₁ s)) s)
    (hc₂_hasDeriv : ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt c₂ (chartPhaseVF (I := I) g α (c₂ s)) s)
    (hc₁_in_ball : ∀ s ∈ Set.Ioo (-T) T, c₁ s ∈ Metric.closedBall z₀ r)
    (hc₂_in_ball : ∀ s ∈ Set.Ioo (-T) T, c₂ s ∈ Metric.closedBall z₀ r)
    (h_eq_at_zero : c₁ 0 = c₂ 0) :
    ∀ s ∈ Set.Ioo (-T) T, c₁ s = c₂ s :=
  chartPhaseVF_orbit_uniqueness_uniform_Ioo (I := I) g α
    (K := Metric.closedBall z₀ r)
    (isCompact_closedBall _ _) hr_subset hT_pos
    hc₁_hasDeriv hc₂_hasDeriv hc₁_in_ball hc₂_in_ball h_eq_at_zero

end UniformOnClosedBall

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
