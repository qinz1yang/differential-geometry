import DifferentialGeometry.Analysis.Calculus.Compactness.SmoothMap
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Composition
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.Christoffel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Topology
open scoped ContDiff

section LocalIdentification

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem mapCInfConvergenceOnCompacts_of_pointwise_of_local_jet_bounds
    {U : Set E} (hU : IsOpen U) (f : ℕ → E → F) (f₀ : E → F)
    (hf : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (f k) U)
    (hbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ k : ℕ, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (f k) x‖ ≤ C)
    (hpoint : ∀ x ∈ U, Tendsto (fun k => f k x) atTop (𝓝 (f₀ x))) :
    MapCInfConvergenceOnCompacts U f f₀ := by
  classical
  intro K hK hKU p ε hε
  by_contra hbad
  push Not at hbad
  choose k hk hbad using hbad
  choose r hr hbad using hbad
  choose x hx hbad using hbad
  have hkTop : Tendsto k atTop atTop := tendsto_atTop_mono hk tendsto_id
  obtain ⟨σ, fLimit, hσ, _, hconv⟩ := exists_cInf_subseq_on hU
    (fun n => f (k n)) (fun n => hf (k n)) (by
      intro j C hC hCU
      obtain ⟨B, hB⟩ := hbdd j C hC hCU
      exact ⟨B, fun n y hy => hB (k n) y hy⟩)
  have heq : Set.EqOn f₀ fLimit U := by
    intro y hy
    have hto₀ := (hpoint y hy).comp (hkTop.comp hσ.tendsto_atTop)
    have htoLimit := (tendstoUniformlyOn_of_cPConvergence
      (hconv {y} isCompact_singleton (Set.singleton_subset_iff.mpr hy) 0)).tendsto_at
        (Set.mem_singleton y)
    exact tendsto_nhds_unique hto₀ htoLimit
  have hconv₀ : MapCInfConvergenceOnCompacts U (fun n => f (k (σ n))) f₀ :=
    hconv.congr hU (fun _ _ _ => rfl) heq
  obtain ⟨N, hN⟩ := hconv₀ K hK hKU p ε hε
  exact not_lt_of_ge
    (hN N le_rfl (r (σ N)) (hr (σ N)) (x (σ N)) (hx (σ N))) (hbad (σ N))

theorem iteratedFDeriv_norm_le_of_pointwise_of_local_jet_bounds
    {U : Set E} (hU : IsOpen U) (f : ℕ → E → F) (f₀ : E → F)
    (hf : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (f k) U)
    (hf₀ : ContDiffOn ℝ (∞ : WithTop ℕ∞) f₀ U)
    (hbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ k : ℕ, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (f k) x‖ ≤ C)
    (hpoint : ∀ x ∈ U, Tendsto (fun k => f k x) atTop (𝓝 (f₀ x)))
    (r : ℕ) {x : E} (hx : x ∈ U) {C : ℝ}
    (hC : ∀ᶠ k in atTop, ‖iteratedFDeriv ℝ r (f k) x‖ ≤ C) :
    ‖iteratedFDeriv ℝ r f₀ x‖ ≤ C := by
  have hconv := mapCInfConvergenceOnCompacts_of_pointwise_of_local_jet_bounds
    hU f f₀ hf hbdd hpoint
  have hjet := (hconv.tendstoUniformlyOn_iteratedFDeriv hU isCompact_singleton
    (Set.singleton_subset_iff.mpr hx) hf hf₀ r).tendsto_at (Set.mem_singleton x)
  exact le_of_tendsto hjet.norm hC

end LocalIdentification

end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Topology
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

local instance terminalCoordinateJetsC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

omit [CompleteSpace E] [T2Space M] in
private theorem terminalCoordinate_metric_component_smooth
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := ℝ) E) {U : Set E}
    (hU : U ⊆ (extChartAt I x₀).target) :
    ContDiffOn ℝ (∞ : WithTop ℕ∞)
      (metricFlatModelInChartComponent (I := I) g x₀ i j) U := by
  intro y hy
  have h := metricFlatModelInChart_component_contDiffWithinAt_of_mem
    (I := I) g x₀ (hU hy) i j
  rw [ModelWithCorners.range_eq_univ (I := I)] at h
  exact (contDiffWithinAt_univ.mp h).contDiffWithinAt

theorem solution_metric_coordinates_cInf_at_carrier_time
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {τ : ℝ} (hτ : τ ∈ D.carrier)
    (t : ℕ → ℝ) (ht : ∀ k, t k ∈ D.carrier) (htτ : Tendsto t atTop (𝓝 τ))
    (x₀ : M) (i j : CoordinateIdx (𝕜 := ℝ) E)
    {U : Set E} (hU : IsOpen U) (hchart : U ⊆ (extChartAt I x₀).target)
    (hbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ k : ℕ, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ r
          (metricFlatModelInChartComponent (I := I) (S.base.metric (t k)) x₀ i j) y‖ ≤ C) :
    MapCInfConvergenceOnCompacts U
      (fun k => metricFlatModelInChartComponent (I := I) (S.base.metric (t k)) x₀ i j)
      (metricFlatModelInChartComponent (I := I) (S.base.metric τ) x₀ i j) := by
  refine mapCInfConvergenceOnCompacts_of_pointwise_of_local_jet_bounds hU _ _
    (fun k => terminalCoordinate_metric_component_smooth
      (S.base.metric (t k)) x₀ i j hchart) hbdd ?_
  intro y hy
  let p := (extChartAt I x₀).symm y
  let v := (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ p
    ((Module.finBasis ℝ E) i)
  let w := (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ p
    ((Module.finBasis ℝ E) j)
  have htime : Tendsto t atTop (𝓝[D.carrier] τ) :=
    tendsto_nhdsWithin_iff.mpr ⟨htτ, Filter.Eventually.of_forall ht⟩
  have hinner := (hS.smoothMetric.coeff_cont p v w τ hτ).tendsto.comp htime
  have heq : ∀ s : ℝ,
      metricFlatModelInChartComponent (I := I) (S.base.metric s) x₀ i j y =
        (S.base.metric s).inner p v w := by
    intro s
    exact Geometry.Connection.metricFlatModelInChart_apply_of_target
      (I := I) (S.base.metric s) x₀
      (hchart hy) ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) j)
  simp_rw [heq]
  exact hinner

theorem solution_metric_coordinate_jet_bound_at_carrier_time
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {τ : ℝ} (hτ : τ ∈ D.carrier)
    (t : ℕ → ℝ) (ht : ∀ k, t k ∈ D.carrier) (htτ : Tendsto t atTop (𝓝 τ))
    (x₀ : M) (i j : CoordinateIdx (𝕜 := ℝ) E)
    {U : Set E} (hU : IsOpen U) (hchart : U ⊆ (extChartAt I x₀).target)
    (hbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ k : ℕ, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ r
          (metricFlatModelInChartComponent (I := I) (S.base.metric (t k)) x₀ i j) y‖ ≤ C)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (r : ℕ) {C : ℝ}
    (hC : ∀ᶠ k in atTop, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ r
        (metricFlatModelInChartComponent (I := I) (S.base.metric (t k)) x₀ i j) y‖ ≤ C) :
    ∀ y ∈ K, ‖iteratedFDeriv ℝ r
      (metricFlatModelInChartComponent (I := I) (S.base.metric τ) x₀ i j) y‖ ≤ C := by
  have hconv := solution_metric_coordinates_cInf_at_carrier_time S hS hτ t ht htτ
    x₀ i j hU hchart hbdd
  have hjet := hconv.tendstoUniformlyOn_iteratedFDeriv hU hK hKU
    (fun k => terminalCoordinate_metric_component_smooth
      (S.base.metric (t k)) x₀ i j hchart)
    (terminalCoordinate_metric_component_smooth (S.base.metric τ) x₀ i j hchart) r
  intro y hy
  exact le_of_tendsto (hjet.tendsto_at hy).norm (hC.mono fun k hk => hk y hy)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
