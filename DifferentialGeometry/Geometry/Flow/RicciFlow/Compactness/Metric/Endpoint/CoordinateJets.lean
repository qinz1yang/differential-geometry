import DifferentialGeometry.Analysis.Calculus.Compactness.SmoothLimits
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.Christoffel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic

set_option autoImplicit false

noncomputable section

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
