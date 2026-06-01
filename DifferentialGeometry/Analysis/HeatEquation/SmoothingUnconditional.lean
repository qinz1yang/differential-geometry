import DifferentialGeometry.Analysis.HeatEquation.SmoothingBridge
import DifferentialGeometry.Analysis.HeatEquation.HeatSemigroupIteratedDomain
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartPushed.SideH2kBridge

/-!
# Truly unconditional smoothing of the heat semigroup

For a closed Riemannian manifold `(M, g)` modelled on a finite-dimensional real
inner-product space `E` with `n := finrank ℝ E ≥ 1`, given an initial datum
`u_0 ∈ Lp ℝ 2 μ_g` and a positive time `t > 0`, the `Lp` element
`heatSemigroup g t u_0` is a.e.-equal to a smooth function `u_smooth : M → ℝ`
of class `C^∞`. This is the truly unconditional smoothing endpoint of the heat
semigroup on a closed Riemannian manifold: no auxiliary regularity hypothesis
appears in the theorem statement.

## Composition

The proof composes three ingredients:

1. `heatSemigroup_smooth_representative_of_chartSideBridges` — the
   bridge-form spatial smoothing of the heat semigroup, which reduces the
   `C^∞`-representative production to the chart-side `H^{2k}` bridge family
   on the canonical function representative of `heatSemigroup g t u_0`.
2. `heatSemigroup_mem_laplacianDomainPow_all` — for every `k : ℕ`, the
   heat-evolved `Lp` element admits an `H1Compl g` lift
   `u_h ∈ laplacianDomainPow g k` with `H1ComplToLp g u_h = heatSemigroup g t u_0`.
3. `chartSideH2kBridge_of_laplacianDomainPow_unconditional` — for every `k`
   and every `u_h ∈ laplacianDomainPow g k`, the chart-side `H^{2k}` bridge
   for the canonical function representative `(H1ComplToLp g u_h).coeFn` holds
   unconditionally.

Combining (2) and (3) yields the chart-side bridge family on the canonical
function representative of `heatSemigroup g t u_0` for every `k`, which (1)
turns into the `C^∞`-representative.

## Main results

* `heatSemigroup_smooth_representative_of_closed` — for every `t > 0`,
  `heatSemigroup g t u_0` admits a `C^∞` a.e.-representative.
* `heatSemigroup_smooth_in_space_and_time_unconditional` — the combined
  endpoint: a `C^∞` spatial representative at every `t > 0`, together with
  `C^∞ ((0, ∞); Lp)` time regularity.

## Sign convention

Geometer convention `Δ_g = div_g ∘ grad_g`. The resolvent is `(1 - Δ_g)⁻¹`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace HeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge
open DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Unconditional chart-side `H^{2k}` bridge for the heat output.**

For a closed Riemannian manifold `(M, g)`, `t > 0`, `u_0 ∈ Lp ℝ 2 μ_g`, and
every `k : ℕ`, the chart-side `H^{2k}` bridge holds for the canonical
function representative of `heatSemigroup g t u_0`, unconditionally. -/
theorem chartSideH2kBridge_heat_unconditional
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (k : ℕ) :
    ChartSideH2kBridge (I := I) (M := M) g k
      (((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  obtain ⟨u_h, hu_h_mem, hu_h_eq⟩ :=
    heatSemigroup_mem_laplacianDomainPow_all
      (I := I) (M := M) g ht u_0 k
  have h_bridge_lift :=
    chartSideH2kBridge_of_laplacianDomainPow_unconditional
      (I := I) (M := M) g k hu_h_mem
  have h_coe : ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =
      ((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
    rw [hu_h_eq]
  rw [h_coe] at h_bridge_lift
  exact h_bridge_lift

/-- **Smoothing of the heat semigroup on a closed manifold**.

For a closed Riemannian manifold `(M, g)`, `t > 0`, and any initial datum
`u_0 ∈ Lp ℝ 2 μ_g`, the `Lp` element `heatSemigroup g t u_0` is a.e.-equal
to a smooth function `u_smooth : M → ℝ` of class `C^∞`. No regularity
hypothesis on `u_0` is required.

The proof feeds the chart-side bridge family `chartSideH2kBridge_heat_unconditional`
into the bridge-form smoothing theorem
`heatSemigroup_smooth_representative_of_chartSideBridges`. -/
theorem heatSemigroup_smooth_representative_of_closed
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∃ u_smooth : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ u_smooth ∧
      ((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g] u_smooth := by
  apply heatSemigroup_smooth_representative_of_chartSideBridges
    (I := I) (M := M) g ht u_0
  intro k
  exact chartSideH2kBridge_heat_unconditional
    (I := I) (M := M) g ht u_0 k

/-- **Truly unconditional combined space-time smoothing endpoint of the
heat semigroup**.

For a closed Riemannian manifold `(M, g)` and any initial datum
`u_0 ∈ Lp ℝ 2 μ_g`:

* for every `t > 0`, `heatSemigroup g t u_0` admits a smooth a.e.-representative;
* the map `t ↦ heatSemigroup g t u_0` is `C^∞ ((0, ∞); Lp)`.

No regularity hypothesis on `u_0` is required. -/
theorem heatSemigroup_smooth_in_space_and_time_unconditional
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    (∀ t : ℝ, 0 < t →
      ∃ u_smooth_t : M → ℝ,
        ContMDiff I 𝓘(ℝ, ℝ) ∞ u_smooth_t ∧
        ((heatSemigroup (I := I) (M := M) g t u_0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
            riemannianVolumeMeasure (I := I) (M := M) g] u_smooth_t) ∧
    ContDiffOn ℝ ∞
      (fun t : ℝ =>
        (heatSemigroup (I := I) (M := M) g t u_0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)))
      (Set.Ioi (0 : ℝ)) := by
  apply heatSemigroup_smooth_in_space_and_time_of_chartSideBridges
    (I := I) (M := M) g u_0
  intro t ht k
  exact chartSideH2kBridge_heat_unconditional
    (I := I) (M := M) g ht u_0 k

end HeatEquation
end Analysis
end DifferentialGeometry

end
