import DifferentialGeometry.Analysis.HeatEquation.Smoothing
import DifferentialGeometry.Analysis.HeatEquation.HeatSemigroupIteratedDomain
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.PowH2kBridge

/-!
# Bridge-driven smoothing of the heat semigroup

For a closed Riemannian manifold `(M, g)` modelled on a finite-dimensional real
inner-product space `E` with `n := finrank ℝ E ≥ 1`, given an initial datum
`u_0 ∈ Lp ℝ 2 μ_g` and a positive time `t > 0`, this file re-expresses the
smoothing property of the heat semigroup in terms of the chart-side
`H^{2k}` bridge hypothesis `ChartSideH2kBridge` from
`Laplacian/Regularity/LaplacianDomainPowH2kBridge.lean`.

The iterated-regularity hypothesis exposed by
`heatSemigroup_smooth_representative` is the manifold-level chart-Sobolev
predicate `MemWkpChart g (2k) 2`. The chart-side bridge `ChartSideH2kBridge`
is the corresponding per-chart `MemWkp (2k) 2` membership of the POU-cut
chart-pushed function (under the canonical atlas POU). By the unfolding
already given in `LaplacianDomainPowH2kBridge.memWkpChart_2k_of_chartSideH2kBridge`,
the two are equivalent for the same `u : M → ℝ`. We package this here as
the public bridge-form smoothing theorem.

## Connection to `laplacianDomainPow g k`

For every `k`, by `heatSemigroup_mem_laplacianDomainPow_all`, the heat-evolved
`Lp` element admits an `H1Compl g` lift `u_h_k ∈ laplacianDomainPow g k` with
`H1ComplToLp g u_h_k = heatSemigroup g t u_0`. Thus the canonical function
representatives `((H1ComplToLp u_h_k) : M → ℝ)` and `((heatSemigroup g t u_0) : M → ℝ)`
agree a.e., which means the chart-side bridge for the heat representative
also yields the chart-side bridge for each lift `u_h_k`. Consequently, the
bridge hypothesis stated for `((heatSemigroup g t u_0) : M → ℝ)` is the
correct chart-side packaging of iterated elliptic regularity at all orders.

## Main results

* `chartSideH2kBridge_iff_memWkpChart_two_k` — the equivalence
  `ChartSideH2kBridge g k u ↔ MemWkpChart g (2k) 2 u`.
* `heatSemigroup_smooth_representative_of_chartSideBridges` — bridge-form
  spatial smoothing.
* `heatSemigroup_smooth_in_space_and_time_of_chartSideBridges` — combined
  bridge-form space-time endpoint.

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

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- **`ChartSideH2kBridge g k u ↔ MemWkpChart g (2k) 2 u`.**

The chart-side `H^{2k}` bridge hypothesis is exactly the manifold-level
chart-Sobolev `(2k, 2)`-membership predicate. Both unfold to the same
per-chart `MemWkp (2k) 2` quantification under the canonical atlas
partition of unity. -/
theorem chartSideH2kBridge_iff_memWkpChart_two_k
    (g : SmoothRiemannianMetric I M) (k : ℕ) (u : M → ℝ) :
    ChartSideH2kBridge (I := I) (M := M) g k u ↔
      MemWkpChart (I := I) (M := M) g (2 * k) 2 u := by
  refine ⟨fun h => memWkpChart_2k_of_chartSideH2kBridge
    (I := I) (M := M) g k h, fun h => ?_⟩
  intro α
  exact h α

/-- **Bridge-form smoothing of the heat semigroup**.

For a closed Riemannian manifold `(M, g)`, `t > 0`, and `u_0 ∈ Lp ℝ 2 μ_g`,
given the chart-side `H^{2k}` bridge for every `k : ℕ` on the `Lp`-coercion
of `heatSemigroup g t u_0`, the `Lp` element admits a `C^∞`
a.e.-representative.

This is a wrapper around `heatSemigroup_smooth_representative` rephrased
on the chart-side bridge: by `chartSideH2kBridge_iff_memWkpChart_two_k`,
the family of bridges is exactly the family of chart-Sobolev memberships
`MemWkpChart g (2k) 2`. -/
theorem heatSemigroup_smooth_representative_of_chartSideBridges
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (h_bridges : ∀ k : ℕ,
      ChartSideH2kBridge (I := I) (M := M) g k
        (((heatSemigroup (I := I) (M := M) g t u_0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    ∃ u_smooth : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ u_smooth ∧
      ((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g] u_smooth := by
  have h_iterated_regularity : ∀ k : ℕ,
      MemWkpChart (I := I) (M := M) g (2 * k) 2
        (((heatSemigroup (I := I) (M := M) g t u_0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
    intro k
    exact (chartSideH2kBridge_iff_memWkpChart_two_k
      (I := I) (M := M) g k _).mp (h_bridges k)
  exact heatSemigroup_smooth_representative (I := I) (M := M) g ht u_0
    h_iterated_regularity

/-- **Bridge-form combined space-time smoothing endpoint of the heat
semigroup**.

For every `t > 0`, given the chart-side `H^{2k}` bridge for every `k`
uniformly in `t`, the `Lp` element `heatSemigroup g t u_0` is a.e.-equal
to a smooth spatial function. Simultaneously, the map
`t ↦ heatSemigroup g t u_0` is `C^∞ ((0, ∞); Lp)`. -/
theorem heatSemigroup_smooth_in_space_and_time_of_chartSideBridges
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (h_bridges_uniform :
      ∀ t : ℝ, 0 < t → ∀ k : ℕ,
        ChartSideH2kBridge (I := I) (M := M) g k
          (((heatSemigroup (I := I) (M := M) g t u_0 :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
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
  refine ⟨?_, ?_⟩
  · intro t ht
    exact heatSemigroup_smooth_representative_of_chartSideBridges
      (I := I) (M := M) g ht u_0 (h_bridges_uniform t ht)
  · exact heatSemigroup_contMDiff_in_time (I := I) (M := M) g u_0

/-- **Documentation lemma**: the chart-side bridge on the heat representative
implies a uniform-`k` family of bridges on the canonical function representatives
of the `H1Compl` lifts `u_h_k ∈ laplacianDomainPow g k`. -/
theorem chartSideH2kBridge_heat_implies_chartSideH2kBridge_lifts
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (h_bridges : ∀ k : ℕ,
      ChartSideH2kBridge (I := I) (M := M) g k
        (((heatSemigroup (I := I) (M := M) g t u_0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    ∀ k : ℕ, ∃ u_h : H1Compl (I := I) (M := M) g,
      u_h ∈ laplacianDomainPow (I := I) (M := M) g k ∧
        H1ComplToLp (I := I) (M := M) g u_h =
          heatSemigroup (I := I) (M := M) g t u_0 ∧
        ChartSideH2kBridge (I := I) (M := M) g k
          (((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  intro k
  obtain ⟨u_h, hu_h_mem, hu_h_eq⟩ :=
    heatSemigroup_mem_laplacianDomainPow_all (I := I) (M := M) g ht u_0 k
  refine ⟨u_h, hu_h_mem, hu_h_eq, ?_⟩
  have h_coe : ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =
      ((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
    rw [hu_h_eq]
  rw [h_coe]
  exact h_bridges k

/-- **Documentation lemma**: bridge-driven chart-Sobolev `H^{2k}` regularity
for the canonical function representative of every lift
`u_h ∈ laplacianDomainPow g k` of `heatSemigroup g t u_0`.

This explicitly connects the chart-side bridge on the heat output to the
manifold-level `MemWkpChart g (2k) 2` regularity at the `H1Compl`-lift level. -/
theorem laplacianDomainPow_memWkpChart_2k_of_chartSideBridges_heat
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (h_bridges : ∀ k : ℕ,
      ChartSideH2kBridge (I := I) (M := M) g k
        (((heatSemigroup (I := I) (M := M) g t u_0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    ∀ k : ℕ, ∃ u_h : H1Compl (I := I) (M := M) g,
      u_h ∈ laplacianDomainPow (I := I) (M := M) g k ∧
        H1ComplToLp (I := I) (M := M) g u_h =
          heatSemigroup (I := I) (M := M) g t u_0 ∧
        MemWkpChart (I := I) (M := M) g (2 * k) 2
          (((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) ∧
        wkpNormChart (I := I) (M := M) g (2 * k) 2
          (((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) < ⊤ := by
  intro k
  obtain ⟨u_h, hu_h_mem, hu_h_eq, h_bridge_lift⟩ :=
    chartSideH2kBridge_heat_implies_chartSideH2kBridge_lifts
      (I := I) (M := M) g ht u_0 h_bridges k
  refine ⟨u_h, hu_h_mem, hu_h_eq, ?_, ?_⟩
  · exact (laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
      (I := I) (M := M) g k hu_h_mem h_bridge_lift).1
  · exact (laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
      (I := I) (M := M) g k hu_h_mem h_bridge_lift).2

/-- **At `k = 0`, the chart-side `H⁰` bridge for the heat representative is
unconditional.** -/
theorem chartSideH2kBridge_heat_zero
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ChartSideH2kBridge (I := I) (M := M) g 0
      (((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  obtain ⟨u_h, _hu_h_mem, hu_h_eq⟩ :=
    heatSemigroup_mem_laplacianDomainPow_all (I := I) (M := M) g ht u_0 0
  have h_coe : ((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
    rw [hu_h_eq]
  rw [h_coe]
  exact chartSideH2kBridge_zero (I := I) (M := M) g u_h

/-- **At `k = 1`, the chart-side `H²` bridge for the heat representative is
unconditional.** -/
theorem chartSideH2kBridge_heat_one
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ChartSideH2kBridge (I := I) (M := M) g 1
      (((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  obtain ⟨u_h, hu_h_mem, hu_h_eq⟩ :=
    heatSemigroup_mem_laplacianDomainPow_all (I := I) (M := M) g ht u_0 1
  have h_coe : ((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
    rw [hu_h_eq]
  rw [h_coe]
  exact chartSideH2kBridge_one (I := I) (M := M) g hu_h_mem

end HeatEquation
end Analysis
end DifferentialGeometry

end
