import DifferentialGeometry.Analysis.Sobolev.Euclidean.Composition
import DifferentialGeometry.Topology.Manifold.ChartPartialDiffeomorph
import DifferentialGeometry.Analysis.Elliptic.MetricExtension

noncomputable section

open Set Filter MeasureTheory Manifold
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open scoped Topology ContDiff Manifold ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι
local notation "H" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem exists_weak_chart_coordinates_of_continuousOn
    {Ω : Set V} (hΩ : IsOpen Ω) {f : V → F} (hfc : ContinuousOn f Ω)
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    {r : F → M} {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r U)
    (hfU : MapsTo f Ω U) {x₀ : V} (hx₀ : x₀ ∈ Ω) :
    let p := r (f x₀)
    let χ : F → H := fun y => toEuclidean (extChartAt 𝓘(ℝ, E) p (r y))
    let v : V → H := χ ∘ f
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall x₀ ρ ⊆ Ω ∧
      MapsTo (r ∘ f) (Metric.closedBall x₀ ρ) (extChartAt 𝓘(ℝ, E) p).source ∧
      MapsTo v (Metric.closedBall x₀ ρ)
        (DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid
          (I := 𝓘(ℝ, E)) p) ∧
      ContinuousOn v (Metric.closedBall x₀ ρ) ∧
      (∀ x ∈ Metric.closedBall x₀ ρ,
        (extChartAt 𝓘(ℝ, E) p).symm ((toEuclidean (E := E)).symm (v x)) = r (f x)) ∧
      ∃ hv : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => v x k) (Metric.ball x₀ ρ),
        ∀ x ∈ Metric.ball x₀ ρ, ∀ j,
          WithLp.toLp 2 (fun k => (hv k).weakGrad x j) =
            fderiv ℝ χ (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j)) := by
  let p := r (f x₀)
  let chart := extChartAtPartialDiffeomorph 𝓘(ℝ, E) ∞ p
  let W : Set F := U ∩ r ⁻¹' chart.source
  have hW : IsOpen W := hr.continuousOn.isOpen_inter_preimage hU chart.open_source
  have hmem : f x₀ ∈ W := ⟨hfU hx₀, mem_extChartAt_source (r (f x₀))⟩
  let χ : F → H := fun y => toEuclidean (chart (r y))
  have hχ : ContDiffOn ℝ ∞ χ W := by
    have hchart : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ (chart ∘ r) W :=
      chart.contMDiffOn_toFun.comp (hr.mono inter_subset_left) inter_subset_right
    exact ((toEuclidean (E := E)).contDiff.contMDiff.comp_contMDiffOn hchart).contDiffOn
  obtain ⟨ρ, hρ, hball, hmaps, hv, hgrad⟩ :=
    exists_memW1pWitnesses_comp_contDiffOn_of_continuousOn hΩ hfc hf hW χ hχ hx₀ hmem
  have hrmaps : MapsTo (r ∘ f) (Metric.closedBall x₀ ρ) chart.source :=
    fun x hx => (hmaps hx).2
  have hvmaps : MapsTo (χ ∘ f) (Metric.closedBall x₀ ρ)
      (DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid
        (I := 𝓘(ℝ, E)) p) := by
    intro x hx
    exact ⟨chart (r (f x)), chart.toOpenPartialHomeomorph.map_source (hrmaps hx), rfl⟩
  refine ⟨ρ, hρ, hball, hrmaps, hvmaps, ?_, ?_, hv, hgrad⟩
  · exact hχ.continuousOn.comp (hfc.mono hball) hmaps
  · intro x hx
    change chart.symm ((toEuclidean (E := E)).symm (toEuclidean (chart (r (f x))))) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact chart.toOpenPartialHomeomorph.left_inv (hrmaps hx)

end DifferentialGeometry.Geometry

end
