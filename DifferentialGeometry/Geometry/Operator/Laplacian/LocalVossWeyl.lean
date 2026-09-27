import DifferentialGeometry.Geometry.Operator.Laplacian.VossWeylFormula
import DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification
import DifferentialGeometry.Bundle.SmoothScalarGerm

noncomputable section

open Filter Set
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

omit [I.Boundaryless] in
theorem chartVossWeylLaplacian_congr_of_eventuallyEq
    (g : SmoothRiemannianMetric I M) (a : M) {f h : M → ℝ} {x : M}
    (hx : x ∈ (extChartAt I a).source) (heq : f =ᶠ[𝓝 x] h) :
    chartVossWeylLaplacian g a f x = chartVossWeylLaplacian g a h x := by
  have hsymm : Tendsto (extChartAt I a).symm (𝓝 (extChartAt I a x)) (𝓝 x) := by
    simpa only [(extChartAt I a).left_inv hx] using
      (continuousAt_extChartAt_symm' (I := I) hx).tendsto
  have hs : scalarOnE (I := I) a f =ᶠ[𝓝 (extChartAt I a x)]
      scalarOnE (I := I) a h := heq.comp_tendsto hsymm
  have hi (i : Fin (Module.finrank ℝ E)) :
      chartVossWeylIntegrand g a f i =ᶠ[𝓝 (extChartAt I a x)]
        chartVossWeylIntegrand g a h i := by
    filter_upwards [hs.fderiv (𝕜 := ℝ)] with y hy
    simp only [chartVossWeylIntegrand, gradChartCoeffOnE, partialDeriv, hy]
  unfold chartVossWeylLaplacian
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  unfold partialDeriv
  rw [(hi i).fderiv_eq]

theorem laplacian_eq_chartVossWeyl_of_contMDiffOn
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (a : M) {f : M → ℝ} {U : Set M} {x : M}
    (hU : IsOpen U) (hxU : x ∈ U) (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    (hx : x ∈ (chartAt H a).source) :
    laplacian (Connection.LeviCivita g) g f x = chartVossWeylLaplacian g a f x := by
  obtain ⟨F, hF, hFf⟩ := exists_smooth_germ hU hxU hf
  calc
    laplacian (Connection.LeviCivita g) g f x =
        laplacian (Connection.LeviCivita g) g F x :=
      laplacian_congr_of_eventuallyEq (Connection.LeviCivita g) g
        (hf.contMDiffAt (hU.mem_nhds hxU)) hF.contMDiffAt hFf.symm
    _ = ΔG g ⟨F, hF⟩ x := laplacian_levi_eq g hF x
    _ = chartVossWeylLaplacian g a F x :=
      voss_weyl_laplacian_formula_pointwise g a hF hx
    _ = chartVossWeylLaplacian g a f x :=
      chartVossWeylLaplacian_congr_of_eventuallyEq g a
        (by rwa [extChartAt_source (I := I) a]) hFf

end DifferentialGeometry.Geometry.Operator
