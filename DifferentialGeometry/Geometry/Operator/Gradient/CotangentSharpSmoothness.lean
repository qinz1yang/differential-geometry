import DifferentialGeometry.Geometry.Operator.Gradient.MetricSharpSmoothness
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.InverseMetric

set_option autoImplicit false

noncomputable section

open DifferentialGeometry.Integral.DivergenceTheorem
open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Operator

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [InnerProductSpace ℝ E] in
theorem cotangentSharp_gen_eq_metricSharp
    (g : SmoothRiemannianMetric I M) (x : M)
    (β : Tensor0SSpace 1 I x) :
    cotangentSharp (I := I) g x β =
      metricSharp (I := I) g x (cotangentToDual (I := I) β) := by
  apply metricFlatLinear_injective (I := I) g x
  ext w
  change g.inner x (cotangentSharp (I := I) g x β) w =
    g.inner x (metricSharp (I := I) g x (cotangentToDual (I := I) β)) w
  rw [cotangentSharp_inner (I := I) g x β w,
    inner_metricSharp (I := I) g x (cotangentToDual (I := I) β) w]

omit [InnerProductSpace ℝ E] in
theorem cotangentToDual_gen_chartBasis_eval
    (α : M) (j : Fin (Module.finrank ℝ E))
    (β : Π b : M, Tensor0SSpace 1 I b) (b : M) :
    cotangentToDual (I := I) (β b) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b) =
      β b (fun _ : Fin 1 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b) :=
  cotangentToDual_apply (I := I) (β b) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b)

omit [InnerProductSpace ℝ E] in
theorem cotangentSharp_gen_contMDiff_total (g : SmoothRiemannianMetric I M)
    {β : Π b : M, Tensor0SSpace 1 I b}
    (hβ : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => β b (fun _ : Fin 1 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M =>
        TotalSpace.mk' E b (cotangentSharp (I := I) g b (β b))) := by
  set cv : Π b : M, TangentSpace I b →ₗ[ℝ] ℝ :=
    fun b => cotangentToDual (I := I) (β b) with hcv
  have hcv_smooth : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => cv b (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source := by
    intro α j
    have heq :
        (fun b : M => cv b (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b)) =
          fun b : M => β b (fun _ : Fin 1 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b) := by
      funext b
      exact cotangentToDual_gen_chartBasis_eval (I := I) α j β b
    rw [heq]
    exact hβ α j
  have hmetric :=
    metricSharp_contMDiff_total (I := I) g (cv := cv) hcv_smooth
  have hsection_eq :
      (fun b : M =>
          TotalSpace.mk' E b (cotangentSharp (I := I) g b (β b))) =
        fun b : M =>
          TotalSpace.mk' E b (metricSharp (I := I) g b (cv b)) := by
    funext b
    change TotalSpace.mk' E b (cotangentSharp (I := I) g b (β b)) =
      TotalSpace.mk' E b (metricSharp (I := I) g b (cotangentToDual (I := I) (β b)))
    rw [cotangentSharp_gen_eq_metricSharp (I := I) g b (β b)]
  rw [hsection_eq]
  exact hmetric

omit [InnerProductSpace ℝ E] in
theorem cotangentSharp_gen_mdiffAt (g : SmoothRiemannianMetric I M)
    {β : Π b : M, Tensor0SSpace 1 I b}
    (hβ : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => β b (fun _ : Fin 1 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source)
    (x : M) :
    MDiffAt (T% (fun y : M => cotangentSharp (I := I) g y (β y))) x :=
  (cotangentSharp_gen_contMDiff_total (I := I) g hβ).contMDiffAt.mdifferentiableAt
    (by simp)

end Operator
end Geometry
end DifferentialGeometry
