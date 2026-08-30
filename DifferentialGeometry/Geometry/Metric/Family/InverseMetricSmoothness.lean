import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.ManifoldSmoothness
import DifferentialGeometry.Geometry.Metric.Family.InverseMetricRegularity
import DifferentialGeometry.Bundle.ContinuousLinearMapSection.ParametricSmoothness

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator


noncomputable section


open Set Function Bundle DifferentialGeometry.Tensor0SBundle
open scoped Topology Manifold BigOperators ContDiff Matrix

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]

namespace MetricFamilySmoothOn

theorem inverseMetricSharpFib_jointContMDiffOn
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 1 ℝ E →L[ℝ] E)
        (E := fun z : M => Tensor0SSpace 1 I z →L[ℝ] TangentSpace I z) p.1
        (inverseMetricSharpFib (I := I) (g_fam p.2) p.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
  apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SSpace 1 I x)
    (F₂ := E) (V₂ := fun x : M => TangentSpace I x)
    (φ := fun p : M × ℝ => inverseMetricSharpFib (I := I) (g_fam p.2) p.1)
    (S := D.regular)
  intro Y
  set cv : ℝ → Π b : M, TangentSpace I b →ₗ[ℝ] ℝ :=
    fun _ b => cotangentToDualLinear (I := I) (x := b) (Y b) with hcvdef
  have hinv : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => chartInvGramMatrix (I := I) (g_fam p.2) α p.1 i j)
        ((chartAt H α).source ×ˢ D.regular) :=
    fun α i j => MetricFamilySmoothOn.chartInvGramMatrix_jointContMDiffOn
      (I := I) g_fam hG α i j
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => cv p.2 p.1 (chartBasisVecFiber (I := I) α j p.1))
        ((chartAt H α).source ×ˢ D.regular) := by
    intro α j
    have hbase := cotangentSection_chartComponent_contMDiffOn (I := I) Y α j
    have heqfn : (fun p : M × ℝ => cv p.2 p.1 (chartBasisVecFiber (I := I) α j p.1)) =
        (fun p : M × ℝ => (fun b : M => Tensor0SSpace.toModel (Y b)
          (fun _ : Fin 1 => chartBasisVecFiber (I := I) α j b)) p.1) := by
      funext p
      rw [hcvdef]
      simp only
      rw [cotangentToDualLinear_apply, cotangentToDual_apply]
      rfl
    rw [heqfn]
    exact hbase.comp contMDiffOn_fst (fun p hp => hp.1)
  have hjoint := metricSharp_jointContMDiffOn (I := I)
    (gfam := fun t => g_fam t) (cv := cv) (S := D.regular)
    D.regular_isOpen hinv hcv
  refine hjoint.congr (fun p _ => ?_)
  change TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
      (DifferentialGeometry.Geometry.Operator.metricSharp
        (I := I) (g_fam p.2) p.1 (cv p.2 p.1)) =
    TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
      (inverseMetricSharpFib (I := I) (g_fam p.2) p.1 (Y p.1))
  rw [inverseMetricSharpFib_apply, hcvdef]

end MetricFamilySmoothOn

end DifferentialGeometry.Geometry.Curvature
