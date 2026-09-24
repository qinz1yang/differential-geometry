import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.ManifoldSmoothness
import DifferentialGeometry.Geometry.Metric.Family.InverseMetric.Regularity
import DifferentialGeometry.Bundle.PartialMfderiv.Basic

noncomputable section

open Bundle Filter Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn

open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem gradient_joint_contMDiffOn
    {D : RealTimeInterval}
    {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn (I := I) (M := M) D g)
    {f : ℝ × M → ℝ}
    (hf : ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ f (D.regular ×ˢ (univ : Set M))) :
    ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M => (⟨p.2, gradientFun (g p.1) (fun x => f (p.1, x)) p.2⟩ :
        TangentBundle I M)) (D.regular ×ˢ (univ : Set M)) := by
  let cv := fun t x => (mvfderiv (I := I) (fun y => f (t, y)) x).toLinearMap
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => cv p.2 p.1 (chartBasisVecFiber (I := I) α j p.1))
        ((chartAt H α).source ×ˢ D.regular) := by
    intro α j p hp
    have hfAt := hf.contMDiffAt (x := (p.2, p.1))
      ((D.regular_isOpen.prod isOpen_univ).mem_nhds ⟨hp.2, mem_univ p.1⟩)
    have hXAt := (chartBasisVec_contMDiffOn (I := I) α j).contMDiffAt
      ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hp.1)
    have hd := DifferentialGeometry.prodExtDerivAt_smooth hfAt hXAt
    exact (hd.comp p (contMDiffAt_snd.prodMk contMDiffAt_fst)).contMDiffWithinAt
  have hgrad := metricSharp_jointContMDiffOn g cv D.regular_isOpen
    (chartInvGramMatrix_jointContMDiffOn g hg) hcv
  exact hgrad.comp (contMDiffOn_snd.prodMk contMDiffOn_fst) (fun p hp => ⟨hp.2, hp.1⟩)

end DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
