import DifferentialGeometry.Analysis.Calculus.Derivative.ImmersionLiftRegularity
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import Mathlib.Geometry.Manifold.MFDeriv.Atlas



noncomputable section

open Set Filter Function Manifold ContinuousMap
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]

set_option backward.isDefEq.respectTransparency false in



theorem contDiffAt_parameterLift_of_manifoldImmersion {f : E → M} {ψ : G → E} {x : G}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hi : Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (ψ x))) (hψ : ContinuousAt ψ x)
    (hc : ContMDiffAt 𝓘(ℝ, G) 𝓘(ℝ, F) ∞ (f ∘ ψ) x) : ContDiffAt ℝ ∞ ψ x := by
  let c := chartAt F (f (ψ x))
  let s : Set E := f ⁻¹' c.source
  have hs : IsOpen s := c.open_source.preimage hf.continuous
  have hx : ψ x ∈ s := mem_chart_source F (f (ψ x))
  have hg : ContDiffOn ℝ ∞ (c ∘ f) s :=
    (contMDiffOn_chart.comp hf.contMDiffOn (fun _ hy => hy)).contDiffOn
  have hd : fderiv ℝ (c ∘ f) (ψ x) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (ψ x) := by
    rw [(hf.mdifferentiable (by simp) (ψ x)).mfderiv]
    simp only [writtenInExtChartAt, mfld_simps, c, fderivWithin_univ]
  have hcp : f (ψ x) ∈ c.source := mem_chart_source F _
  have hca : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ c (f (ψ x)) :=
    (contMDiffOn_chart _ hcp).contMDiffAt (c.open_source.mem_nhds hcp)
  have hcomp : ContDiffAt ℝ ∞ ((c ∘ f) ∘ ψ) x := (hca.comp x hc).contDiffAt
  exact DifferentialGeometry.Analysis.contDiffAt_lift_of_immersion hs hg hx (hd ▸ hi) hψ hcomp

end DifferentialGeometry.Geometry
