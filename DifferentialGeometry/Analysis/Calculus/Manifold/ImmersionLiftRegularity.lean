import DifferentialGeometry.Analysis.Calculus.Derivative.ImmersionLiftRegularity
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import Mathlib.Geometry.Manifold.MFDeriv.Atlas



noncomputable section

open Set Filter Function Manifold ContinuousMap
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in

theorem contDiffAt_parameterLift_of_manifoldImmersion {f : E → M} {ψ : G → E} {x : G}
    (hf : ContMDiff 𝓘(ℝ, E) I ∞ f)
    (hi : Injective (mfderiv 𝓘(ℝ, E) I f (ψ x))) (hψ : ContinuousAt ψ x)
    (hc : ContMDiffAt 𝓘(ℝ, G) I ∞ (f ∘ ψ) x) : ContDiffAt ℝ ∞ ψ x := by
  let c := extChartAt I (f (ψ x))
  let s : Set E := f ⁻¹' (chartAt H (f (ψ x))).source
  have hs : IsOpen s := (chartAt H (f (ψ x))).open_source.preimage hf.continuous
  have hx : ψ x ∈ s := mem_chart_source H (f (ψ x))
  have hg : ContDiffOn ℝ ∞ (c ∘ f) s :=
    ((contMDiffOn_extChartAt (I := I) (x := f (ψ x)) (n := ∞)).comp hf.contMDiffOn
      (fun _ hy => hy)).contDiffOn
  have hd : fderiv ℝ (c ∘ f) (ψ x) = mfderiv 𝓘(ℝ, E) I f (ψ x) := by
    rw [(hf.mdifferentiable (by simp) (ψ x)).mfderiv]
    simp only [writtenInExtChartAt, mfld_simps, c, fderivWithin_univ]
    simp [tangentSpaceCastModel]
    rfl
  have hca : ContMDiffAt I 𝓘(ℝ, F) ∞ (↑c : M → F) (f (ψ x)) :=
    (contMDiffOn_extChartAt (I := I) (x := f (ψ x)) (n := ∞)).contMDiffAt
      ((chartAt H (f (ψ x))).open_source.mem_nhds (mem_chart_source H (f (ψ x))))
  have hcomp : ContDiffAt ℝ ∞ ((c ∘ f) ∘ ψ) x := by
    simpa only [Function.comp_assoc] using (hca.comp x hc).contDiffAt
  exact DifferentialGeometry.Analysis.contDiffAt_lift_of_immersion hs hg hx (hd ▸ hi) hψ hcomp

end DifferentialGeometry.Geometry
