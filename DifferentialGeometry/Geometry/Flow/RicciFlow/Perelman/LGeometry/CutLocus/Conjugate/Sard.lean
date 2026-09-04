import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Defs
import DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lConjugateChart_null
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau : Real) (alpha : M) :
    DifferentialGeometry.Integral.Measure.modelHaar (E := E)
        ((fun Z : E => (extChartAt I alpha) (lExp S T x Z tau)) ''
          {Z : E | IsLConjugate S T x Z tau ∧
            lExp S T x Z tau ∈ (chartAt H alpha).source}) = 0 := by
  let f : E → M := fun Z => lExp S T x Z tau
  let g : E → E := fun Z => (extChartAt I alpha) (f Z)
  let s : Set E := {Z : E | IsLConjugate S T x Z tau ∧
    f Z ∈ (chartAt H alpha).source}
  have hpair : ContMDiff 𝓘(Real, E)
      (𝓘(Real, E).prod 𝓘(Real, Real)) ∞
      (fun Z : E => (Z, tau)) :=
    contMDiff_id.prodMk contMDiff_const
  have hUopen : IsOpen
      ((fun Z : E => (Z, tau)) ⁻¹' lExpPosDom S T x) :=
    (lExpPosDom_open S hS T x).preimage hpair.continuous
  have hf (Z : E) (hZ : Z ∈ s) :
      MDifferentiableAt 𝓘(Real, E) I f Z := by
    have hfU : ContMDiffOn 𝓘(Real, E) I ∞ f
        ((fun W : E => (W, tau)) ⁻¹' lExpPosDom S T x) := by
      apply (lExp_smoothOn S hS T x).comp hpair.contMDiffOn
      intro W hW
      exact hW
    exact (hfU.contMDiffAt (hUopen.mem_nhds hZ.1.1)).mdifferentiableAt
      (by simp)
  let dg : E → E →L[Real] E := fun Z =>
    (mfderiv I 𝓘(Real, E) (extChartAt I alpha) (f Z)).comp
      (mfderiv 𝓘(Real, E) I f Z)
  have hg (Z : E) (hZ : Z ∈ s) : HasFDerivAt g (dg Z) Z := by
    have hchart : MDifferentiableAt I 𝓘(Real, E)
        (extChartAt I alpha) (f Z) :=
      mdifferentiableAt_extChartAt hZ.2
    have hcomp : HasMFDerivAt 𝓘(Real, E) 𝓘(Real, E) g Z (dg Z) := by
      exact hchart.hasMFDerivAt.comp Z (hf Z hZ).hasMFDerivAt
    have hraw := hasMFDerivAt_iff_hasFDerivAt.mp hcomp
    unfold HasFDerivAt at hraw ⊢
    exact hraw
  have hdet (Z : E) (hZ : Z ∈ s) : (dg Z).det = 0 := by
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot]
    rcases (isLConjugate_iff S T x Z tau).1 hZ.1 with
      ⟨_hdom, V, hV, hV0⟩
    intro hker
    have hV0' : (mfderiv 𝓘(Real, E) I f Z) V = 0 := by
      simpa only [f] using hV0
    have hVker : V ∈ LinearMap.ker (dg Z).toLinearMap := by
      change (dg Z) V = 0
      rw [show dg Z =
          (mfderiv I 𝓘(Real, E) (extChartAt I alpha) (f Z)).comp
            (mfderiv 𝓘(Real, E) I f Z) from rfl]
      calc
        ((mfderiv I 𝓘(Real, E) (extChartAt I alpha) (f Z)).comp
            (mfderiv 𝓘(Real, E) I f Z)) V =
            (mfderiv I 𝓘(Real, E) (extChartAt I alpha) (f Z))
              ((mfderiv 𝓘(Real, E) I f Z) V) := rfl
        _ = (mfderiv I 𝓘(Real, E) (extChartAt I alpha) (f Z)) 0 := by
          rw [hV0']
        _ = 0 := map_zero _
    rw [hker] at hVker
    exact hV (by simpa only [Submodule.mem_bot] using hVker)
  simpa only [f, g, s] using
    (addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
      (μ := DifferentialGeometry.Integral.Measure.modelHaar (E := E))
      (f := g) (s := s) (f' := dg)
      (hf' := fun Z hZ => (hg Z hZ).hasFDerivWithinAt)
      (h'f' := hdet))

end DifferentialGeometry.PDE.RicciFlow.Perelman
