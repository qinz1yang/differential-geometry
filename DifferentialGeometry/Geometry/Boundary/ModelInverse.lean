import DifferentialGeometry.Geometry.Boundary.ModelExtension
import DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold

namespace Poincare.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [HasSmoothBoundary E H I]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_localInverse_of_model
    {f : E → F} {U : Set E} {y : E} (hU : IsOpen U) (hyU : y ∈ U)
    (hy : y ∈ range I) (hf : ContDiffOn ℝ ∞ f (U ∩ range I))
    (hinj : Function.Injective (fderivWithin ℝ f (range I) y))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    ∃ e : OpenPartialHomeomorph E F,
      y ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      EqOn e f (e.source ∩ range I) := by
  have hex : ∃ V : Set E, IsOpen V ∧ y ∈ V ∧ V ⊆ U ∧
      ∃ g : E → F, ContDiffOn ℝ ∞ g V ∧ EqOn g f (V ∩ range I) := by
    by_cases hb : y ∈ frontier (range I)
    · exact exists_contDiffOn_extension_of_model I hU hyU hb hf
    · have hi : y ∈ interior (range I) := (mem_interior_iff_notMem_frontier hy).mpr hb
      exact ⟨U ∩ interior (range I), hU.inter isOpen_interior, ⟨hyU, hi⟩,
        inter_subset_left, f, hf.mono (inter_subset_inter_right U interior_subset),
        fun _ _ ↦ rfl⟩
  obtain ⟨V, hV, hyV, hVU, g, hg, heq⟩ := hex
  have hevent : g =ᶠ[𝓝[range I] y] f := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hyV), self_mem_nhdsWithin]
      with z hz hzI
    exact heq ⟨hz, hzI⟩
  have hdg := ((hg.contDiffAt (hV.mem_nhds hyV)).differentiableAt (by simp)).hasFDerivAt
  have hdf : fderiv ℝ g y = fderivWithin ℝ f (range I) y :=
    (hdg.hasFDerivWithinAt.congr_of_eventuallyEq hevent.symm (heq ⟨hyV, hy⟩).symm).fderivWithin
      (I.uniqueDiffOn y hy) |>.symm
  let A := fderivWithin ℝ f (range I) y
  let L : E ≃L[ℝ] F := (A.toLinearMap.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv
  have hd : HasFDerivAt g (L : E →L[ℝ] F) y := by
    change HasFDerivAt g A y
    rwa [hdf] at hdg
  obtain ⟨e, hye, heV, he, hi, heg⟩ :=
    Poincare.Analysis.exists_localInverse_of_hasFDerivAt_equiv hg hV hyV hd
  exact ⟨e, hye, heV.trans hVU, he, hi, fun z hz ↦ (heg z).trans (heq ⟨heV hz.1, hz.2⟩)⟩

end Poincare.Geometry.Boundary
