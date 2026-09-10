import DifferentialGeometry.Topology.Manifold.InteriorAtlas
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
namespace Poincare.Manifold
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners 𝕜 E H)

theorem mfderiv_eq_fderiv_extChartAt_of_isInteriorPoint {f : M → F} {x : M}
    (hf : MDifferentiableAt I 𝓘(𝕜, F) f x) (hx : I.IsInteriorPoint x) :
    (show E →L[𝕜] F from mfderiv I 𝓘(𝕜, F) f x) =
      fderiv 𝕜 (fun y => f ((extChartAt I x).symm y)) (extChartAt I x x) := by
  rw [hf.mfderiv, fderivWithin_of_mem_nhds (range_mem_nhds_isInteriorPoint hx)]
  rfl

theorem extChartAt_subtype_val_symm_eventuallyEq (U : TopologicalSpace.Opens M) (x : U) :
    (extChartAt I (x : M)).symm =ᶠ[𝓝 (extChartAt I (x : M) x)]
      Subtype.val ∘ (extChartAt I x).symm := by
  have ht : Tendsto I.symm (𝓝 (extChartAt I (x : M) x))
      (𝓝 (chartAt H (x : M) x)) := by
    convert! I.continuous_symm.continuousAt.tendsto using 1
    change 𝓝 (chartAt H (x : M) x) = 𝓝 (I.symm (I (chartAt H (x : M) x)))
    rw [I.left_inv]
  exact (U.chartAt_subtype_val_symm_eventuallyEq (H := H) (x := x)).comp_tendsto ht

theorem mfderiv_openRestriction {U : TopologicalSpace.Opens M} {f : M → F}
    (hf : ContMDiff I 𝓘(𝕜, F) ∞ f) (x : U) (hx : I.IsInteriorPoint (x : M)) :
    (show E →L[𝕜] F from mfderiv I 𝓘(𝕜, F) (fun y : U => f y) x) =
      (show E →L[𝕜] F from mfderiv I 𝓘(𝕜, F) f (x : M)) := by
  erw [mfderiv_eq_fderiv_extChartAt_of_isInteriorPoint I
    ((hf.comp contMDiff_subtype_val).mdifferentiableAt (by simp))
    (I.isInteriorPoint_iff_isInteriorPoint_val.mpr hx),
    mfderiv_eq_fderiv_extChartAt_of_isInteriorPoint I (hf.mdifferentiableAt (by simp)) hx]
  change fderiv 𝕜 (fun y => f (((extChartAt I x).symm y : U) : M))
      (extChartAt I (x : M) x) = _
  exact ((extChartAt_subtype_val_symm_eventuallyEq I U x).fun_comp f).fderiv_eq.symm

theorem mfderiv_interiorAtlas [IsManifold I ∞ M] [BoundarylessManifold I M]
    {f : M → F} (hf : ContMDiff I 𝓘(𝕜, F) ∞ f) (x : M) :
    let _ := interiorChartedSpace I ∞ (M := M)
    (show E →L[𝕜] F from mfderiv 𝓘(𝕜, E) 𝓘(𝕜, F) f x) =
      (show E →L[𝕜] F from mfderiv I 𝓘(𝕜, F) f x) := by
  let _ := interiorChartedSpace I ∞ (M := M)
  change (show E →L[𝕜] F from mfderiv 𝓘(𝕜, E) 𝓘(𝕜, F) f x) =
    (show E →L[𝕜] F from mfderiv I 𝓘(𝕜, F) f x)
  have hf' : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, F) ∞ f :=
    hf.comp (contMDiff_interiorAtlas_id I ∞)
  erw [mfderiv_eq_fderiv_extChartAt_of_isInteriorPoint 𝓘(𝕜, E)
    (hf'.mdifferentiableAt (by simp)) BoundarylessManifold.isInteriorPoint,
    mfderiv_eq_fderiv_extChartAt_of_isInteriorPoint I
      (hf.mdifferentiableAt (by simp)) BoundarylessManifold.isInteriorPoint]
  rfl
end Poincare.Manifold
