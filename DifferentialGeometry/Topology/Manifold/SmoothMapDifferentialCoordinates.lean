import DifferentialGeometry.Topology.Manifold.SmoothOrientation
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E H M F K N : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable [TopologicalSpace M] [ChartedSpace H M]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable [TopologicalSpace K] (J : ModelWithCorners ℝ F K)
variable [TopologicalSpace N] [ChartedSpace K N]

def differentialEquivOfBijective (f : M → N)
    (hf : ∀ x : M, Bijective (mfderiv I J f x)) (x : M) : E ≃L[ℝ] F := by
  let D : E →L[ℝ] F := mfderiv I J f x
  exact (LinearEquiv.ofBijective D.toLinearMap (hf x)).toContinuousLinearEquiv

omit [FiniteDimensional ℝ F] in
theorem differentialEquivOfBijective_apply (f : M → N)
    (hf : ∀ x : M, Bijective (mfderiv I J f x)) (x : M) (v : E) :
    differentialEquivOfBijective I J f hf x v = mfderiv I J f x v := rfl

variable [IsManifold I ∞ M] [IsManifold J ∞ N]

theorem preferredChartTangentEquiv_symm_apply (p x : M)
    (hx : x ∈ (chartAt H p).source) (v : E) :
    (preferredChartTangentEquiv I p x hx).symm v =
      mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) (extChartAt I p x) v := by
  apply (preferredChartTangentEquiv I p x hx).injective
  have h := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' (I := I)
    (by simpa only [extChartAt_source] using hx)
  have hv : preferredChartTangentEquiv I p x hx
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) (extChartAt I p x) v) = v :=
    congrArg (fun A : E →L[ℝ] E => A v) h
  exact ((preferredChartTangentEquiv I p x hx).apply_symm_apply v).trans hv.symm

def coordinateDifferentialEquiv (f : M → N)
    (hf : ∀ x : M, Bijective (mfderiv I J f x)) (p : M)
    (x : ↥((chartAt H p).source ∩ f ⁻¹' (chartAt K (f p)).source)) : E ≃L[ℝ] F :=
  ((preferredChartTangentEquiv I p x.val x.property.1).symm.trans
    (differentialEquivOfBijective I J f hf x.val)).trans
    (preferredChartTangentEquiv J (f p) (f x.val) x.property.2)

theorem coordinateDifferentialEquiv_eq (f : M → N)
    (hf : ∀ x : M, Bijective (mfderiv I J f x)) (p : M)
    (x : ↥((chartAt H p).source ∩ f ⁻¹' (chartAt K (f p)).source)) :
    (coordinateDifferentialEquiv I J f hf p x : E →L[ℝ] F) =
      inTangentCoordinates I J id f (mfderiv I J f) p x.val := by
  rw [inTangentCoordinates_eq_mfderiv_comp x.property.1 x.property.2]
  apply ContinuousLinearMap.ext
  intro v
  change preferredChartTangentEquiv J (f p) (f x.val) x.property.2
    (differentialEquivOfBijective I J f hf x.val
      ((preferredChartTangentEquiv I p x.val x.property.1).symm v)) = _
  rw [preferredChartTangentEquiv_apply, differentialEquivOfBijective_apply,
    preferredChartTangentEquiv_symm_apply]
  rfl

theorem continuousAt_coordinateDifferentialEquiv (f : M → N)
    (hf : ContMDiff I J ∞ f) (hbij : ∀ x : M, Bijective (mfderiv I J f x)) (p : M) :
    ContinuousAt (fun x : ↥((chartAt H p).source ∩ f ⁻¹' (chartAt K (f p)).source) =>
      (coordinateDifferentialEquiv I J f hbij p x : E →L[ℝ] F))
        ⟨p, mem_chart_source H p, mem_chart_source K (f p)⟩ := by
  have h : ContinuousAt (inTangentCoordinates I J id f (mfderiv I J f) p) p :=
    (hf.contMDiffAt.mfderiv_const (m := 0) (by simp)).continuousAt
  have h' := h.comp (continuous_subtype_val.continuousAt (x :=
    (⟨p, mem_chart_source H p, mem_chart_source K (f p)⟩ :
      ↥((chartAt H p).source ∩ f ⁻¹' (chartAt K (f p)).source))))
  have he : (fun x : ↥((chartAt H p).source ∩ f ⁻¹' (chartAt K (f p)).source) =>
      (coordinateDifferentialEquiv I J f hbij p x : E →L[ℝ] F)) =
      (fun x => inTangentCoordinates I J id f (mfderiv I J f) p x.val) := by
    funext x
    exact coordinateDifferentialEquiv_eq I J f hbij p x
  rw [he]
  exact h'
end DifferentialGeometry.Topology.Manifold
