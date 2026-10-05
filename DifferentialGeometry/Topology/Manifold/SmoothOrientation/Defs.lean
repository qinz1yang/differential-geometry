import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.LinearAlgebra.Orientation
import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
section Manifold
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def preferredChartTangentEquiv (p x : M) (hx : x ∈ (chartAt H p).source) : E ≃L[ℝ] E := by
  let D : E →L[ℝ] E := mfderiv I 𝓘(ℝ, E) (extChartAt I p) x
  have hD : Injective D :=
    (isInvertible_mfderiv_extChartAt (I := I) (by simpa only [extChartAt_source] using hx)).injective
  exact (D.toLinearMap.linearEquivOfInjective hD rfl).toContinuousLinearEquiv

theorem preferredChartTangentEquiv_apply (p x : M) (hx : x ∈ (chartAt H p).source) (v : E) :
    preferredChartTangentEquiv I p x hx v = mfderiv I 𝓘(ℝ, E) (extChartAt I p) x v := rfl

def SmoothOrientation (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] : Type _ :=
  {o : M → Orientation ℝ E (Fin (Module.finrank ℝ E)) //
    ∀ p : M, IsLocallyConstant (fun x : (chartAt H p).source =>
      Orientation.map (Fin (Module.finrank ℝ E))
        (preferredChartTangentEquiv I p x.val x.property).toLinearEquiv (o x.val))}
end Manifold

section Euclidean
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem preferredChartTangentEquiv_model (p x : E) (hx : x ∈ (chartAt E p).source) :
    preferredChartTangentEquiv 𝓘(ℝ, E) p x hx = ContinuousLinearEquiv.refl ℝ E := by
  ext v
  rw [preferredChartTangentEquiv_apply]
  rw [extChartAt_model_space_eq_id]
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (id : E → E) x v = v
  rw [mfderiv_id]
  rfl

def euclideanSmoothOrientation (o : Orientation ℝ E (Fin (Module.finrank ℝ E))) :
    SmoothOrientation 𝓘(ℝ, E) E := by
  refine ⟨fun _ => o, ?_⟩
  intro p
  have he : (fun x : (chartAt E p).source =>
      Orientation.map (Fin (Module.finrank ℝ E))
        (preferredChartTangentEquiv 𝓘(ℝ, E) p x.val x.property).toLinearEquiv o) =
      Function.const (chartAt E p).source o := by
    funext x
    rw [preferredChartTangentEquiv_model]
    change Orientation.map (Fin (Module.finrank ℝ E)) (LinearEquiv.refl ℝ E) o = o
    rw [Orientation.map_refl]
    rfl
  rw [he]
  exact IsLocallyConstant.const o

theorem euclideanSmoothOrientation_apply (o : Orientation ℝ E (Fin (Module.finrank ℝ E))) (p : E) :
    (euclideanSmoothOrientation E o).val p = o := rfl
end Euclidean
end DifferentialGeometry.Topology.Manifold
