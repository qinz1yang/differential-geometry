import DifferentialGeometry.Bundle.VectorField.Pushforward
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.Calculus.Deriv.Add

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold

namespace Poincare.Geometry.VectorField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiff_pushforward_const
    [FiniteDimensional ℝ E]
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (c : E) :
    ContDiff ℝ ∞ (DifferentialGeometry.Diffeomorph.pushforward f (fun _ ↦ c)) := by
  have hc : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun z ↦ (⟨z, c⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  exact contMDiff_vectorSpace_iff_contDiff.mp
    (DifferentialGeometry.Diffeomorph.pushforward_contMDiff f hc)

theorem pushforward_const_ne_zero
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) {c : E} (hc : c ≠ 0) (x : E) :
    DifferentialGeometry.Diffeomorph.pushforward f (fun _ ↦ c) x ≠ 0 := by
  intro hz
  have hi := DifferentialGeometry.Diffeomorph.pushforward_image f (fun _ ↦ c) (f.symm x)
  rw [f.apply_symm_apply] at hi
  have he : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (f.symm x) c = 0 := hi.symm.trans hz
  have hback := DifferentialGeometry.Diffeomorph.mfderiv_symm_self f (f.symm x) c
  rw [he, map_zero] at hback
  exact hc hback.symm

private theorem pushforward_modelSpace_apply
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (c x : E) :
    DifferentialGeometry.Diffeomorph.pushforward f (fun _ ↦ c) x =
      fderiv ℝ f (f.symm x) c := by
  have h := DifferentialGeometry.Diffeomorph.pushforward_image f (fun _ ↦ c) (f.symm x)
  rw [f.apply_symm_apply, mfderiv_eq_fderiv] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem tsupport_pushforward_const_sub_subset
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (c : E) :
    let W : E → E := DifferentialGeometry.Diffeomorph.pushforward f (fun _ ↦ c)
    tsupport (fun x ↦ W x - c) ⊆
      tsupport (fun x ↦ f x - x) := by
  dsimp only
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hxt
  have he : (f : E → E) =ᶠ[𝓝 x] id :=
    (notMem_tsupport_iff_eventuallyEq.mp hxt).mono (fun _ h ↦ sub_eq_zero.mp h)
  have hfx : f x = x := he.eq_of_nhds
  have hfi : f.symm x = x := by
    apply f.injective
    exact (f.apply_symm_apply x).trans hfx.symm
  have hdf : fderiv ℝ f x = ContinuousLinearMap.id ℝ E :=
    he.fderiv_eq.trans (fderiv_id)
  apply hx
  exact sub_eq_zero.mpr ((pushforward_modelSpace_apply f c x).trans (by
    rw [hfi, hdf, ContinuousLinearMap.id_apply]))

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_pushforward_const_orbit
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (c x : E) (t : ℝ) :
    HasDerivAt (fun t ↦ f (f.symm x + t • c))
      (DifferentialGeometry.Diffeomorph.pushforward f (fun _ ↦ c)
        (f (f.symm x + t • c)) : E) t := by
  have he := pushforward_modelSpace_apply f c (f (f.symm x + t • c))
  rw [f.symm_apply_apply] at he
  rw [he]
  have ht : HasDerivAt (fun t : ℝ ↦ f.symm x + t • c) c t := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const c).const_add (f.symm x)
  exact (f.contMDiff.contDiff.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t ht

end Poincare.Geometry.VectorField
