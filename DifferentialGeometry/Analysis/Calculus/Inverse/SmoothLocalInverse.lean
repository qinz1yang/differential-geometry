import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace









noncomputable section

open Set Filter Function
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]



theorem exists_smooth_localInverse {f : E → E} {s : Set E} {x : E}
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) (hx : x ∈ s)
    (A : E ≃L[ℝ] E) (hA : HasFDerivAt f (A : E →L[ℝ] E) x) :
    ∃ e : OpenPartialHomeomorph E E, x ∈ e.source ∧ e.source ⊆ s ∧
      (e : E → E) = f ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  have hfx : ContDiffAt ℝ ∞ f x := (hf x hx).contDiffAt (hs.mem_nhds hx)
  have hdf : ContinuousAt (fderiv ℝ f) x :=
    (hf.continuousOn_fderiv_of_isOpen hs (by simp) x hx).continuousAt (hs.mem_nhds hx)
  have hinv : ∀ᶠ y in 𝓝 x, ∃ B : E ≃L[ℝ] E, (B : E →L[ℝ] E) = fderiv ℝ f y := by
    have hAn : {D : E →L[ℝ] E | ∃ B : E ≃L[ℝ] E, (B : E →L[ℝ] E) = D} ∈
        𝓝 (fderiv ℝ f x) := by
      rw [hA.fderiv]
      exact A.nhds
    exact hdf hAn
  obtain ⟨V, hVsub, hVo, hxV⟩ := mem_nhds_iff.mp (Filter.inter_mem (hs.mem_nhds hx) hinv)
  let φ := hfx.toOpenPartialHomeomorph f hA (by simp : (∞ : ℕ∞ω) ≠ 0)
  let e := φ.restrOpen V hVo
  have hxe : x ∈ e.source := ⟨hfx.mem_toOpenPartialHomeomorph_source hA (by simp), hxV⟩
  have hes : e.source ⊆ s := fun _ hy => (hVsub hy.2).1
  refine ⟨e, hxe, hes, rfl, ?_⟩
  intro y hy
  have hys := e.map_target hy
  obtain ⟨B, hB⟩ := (hVsub hys.2).2
  have hfy : ContDiffAt ℝ ∞ f (e.symm y) :=
    (hf _ (hes hys)).contDiffAt (hs.mem_nhds (hes hys))
  apply ContDiffAt.contDiffWithinAt
  apply e.contDiffAt_symm hy (f₀' := B)
  · change HasFDerivAt f (B : E →L[ℝ] E) (e.symm y)
    rw [hB]
    exact (hfy.differentiableAt (by simp)).hasFDerivAt
  · exact hfy



theorem exists_smooth_local_leftInverse {f : E → F} {s : Set E} {x : E}
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) (hx : x ∈ s)
    (hi : Injective (fderiv ℝ f x)) :
    ∃ (r : F → E) (U : Set F) (V : Set E), IsOpen U ∧ f x ∈ U ∧
      IsOpen V ∧ x ∈ V ∧ V ⊆ s ∧ ContDiffOn ℝ ∞ r U ∧
      (∀ y ∈ V, r (f y) = y) ∧ r (f x) = x := by
  obtain ⟨L, hL⟩ := (fderiv ℝ f x).toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hi)
  let A : F →L[ℝ] E := L.toContinuousLinearMap
  let h : E → E := A ∘ f
  have hh : ContDiffOn ℝ ∞ h s := A.contDiff.comp_contDiffOn hf
  have hhderiv : HasFDerivAt h (ContinuousLinearMap.id ℝ E) x := by
    have hd := A.hasFDerivAt.comp x
      (((hf x hx).contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    convert hd using 1
    apply ContinuousLinearMap.ext
    intro v
    exact (congrArg (fun B : E →ₗ[ℝ] E => B v) hL).symm
  obtain ⟨e, hxe, hes, he, hei⟩ := exists_smooth_localInverse hs hh hx
    (ContinuousLinearEquiv.refl ℝ E) hhderiv
  let r : F → E := e.symm ∘ A
  let U : Set F := A ⁻¹' e.target
  have hUf : f x ∈ U := by
    change h x ∈ e.target
    rw [← he]
    exact e.map_source hxe
  have hr : ContDiffOn ℝ ∞ r U := hei.comp A.contDiff.contDiffOn (fun _ hy => hy)
  have hleft (y : E) (hy : y ∈ e.source) : r (f y) = y := by
    change e.symm (h y) = y
    rw [← he]
    exact e.left_inv hy
  exact ⟨r, U, e.source, e.open_target.preimage A.continuous, hUf,
    e.open_source, hxe, hes, hr, hleft, hleft x hxe⟩

end DifferentialGeometry.Analysis
