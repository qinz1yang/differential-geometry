import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.Orientation
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Matrix
import DifferentialGeometry.Bundle.Orientation.Classes

noncomputable section

open Set Module

namespace Poincare.ContinuousAlternatingMap

variable {m : ℕ} {E : Type*}

section Topological

variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

def positiveForms (o : Orientation ℝ E (Fin m)) : Set (E [⋀^Fin m]→L[ℝ] ℝ) :=
  {η | ∃ h : η.toAlternatingMap ≠ 0, rayOfNeZero ℝ η.toAlternatingMap h = o}

theorem ne_zero_of_mem_positiveForms {o : Orientation ℝ E (Fin m)}
    {η : E [⋀^Fin m]→L[ℝ] ℝ} (hη : η ∈ positiveForms o) : η ≠ 0 := by
  obtain ⟨h, _⟩ := hη
  intro hz
  exact h (congrArg ContinuousAlternatingMap.toAlternatingMap hz)

theorem convex_positiveForms (o : Orientation ℝ E (Fin m)) :
    Convex ℝ (positiveForms o) := by
  intro η hη θ hθ a b ha hb hab
  obtain ⟨hη0, hη⟩ := hη
  obtain ⟨hθ0, hθ⟩ := hθ
  have hsame : SameRay ℝ η.toAlternatingMap θ.toAlternatingMap :=
    (ray_eq_iff hη0 hθ0).mp (hη.trans hθ.symm)
  obtain ⟨c, hc, heq⟩ := hsame.exists_pos_right hη0 hθ0
  have hform : η = c • θ := ContinuousAlternatingMap.toAlternatingMap_injective heq
  have hpos : 0 < a * c + b := by
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by linarith
      simpa [hb0, ha1] using hc
    · exact add_pos_of_nonneg_of_pos (mul_nonneg ha hc.le) (lt_of_le_of_ne hb (Ne.symm hb0))
  rw [hform, smul_smul, ← add_smul]
  refine ⟨smul_ne_zero hpos.ne' hθ0, ?_⟩
  exact (ray_pos_smul hθ0 hpos _).trans hθ

theorem comp_mem_positiveForms {F : Type*} [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] {o : Orientation ℝ E (Fin m)}
    {η : E [⋀^Fin m]→L[ℝ] ℝ} (hη : η ∈ positiveForms o) (e : F ≃L[ℝ] E) :
    η.compContinuousLinearMap e.toContinuousLinearMap ∈
      positiveForms (Orientation.map (Fin m) e.symm.toLinearEquiv o) := by
  obtain ⟨hη0, hη⟩ := hη
  refine ⟨mt (η.toAlternatingMap.compLinearEquiv_eq_zero_iff e.toLinearEquiv).mp hη0, ?_⟩
  rw [← hη, Orientation.map_apply]
  rfl

end Topological

section Normed

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem continuous_topForm (hm : finrank ℝ E = m) (η : E [⋀^Fin m]→ₗ[ℝ] ℝ) :
    Continuous η := by
  let b := finBasisOfFinrankEq ℝ E hm
  rw [η.eq_smul_basis_det b]
  change Continuous (fun v => η b * b.det v)
  apply continuous_const.mul
  change Continuous (fun v : Fin m → E => b.det v)
  simp only [Basis.det_apply]
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_apply i).comp
    (b.equivFun.toContinuousLinearEquiv.continuous.comp (continuous_apply j))

theorem nonempty_positiveForms (hm : finrank ℝ E = m) (o : Orientation ℝ E (Fin m)) :
    (positiveForms o).Nonempty := by
  let η : E [⋀^Fin m]→L[ℝ] ℝ :=
    { toAlternatingMap := o.someVector, cont := continuous_topForm hm o.someVector }
  exact ⟨η, o.someVector_ne_zero, o.someVector_ray⟩

end Normed

end Poincare.ContinuousAlternatingMap
