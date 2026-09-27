import DifferentialGeometry.Topology.ProjectiveSpace.Real
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace Real A]

def realProjectiveSpaceToProjectivization (p : RealProjectiveSpace A) :
    Projectivization Real A :=
  Quotient.lift (fun y : Metric.sphere (0 : A) 1 =>
    Projectivization.mk Real (y : A) (ne_zero_of_mem_unit_sphere y)) (by
    intro x y hxy
    have hq : realProjectiveSpaceQuotientMap x = realProjectiveSpaceQuotientMap y :=
      Quotient.sound hxy
    rcases realProjectiveSpaceQuotientMap_eq_iff.mp hq with rfl | hneg
    · rfl
    · apply (Projectivization.mk_eq_mk_iff' Real _ _ _ _).mpr
      exact ⟨-1, by simpa only [neg_one_smul] using hneg.symm⟩) p

theorem realProjectiveSpaceToProjectivization_injective :
    Function.Injective (realProjectiveSpaceToProjectivization (A := A)) := by
  intro p q
  induction p using Quotient.inductionOn with
  | _ x =>
    induction q using Quotient.inductionOn with
    | _ y =>
      intro h
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' Real _ _ _ _).mp h
      have hn := congrArg norm ha
      rw [norm_smul, norm_eq_of_mem_sphere x,
        norm_eq_of_mem_sphere y, mul_one] at hn
      have haone : a = 1 ∨ a = -1 := by
        rw [Real.norm_eq_abs] at hn
        exact (abs_eq (by norm_num : (0 : Real) ≤ 1)).mp hn
      apply realProjectiveSpaceQuotientMap_eq_iff.mpr
      rcases haone with rfl | rfl
      · exact Or.inl (Subtype.ext (by simpa using ha.symm))
      · exact Or.inr (by simpa using ha.symm)

theorem realProjectiveSpaceToProjectivization_surjective :
    Function.Surjective (realProjectiveSpaceToProjectivization (A := A)) := by
  intro p
  induction p using Projectivization.ind with
  | h v hv =>
    let y : Metric.sphere (0 : A) 1 := ⟨‖v‖⁻¹ • v, by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
    refine ⟨realProjectiveSpaceQuotientMap y, ?_⟩
    apply (Projectivization.mk_eq_mk_iff' Real _ _ _ _).mpr
    exact ⟨‖v‖⁻¹, rfl⟩

noncomputable def realProjectiveSpaceEquivProjectivization :
    RealProjectiveSpace A ≃ Projectivization Real A :=
  Equiv.ofBijective realProjectiveSpaceToProjectivization
    ⟨realProjectiveSpaceToProjectivization_injective,
      realProjectiveSpaceToProjectivization_surjective⟩

end DifferentialGeometry
