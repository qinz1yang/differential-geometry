/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

noncomputable section

open Set Filter MeasureTheory

namespace DifferentialGeometry.MeasurableOrbitDescent

variable {Γ X Y : Type*} [Group Γ] [Countable Γ] [MulAction Γ X]
variable [MeasurableSpace X] [MeasurableSpace Y] [TopologicalSpace Y]
variable [BorelSpace Y] [T2Space Y] [SecondCountableTopology Y]

omit [Countable Γ] [MeasurableSpace X] [MeasurableSpace Y]
    [TopologicalSpace Y] [BorelSpace Y] [T2Space Y]
    [SecondCountableTopology Y] in
theorem invariant_locus_smul (F : X → Y) (a : Γ) (x : X) :
    (∀ γ : Γ, F (γ • (a • x)) = F (a • x)) ↔
      ∀ γ : Γ, F (γ • x) = F x := by
  constructor
  · intro hx γ
    have hγ := hx (γ * a⁻¹)
    have h1 := hx a⁻¹
    simpa only [mul_smul, inv_smul_smul] using hγ.trans h1.symm
  · intro hx γ
    simpa only [mul_smul] using (hx (γ * a)).trans (hx a).symm

theorem exists_invariant_representative (μ : Measure X)
    (hm : ∀ γ : Γ, Measurable (fun x : X => γ • x))
    (F : X → Y) (hF : Measurable F)
    (hInv : ∀ γ : Γ, (fun x => F (γ • x)) =ᵐ[μ] F) (y₀ : Y) :
    ∃ F' : X → Y, Measurable F' ∧ F' =ᵐ[μ] F ∧
      ∀ (γ : Γ) (x : X), F' (γ • x) = F' x := by
  classical
  let S : Set X := {x | ∀ γ : Γ, F (γ • x) = F x}
  have hS : MeasurableSet S := by
    simpa only [S, ofPred_forall, Function.comp_def] using
      (MeasurableSet.iInter fun γ => measurableSet_eq_fun (hF.comp (hm γ)) hF)
  have hSa : ∀ᵐ x ∂μ, x ∈ S := ae_all_iff.mpr hInv
  let F' : X → Y := S.piecewise F (fun _ => y₀)
  refine ⟨F', hF.piecewise hS measurable_const, ?_, ?_⟩
  · filter_upwards [hSa] with x hx
    exact piecewise_eq_of_mem S F (fun _ => y₀) hx
  · intro γ x
    have hs : γ • x ∈ S ↔ x ∈ S := invariant_locus_smul F γ x
    by_cases hx : x ∈ S
    · change S.piecewise F (fun _ => y₀) (γ • x) =
        S.piecewise F (fun _ => y₀) x
      rw [piecewise_eq_of_mem S F (fun _ => y₀) (hs.mpr hx),
        piecewise_eq_of_mem S F (fun _ => y₀) hx]
      exact hx γ
    · change S.piecewise F (fun _ => y₀) (γ • x) =
        S.piecewise F (fun _ => y₀) x
      rw [piecewise_eq_of_notMem S F (fun _ => y₀) (hs.not.mpr hx),
        piecewise_eq_of_notMem S F (fun _ => y₀) hx]

theorem exists_measurable_descent (μ : Measure X)
    (hm : ∀ γ : Γ, Measurable (fun x : X => γ • x))
    (F : X → Y) (hF : Measurable F)
    (hInv : ∀ γ : Γ, (fun x => F (γ • x)) =ᵐ[μ] F) (y₀ : Y) :
    ∃ Fq : MulAction.orbitRel.Quotient Γ X → Y, Measurable Fq ∧
      (fun x => Fq (Quotient.mk'' x)) =ᵐ[μ] F := by
  obtain ⟨F', hF', he, hI⟩ := exists_invariant_representative μ hm F hF hInv y₀
  let Fq : MulAction.orbitRel.Quotient Γ X → Y :=
    Quotient.lift F' (fun x y h => by
      obtain ⟨γ, rfl⟩ := h
      exact hI γ y)
  exact ⟨Fq, measurable_from_quotient.mpr hF', he⟩

end DifferentialGeometry.MeasurableOrbitDescent
