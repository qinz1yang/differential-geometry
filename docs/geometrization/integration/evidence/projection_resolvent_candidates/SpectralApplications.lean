import DifferentialGeometry.Analysis.InnerProductSpace.FiniteNormalReduction
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

noncomputable section

open Submodule ContinuousLinearMap
open scoped BigOperators

namespace SpectralApplications

private abbrev H := EuclideanSpace ℝ (Fin 3)
private def e (i : Fin 3) : H := PiLp.single 2 i 1
private def L : Submodule ℝ H := ℝ ∙ e 0
private def V : Submodule ℝ H := ℝ ∙ e 2
private def planes (i : Bool) : Submodule ℝ H := if i then ⊤ else L
private def centers (i : Bool) : H := if i then e 2 else e 1
private def weights (i : Bool) : ℝ := if i then 0 else 1
private def O : H →L[ℝ] H := ∑ i : Bool, weights i • (planes i)ᗮ.starProjection
private def Q : H →L[ℝ] H := (⨆ a ∈ ({1} : Set ℝ), Module.End.eigenspace O.toLinearMap a).starProjection

private theorem e_ne_zero (i : Fin 3) : e i ≠ 0 := by
  intro h
  have hh := congrArg (fun v : H => v i) h
  norm_num [e] at hh

private theorem dim_L : Module.finrank ℝ L = 1 := finrank_span_singleton (e_ne_zero 0)

private theorem mem_Vorth (i : Fin 3) (hi : i ≠ 2) : e i ∈ Vᗮ := by
  rw [V, mem_orthogonal_singleton_iff_inner_right]
  simp [e, EuclideanSpace.inner_single_left, PiLp.single_eq_of_ne, hi.symm]

example : Module.finrank ℝ Lᗮ = 2 := by
  have h := L.finrank_add_finrank_orthogonal
  rw [dim_L, finrank_euclideanSpace_fin] at h
  omega

example : O = Lᗮ.starProjection := by
  simp [O, weights, planes]

example : V.starProjection (∑ i : Bool, weights i • Q (e 1 + e 2 - centers i)) = e 2 := by
  have hL : ∀ i ∈ (Finset.univ : Finset Bool), weights i ≠ 0 → planes i ≤ Vᗮ := by
    intro i hi hw
    cases i
    · simp only [planes, Bool.false_eq_true, ↓reduceIte]
      exact Submodule.span_le.mpr (by simpa using mem_Vorth 0 (by decide))
    · simp [weights] at hw
  have hx : ∀ i ∈ (Finset.univ : Finset Bool), weights i ≠ 0 → centers i ∈ Vᗮ := by
    intro i hi hw
    cases i
    · exact mem_Vorth 1 (by decide)
    · simp [weights] at hw
  have h := starProjection_weighted_normal_section V Finset.univ planes centers weights
    (by simp [weights]) hL hx ({1} : Set ℝ) (by simp) (e 1 + e 2)
  change V.starProjection (∑ i : Bool, weights i • Q (e 1 + e 2 - centers i)) =
    V.starProjection (e 1 + e 2) at h
  rw [map_add, (V.starProjection_apply_eq_zero_iff).mpr (mem_Vorth 1 (by decide)),
    starProjection_eq_self_iff.mpr (show e 2 ∈ V from mem_span_singleton_self (e 2)), zero_add] at h
  exact h

example :
    let A : Submodule ℝ H := ℝ ∙ e 1 ⊔ L
    Module.finrank ℝ A ≤ 2 ∧
      Module.finrank ℝ (ContinuousLinearMap.id ℝ H - Lᗮ.starProjection).range ≤ 1 ∧
      Set.MapsTo Lᗮ.starProjection A A ∧
      ∀ v ∈ Aᗮ, Lᗮ.starProjection v = v := by
  have h := finite_affine_family_normal_reduction (Finset.univ : Finset Unit)
    (fun _ => L) (fun _ => e 1) (fun _ => (1 : ℝ)) (by simp)
    (k := 1) (fun _ _ => dim_L.le) ({1} : Set ℝ) (by simp) (e 2)
  have hS : (Finset.univ : Finset Unit) = {()} := by decide
  rw [hS] at h
  dsimp only at h
  simp only [Finset.sum_singleton, one_smul, Finset.sup_singleton,
    Finset.card_singleton, one_mul] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hd : Module.finrank ℝ (({()} : Finset Unit).sup
        (fun _ => ℝ ∙ e 1 ⊔ L) : Submodule ℝ H) ≤ 2 := h.1
    rwa [Finset.sup_singleton] at hd
  · have hd : Module.finrank ℝ (ContinuousLinearMap.id ℝ H -
        ∑ _i ∈ ({()} : Finset Unit), (1 : ℝ) • Lᗮ.starProjection).range ≤ 1 := h.2.1
    rwa [Finset.sum_singleton, one_smul] at hd
  · simpa using h.2.2.1
  · simpa using h.2.2.2.1

example :
    (⨆ a ∈ (∅ : Set ℝ), Module.End.eigenspace (ContinuousLinearMap.id ℝ ℝ).toLinearMap a).starProjection
      (1 : ℝ) ≠ 1 := by
  simp

example :
    (⊤ : Submodule ℂ ℂ).starProjection.comp
      (⨆ a ∈ ({1} : Set ℂ), Module.End.eigenspace (ContinuousLinearMap.id ℂ ℂ).toLinearMap a).starProjection =
        (⊤ : Submodule ℂ ℂ).starProjection := by
  exact starProjection_eigenspace_iSup_of_fixed ⊤ (ContinuousLinearMap.id ℂ ℂ) {1}
    (by simp) (fun _ _ => rfl)

example : Q (e 2) = e 2 := by
  have hO : O = Lᗮ.starProjection := by simp [O, weights, planes]
  have hfix (v : H) (hv : v ∈ Lᗮ) : O v = v := by
    rw [hO, starProjection_eq_self_iff.mpr hv]
  have hmem : e 2 ∈ Lᗮ := by
    rw [L, mem_orthogonal_singleton_iff_inner_right]
    simp [e, EuclideanSpace.inner_single_left]
  exact starProjection_eq_self_iff.mpr
    (le_iSup_eigenspace_of_fixed Lᗮ O.toLinearMap {1} (by simp) hfix hmem)

example :
    (⨆ a ∈ ({1} : Set ℂ), Module.End.eigenspace (ContinuousLinearMap.id ℂ ℂ).toLinearMap a).starProjection.comp
      (⊤ : Submodule ℂ ℂ).starProjection = (⊤ : Submodule ℂ ℂ).starProjection := by
  exact eigenspace_iSup_starProjection_comp_of_fixed ⊤ (ContinuousLinearMap.id ℂ ℂ) {1}
    (by simp) (fun _ _ => rfl)

example : (⊤ : Submodule ℤ ℤ) ≤
    ⨆ a ∈ ({1} : Set ℤ), Module.End.eigenspace (LinearMap.id : Module.End ℤ ℤ) a :=
  le_iSup_eigenspace_of_fixed ⊤ LinearMap.id {1} (by simp) (fun _ _ => rfl)

end SpectralApplications
