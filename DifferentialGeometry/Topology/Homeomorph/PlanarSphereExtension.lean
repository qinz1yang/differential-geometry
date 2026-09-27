/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Homeomorph.CircleIsotopy
import DifferentialGeometry.Topology.Homeomorph.SphereFamilyExtension
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open Set Metric

namespace DifferentialGeometry.Topology

noncomputable def planarReflection :
    EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr.symm.trans
    (Complex.conjLIE.trans Complex.orthonormalBasisOneI.repr)

@[simp]
theorem planarReflection_apply_repr (z : ℂ) :
    planarReflection (Complex.orthonormalBasisOneI.repr z) =
      Complex.orthonormalBasisOneI.repr (star z) := by
  simp [planarReflection]

private noncomputable def planeCircleParameter :
    loopCircle ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).trans
    (Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype fun z => by
      change z ∈ sphere (0 : ℂ) 1 ↔ Complex.orthonormalBasisOneI.repr z ∈ sphere 0 1
      rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm,
        Complex.orthonormalBasisOneI.repr.norm_map])

private theorem planeCircleParameter_apply (θ : loopCircle) :
    (planeCircleParameter θ : EuclideanSpace ℝ (Fin 2)) =
      Complex.orthonormalBasisOneI.repr (AddCircle.toCircle θ : ℂ) := by
  change Complex.orthonormalBasisOneI.repr
    ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero) θ : ℂ) = _
  rw [AddCircle.homeomorphCircle_apply]

private theorem planeCircleParameter_neg (θ : loopCircle) :
    (planeCircleParameter (-θ) : EuclideanSpace ℝ (Fin 2)) =
      planarReflection (planeCircleParameter θ) := by
  rw [planeCircleParameter_apply, planeCircleParameter_apply, planarReflection_apply_repr,
    AddCircle.toCircle_neg, Circle.coe_inv]
  congr 1
  exact Complex.inv_eq_conj (Circle.norm_coe (AddCircle.toCircle θ))

private theorem exists_supported_plane_circle_extension (φ : loopCircle ≃ₜ loopCircle)
    (hφ : HasIncreasingCircleLift φ) :
    ∃ g : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2),
      (∀ x, ‖g x‖ = ‖x‖) ∧
      (∀ θ, g (planeCircleParameter θ) = planeCircleParameter (φ θ)) ∧
      EqOn g id (ball 0 2)ᶜ := by
  obtain ⟨H, hH, hHi, hH0, hH1⟩ := exists_isotopy_circle_of_hasIncreasingCircleLift φ hφ
  let P := planeCircleParameter
  let K (t : unitInterval) := (P.symm.trans (H t)).trans P
  have hK : Continuous (fun p : unitInterval × sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 =>
      K p.1 p.2) := P.continuous.comp
    (hH.comp (continuous_fst.prodMk (P.symm.continuous.comp continuous_snd)))
  have hKi : Continuous (fun p : unitInterval × sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 =>
      (K p.1).symm p.2) := P.continuous.comp
    (hHi.comp (continuous_fst.prodMk (P.symm.continuous.comp continuous_snd)))
  have hK0 : K 0 = Homeomorph.refl _ := by
    apply Homeomorph.ext
    intro x
    change P (H 0 (P.symm x)) = x
    rw [hH0]
    exact P.apply_symm_apply x
  obtain ⟨g, hg, hgS, hgfix⟩ := exists_supported_homeomorph_of_sphere_isotopy K hK hKi hK0
  refine ⟨g, hg, fun θ => ?_, hgfix⟩
  rw [hgS]
  change (P (H 1 (P.symm (P θ))) : EuclideanSpace ℝ (Fin 2)) = P (φ θ)
  rw [P.symm_apply_apply, hH1]

theorem exists_supported_homeomorph_sphere_or_reflection
    (ψ : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    ∃ L : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2),
      (L = LinearIsometryEquiv.refl ℝ _ ∨ L = planarReflection) ∧
      ∃ g : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2),
        (∀ x, ‖g x‖ = ‖x‖) ∧
        (∀ x : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
          g x = ψ ⟨L x, by simpa only [mem_sphere_zero_iff_norm, L.norm_map] using x.property⟩) ∧
        EqOn g id (ball 0 2)ᶜ := by
  let P := planeCircleParameter
  let φ := (P.trans ψ).trans P.symm
  by_cases hφ : HasIncreasingCircleLift φ
  · obtain ⟨g, hg, hgP, hgfix⟩ := exists_supported_plane_circle_extension φ hφ
    refine ⟨LinearIsometryEquiv.refl ℝ _, Or.inl rfl, g, hg, ?_, hgfix⟩
    intro x
    obtain ⟨θ, rfl⟩ := P.surjective x
    rw [hgP]
    change (P (P.symm (ψ (P θ))) : EuclideanSpace ℝ (Fin 2)) = ψ (P θ)
    rw [P.apply_symm_apply]
  · let N : loopCircle ≃ₜ loopCircle := Homeomorph.neg _
    have hN : ¬ HasIncreasingCircleLift N := not_hasIncreasingCircleLift_neg
    have hpos : HasIncreasingCircleLift (N.trans φ) :=
      hasIncreasingCircleLift_comp_of_not_hasIncreasingCircleLift φ N hφ hN
    obtain ⟨g, hg, hgP, hgfix⟩ := exists_supported_plane_circle_extension (N.trans φ) hpos
    refine ⟨planarReflection, Or.inr rfl, g, hg, ?_, hgfix⟩
    intro x
    obtain ⟨θ, rfl⟩ := P.surjective x
    rw [hgP]
    have hneg : P (-θ) =
        ⟨planarReflection (P θ), by
          simpa only [mem_sphere_zero_iff_norm, planarReflection.norm_map] using (P θ).property⟩ :=
      Subtype.ext (planeCircleParameter_neg θ)
    change (P (P.symm (ψ (P (-θ)))) : EuclideanSpace ℝ (Fin 2)) = _
    rw [P.apply_symm_apply, hneg]

end DifferentialGeometry.Topology
