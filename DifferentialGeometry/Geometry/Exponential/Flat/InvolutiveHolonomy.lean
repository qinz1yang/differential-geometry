import DifferentialGeometry.Geometry.Exponential.Flat.OrthogonalFiniteTrace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Determinant
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
An actual finite positive three-dimensional rotation group in which every element squares
to one has cardinality at most four. Its faithful orthogonal matrix representation has
identity trace three and other traces minus one; the finite average bounds its cardinality.
Its actual exponent and cardinality then give a cyclic group or a Klein-four equivalence.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem finite_involutive_rotation_card_le_four (H : Subgroup (E3 ≃ₗᵢ[ℝ] E3))
    [instH : Finite H] (hpos : ∀ γ : H, 0 < LinearMap.det γ.val.toLinearEquiv.toLinearMap)
    (htwo : ∀ γ : H, γ.val ^ 2 = 1) : Nat.card H ≤ 4 := by
  classical
  let instFintype : Fintype H := Fintype.ofFinite H
  let e := EuclideanSpace.basisFun (Fin 3) ℝ
  let rhoL : (E3 ≃ₗᵢ[ℝ] E3) →* Matrix (Fin 3) (Fin 3) ℝ :=
    { toFun := fun K => LinearMap.toMatrix e.toBasis e.toBasis K.toLinearMap
      map_one' := by
        change LinearMap.toMatrix e.toBasis e.toBasis (1 : E3 →ₗ[ℝ] E3) = 1
        exact LinearMap.toMatrix_one e.toBasis
      map_mul' := by
        intro K T
        change LinearMap.toMatrix e.toBasis e.toBasis (K.toLinearMap * T.toLinearMap) = _
        exact LinearMap.toMatrix_mul e.toBasis K.toLinearMap T.toLinearMap }
  have hrhoL : Function.Injective rhoL := by
    intro K T h
    have he := (LinearMap.toMatrix e.toBasis e.toBasis).injective h
    apply LinearIsometryEquiv.ext
    intro x
    exact congrArg (fun f : E3 →ₗ[ℝ] E3 => f x) he
  let rho := rhoL.comp H.subtype
  have hrho : Function.Injective rho := hrhoL.comp Subtype.val_injective
  have ho (g : H) : (rho g).transpose * rho g = 1 := by
    have hu := g.val.toMatrix_mem_unitaryGroup e e
    have hs := Unitary.star_mul_self_of_mem hu
    change (LinearMap.toMatrix e.toBasis e.toBasis g.val.toLinearMap).transpose *
      LinearMap.toMatrix e.toBasis e.toBasis g.val.toLinearMap = 1
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hs
  have hdet (g : H) : (rho g).det = 1 := by
    have hp := congrArg (fun x : H => (rho x).det) (pow_card_eq_one (x := g))
    simp only [map_pow, Matrix.det_pow, map_one, Matrix.det_one] at hp
    have hdpos : 0 < (rho g).det := by
      change 0 < (LinearMap.toMatrix e.toBasis e.toBasis g.val.toLinearMap).det
      rw [LinearMap.det_toMatrix]
      exact hpos g
    exact (pow_eq_one_iff_of_nonneg hdpos.le (Fintype.card_pos (α := H)).ne').mp hp
  have hidentity : (rho (1 : H)).trace = 3 := by
    rw [map_one, Matrix.trace_one]
    norm_num
  have htrace (g : H) (hg : g ≠ 1) : (rho g).trace = -1 := by
    have hg2 : g ^ 2 = 1 := Subtype.ext (htwo g)
    have hp : rho g ^ 2 = 1 := by rw [← map_pow, hg2, map_one]
    have hne : rho g ≠ 1 := by
      intro he
      exact hg (hrho (he.trans (map_one rho).symm))
    exact orthogonal_nontrivial_involution_trace _ (ho g) (hdet g) hp hne
  have hsum : (∑ g : H, (rho g).trace) = (4 : ℝ) - Fintype.card H := by
    rw [← Finset.add_sum_erase Finset.univ (fun g : H => (rho g).trace)
      (Finset.mem_univ (1 : H)), hidentity]
    have he : (∑ g ∈ Finset.univ.erase (1 : H), (rho g).trace) =
        (Fintype.card H - 1) • (-1 : ℝ) := by
      calc
        _ = ∑ g ∈ Finset.univ.erase (1 : H), (-1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro g hg
          exact htrace g (Finset.mem_erase.mp hg).1
        _ = _ := by simp only [Finset.sum_const,
          Finset.card_erase_of_mem (Finset.mem_univ (1 : H)), Finset.card_univ]
    rw [he, nsmul_eq_mul, Nat.cast_sub (Nat.succ_le_of_lt (Fintype.card_pos (α := H)))]
    norm_num
    ring
  have hn := finite_orthogonal_trace_sum_nonneg rho ho
  rw [hsum] at hn
  have hbound : (Fintype.card H : ℝ) ≤ 4 := by linarith
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast hbound

theorem finite_involutive_rotation_classification (H : Subgroup (E3 ≃ₗᵢ[ℝ] E3))
    [instH : Finite H] (hpos : ∀ γ : H, 0 < LinearMap.det γ.val.toLinearEquiv.toLinearMap)
    (htwo : ∀ γ : H, γ.val ^ 2 = 1) :
    IsCyclic H ∨ Nonempty (H ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) := by
  have hbound := finite_involutive_rotation_card_le_four H hpos htwo
  have hdiv : Monoid.exponent H ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one (fun g => Subtype.ext (htwo g))
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h1 | h2
  · let instSubsingleton : Subsingleton H := Monoid.exp_eq_one_iff.mp h1
    exact Or.inl inferInstance
  · have hcardpos : 0 < Nat.card H := Nat.card_pos
    have hcarddiv : 2 ∣ Nat.card H := h2 ▸ Group.exponent_dvd_nat_card
    have hcases : Nat.card H = 2 ∨ Nat.card H = 4 := by
      obtain ⟨m, hm⟩ := hcarddiv
      omega
    rcases hcases with hcard2 | hcard4
    · exact Or.inl (isCyclic_of_prime_card (p := 2) hcard2)
    · let instKlein : IsKleinFour H := ⟨hcard4, h2⟩
      let instTarget : IsKleinFour (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
        { card_four := by simp
          exponent_two := by simp [Monoid.exponent_prod] }
      exact Or.inr IsKleinFour.nonempty_mulEquiv

end DifferentialGeometry.Geometry.FlatSurface
