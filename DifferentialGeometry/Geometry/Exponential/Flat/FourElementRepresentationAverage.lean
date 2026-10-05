import DifferentialGeometry.Geometry.Exponential.Flat.InvolutiveAverageZero
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
A faithful actual four-element positive involutive orthogonal representation has zero vector
average. Its range is an actual SO3 subgroup; a group equivalence transports both cardinality
and the compiled subgroup average without a supplied trace or averaging relation.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem faithful_four_involutive_sum_zero (K : Type*) [instG : Group K] [instF : Fintype K]
    (hc : Fintype.card K = 4) (rho : K →* (E3 ≃ₗᵢ[ℝ] E3))
    (hrho : Function.Injective rho)
    (hpos : ∀ a : K, 0 < LinearMap.det (rho a).toLinearMap)
    (htwo : ∀ a : K, rho a ^ 2 = 1) : ∀ u : E3, (∑ a : K, rho a u) = 0 := by
  let J := rho.range
  let e : K ≃* J := MonoidHom.ofInjective hrho
  let instJ : Fintype J := Fintype.ofEquiv K e.toEquiv
  have hcJ : Fintype.card J = 4 := (Fintype.card_congr e.toEquiv).symm.trans hc
  have hpJ (a : J) : 0 < LinearMap.det a.val.toLinearMap := by
    obtain ⟨b, hb⟩ := a.property
    rw [← hb]
    exact hpos b
  have htJ (a : J) : a.val ^ 2 = 1 := by
    obtain ⟨b, hb⟩ := a.property
    rw [← hb]
    exact htwo b
  intro u
  calc
    _ = ∑ a : J, a.val u := Fintype.sum_equiv e.toEquiv _ _ (by intro a; rfl)
    _ = 0 := positive_involutive_four_sum_zero J hcJ hpJ htJ u

end DifferentialGeometry.Geometry.FlatSurface
