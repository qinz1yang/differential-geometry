import DifferentialGeometry.Geometry.Exponential.Flat.UnitPoleStabilizers
import DifferentialGeometry.Geometry.Exponential.Flat.FiniteOrbitCounts

/-!
The actual holonomy pole orbits are labelled by a set of at most three indices. Their real
orbit and cyclic stabilizer cardinals retain the orbit-stabilizer products and the exact
Burnside sum, supplying numerical signatures without a classification premise.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem affineFree_unitPole_orbit_data (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap) :
    let H := (affineLinearHom.comp G.subtype).range
    ∃ k : ℕ, k ≤ 3 ∧ ∃ e : Fin k ≃ Quotient (MulAction.orbitRel H (unitPoleSet H)),
      (∑ i : Fin k, Nat.card (MulAction.orbit H (e i).out)) +
        2 * (Nat.card H - 1) = k * Nat.card H ∧
      ∀ i : Fin k,
        (Nat.card (MulAction.stabilizer H (e i).out) = 2 ∨
          Nat.card (MulAction.stabilizer H (e i).out) = 3 ∨
          Nat.card (MulAction.stabilizer H (e i).out) = 4 ∨
          Nat.card (MulAction.stabilizer H (e i).out) = 6) ∧
        Nat.card (MulAction.orbit H (e i).out) *
          Nat.card (MulAction.stabilizer H (e i).out) = Nat.card H := by
  classical
  let H := (affineLinearHom.comp G.subtype).range
  let P := unitPoleSet H
  have hf : P.Finite := affineFree_finite_unitPoleSet G b hb hfree hpos
  let instPoleFinite : Finite P := hf.to_subtype
  let Ω := Quotient (MulAction.orbitRel H P)
  let instFintypeH : Fintype H := Fintype.ofFinite H
  let instFintypeP : Fintype P := Fintype.ofFinite P
  let instFintypeΩ : Fintype Ω := Fintype.ofFinite Ω
  let k := Fintype.card Ω
  let e : Fin k ≃ Ω := (Fintype.equivFin Ω).symm
  have hk : k ≤ 3 := by
    have h := affineFree_unitPole_orbits_le_three G b hb hfree hpos
    change Nat.card Ω ≤ 3 at h
    simpa only [Nat.card_eq_fintype_card] using h
  have htwo (a : H) (ha : a ≠ 1) : Nat.card (MulAction.fixedBy P a) = 2 := by
    obtain ⟨γ, hγ⟩ := a.property
    change γ.val.linearIsometryEquiv = a.val at hγ
    have hne : γ.val.linearIsometryEquiv ≠ 1 := by
      intro he
      apply ha
      apply Subtype.ext
      exact hγ.symm.trans he
    have hc := affineFree_unit_fixed_card G b hb hfree γ (hpos γ) hne
    rw [hγ] at hc
    exact (Nat.card_congr (unitPole_fixedByEquiv H a ha)).trans
      ((Nat.card_coe_set_eq _).trans hc)
  have hburn := finite_twoFixed_orbit_card_eq H P htwo
  have hsum := finite_orbit_sum_card H P
  have hsumFin : (∑ i : Fin k, Nat.card (MulAction.orbit H (e i).out)) = Nat.card P := by
    calc
      _ = ∑ w : Ω, Nat.card (MulAction.orbit H w.out) :=
        Fintype.sum_equiv e _ _ (by intro i; rfl)
      _ = _ := hsum.symm
  have hkn : Nat.card Ω = k := Nat.card_eq_fintype_card
  refine ⟨k, hk, e, ?_, ?_⟩
  · rw [hsumFin, ← hburn, hkn]
  · intro i
    have hd := affineFree_unitPole_stabilizer_order_cases G b hb hfree hpos (e i).out
    let instOrbit : Fintype (MulAction.orbit H (e i).out) := Fintype.ofFinite _
    let instStabilizer : Fintype (MulAction.stabilizer H (e i).out) := Fintype.ofFinite _
    have hprod : Nat.card (MulAction.orbit H (e i).out) *
        Nat.card (MulAction.stabilizer H (e i).out) = Nat.card H := by
      simpa only [Nat.card_eq_fintype_card] using
        MulAction.card_orbit_mul_card_stabilizer_eq_card_group H (e i).out
    exact ⟨hd, hprod⟩

end DifferentialGeometry.Geometry.FlatSurface
