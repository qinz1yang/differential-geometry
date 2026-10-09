import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.QuotientCoordinates
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.TranslationLattices

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.HorosphereProjection

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open HyperbolicAction (poMulAction)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)
open MobiusBoundary (ptInfty)
open BusemannCocycle (poConfFactor)
open Horospherical (Horizontal ofCoords horizontal)
open TranslationLattices (latticeGroup translation translation_smul_ofCoords)

variable {m : ℕ} (P : Subgroup (PO (m + 1) 1))

private local instance : MulAction (PO (m + 1) 1) (HUpper (m + 1)) :=
  poMulAction (Nat.le_add_left 1 m)

private local instance : MulAction P (HUpper (m + 1)) :=
  EquivariantMap.subAction (Nat.le_add_left 1 m) P

theorem quotientHorosphereCoordinates_eq_iff_sub_mem
    (ξ : BoundaryH (m + 1)) (c : ℝ) (a : PO (m + 1) 1)
    (ha : (poBoundaryMulAction (Nat.le_add_left 1 m)).smul a ξ = ptInfty)
    (Λ : Submodule ℤ (Horizontal m))
    (hP : P.map (MulAut.conj a).toMonoidHom = latticeGroup Λ)
    (x y : Horizontal m) :
    quotientHorosphereCoordinates P ξ c a ha x = quotientHorosphereCoordinates P ξ c a ha y ↔
      x - y ∈ Λ := by
  let h := Real.exp (Real.log (poConfFactor (Nat.le_add_left 1 m) a ξ) - c)
  have hh : 0 < h := Real.exp_pos _
  constructor
  · intro hq
    have he := congrArg Subtype.val hq
    rw [quotientHorosphereCoordinates_apply, quotientHorosphereCoordinates_apply] at he
    obtain ⟨γ, hγ⟩ := Quotient.exact he
    change (γ : PO (m + 1) 1) • (a⁻¹ • ofCoords y h hh) =
      a⁻¹ • ofCoords x h hh at hγ
    have hg : (MulAut.conj a) (γ : PO (m + 1) 1) ∈ latticeGroup Λ := by
      rw [← hP]
      exact ⟨γ, γ.property, rfl⟩
    obtain ⟨u, hu⟩ := hg
    change translation (u.toAdd : Horizontal m) =
      a * (γ : PO (m + 1) 1) * a⁻¹ at hu
    have hc : translation (u.toAdd : Horizontal m) • ofCoords y h hh = ofCoords x h hh := by
      rw [hu, mul_smul, mul_smul, hγ, smul_inv_smul]
    have hxy : y + (u.toAdd : Horizontal m) = x := by
      have hz := congrArg horizontal hc
      simpa only [translation_smul_ofCoords, Horospherical.horizontal_ofCoords] using hz
    have hs : x - y = (u.toAdd : Horizontal m) := by
      rw [← hxy]
      abel
    rw [hs]
    exact u.toAdd.property
  · intro hxy
    have hg : translation (x - y) ∈ P.map (MulAut.conj a).toMonoidHom := by
      rw [hP]
      exact ⟨Multiplicative.ofAdd (⟨x - y, hxy⟩ : Λ), rfl⟩
    obtain ⟨γ, hγP, hγ⟩ := hg
    change a * γ * a⁻¹ = translation (x - y) at hγ
    apply Subtype.ext
    rw [quotientHorosphereCoordinates_apply, quotientHorosphereCoordinates_apply]
    apply Quotient.sound
    refine ⟨⟨γ, hγP⟩, ?_⟩
    change γ • (a⁻¹ • ofCoords y h hh) = a⁻¹ • ofCoords x h hh
    have hc : a • (γ • (a⁻¹ • ofCoords y h hh)) = ofCoords x h hh := by
      calc
        _ = (a * γ * a⁻¹) • ofCoords y h hh := by rw [mul_smul, mul_smul]
        _ = translation (x - y) • ofCoords y h hh := by rw [hγ]
        _ = ofCoords (y + (x - y)) h hh := translation_smul_ofCoords _ _ _ _
        _ = ofCoords x h hh := by congr 1; abel
    have hz := congrArg (fun p : HUpper (m + 1) => a⁻¹ • p) hc
    simpa only [inv_smul_smul] using hz

end DifferentialGeometry.HorosphereProjection
