import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.SmoothCylinder
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.QuotientCoordinateFibers
import DifferentialGeometry.Topology.Manifold.LatticeQuotient

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open HyperbolicBoundary (poBoundaryMulAction)
open MobiusBoundary (ptInfty)
open CuspCrossSections (endStabilizer)
open Busemann (horosphere)
open BusemannCocycle (poConfFactor)
open Horospherical (Horizontal ofCoords horizontal)
open HorosphereProjection (quotientHorosphereCoordinates)
open TranslationLattices (latticeGroup translation)

private local instance {m : ℕ} : MulAction (PO (m + 1) 1) (HUpper (m + 1)) :=
  HyperbolicAction.poMulAction (Nat.le_add_left 1 m)

private local instance {m : ℕ} (Δ : Subgroup (PO (m + 1) 1)) : MulAction Δ (HUpper (m + 1)) :=
  EquivariantMap.subAction (Nat.le_add_left 1 m) Δ

private theorem isCancelSMul_of_conjugate_lattice
    (P : Subgroup (PO 3 1)) (a : PO 3 1) (Λ : Submodule ℤ (Horizontal 2))
    (hP : (P).map (MulAut.conj a).toMonoidHom = latticeGroup Λ) :
    IsCancelSMul P (HUpper 3) := by
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro γ p hp
  change (γ : PO 3 1) • p = p at hp
  have hg : (MulAut.conj a) (γ : PO 3 1) ∈ latticeGroup Λ := by
    rw [← hP]
    exact ⟨γ, γ.property, rfl⟩
  obtain ⟨u, hu⟩ := hg
  change translation (u.toAdd : Horizontal 2) = a * (γ : PO 3 1) * a⁻¹ at hu
  have hc : translation (u.toAdd : Horizontal 2) • (a • p) = a • p := by
    rw [hu, mul_smul, mul_smul, inv_smul_smul, hp]
  have hz : (u.toAdd : Horizontal 2) = 0 := by
    have hx := congrArg horizontal hc
    simpa only [TranslationLattices.translation_smul, Horospherical.horizontal_ofCoords,
      add_eq_left] using hx
  have hg1 : (MulAut.conj a) (γ : PO 3 1) = 1 := by
    change a * (γ : PO 3 1) * a⁻¹ = 1
    rw [← hu, hz, TranslationLattices.translation_zero]
  have hγ1 : (γ : PO 3 1) = 1 :=
    (MulAut.conj a).injective (by simpa only [map_one] using hg1)
  exact Subtype.ext hγ1

variable {Γ : Subgroup (PO 3 1)} [DiscreteTopology Γ] {r : ℝ}
  (D : FiniteCuspTruncation (Nat.le_add_left 1 2) Γ r) (ξ : D.centers)

local notation "P" => endStabilizer (Nat.le_add_left 1 2) Γ (Set.singleton ξ.val)
local notation "hΓ" => (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ))
local notation "π" => Quotient.mk (MulAction.orbitRel P (HUpper 3))
local notation "S" => (π '' horosphere ξ.val (D.level ξ))

theorem exists_horosphere_torus_diffeomorph_of_translation_lattice
    (a : PO 3 1)
    (ha : (poBoundaryMulAction (Nat.le_add_left 1 2)).smul a ξ.val = ptInfty)
    (Λ : Submodule ℤ (Horizontal 2)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hP : (P).map (MulAut.conj a).toMonoidHom = latticeGroup Λ) :
    let _ := isCancelSMul_of_conjugate_lattice P a Λ hP
    let _ := D.horosphereQuotientChartedSpace hΓ ξ
    ∃ b : Module.Basis (Fin 2) ℤ Λ,
      ∃ F : Diffeomorph ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, Fin 2 → ℝ)
          (Circle × Circle) S ∞,
        (∀ t : Fin 2 → ℝ,
          (F (Circle.exp (2 * Real.pi * t 0), Circle.exp (2 * Real.pi * t 1))).val =
            π ((HyperbolicAction.poMulAction (Nat.le_add_left 1 2)).smul a⁻¹
              (ofCoords ((b.ofZLatticeBasis ℝ Λ).equivFunL.symm t)
                (Real.exp (Real.log (poConfFactor (Nat.le_add_left 1 2) a ξ.val) - D.level ξ))
                (Real.exp_pos _)))) ∧
        (∀ x, F.symm (quotientHorosphereCoordinates P ξ.val (D.level ξ) a ha x) =
          (Circle.exp (2 * Real.pi * (b.ofZLatticeBasis ℝ Λ).equivFunL x 0),
            Circle.exp (2 * Real.pi * (b.ofZLatticeBasis ℝ Λ).equivFunL x 1))) := by
  let _ := isCancelSMul_of_conjugate_lattice P a Λ hP
  let _ := OrbifoldCompactness.properlyDiscontinuous_subAction
    (Nat.le_add_left 1 2) P ((hΓ).mono inf_le_left)
  let _ := D.horosphereQuotientChartedSpace hΓ ξ
  let q := quotientHorosphereCoordinates P ξ.val (D.level ξ) a ha
  have hq : IsLocalDiffeomorph 𝓘(ℝ, Horizontal 2) 𝓘(ℝ, Fin 2 → ℝ) ∞ q :=
    HorosphereProjection.isLocalDiffeomorph_quotientHorosphereCoordinates
      P ξ.val (CuspCrossSections.horospherical_endStabilizer
        (Nat.le_add_left 1 2) Γ hΓ (D.region_nonempty ξ)) (D.level ξ) a ha
  have hs : Function.Surjective q :=
    HorosphereProjection.quotientHorosphereCoordinates_surjective P ξ.val (D.level ξ) a ha
  have hf (x y : Horizontal 2) : q x = q y ↔ x - y ∈ Λ :=
    HorosphereProjection.quotientHorosphereCoordinates_eq_iff_sub_mem
      P ξ.val (D.level ξ) a ha Λ hP x y
  obtain ⟨b, F, hF, hFi⟩ := exists_torus_diffeomorph_of_lattice_fibers Λ q hq hs hf
  refine ⟨b, F, ?_, hFi⟩
  intro t
  rw [hF t]
  exact HorosphereProjection.quotientHorosphereCoordinates_apply P ξ.val (D.level ξ) a ha _

end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation
