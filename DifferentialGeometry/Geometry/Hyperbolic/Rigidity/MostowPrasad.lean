/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.Rigidity.Boundary

open DifferentialGeometry.ProjectiveOrthogonalGroup
open MeasureTheory

namespace DifferentialGeometry.ProjectiveOrthogonalGroup

theorem mostow_rigidity (n : ℕ) (hn : 3 ≤ n) (Γ Λ : Subgroup (PO n 1))
    (disc_Γ : IsDiscrete (SetLike.coe Γ)) (disc_Λ : IsDiscrete (SetLike.coe Λ))
    [HasFundamentalDomain Γ (PO n 1)] [HasFundamentalDomain Λ (PO n 1)]
    (covol_Γ : covolume Γ (PO n 1) ≠ ⊤) (covol_Λ : covolume Λ (PO n 1) ≠ ⊤)
    (f : Γ ≃* Λ) : ∃ g : PO n 1, ∀ γ : Γ, f γ = g * γ * g⁻¹ := by
  have hΓ : Countable ↥Γ := DifferentialGeometry.ProjectiveOrthogonalGroup.Lattices.countable_of_isDiscrete Γ disc_Γ
  have hΛ : Countable ↥Λ := DifferentialGeometry.ProjectiveOrthogonalGroup.Lattices.countable_of_isDiscrete Λ disc_Λ
  have hcovΓ : covolume Γ (PO n 1) ≠ 0 := DifferentialGeometry.ProjectiveOrthogonalGroup.Lattices.covolume_ne_zero Γ disc_Γ
  have hcovΛ : covolume Λ (PO n 1) ≠ 0 := DifferentialGeometry.ProjectiveOrthogonalGroup.Lattices.covolume_ne_zero Λ disc_Λ
  have hΓinf : Infinite ↥Γ :=
    DifferentialGeometry.ProjectiveOrthogonalGroup.Center.infinite_of_finite_covolume (by omega) Γ covol_Γ
  have hΛinf : Infinite ↥Λ :=
    DifferentialGeometry.ProjectiveOrthogonalGroup.Center.infinite_of_finite_covolume (by omega) Λ covol_Λ
  exact DifferentialGeometry.MostowRigidity.exists_conj_of_equivariant_mobius_boundary hn f
    (DifferentialGeometry.MostowRigidity.exists_equivariant_mobius_boundary_homeomorph hn Γ Λ disc_Γ disc_Λ hΓ hΛ hΓinf hΛinf
      covol_Γ hcovΓ covol_Λ hcovΛ f)

theorem mostow_rigidity_conjugacy (n : ℕ) (hn : 3 ≤ n) (Γ Λ : Subgroup (PO n 1))
    (disc_Γ : IsDiscrete (SetLike.coe Γ)) (disc_Λ : IsDiscrete (SetLike.coe Λ))
    [HasFundamentalDomain Γ (PO n 1)] [HasFundamentalDomain Λ (PO n 1)]
    (covol_Γ : covolume Γ (PO n 1) ≠ ⊤) (covol_Λ : covolume Λ (PO n 1) ≠ ⊤)
    (f : Γ ≃* Λ) :
    ∃ g : PO n 1, Λ = Subgroup.map (MulAut.conj g).toMonoidHom Γ := by
  obtain ⟨g, hg⟩ := mostow_rigidity n hn Γ Λ disc_Γ disc_Λ covol_Γ covol_Λ f
  exact ⟨g, DifferentialGeometry.ProjectiveOrthogonalGroup.Lattices.eq_map_conj_of_forall_conj_eq f hg⟩

end DifferentialGeometry.ProjectiveOrthogonalGroup
