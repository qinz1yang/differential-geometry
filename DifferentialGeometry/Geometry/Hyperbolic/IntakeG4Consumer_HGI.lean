import DifferentialGeometry.Geometry.Hyperbolic.Rigidity.MostowPrasad

/-!
# Consumer of the G4 intake (S-HG-INTAKE, suffix `_HGI`)

Algebraic Mostow-Prasad rigidity (lattices in `PO n 1`, `n ≥ 3`) in dimension three:
an isomorphism of cofinite-volume discrete subgroups of `PO 3 1` is realised by conjugation.
-/

set_option autoImplicit false

open MeasureTheory DifferentialGeometry.ProjectiveOrthogonalGroup

theorem mostow_rigidity_conjugacy_three_HGI (Γ Λ : Subgroup (PO 3 1))
    (disc_Γ : IsDiscrete (SetLike.coe Γ)) (disc_Λ : IsDiscrete (SetLike.coe Λ))
    [HasFundamentalDomain Γ (PO 3 1)] [HasFundamentalDomain Λ (PO 3 1)]
    (covol_Γ : covolume Γ (PO 3 1) ≠ ⊤) (covol_Λ : covolume Λ (PO 3 1) ≠ ⊤)
    (f : Γ ≃* Λ) :
    ∃ g : PO 3 1, Λ = Subgroup.map (MulAut.conj g).toMonoidHom Γ :=
  mostow_rigidity_conjugacy 3 le_rfl Γ Λ disc_Γ disc_Λ covol_Γ covol_Λ f
