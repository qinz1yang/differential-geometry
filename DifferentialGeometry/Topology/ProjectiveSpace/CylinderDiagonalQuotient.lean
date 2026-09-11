import DifferentialGeometry.Topology.ProjectiveSpace.SphereAntipodalQuotient

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set Topology
open scoped Manifold ContDiff

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Cylinder" => SphereTwo × ℝ

private local instance cylinderDiagonalQuotientDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

def cylinderDiagonalSetoid : Setoid Cylinder where
  r p q := q = p ∨ q = -p
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      intro p q h
      rcases h with h | h
      · exact Or.inl h.symm
      · right
        rw [h, neg_neg]
    trans := by
      intro p q r hpq hqr
      rcases hpq with hpq | hpq
      · simpa only [hpq] using hqr
      · rcases hqr with hqr | hqr
        · exact Or.inr (hqr.trans hpq)
        · left
          simpa only [hpq, neg_neg] using hqr }

abbrev CylinderDiagonalQuotient := Quotient cylinderDiagonalSetoid

namespace CylinderDiagonalQuotient

def proj : Cylinder → CylinderDiagonalQuotient := Quotient.mk cylinderDiagonalSetoid

theorem proj_eq_iff (p q : Cylinder) : proj p = proj q ↔ q = p ∨ q = (-p.1, -p.2) :=
  Quotient.eq

theorem continuous_proj : Continuous proj := continuous_quotient_mk'

theorem surjective_proj : Function.Surjective proj := Quotient.mk_surjective

theorem isOpenMap_proj : IsOpenMap proj := by
  intro U hU
  apply (isQuotientMap_quotient_mk' (s := cylinderDiagonalSetoid)).isOpen_preimage.mp
  have hsaturation : proj ⁻¹' (proj '' U) = U ∪ (fun p : Cylinder => -p) ⁻¹' U := by
    ext p
    constructor
    · rintro ⟨q, hq, heq⟩
      rcases (proj_eq_iff q p).mp heq with h | h
      · left
        simpa only [h] using hq
      · right
        have hp : p = -q := h
        change -p ∈ U
        simpa only [hp, neg_neg] using hq
    · rintro (hp | hp)
      · exact ⟨p, hp, rfl⟩
      · refine ⟨-p, hp, (proj_eq_iff (-p) p).mpr (Or.inr ?_)⟩
        exact (neg_neg p).symm
  change IsOpen (proj ⁻¹' (proj '' U))
  rw [hsaturation]
  have hneg : Continuous (fun p : Cylinder => -p) :=
    (contMDiff_neg_sphere (n := 2) (m := ∞)).continuous.prodMap continuous_neg
  exact hU.union (hU.preimage hneg)

theorem exists_homeomorph {M : Type*} [TopologicalSpace M]
    (pi : Cylinder → M) (hcontinuous : Continuous pi) (hopen : IsOpenMap pi)
    (hsurjective : Function.Surjective pi)
    (hfibres : ∀ p q : Cylinder, pi p = pi q ↔ q = p ∨ q = (-p.1, -p.2)) :
    ∃ d : CylinderDiagonalQuotient ≃ₜ M, ∀ p : Cylinder, d (proj p) = pi p := by
  let f : C(Cylinder, M) := ⟨pi, hcontinuous⟩
  have hquotient : IsQuotientMap f := hopen.isQuotientMap hcontinuous hsurjective
  have hker (p q : Cylinder) : cylinderDiagonalSetoid p q ↔ Setoid.ker f p q :=
    (hfibres p q).symm
  let e : CylinderDiagonalQuotient ≃ₜ Quotient (Setoid.ker f) :=
    Homeomorph.Quotient.congrRight hker
  exact ⟨e.trans hquotient.homeomorph, fun _ => rfl⟩

end CylinderDiagonalQuotient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
