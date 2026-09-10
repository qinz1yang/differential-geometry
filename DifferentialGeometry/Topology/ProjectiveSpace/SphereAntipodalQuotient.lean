import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Homeomorph.Quotient

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set Topology
open scoped Manifold ContDiff

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private local instance sphereAntipodalQuotientDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

def sphereAntipodalSetoid : Setoid SphereTwo where
  r x y := y = x ∨ y = -x
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      intro x y h
      rcases h with h | h
      · exact Or.inl h.symm
      · right
        rw [h, neg_neg]
    trans := by
      intro x y z hxy hyz
      rcases hxy with hxy | hxy
      · simpa only [hxy] using hyz
      · rcases hyz with hyz | hyz
        · exact Or.inr (hyz.trans hxy)
        · left
          simpa only [hxy, neg_neg] using hyz }

abbrev SphereAntipodalQuotient := Quotient sphereAntipodalSetoid

namespace SphereAntipodalQuotient

def proj : SphereTwo → SphereAntipodalQuotient := Quotient.mk sphereAntipodalSetoid

theorem proj_eq_iff (x y : SphereTwo) : proj x = proj y ↔ y = x ∨ y = -x :=
  Quotient.eq

theorem continuous_proj : Continuous proj := continuous_quotient_mk'

theorem surjective_proj : Function.Surjective proj := Quotient.mk_surjective

theorem isOpenMap_proj : IsOpenMap proj := by
  intro U hU
  apply (isQuotientMap_quotient_mk' (s := sphereAntipodalSetoid)).isOpen_preimage.mp
  have hsaturation : proj ⁻¹' (proj '' U) = U ∪ (fun x : SphereTwo => -x) ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨y, hy, heq⟩
      rcases (proj_eq_iff y x).mp heq with h | h
      · left
        simpa only [h] using hy
      · right
        change -x ∈ U
        simpa only [h, neg_neg] using hy
    · rintro (hx | hx)
      · exact ⟨x, hx, rfl⟩
      · refine ⟨-x, hx, (proj_eq_iff (-x) x).mpr (Or.inr ?_)⟩
        exact (neg_neg x).symm
  change IsOpen (proj ⁻¹' (proj '' U))
  rw [hsaturation]
  exact hU.union (hU.preimage (contMDiff_neg_sphere (n := 2) (m := ∞)).continuous)

theorem exists_homeomorph {M : Type*} [TopologicalSpace M]
    (pi : SphereTwo → M) (hcontinuous : Continuous pi) (hopen : IsOpenMap pi)
    (hsurjective : Function.Surjective pi)
    (hfibres : ∀ x y : SphereTwo, pi x = pi y ↔ y = x ∨ y = -x) :
    ∃ d : SphereAntipodalQuotient ≃ₜ M, ∀ x : SphereTwo, d (proj x) = pi x := by
  let f : C(SphereTwo, M) := ⟨pi, hcontinuous⟩
  have hquotient : IsQuotientMap f := hopen.isQuotientMap hcontinuous hsurjective
  have hker (x y : SphereTwo) : sphereAntipodalSetoid x y ↔ Setoid.ker f x y :=
    (hfibres x y).symm
  let e : SphereAntipodalQuotient ≃ₜ Quotient (Setoid.ker f) :=
    Homeomorph.Quotient.congrRight hker
  exact ⟨e.trans hquotient.homeomorph, fun _ => rfl⟩

def productProjection (p : SphereTwo × ℝ) : SphereAntipodalQuotient × ℝ :=
  (proj p.1, p.2)

theorem productProjection_eq_iff (p q : SphereTwo × ℝ) :
    productProjection p = productProjection q ↔ q = p ∨ q = (-p.1, p.2) := by
  constructor
  · intro h
    have hsphere : proj p.1 = proj q.1 := congrArg Prod.fst h
    have hline : p.2 = q.2 := congrArg (fun z : SphereAntipodalQuotient × ℝ => z.2) h
    rcases (proj_eq_iff p.1 q.1).mp hsphere with hfirst | hfirst
    · exact Or.inl (Prod.ext hfirst hline.symm)
    · exact Or.inr (Prod.ext hfirst hline.symm)
  · rintro (rfl | rfl)
    · rfl
    · exact Prod.ext ((proj_eq_iff p.1 (-p.1)).mpr (Or.inr rfl)) rfl

theorem continuous_productProjection : Continuous productProjection :=
  continuous_proj.prodMap continuous_id

theorem isOpenMap_productProjection : IsOpenMap productProjection :=
  isOpenMap_proj.prodMap IsOpenMap.id

theorem surjective_productProjection : Function.Surjective productProjection :=
  surjective_proj.prodMap Function.surjective_id

theorem exists_product_homeomorph {M : Type*} [TopologicalSpace M]
    (pi : SphereTwo × ℝ → M) (hcontinuous : Continuous pi) (hopen : IsOpenMap pi)
    (hsurjective : Function.Surjective pi)
    (hfibres : ∀ p q : SphereTwo × ℝ, pi p = pi q ↔ q = p ∨ q = (-p.1, p.2)) :
    ∃ d : (SphereAntipodalQuotient × ℝ) ≃ₜ M,
      ∀ p : SphereTwo × ℝ, d (productProjection p) = pi p := by
  let f : C(SphereTwo × ℝ, M) := ⟨pi, hcontinuous⟩
  let q : C(SphereTwo × ℝ, SphereAntipodalQuotient × ℝ) :=
    ⟨productProjection, continuous_productProjection⟩
  have hq : IsQuotientMap q := isOpenMap_productProjection.isQuotientMap
    continuous_productProjection surjective_productProjection
  have hf : IsQuotientMap f := hopen.isQuotientMap hcontinuous hsurjective
  have hker (x y : SphereTwo × ℝ) : Setoid.ker q x y ↔ Setoid.ker f x y :=
    (productProjection_eq_iff x y).trans (hfibres x y).symm
  let e : Quotient (Setoid.ker q) ≃ₜ Quotient (Setoid.ker f) :=
    Homeomorph.Quotient.congrRight hker
  refine ⟨(hq.homeomorph.symm.trans e).trans hf.homeomorph, ?_⟩
  intro p
  have hp : hq.homeomorph (Quotient.mk (Setoid.ker q) p) = q p := rfl
  change hf.homeomorph (e (hq.homeomorph.symm (q p))) = pi p
  rw [← hp, hq.homeomorph.symm_apply_apply]
  rfl

end SphereAntipodalQuotient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
