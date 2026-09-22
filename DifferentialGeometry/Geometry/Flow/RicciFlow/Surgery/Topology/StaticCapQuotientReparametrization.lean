import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCapWitnessProducer
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Homeomorph.Quotient

set_option autoImplicit false
noncomputable section

open Set Function

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable (δ : ℝ) (ζ a : Sphere 2 ≃ₜ Sphere 2) (B : ThreeBall ≃ₜ ThreeBall)
  (hboundary : ∀ y, B (sphereToThreeBall y) = sphereToThreeBall (a y))

include hboundary in
private theorem staticCapGluingRel_reparametrize_iff
    (x y : neckRetainedCollar δ ⊕ ThreeBall) :
    staticCapGluingRel δ (a.trans ζ) x y ↔
      staticCapGluingRel δ ζ
        (Homeomorph.sumCongr (Homeomorph.refl (neckRetainedCollar δ)) B x)
        (Homeomorph.sumCongr (Homeomorph.refl (neckRetainedCollar δ)) B y) := by
  let e := Homeomorph.sumCongr (Homeomorph.refl (neckRetainedCollar δ)) B
  constructor
  · rintro ⟨z, hz, rfl, rfl⟩
    refine ⟨a z, hz, ?_, rfl⟩
    exact congrArg Sum.inr (hboundary z)
  · rintro ⟨z, hz, hx, hy⟩
    refine ⟨a.symm z, hz, ?_, ?_⟩
    · apply e.injective
      change e x = Sum.inr (B (sphereToThreeBall (a.symm z)))
      rw [hboundary, a.apply_symm_apply]
      exact hx
    · apply e.injective
      change e y = Sum.inl (⟨(ζ (a (a.symm z)), 0), le_rfl, hz⟩ : neckRetainedCollar δ)
      rw [a.apply_symm_apply]
      exact hy

def staticCapQuotientReparametrization :
    StaticCapQuotient δ (a.trans ζ) ≃ₜ StaticCapQuotient δ ζ :=
  (quotientEqvGenHomeomorph (staticCapGluingRel δ (a.trans ζ))).symm.trans
    ((Homeomorph.Quot.congr (Homeomorph.sumCongr (Homeomorph.refl (neckRetainedCollar δ)) B)
      (staticCapGluingRel_reparametrize_iff δ ζ a B hboundary)).trans
      (quotientEqvGenHomeomorph (staticCapGluingRel δ ζ)))

@[simp] theorem staticCapQuotientReparametrization_retained (x : neckRetainedCollar δ) :
    staticCapQuotientReparametrization δ ζ a B hboundary (Quotient.mk _ (Sum.inl x)) =
      Quotient.mk _ (Sum.inl x) := rfl

@[simp] theorem staticCapQuotientReparametrization_cap (x : ThreeBall) :
    staticCapQuotientReparametrization δ ζ a B hboundary (Quotient.mk _ (Sum.inr x)) =
      Quotient.mk _ (Sum.inr (B x)) := rfl

@[simp] theorem staticCapQuotientReparametrization_symm_retained (x : neckRetainedCollar δ) :
    (staticCapQuotientReparametrization δ ζ a B hboundary).symm (Quotient.mk _ (Sum.inl x)) =
      Quotient.mk _ (Sum.inl x) := rfl

@[simp] theorem staticCapQuotientReparametrization_symm_cap (x : ThreeBall) :
    (staticCapQuotientReparametrization δ ζ a B hboundary).symm (Quotient.mk _ (Sum.inr x)) =
      Quotient.mk _ (Sum.inr (B.symm x)) := rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
