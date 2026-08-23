import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison

set_option autoImplicit false

noncomputable section

namespace Tensor0SBundle

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem inner0S_identity_eq_sum {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric_gen I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A B : Tensor0SSpace s I x) :
    inner0S (I := I) g x s A B =
      ∑ slots : Fin s -> Idx,
        component0S (I := I) basis A slots * component0S (I := I) basis B slots := by
  rw [inner0S_eq_coord (I := I) g x s basis (identityInvMetric (Idx := Idx)) hinv,
    coordInner0S_identity_eq_sum (I := I) (x := x) s A B basis]
  apply Finset.sum_congr rfl
  intro slots _
  rfl

theorem inner0S_domDomCongr {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric_gen I M) (x : M) {s s' : Nat}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (e : Fin s ≃ Fin s') (A B : Tensor0SSpace s I x) :
    inner0S (I := I) g x s' (A.domDomCongr e) (B.domDomCongr e) =
      inner0S (I := I) g x s A B := by
  classical
  rw [inner0S_identity_eq_sum (I := I) g x s' basis hinv,
    inner0S_identity_eq_sum (I := I) g x s basis hinv]
  refine Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl Idx)) _ _ ?_
  intro w
  simp only [component0S_apply, Equiv.arrowCongr_apply, Equiv.symm_symm,
    Equiv.coe_refl, Function.comp, id_eq]
  rfl

end Tensor0SBundle
