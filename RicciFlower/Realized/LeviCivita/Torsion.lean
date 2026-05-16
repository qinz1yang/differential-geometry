import RicciFlower.Realized.LeviCivita.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Torsion-Free Calculus

Concrete consequences of mathlib's torsion tensor for RicciFlower
Levi-Civita packages.
-/

namespace RicciFlower
namespace Realized
namespace LeviCivita

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

/-- Pointwise torsion-free equation:
`nabla_X Y - nabla_Y X = [X,Y]`. -/
theorem torsion_free_at_apply
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {x : M}
    (htf : IsTorsionFreeAt (I := I) cov x)
    {X Y : (p : M) -> TangentSpace I p}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov Y x (X x) - cov X x (Y x) = VectorField.mlieBracket I X Y x := by
  unfold IsTorsionFreeAt at htf
  have hzero :=
    congrArg
      (fun T : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x =>
        T (X x) (Y x))
      htf
  change cov.torsion x (X x) (Y x) = 0 at hzero
  rw [cov.torsion_apply hX hY] at hzero
  exact sub_eq_zero.mp hzero

/-- Global torsion-free equation at a point. -/
theorem torsion_free_apply
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (htf : IsTorsionFree (I := I) cov)
    {x : M} {X Y : (p : M) -> TangentSpace I p}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov Y x (X x) - cov X x (Y x) = VectorField.mlieBracket I X Y x :=
  torsion_free_at_apply (I := I) (htf x) hX hY

/-- Family torsion-free equation at a flow time. -/
theorem torsion_free_family_apply
    {D : RealTimeInterval}
    {G : RealizedMetricFamilyOn (I := I) (M := M) D}
    (htf : IsTorsionFreeFamilyOn (I := I) G)
    (t : RealTimeInterval.FlowTime D)
    {x : M} {X Y : (p : M) -> TangentSpace I p}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    G.connectionAt t Y x (X x) - G.connectionAt t X x (Y x) =
      VectorField.mlieBracket I X Y x :=
  torsion_free_apply (I := I) (htf t) hX hY

end LeviCivita
end Realized
end RicciFlower
