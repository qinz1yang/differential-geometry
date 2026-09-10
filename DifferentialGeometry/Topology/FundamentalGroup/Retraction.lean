import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

namespace DifferentialGeometry.Topology

theorem injective_fundamentalGroup_map_of_leftInverse
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (r : C(Y, X)) (hr : Function.LeftInverse r f) (x₀ : X) :
    Function.Injective (FundamentalGroup.map f x₀) := by
  have hi : Function.LeftInverse (FundamentalGroup.mapOfEq r (hr x₀))
      (FundamentalGroup.map f x₀) := by
    intro p
    rw [FundamentalGroup.mapOfEq_apply]
    induction p using Path.Homotopic.Quotient.ind with
    | mk p =>
      change Path.Homotopic.Quotient.mk
        (((p.map f.continuous).map r.continuous).cast (hr x₀).symm (hr x₀).symm) =
        Path.Homotopic.Quotient.mk p
      congr 1
      ext t
      exact hr (p t)
  exact hi.injective

end DifferentialGeometry.Topology
