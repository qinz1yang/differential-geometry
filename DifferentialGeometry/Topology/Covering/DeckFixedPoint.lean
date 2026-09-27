import Mathlib.Topology.Covering.Basic



namespace DifferentialGeometry.Topology.Covering

variable {B C : Type*} [TopologicalSpace B] [TopologicalSpace C]

theorem deck_eq_id_of_fixed_point [PreconnectedSpace C]
    {p : C → B} (hp : IsCoveringMap p) (F : C → C) (hF : Continuous F)
    (hproj : ∀ x, p (F x) = p x) (x : C) (hx : F x = x) : F = id :=
  hp.eq_of_comp_eq hF continuous_id (funext hproj) x hx

end DifferentialGeometry.Topology.Covering
