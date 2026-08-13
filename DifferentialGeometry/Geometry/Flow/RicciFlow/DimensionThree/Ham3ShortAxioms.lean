import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonPositiveRicci

namespace DifferentialGeometry

open DifferentialGeometry.PDE.RicciFlow

run_cmd do
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``ricci_flow_short_time_existence,
    ``HamiltonPositiveRicci.ham3_short_isSolution,
    ``HamiltonPositiveRicci.ham3_short_smooth_solution
  ]
  for declaration in declarations do
    let axioms ← Lean.collectAxioms declaration
    unless axioms.size == expected.size &&
        axioms.all (fun dependency => expected.contains dependency) do
      let found := String.intercalate ", " (axioms.toList.map toString)
      throwError "unexpected axioms for '{declaration}': [{found}]"
end DifferentialGeometry
