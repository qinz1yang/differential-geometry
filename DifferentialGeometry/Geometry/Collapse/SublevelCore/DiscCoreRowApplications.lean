import DifferentialGeometry.Geometry.Collapse.SublevelCore.DiscCoreRow

/-!
# Consumer of the LC45 row: the trivial line bundle over the circle

`circleLine_disc_cores`: for the trivial line bundle over the circle and the identity map, the
cores `{|v| ≤ T}` are compact and every compact set lies in the interior of the core of every
large radius (from `lc45_disc_cores_and_normal_flow_coordinate`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

/-- Disc cores of the trivial line bundle over the circle. -/
theorem circleLine_disc_cores :
    let e := Diffeomorph.refl ((𝓡 1).prod 𝓘(ℝ, ℝ)) (TotalSpace ℝ (Bundle.Trivial Circle ℝ)) ∞
    (∀ T : ℝ, IsCompact {x | ‖(e.symm x).2‖ ≤ T}) ∧
      ∀ K : Set (TotalSpace ℝ (Bundle.Trivial Circle ℝ)), IsCompact K → ∃ T₀ : ℝ, 0 < T₀ ∧
        ∀ T, T₀ ≤ T → K ⊆ interior {x | ‖(e.symm x).2‖ ≤ T} := by
  intro e
  obtain ⟨-, -, -, -, hc, -, -, -, -, hex, -⟩ :=
    lc45_disc_cores_and_normal_flow_coordinate (IB := 𝓡 1) e (m := 1) (by simp)
  exact ⟨hc, hex⟩

end DifferentialGeometry.Geometry.Collapse
