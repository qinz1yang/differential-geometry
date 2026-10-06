import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimDomainComponents74
import DifferentialGeometry.Topology.Manifold.OneManifold.CircleKernelExampleBCF

/-!
# Consumer of `componentEquiv74`: the unit circle domain has loops as its only components

On the circle domain of `exists_compactOneDomain_circle_BCF` (no arc, at least one loop) every
actual component of the carrier is the range of a loop, and there is at least one component.
-/

set_option autoImplicit false

noncomputable section

open Set Function

namespace DifferentialGeometry.Topology.SmoothCompactOneDomain_BCF

open GC.GraphManifold.Assembly.FC39P0

/-- **Components of the circle domain**: nonempty, and every component is a loop range. -/
theorem circle_components_R74 :
    ∃ D : SmoothCompactOneDomain_BCF unitCircle_BCF, Nonempty (ActualComponent D.carrier) ∧
      ∀ c : ActualComponent D.carrier, ∃ j : Fin D.l, c.1 = range (D.loop j) := by
  obtain ⟨D, -, hm, hl⟩ := exists_compactOneDomain_circle_BCF
  refine ⟨D, ⟨D.componentEquiv74 (Sum.inr ⟨0, hl⟩)⟩, fun c => ?_⟩
  rcases hi : D.componentEquiv74.symm c with k | j
  · exact absurd k.2 (by omega)
  · refine ⟨j, ?_⟩
    have hc : D.componentEquiv74 (Sum.inr j) = c := by
      rw [← hi, Equiv.apply_symm_apply]
    rw [← hc]
    rfl

end DifferentialGeometry.Topology.SmoothCompactOneDomain_BCF
