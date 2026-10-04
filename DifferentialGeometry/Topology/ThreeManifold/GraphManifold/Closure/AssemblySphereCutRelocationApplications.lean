import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelocation
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.NormalizeTerminalSplit

/-!
# Consumers of the cap relocation target

* `exists_capRelocationTarget_inter_interior`: every raw presentation has a fibred piece and a base
  point whose relocation target is a nonempty open subset of the interior.
* `sphereTwoTimesCircle_capRelocationTarget_inter_interior`: the same for the universe-`u` raw
  presentation of `S² × S¹` (`Seifert/NormalizeTerminalSplit.lean:63`), the `S² × S¹` summand of
  the non-separating case of L2-relative.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- Every raw presentation has a nonempty open relocation target inside the interior. -/
theorem exists_capRelocationTarget_inter_interior {Q : CompactCarrier.{u}}
    (R : RawGraphPresentation Q) :
    ∃ (j : Fin R.components.count) (b : (R.fibration j).base.Carrier),
      IsOpen (capRelocationTarget R j b ∩ Q.interior) ∧
        (capRelocationTarget R j b ∩ Q.interior).Nonempty := by
  let j : Fin R.components.count := ⟨0, R.components.count_pos⟩
  obtain ⟨b⟩ := (inferInstance : Nonempty (R.fibration j).base.Carrier)
  exact ⟨j, b, (isOpen_capRelocationTarget R j b).inter Q.interior.isOpen,
    capRelocationTarget_inter_interior_nonempty R j b⟩

/-- The `S² × S¹` summand has a nonempty open relocation target inside its interior. -/
theorem sphereTwoTimesCircle_capRelocationTarget_inter_interior :
    ∃ (j : Fin sphereTwoTimesCircleUliftRawGraphPresentation.{u}.components.count)
      (b : (sphereTwoTimesCircleUliftRawGraphPresentation.{u}.fibration j).base.Carrier),
      (capRelocationTarget sphereTwoTimesCircleUliftRawGraphPresentation.{u} j b ∩
        (NoCuts.carrier sphereTwoTimesCircleLift.ulift.{0, u}).interior).Nonempty := by
  obtain ⟨j, b, -, h⟩ := exists_capRelocationTarget_inter_interior
    sphereTwoTimesCircleUliftRawGraphPresentation.{u}
  exact ⟨j, b, h⟩

end GC.GraphManifold.Assembly
