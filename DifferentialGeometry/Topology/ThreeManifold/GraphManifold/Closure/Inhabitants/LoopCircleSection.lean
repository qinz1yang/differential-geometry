import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopBundle
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopRegion

/-!
The true global first-circle section is smooth and projects to every actual base point.
Both prescribed corner charts recover the same original rim point with angle one.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

def loopCircleSection (z : loopCircleBase) : SphereCarrier.{0} :=
  (loopCircleBundle.symm (z, 1)).val

theorem loopCircleSection_domain (z : loopCircleBase) : loopCircleSection z ∈ loopCircleDomain :=
  (loopCircleBundle.symm (z, 1)).property

theorem loopCircleSection_smooth : ContMDiff (𝓡 2) (𝓡 3) ∞ loopCircleSection := by
  have hp : ContMDiff (𝓡 2) ((𝓡 2).prod (𝓡 1)) ∞
      (fun z : loopCircleBase => (z, (1 : Circle))) := contMDiff_id.prodMk contMDiff_const
  exact contMDiff_subtype_val.comp (loopCircleBundle.symm.contMDiff.comp hp)

theorem loopCircleSection_projection (z : loopCircleBase) :
    loopCircleProjection ⟨loopCircleSection z, loopCircleSection_domain z⟩ = z := by
  change (loopCircleBundle (loopCircleBundle.symm (z, 1))).1 = z
  rw [loopCircleBundle.apply_symm_apply]

theorem loopCircleSection_inverse (z : loopCircleBase) :
    loopCircleCoordinates.symm (loopCircleSection z) = (z.val, 1) :=
  loopCircleCoordinates.left_inv z.property

theorem loopCircleSection_rim (b : Bool) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    loopCircleSection (loopBaseCorner b v) =
      standardLoopBallHandleCycle.rimChart ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (1, v) := by
  have he := loopRimOrbit_inverse b 1 v hv
  rw [← loopCornerChart_apply, ← loopBaseCorner_val b v hv] at he
  exact (congrArg loopCircleCoordinates he).symm.trans
    (loopCircleCoordinates.right_inv (loopRegionRim_domain b 1 v hv))

end GC.GraphManifold.Assembly
