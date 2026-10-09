import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopDefiningFamily
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopPositiveGeometry

/-!
The actual compact rounded and cornered base sets satisfy all genuine global defining inequalities.
The whole physical section height and both prescribed positive corner fills give the inclusion.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

theorem loopCircleSection_height (z : loopCircleBase) :
    cliffordHeight (loopCircleSection z) = 1-2*‖z.val‖^2 := by
  have he := loopCircleProjection_val ⟨loopCircleSection z,loopCircleSection_domain z⟩
  rw [loopCircleSection_projection] at he
  have hn : ‖z.val‖^2 = ‖sphereSecond (loopCircleSection z)‖^2 := by
    rw [he,modelPlaneComplex.symm.norm_map]
  rw [norm_sphereSecond_sq_eq] at hn
  linarith

theorem loopCircleRounded_family {z : loopCircleBase} (hz : loopCircleBaseRounding z ≤ 0) :
    ∀ l : Fin 3, loopDefining l z ≤ 0 := by
  have hs : z.val ∈ loopShellBase := by
    rw [← loopShellRounding_sublevel]
    exact hz
  have hh : 0 ≤ cliffordHeight (loopCircleSection z) := by
    rw [loopCircleSection_height]
    linarith [hs.2]
  intro l
  fin_cases l
  · change loopHandleDefining z ≤ 0
    by_contra hp
    have hneg := loopHandleDefining_positive_height (lt_of_not_ge hp)
    linarith
  · change loopBallDefining z ≤ 0
    by_contra hp
    have hneg := loopBallDefining_positive_height (lt_of_not_ge hp)
    linarith
  · change 1/8-‖z.val‖^2 ≤ 0
    linarith [hs.1]

theorem loopCircleCornerBase_family {z : loopCircleBase} (hz : z ∈ loopCircleCornerBase) :
    ∀ l : Fin 3, loopDefining l z ≤ 0 := by
  rcases hz with hrounded | hfill
  · exact loopCircleRounded_family hrounded
  · obtain ⟨b,hb⟩ := Set.mem_iUnion.mp hfill
    obtain ⟨v,hv,rfl⟩ := hb
    have hs := loopCornerFill_source hv
    intro l
    fin_cases l
    · change loopDefining 0 (loopBaseCorner b v) ≤ 0
      rw [loopDefining_chart_first b hs]
      linarith [hv.1.1.1]
    · change loopDefining 1 (loopBaseCorner b v) ≤ 0
      rw [loopDefining_chart_second b hs]
      linarith [hv.1.2.1]
    · exact (loopDefining_chart_other b 2 (by decide) (by decide) hs).le

end GC.GraphManifold.Assembly
