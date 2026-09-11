import DifferentialGeometry.Analysis.Calculus.Retraction.Ball
import Mathlib.Topology.ContinuousMap.Basic

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology
namespace DifferentialGeometry.Topology.ClosedBall
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (a : E) {r : ℝ} (hr : 0 ≤ r)

def retraction : C(E, closedBall a r) := by
  refine ⟨fun x => ⟨a + DifferentialGeometry.Analysis.Calculus.ballRetraction r (x - a), ?_⟩, ?_⟩
  · rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact DifferentialGeometry.Analysis.Calculus.ballRetraction_mem_closedBall hr _
  · exact (continuous_const.add
      ((DifferentialGeometry.Analysis.Calculus.lipschitzWith_ballRetraction hr).continuous.comp
        (continuous_id.sub continuous_const))).subtype_mk _


@[simp]
theorem retraction_apply (x : E) :
    (retraction a hr x : E) = a + min 1 (r / ‖x - a‖) • (x - a) := rfl


theorem retraction_apply_of_mem {x : E} (hx : x ∈ closedBall a r) :
    (retraction a hr x : E) = x := by
  change a + DifferentialGeometry.Analysis.Calculus.ballRetraction r (x - a) = x
  rw [DifferentialGeometry.Analysis.Calculus.ballRetraction_eq_self_of_mem
    (by simpa only [mem_closedBall, dist_eq_norm] using hx)]
  abel


@[simp]
theorem retraction_coe (x : closedBall a r) : retraction a hr (x : E) = x :=
  Subtype.ext (retraction_apply_of_mem a hr x.property)


theorem retraction_leftInverse : Function.LeftInverse (retraction a hr)
    (Subtype.val : closedBall a r → E) := retraction_coe a hr


theorem dist_retraction_center (x : E) :
    dist (retraction a hr x : E) a = min (dist x a) r := by
  by_cases hx : x ∈ closedBall a r
  · rw [retraction_apply_of_mem a hr hx, min_eq_left hx]
  · have hlt : r < ‖x - a‖ := lt_of_not_ge (by simpa only [mem_closedBall, dist_eq_norm] using hx)
    have hnorm : 0 < ‖x - a‖ := hr.trans_lt hlt
    have hfactor : r / ‖x - a‖ ≤ 1 := (div_le_one hnorm).mpr hlt.le
    rw [retraction_apply, dist_eq_norm, add_sub_cancel_left, min_eq_right hfactor,
      norm_smul, Real.norm_of_nonneg (div_nonneg hr (norm_nonneg _)),
      div_mul_cancel₀ _ hnorm.ne', dist_eq_norm, min_eq_right hlt.le]


theorem retraction_mem_sphere {x : E} (hx : r ≤ dist x a) :
    (retraction a hr x : E) ∈ sphere a r := by
  rw [mem_sphere, dist_retraction_center, min_eq_right hx]


theorem retraction_mem_sphere_of_not_mem {x : E} (hx : x ∉ closedBall a r) :
    (retraction a hr x : E) ∈ sphere a r :=
  retraction_mem_sphere a hr (le_of_lt (lt_of_not_ge hx))

theorem retraction_eventuallyEq_id {x : E} (hx : x ∈ ball a r) :
    (fun y => (retraction a hr y : E)) =ᶠ[𝓝 x] id := by
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  exact retraction_apply_of_mem a hr (ball_subset_closedBall hy)

end DifferentialGeometry.Topology.ClosedBall
