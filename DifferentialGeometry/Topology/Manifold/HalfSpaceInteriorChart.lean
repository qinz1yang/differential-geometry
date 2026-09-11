import DifferentialGeometry.Topology.Manifold.HalfClosedInterval
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
private abbrev One := EuclideanSpace ℝ (Fin 1)

def halfSpaceInteriorChart (a : ℝ) : OpenPartialHomeomorph ℝ (EuclideanHalfSpace 1) where
  toFun t := ⟨WithLp.toLp 2 (fun _ => max (t - a) 0), by
    change 0 ≤ max (t - a) 0
    exact le_max_right _ _⟩
  invFun y := y.val 0 + a
  source := Ioi a
  target := {y | 0 < y.val 0}
  map_source' := by
    intro t ht
    change 0 < max (t - a) 0
    rw [max_eq_left (sub_nonneg.mpr ht.le)]
    exact sub_pos.mpr ht
  map_target' := by
    intro y hy
    change a < y.val 0 + a
    change 0 < y.val 0 at hy
    linarith
  left_inv' := by
    intro t ht
    change max (t - a) 0 + a = t
    rw [max_eq_left (sub_nonneg.mpr ht.le)]
    ring
  right_inv' := by
    intro y hy
    apply Subtype.ext
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change max (y.val 0 + a - a) 0 = y.val 0
    rw [add_sub_cancel_right, max_eq_left y.property]
  open_source := isOpen_Ioi
  open_target := isOpen_lt continuous_const ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp continuous_subtype_val)
  continuousOn_toFun := by
    have ht : Continuous (fun t : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => max (t - a) 0)) :=
      (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun _ => (continuous_id.sub continuous_const).max continuous_const))
    exact (ht.subtype_mk _).continuousOn
  continuousOn_invFun := ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp continuous_subtype_val).add continuous_const |>.continuousOn

theorem halfSpaceInteriorChart_apply (a t : ℝ) (ht : a < t) :
    (halfSpaceInteriorChart a t).val 0 = t - a := max_eq_left (sub_nonneg.mpr ht.le)

theorem halfSpaceInteriorChart_symm_apply (a : ℝ) (y : EuclideanHalfSpace 1) :
    (halfSpaceInteriorChart a).symm y = y.val 0 + a := rfl

theorem halfSpaceInteriorChart_contMDiffOn (a : ℝ) :
    ContMDiffOn 𝓘(ℝ) (𝓡∂ 1) ∞ (halfSpaceInteriorChart a) (Ioi a) := by
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_iff]
  refine ⟨(halfSpaceInteriorChart a).continuousOn.continuousAt (isOpen_Ioi.mem_nhds hx), ?_⟩
  rw [extChartAt_model_space_eq_id]
  change ContDiffWithinAt ℝ ∞ (fun t : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => max (t - a) 0)) (range (id : ℝ → ℝ)) x
  rw [range_id]
  apply ContDiffAt.contDiffWithinAt
  let e : ℝ ≃L[ℝ] One := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).symm
  have ha : ContDiff ℝ ∞ (fun t : ℝ => e (t - a)) := e.contDiff.comp (contDiff_id.sub contDiff_const)
  apply ha.contDiffAt.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hx] with t ht
  ext i
  change max (t - a) 0 = t - a
  exact max_eq_left (sub_nonneg.mpr ht.le)

theorem halfSpaceInteriorChart_symm_contMDiff (a : ℝ) :
    ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ (halfSpaceInteriorChart a).symm := by
  have he : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ (fun y : EuclideanHalfSpace 1 => y.val 0) :=
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).contDiff.contMDiff.comp (𝓡∂ 1).contMDiff
  exact he.add contMDiff_const
end DifferentialGeometry.Topology.Manifold
