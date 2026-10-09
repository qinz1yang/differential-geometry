import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopRounding

/-!
The full compact rounded orbit shell with the actual deep core as its second boundary.
Its smooth outer factor is identically one on both entire fixed corner-chart targets.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

private def shellCoreRadius : ℝ := Real.sqrt (7 / 4)

private theorem shellCoreRadius_pos : 0 < shellCoreRadius := by
  apply Real.sqrt_pos.mpr
  norm_num

private theorem shellCoreRadius_sq : shellCoreRadius ^ 2 = 7 / 4 :=
  Real.sq_sqrt (by norm_num)

private theorem shellCoreRadius_gt : 21 / 16 < shellCoreRadius := by
  nlinarith [shellCoreRadius_pos, shellCoreRadius_sq]

private def shellOuterFactor (r : ℝ) : ℝ :=
  (1 - Real.smoothTransition (16 * (r - 5 / 4))) +
    Real.smoothTransition (16 * (r - 5 / 4)) * (shellCoreRadius - r)

private theorem shellOuterFactor_small {r : ℝ} (hr : r ≤ 5 / 4) : shellOuterFactor r = 1 := by
  rw [shellOuterFactor, Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring

private theorem shellOuterFactor_large {r : ℝ} (hr : 21 / 16 ≤ r) :
    shellOuterFactor r = shellCoreRadius - r := by
  rw [shellOuterFactor, Real.smoothTransition.one_of_one_le (by linarith)]
  ring

private theorem shellOuterFactor_smooth : ContDiff ℝ ∞ shellOuterFactor := by
  have hc : ContDiff ℝ ∞ (fun r : ℝ => Real.smoothTransition (16 * (r - 5 / 4))) :=
    (Real.smoothTransition.contDiff (n := ⊤)).comp
      (contDiff_const.mul (contDiff_id.sub contDiff_const))
  exact (contDiff_const.sub hc).add (hc.mul (contDiff_const.sub contDiff_id))

private theorem shellOuterFactor_pos {r : ℝ} (hr : r < shellCoreRadius) :
    0 < shellOuterFactor r := by
  have hc0 := Real.smoothTransition.nonneg (16 * (r - 5 / 4))
  have hc1 := Real.smoothTransition.le_one (16 * (r - 5 / 4))
  by_cases he : Real.smoothTransition (16 * (r - 5 / 4)) = 1
  · rw [shellOuterFactor, he]
    linarith
  · have hc : Real.smoothTransition (16 * (r - 5 / 4)) < 1 := lt_of_le_of_ne hc1 he
    have hm := mul_nonneg hc0 (sub_nonneg.mpr hr.le)
    dsimp [shellOuterFactor]
    linarith

private theorem shellOuterFactor_zero : shellOuterFactor shellCoreRadius = 0 := by
  rw [shellOuterFactor_large shellCoreRadius_gt.le, sub_self]

private theorem shellOuterFactor_zero_iff {r : ℝ} :
    shellOuterFactor r = 0 ↔ r = shellCoreRadius := by
  constructor
  · intro h
    rcases lt_trichotomy r shellCoreRadius with hl | he | hg
    · exact False.elim ((shellOuterFactor_pos hl).ne' h)
    · exact he
    · rw [shellOuterFactor_large (by linarith [shellCoreRadius_gt])] at h
      linarith
  · intro h
    rw [h]
    exact shellOuterFactor_zero

private theorem shellOuterFactor_nonneg {r : ℝ} (hr : r ≤ shellCoreRadius) :
    0 ≤ shellOuterFactor r := by
  rcases lt_or_eq_of_le hr with hl | he
  · exact (shellOuterFactor_pos hl).le
  · rw [he, shellOuterFactor_zero]

private theorem shellScalar_nonpos_iff {r : ℝ} :
    16 * (1 - r) * shellOuterFactor r ≤ 0 ↔ 1 ≤ r ∧ r ≤ shellCoreRadius := by
  constructor
  · intro h
    have h1 : 1 ≤ r := by
      by_contra hn
      have hr : r < 1 := not_le.mp hn
      have hf : 0 < shellOuterFactor r := shellOuterFactor_pos (by
        linarith [shellCoreRadius_gt])
      have hp : 0 < 16 * (1 - r) * shellOuterFactor r := mul_pos (by linarith) hf
      linarith
    have h2 : r ≤ shellCoreRadius := by
      by_contra hn
      have hr : shellCoreRadius < r := not_le.mp hn
      have hf : shellOuterFactor r < 0 := by
        rw [shellOuterFactor_large (by linarith [shellCoreRadius_gt])]
        linarith
      have hp : 0 < 16 * (1 - r) * shellOuterFactor r :=
        mul_pos_of_neg_of_neg (by linarith [shellCoreRadius_gt]) hf
      linarith
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (shellOuterFactor_nonneg h2)

def loopModelRadius (z : EuclideanSpace ℝ (Fin 2)) : ℝ := 1 - loopInnerRounding z / 16

theorem loopModelRadius_eq_sqrt (z : EuclideanSpace ℝ (Fin 2)) :
    loopModelRadius z = Real.sqrt (2 * (1 - ‖z‖ ^ 2)) := by
  rw [loopModelRadius, loopInnerRounding]
  ring

private theorem modelRadius_nonneg (z : EuclideanSpace ℝ (Fin 2)) : 0 ≤ loopModelRadius z := by
  rw [loopModelRadius_eq_sqrt]
  exact Real.sqrt_nonneg _

theorem loopModelRadius_sq {z : EuclideanSpace ℝ (Fin 2)} (hz : ‖z‖ < 1) :
    loopModelRadius z ^ 2 = 2 * (1 - ‖z‖ ^ 2) := by
  rw [loopModelRadius_eq_sqrt, Real.sq_sqrt]
  nlinarith [norm_nonneg z]

private theorem innerRounding_eq_radius (z : EuclideanSpace ℝ (Fin 2)) :
    loopInnerRounding z = 16 * (1 - loopModelRadius z) := by
  rw [loopModelRadius]
  ring

theorem loopModelRadius_smooth : ContDiffOn ℝ ∞ loopModelRadius {z | ‖z‖ < 1} :=
  contDiffOn_const.sub (loopInnerRounding_smooth.div_const 16)

def loopShellRounding (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  loopInnerRounding z * shellOuterFactor (loopModelRadius z)

theorem loopShellRounding_inner (z : EuclideanSpace ℝ (Fin 2))
    (hr : loopModelRadius z ≤ 5 / 4) :
    loopShellRounding z = 16 * (1 - loopModelRadius z) := by
  rw [loopShellRounding, shellOuterFactor_small hr, mul_one]
  exact innerRounding_eq_radius z

theorem loopShellRounding_outer (z : EuclideanSpace ℝ (Fin 2))
    (hr : 21 / 16 ≤ loopModelRadius z) :
    loopShellRounding z = 16 * (1 - loopModelRadius z) *
      (Real.sqrt (7 / 4) - loopModelRadius z) := by
  rw [loopShellRounding, shellOuterFactor_large hr, innerRounding_eq_radius]
  rfl

theorem loopShellRounding_smooth :
    ContDiffOn ℝ ∞ loopShellRounding {z | ‖z‖ < 1} :=
  loopInnerRounding_smooth.mul (shellOuterFactor_smooth.comp_contDiffOn loopModelRadius_smooth)

theorem loopShellRounding_corner (b : Bool) (v : ℝ × ℝ) (hv : v ∈ rimBox 2) :
    loopShellRounding (loopCornerChart b v) = -standardRimRounding v := by
  have hr : loopModelRadius (loopCornerChart b v) < 9 / 8 := by
    rw [loopModelRadius, loopInnerRounding_corner b v hv]
    have hs := (standardRimRounding_le_min v).trans (min_le_left v.1 v.2)
    linarith [(abs_lt.mp hv.1).2]
  rw [loopShellRounding, shellOuterFactor_small (by linarith [hr]), mul_one]
  exact loopInnerRounding_corner b v hv

theorem loopShellRounding_source {z : EuclideanSpace ℝ (Fin 2)}
    (hz : loopShellRounding z ≤ 0) : ‖z‖ < 1 := by
  by_contra hn
  have hh : 1 ≤ ‖z‖ := not_lt.mp hn
  have ha : 2 * (1 - ‖z‖ ^ 2) ≤ 0 := by nlinarith
  have hr : loopModelRadius z = 0 := by
    rw [loopModelRadius_eq_sqrt]
    exact Real.sqrt_eq_zero'.mpr ha
  rw [loopShellRounding, innerRounding_eq_radius, hr,
    shellOuterFactor_small (by norm_num : (0 : ℝ) ≤ 5 / 4)] at hz
  norm_num at hz

theorem loopShellRounding_sublevel : {z | loopShellRounding z ≤ 0} = loopShellBase := by
  ext z
  constructor
  · intro hz
    change loopShellRounding z ≤ 0 at hz
    have hsrc := loopShellRounding_source hz
    have hs := loopModelRadius_sq hsrc
    have hn := modelRadius_nonneg z
    rw [loopShellRounding, innerRounding_eq_radius, shellScalar_nonpos_iff] at hz
    have hm := mul_nonneg (sub_nonneg.mpr hz.2)
      (add_nonneg shellCoreRadius_pos.le hn)
    change 1 / 8 ≤ ‖z‖ ^ 2 ∧ ‖z‖ ^ 2 ≤ 1 / 2
    constructor <;> nlinarith [shellCoreRadius_sq, hz.1]
  · intro hz
    have hsrc := loopShellBase_source hz
    have hs := loopModelRadius_sq hsrc
    have hn := modelRadius_nonneg z
    change 1 / 8 ≤ ‖z‖ ^ 2 ∧ ‖z‖ ^ 2 ≤ 1 / 2 at hz
    change loopShellRounding z ≤ 0
    rw [loopShellRounding, innerRounding_eq_radius, shellScalar_nonpos_iff]
    constructor <;> nlinarith [shellCoreRadius_sq, shellCoreRadius_pos, hz.1, hz.2]

theorem loopShellRounding_zero_iff {z : EuclideanSpace ℝ (Fin 2)} :
    loopShellRounding z = 0 ↔ ‖z‖ ^ 2 = 1 / 2 ∨ ‖z‖ ^ 2 = 1 / 8 := by
  constructor
  · intro hz
    have hsrc := loopShellRounding_source hz.le
    have hs := loopModelRadius_sq hsrc
    rw [loopShellRounding, mul_eq_zero] at hz
    rcases hz with hi | ho
    · exact Or.inl ((loopInnerRounding_zero_iff hsrc).mp hi)
    · have hr := shellOuterFactor_zero_iff.mp ho
      rw [hr, shellCoreRadius_sq] at hs
      exact Or.inr (by linarith)
  · intro hz
    rcases hz with hi | ho
    · have hsrc : ‖z‖ < 1 := by nlinarith [norm_nonneg z]
      rw [loopShellRounding, (loopInnerRounding_zero_iff hsrc).mpr hi, zero_mul]
    · have hr : loopModelRadius z = shellCoreRadius := by
        rw [loopModelRadius_eq_sqrt, ho]
        congr 1
        norm_num [shellCoreRadius]
      rw [loopShellRounding, hr, shellOuterFactor_zero, mul_zero]

theorem loopShellRounding_compact : IsCompact {z | loopShellRounding z ≤ 0} := by
  rw [loopShellRounding_sublevel]
  have hc : IsClosed loopShellBase :=
    (isClosed_le continuous_const (continuous_norm.pow 2)).inter
      (isClosed_le (continuous_norm.pow 2) continuous_const)
  exact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).of_isClosed_subset hc
    (fun z hz => mem_closedBall_zero_iff.mpr (loopShellBase_source hz).le)

end GC.GraphManifold.Assembly
