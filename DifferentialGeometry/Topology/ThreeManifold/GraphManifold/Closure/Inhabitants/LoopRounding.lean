import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopCorners

/-!
The actual smooth inner rounding in the free orbit plane, with the same standard function.
Its pullback to both genuine loop corner charts is exactly the negative standard rim rounding.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

def loopInnerRounding (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  16 * (1 - Real.sqrt (2 * (1 - ‖z‖ ^ 2)))

theorem loopInnerRounding_smooth :
    ContDiffOn ℝ ∞ loopInnerRounding {z | ‖z‖ < 1} := by
  intro z hz
  have hp : 0 < 2 * (1 - ‖z‖ ^ 2) := by
    change ‖z‖ < 1 at hz
    nlinarith [norm_nonneg z]
  have hg : ContDiff ℝ ∞ (fun w : EuclideanSpace ℝ (Fin 2) =>
      (2 : ℝ) * (1 - ‖w‖ ^ 2)) :=
    contDiff_const.mul (contDiff_const.sub (contDiff_norm_sq ℝ))
  have hs := (Real.contDiffAt_sqrt hp.ne').comp z hg.contDiffAt
  exact (contDiffAt_const.mul (contDiffAt_const.sub hs)).contDiffWithinAt

theorem loopInnerRounding_zero_iff {z : EuclideanSpace ℝ (Fin 2)} (hz : ‖z‖ < 1) :
    loopInnerRounding z = 0 ↔ ‖z‖ ^ 2 = 1 / 2 := by
  have hp : 0 ≤ 2 * (1 - ‖z‖ ^ 2) := by nlinarith [norm_nonneg z]
  constructor
  · intro h
    have hs : Real.sqrt (2 * (1 - ‖z‖ ^ 2)) = 1 := by
      dsimp [loopInnerRounding] at h
      linarith
    have hh := Real.sq_sqrt hp
    rw [hs] at hh
    linarith
  · intro h
    have ha : (2 : ℝ) * (1 - ‖z‖ ^ 2) = 1 := by rw [h]; norm_num
    rw [loopInnerRounding, ha, Real.sqrt_one]
    ring

theorem loopInnerRounding_le_zero_iff {z : EuclideanSpace ℝ (Fin 2)} (hz : ‖z‖ < 1) :
    loopInnerRounding z ≤ 0 ↔ ‖z‖ ^ 2 ≤ 1 / 2 := by
  have hp : 0 ≤ 2 * (1 - ‖z‖ ^ 2) := by nlinarith [norm_nonneg z]
  have hh := Real.sq_sqrt hp
  have hs := Real.sqrt_nonneg (2 * (1 - ‖z‖ ^ 2))
  dsimp [loopInnerRounding]
  constructor <;> intro h <;> nlinarith

theorem loopInnerRounding_corner (b : Bool) (v : ℝ × ℝ) (hv : v ∈ rimBox 2) :
    loopInnerRounding (loopCornerChart b v) = -standardRimRounding v := by
  let q : ModelSpace := neckRim (1 / 16) (1, v)
  have hx := abs_lt.mp hv.1
  have hy := abs_lt.mp hv.2
  have hs : 0 < 1 + (1 / 16 : ℝ) * v.1 := by linarith [hx.1]
  have hn : ‖q.1‖ = 1 + (1 / 16 : ℝ) * v.1 := by
    change ‖(1 + (1 / 16 : ℝ) * v.1) • planeOfCircle 1‖ = _
    rw [norm_smul, Real.norm_of_nonneg hs.le, planeOfCircle,
      LinearIsometryEquiv.norm_map, Circle.norm_coe, mul_one]
  have hq : q ∈ neckDomain (1 / 16) := by
    change ‖q.1‖ < 1 + 2 * (1 / 16 : ℝ) ∧ |(1 / 16 : ℝ) * v.2| < 2 * (1 / 16 : ℝ)
    rw [hn, abs_lt]
    exact ⟨by linarith [hx.2], by constructor <;> linarith [hy.1, hy.2]⟩
  have hrpos : 0 < neckRadius (1 / 16) ‖q.1‖ q.2 := by
    rw [← neckRatio_mul (by rw [hn]; exact hs.ne')]
    apply mul_pos (neckRatio_pos (by norm_num) (by norm_num) (by
      change 1 / 4 ≤ 1 + (1 / 16 : ℝ) * v.2
      linarith [hy.1]))
    rw [hn]
    exact hs
  have hrbound : neckRadius (1 / 16) ‖q.1‖ q.2 < 9 / 8 := by
    have h := neckRadius_le_left (ε := (1 / 16)) (by norm_num) ‖q.1‖ q.2
    apply lt_of_le_of_lt h
    rw [hn]
    linarith [hx.2]
  let P : ModelSpace := zoneChartMap (1 / 16) (modelBase (0 : Fin 1)) (neckFlip b q)
  have hnP : ‖P.1‖ = neckRadius (1 / 16) ‖q.1‖ q.2 :=
    modelNeck_fst_norm (by norm_num) (by norm_num) (0 : Fin 1) b hq
  have hP : ‖P.1‖ ^ 2 ≤ 2 := by
    rw [hnP]
    nlinarith
  have he : standardLoopBallHandleCycle.rimChart
      ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (1, v) = modelSphere.{0} 1 P := by
    change (modelNeck.{0} (len := 1) (ε := (1 / 16 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) 0 b) q = _
    rw [modelNeck_apply]
    rfl
  have hh := norm_sphereSecond_sq_eq (modelSphere.{0} 1 P)
  rw [cliffordHeight_modelSphere 1 hP, hnP] at hh
  have hz : ‖loopCornerChart b v‖ ^ 2 =
      (1 - (neckRadius (1 / 16) ‖q.1‖ q.2 ^ 2 - 1)) / 2 := by
    rw [loopCornerChart_apply, loopRimOrbitBase, modelPlaneComplex.symm.norm_map]
    rw [he]
    exact hh
  have ha : 2 * (1 - ‖loopCornerChart b v‖ ^ 2) =
      neckRadius (1 / 16) ‖q.1‖ q.2 ^ 2 := by rw [hz]; ring
  have hround : neckRounding (1 / 16) q = standardRimRounding v := by
    rw [neckRounding, hn]
    change standardRimRounding
      (((1 + (1 / 16 : ℝ) * v.1 - 1) / (1 / 16)),
        (((1 / 16 : ℝ) * v.2) / (1 / 16))) = _
    have he1 : (1 + (1 / 16 : ℝ) * v.1 - 1) / (1 / 16) = v.1 := by ring
    have he2 : ((1 / 16 : ℝ) * v.2) / (1 / 16) = v.2 := by ring
    rw [he1, he2]
  have hr := one_add_mul_neckRounding (ε := (1 / 16)) (by norm_num) q
  rw [hround] at hr
  rw [loopInnerRounding, ha, Real.sqrt_sq hrpos.le, ← hr]
  ring

end GC.GraphManifold.Assembly
