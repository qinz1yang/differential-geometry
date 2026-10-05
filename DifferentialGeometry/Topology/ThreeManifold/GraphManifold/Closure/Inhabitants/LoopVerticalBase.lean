import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopBundle

/-!
Every actual handle slice is a whole fibre of the genuine free-circle projection.
The same true base point exists at every time, including both handle endpoints.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

theorem loopHandleOrbitBase_source (t : Icc (0 : ℝ) 1) : ‖loopHandleOrbitBase t‖ < 1 := by
  have hn : ‖planeOfCircle (1 : Circle)‖ = 1 := by
    rw [planeOfCircle, LinearIsometryEquiv.norm_map, Circle.norm_coe]
  have hq : (planeOfCircle 1, (t : ℝ)) ∈ zoneDomain := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hn]
      norm_num
    · linarith [t.2.1]
    · linarith [t.2.2]
  have hu := zoneHeight_mem (s := 1) (t := t) (by norm_num) (by norm_num)
    (by linarith [t.2.1]) (by linarith [t.2.2])
  have hratio : 0 < zoneRatio (1 / 16) 1 (zoneHeight 1 t) :=
    zoneRatio_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu.1 hu.2
  have hle := zoneRadius_le (ε := (1 / 16)) (s := 1) (u := zoneHeight 1 t)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by linarith [hu.1]) (by linarith [hu.2])
  let P : ModelSpace := zoneChartMap (1 / 16) 0 (planeOfCircle 1, (t : ℝ))
  have hnorm : ‖P.1‖ = zoneRadius (1 / 16) 1 (zoneHeight 1 t) := by
    have he := norm_zoneChartMap_fst (ε := (1 / 16)) (by norm_num) (by norm_num) 0 hq
    rwa [hn] at he
  have hpos : 0 < ‖P.1‖ := by
    rw [hnorm, zoneRadius, one_mul]
    exact hratio
  have hbound : ‖P.1‖ ≤ 1 := by rw [hnorm]; exact hle
  have hs : ‖P.1‖ ^ 2 ≤ 2 := by nlinarith [norm_nonneg P.1]
  have hsec := norm_modelSecond_sq 1 hs
  rw [loopHandleOrbitBase, modelPlaneComplex.symm.norm_map]
  change ‖modelSecond 1 P‖ < 1
  nlinarith [norm_nonneg (modelSecond 1 P)]

def loopHandleBase (t : Icc (0 : ℝ) 1) : loopCircleBase :=
  ⟨loopHandleOrbitBase t, loopHandleOrbitBase_source t⟩

theorem loopHandle_vertical_fibre (t : Icc (0 : ℝ) 1) :
    (fun x : ClosedCell 2 =>
      (standardLoopBallHandleCycle.handle ⟨0, standardLoopBallHandleCycle.len_pos⟩).map
        (x, t)) '' diskRim =
      Subtype.val '' (loopCircleProjection ⁻¹' {loopHandleBase t}) := by
  rw [loopCircleProjection_fibre]
  exact loopHandle_vertical_orbit t

end GC.GraphManifold.Assembly
