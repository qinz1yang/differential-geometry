import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopShell

/-!
Every time slice of the actual one-handle loop has its whole first-Clifford circle orbit.
The base coordinate is the actual second Clifford component, retaining both endpoints.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

private def verticalRadius (t : Icc (0 : ℝ) 1) : ℝ :=
  zoneRatio (1 / 16) 1 (zoneHeight 1 t)

private theorem verticalRadius_pos (t : Icc (0 : ℝ) 1) : 0 < verticalRadius t := by
  have hu := zoneHeight_mem (s := 1) (t := t) (by norm_num) (by norm_num)
    (by linarith [t.2.1]) (by linarith [t.2.2])
  exact zoneRatio_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu.1 hu.2

private theorem verticalRadius_le (t : Icc (0 : ℝ) 1) : verticalRadius t ≤ 1 := by
  have hu := zoneHeight_mem (s := 1) (t := t) (by norm_num) (by norm_num)
    (by linarith [t.2.1]) (by linarith [t.2.2])
  have hr := zoneRadius_le (ε := (1 / 16)) (s := 1) (u := zoneHeight 1 t)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by linarith [hu.1]) (by linarith [hu.2])
  simpa only [verticalRadius, zoneRadius, one_mul] using hr

private theorem verticalPlane_norm (θ : Circle) : ‖planeOfCircle θ‖ = 1 := by
  rw [planeOfCircle, LinearIsometryEquiv.norm_map, Circle.norm_coe]

private theorem verticalHandle_eq (t : Icc (0 : ℝ) 1) (θ : Circle) :
    (standardLoopBallHandleCycle.handle ⟨0, standardLoopBallHandleCycle.len_pos⟩).map
      (circleRimPoint θ, t) =
    modelSphere.{0} 1 (verticalRadius t • planeOfCircle θ, zoneHeight 1 t) := by
  change modelSphere.{0} 1
    (zoneChartMap (1 / 16) (modelBase (0 : Fin 1))
      ((circleRimPoint θ : ModelPlane), (t : ℝ))) = _
  rw [zoneChartMap_apply, circleRimPoint_val]
  have hb : modelBase (0 : Fin 1) = 0 := by norm_num [modelBase]
  rw [hb]
  change modelSphere.{0} 1
    (zoneRatio (1 / 16) ‖planeOfCircle θ‖ (zoneHeight ‖planeOfCircle θ‖ t) •
      planeOfCircle θ, 0 + zoneHeight ‖planeOfCircle θ‖ t) = _
  rw [verticalPlane_norm, zero_add]
  rfl

def loopHandleOrbitBase (t : Icc (0 : ℝ) 1) : EuclideanSpace ℝ (Fin 2) :=
  modelPlaneComplex.symm (modelSecond 1
    (zoneChartMap (1 / 16) 0 (planeOfCircle 1, (t : ℝ))))

private theorem verticalBase_eq (t : Icc (0 : ℝ) 1) (θ : Circle) :
    loopHandleOrbitBase t = modelPlaneComplex.symm
      (modelSecond 1 (verticalRadius t • planeOfCircle θ, zoneHeight 1 t)) := by
  rw [loopHandleOrbitBase, zoneChartMap_apply, verticalPlane_norm, zero_add]
  change modelPlaneComplex.symm
    (modelSecond 1 (verticalRadius t • planeOfCircle 1, zoneHeight 1 t)) = _
  congr 1
  simp only [modelSecond, norm_smul, verticalPlane_norm]

private theorem verticalPoint_source (t : Icc (0 : ℝ) 1) (θ : Circle) :
    ‖verticalRadius t • planeOfCircle θ‖ ^ 2 ≤ 2 := by
  rw [norm_smul, Real.norm_of_nonneg (verticalRadius_pos t).le,
    verticalPlane_norm, mul_one]
  nlinarith [verticalRadius_pos t, verticalRadius_le t]

private theorem verticalInverse (t : Icc (0 : ℝ) 1) (θ : Circle) :
    loopCircleCoordinates.symm
      ((standardLoopBallHandleCycle.handle ⟨0, standardLoopBallHandleCycle.len_pos⟩).map
        (circleRimPoint θ, t)) = (loopHandleOrbitBase t, θ) := by
  rw [verticalHandle_eq, loopCircleCoordinates_inverse]
  refine Prod.ext ?_ ?_
  · have hs := sphereSecond_modelSphere.{0} 1
      (p := (verticalRadius t • planeOfCircle θ, zoneHeight 1 t))
      (verticalPoint_source t θ)
    rw [hs]
    exact (verticalBase_eq t θ).symm
  · have hs := sphereFirst_modelSphere.{0} 1
      (p := (verticalRadius t • planeOfCircle θ, zoneHeight 1 t))
      (verticalPoint_source t θ)
    rw [hs, modelFirst, map_smul, smul_smul]
    have he : modelPlaneComplex (planeOfCircle θ) = (θ : ℂ) :=
      modelPlaneComplex.apply_symm_apply (θ : ℂ)
    rw [he]
    exact unitOf_smul (mul_pos (by positivity) (verticalRadius_pos t)) θ

private theorem verticalTarget (t : Icc (0 : ℝ) 1) (θ : Circle) :
    sphereFirst ((standardLoopBallHandleCycle.handle
      ⟨0, standardLoopBallHandleCycle.len_pos⟩).map (circleRimPoint θ, t)) ≠ 0 := by
  have hs := sphereFirst_modelSphere.{0} 1
    (p := (verticalRadius t • planeOfCircle θ, zoneHeight 1 t))
    (verticalPoint_source t θ)
  rw [verticalHandle_eq, hs, modelFirst]
  apply smul_ne_zero (by positivity)
  rw [← modelPlaneComplex.map_zero]
  apply modelPlaneComplex.injective.ne
  apply smul_ne_zero (verticalRadius_pos t).ne'
  exact norm_ne_zero_iff.mp (by rw [verticalPlane_norm]; norm_num)

theorem loopHandle_vertical_orbit (t : Icc (0 : ℝ) 1) :
    (fun x : ClosedCell 2 =>
      (standardLoopBallHandleCycle.handle ⟨0, standardLoopBallHandleCycle.len_pos⟩).map
        (x, t)) '' diskRim =
      loopCircleCoordinates '' ({loopHandleOrbitBase t} ×ˢ Set.univ) := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨θ, rfl⟩ := exists_circleRimPoint_eq hx
    refine ⟨(loopHandleOrbitBase t, θ), ⟨rfl, mem_univ θ⟩, ?_⟩
    rw [← verticalInverse t θ]
    exact loopCircleCoordinates.right_inv (verticalTarget t θ)
  · rintro ⟨⟨z, θ⟩, hp, rfl⟩
    have hz : z = loopHandleOrbitBase t := hp.1
    subst z
    refine ⟨circleRimPoint θ, circleRimPoint_mem_diskRim θ, ?_⟩
    rw [← verticalInverse t θ]
    exact (loopCircleCoordinates.right_inv (verticalTarget t θ)).symm

end GC.GraphManifold.Assembly
