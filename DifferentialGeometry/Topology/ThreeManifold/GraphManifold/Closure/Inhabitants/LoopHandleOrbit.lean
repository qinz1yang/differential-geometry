import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopHandleDefining

/-!
The genuine first-circle action preserves the original handle radial and time coordinates.
The actual global circle section therefore recovers the same handle defining coordinates.
-/

set_option autoImplicit false
noncomputable section
open Set Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

private theorem handleOrbit_chart (y : ModelSpace) :
    loopActualHandleChart y = modelSphere.{0} 1 (zoneChartMap (1 / 16) 0 y) := by
  rw [loopActualHandleChart, modelHandleChart_apply]
  have hb : modelBase (0 : Fin 1) = 0 := by norm_num [modelBase]
  rw [hb, zoneSphere]

private theorem handleOrbit_model_bound {y : ModelSpace}
    (hy : y ∈ loopActualHandleChart.source) : ‖(zoneChartMap (1 / 16) 0 y).1‖ ^ 2 ≤ 2 := by
  rw [loopActualHandleChart_source] at hy
  have hm := zoneChartMap_mem_modelSlab (by norm_num : 0 < (1 / 16 : ℝ))
    (by norm_num : (1 / 16 : ℝ) ≤ 1 / 8) (by norm_num : 0 < (1 : ℕ)) 0 hy
  have hn := norm_nonneg (zoneChartMap (1 / 16) 0 y).1
  nlinarith [hm.1]

private theorem handleOrbit_plane (θ : Circle) : modelPlaneComplex (planeOfCircle θ) = θ := by
  rw [modelPlaneComplex, planeOfCircle, LinearIsometryEquiv.symm_apply_apply]

def loopHandleRotation (y : ModelSpace) (θ : Circle) : ModelSpace :=
  (‖y.1‖ • planeOfCircle θ, y.2)

theorem loopHandleRotation_norm (y : ModelSpace) (θ : Circle) :
    ‖(loopHandleRotation y θ).1‖ = ‖y.1‖ := by
  have hθ : ‖planeOfCircle θ‖ = 1 := by simp [planeOfCircle]
  change ‖‖y.1‖ • planeOfCircle θ‖ = ‖y.1‖
  rw [norm_smul, hθ, mul_one, Real.norm_of_nonneg (norm_nonneg _)]

theorem loopHandleRotation_source {y : ModelSpace}
    (hy : y ∈ loopActualHandleChart.source) (θ : Circle) :
    loopHandleRotation y θ ∈ loopActualHandleChart.source := by
  rw [loopActualHandleChart_source] at hy ⊢
  exact ⟨by rw [loopHandleRotation_norm]; exact hy.1, hy.2⟩

private def handleOrbitAmplitude (y : ModelSpace) : ℝ :=
  (Real.sqrt 2)⁻¹ * zoneRatio (1 / 16) ‖y.1‖ (zoneHeight ‖y.1‖ y.2) * ‖y.1‖

private theorem handleOrbit_coord_nonzero {y : ModelSpace}
    (hy : y ∈ loopActualHandleChart.source) (hd : loopActualHandleChart y ∈ loopCircleDomain) :
    y.1 ≠ 0 := by
  intro he
  apply hd
  rw [handleOrbit_chart, sphereFirst_modelSphere 1 (handleOrbit_model_bound hy),
    zoneChartMap_apply]
  simp [he, modelFirst, modelPlaneComplex]

private theorem handleOrbit_amplitude_pos {y : ModelSpace}
    (hy : y ∈ loopActualHandleChart.source) (hd : loopActualHandleChart y ∈ loopCircleDomain) :
    0 < handleOrbitAmplitude y := by
  have hq : y ∈ zoneDomain := by rwa [loopActualHandleChart_source] at hy
  have hh := zoneHeight_mem (norm_nonneg y.1) hq.1 hq.2.1 hq.2.2
  exact mul_pos (mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num)))
    (zoneRatio_pos (by norm_num) (by norm_num) (norm_nonneg _) hq.1 hh.1 hh.2))
    (norm_pos_iff.mpr (handleOrbit_coord_nonzero hy hd))

theorem loopHandleRotation_first {y : ModelSpace}
    (hy : y ∈ loopActualHandleChart.source) (θ : Circle) :
    sphereFirst (loopActualHandleChart (loopHandleRotation y θ)) =
      handleOrbitAmplitude y • (θ : ℂ) := by
  rw [handleOrbit_chart, sphereFirst_modelSphere 1
    (handleOrbit_model_bound (loopHandleRotation_source hy θ)), zoneChartMap_apply]
  simp only [loopHandleRotation_norm]
  change modelFirst (zoneRatio (1 / 16) ‖y.1‖ (zoneHeight ‖y.1‖ y.2) •
    (‖y.1‖ • planeOfCircle θ)) = _
  rw [modelFirst, map_smul, map_smul, handleOrbit_plane, smul_smul, smul_smul]
  rfl

theorem loopHandleRotation_second {y : ModelSpace}
    (hy : y ∈ loopActualHandleChart.source) (θ : Circle) :
    sphereSecond (loopActualHandleChart (loopHandleRotation y θ)) =
      sphereSecond (loopActualHandleChart y) := by
  rw [handleOrbit_chart, handleOrbit_chart,
    sphereSecond_modelSphere 1 (handleOrbit_model_bound (loopHandleRotation_source hy θ)),
    sphereSecond_modelSphere 1 (handleOrbit_model_bound hy)]
  have hn : ‖(zoneChartMap (1 / 16) 0 (loopHandleRotation y θ)).1‖ =
      ‖(zoneChartMap (1 / 16) 0 y).1‖ := by
    rw [norm_zoneChartMap_fst (by norm_num) (by norm_num) _
      (by rw [← loopActualHandleChart_source]; exact loopHandleRotation_source hy θ),
      norm_zoneChartMap_fst (by norm_num) (by norm_num) _
        (by rw [← loopActualHandleChart_source]; exact hy), loopHandleRotation_norm]
    rfl
  have hh : (zoneChartMap (1 / 16) 0 (loopHandleRotation y θ)).2 =
      (zoneChartMap (1 / 16) 0 y).2 := by
    simp only [zoneChartMap_apply, loopHandleRotation_norm]
    rfl
  simp only [modelSecond, hn, hh]

theorem loopHandleRotation_domain {y : ModelSpace}
    (hy : y ∈ loopActualHandleChart.source) (hd : loopActualHandleChart y ∈ loopCircleDomain)
    (θ : Circle) : loopActualHandleChart (loopHandleRotation y θ) ∈ loopCircleDomain := by
  change sphereFirst _ ≠ 0
  rw [loopHandleRotation_first hy θ]
  exact smul_ne_zero (handleOrbit_amplitude_pos hy hd).ne' (Circle.coe_ne_zero θ)

theorem loopHandleRotation_section {y : ModelSpace}
    (hy : y ∈ loopActualHandleChart.source) (hd : loopActualHandleChart y ∈ loopCircleDomain) :
    loopCircleSection (loopCircleProjection ⟨loopActualHandleChart y, hd⟩) =
      loopActualHandleChart (loopHandleRotation y 1) := by
  let z := loopCircleProjection ⟨loopActualHandleChart y, hd⟩
  have he : loopCircleCoordinates.symm (loopActualHandleChart (loopHandleRotation y 1)) =
      (z.val, (1 : Circle)) := by
    rw [loopCircleCoordinates_inverse]
    apply Prod.ext
    · rw [loopHandleRotation_second hy 1]
      exact (loopCircleProjection_val ⟨loopActualHandleChart y, hd⟩).symm
    · rw [loopHandleRotation_first hy 1, unitOf_smul (handleOrbit_amplitude_pos hy hd)]
  have hs := loopCircleSection_inverse z
  have hh := congrArg loopCircleCoordinates (hs.trans he.symm)
  exact (loopCircleCoordinates.right_inv (loopCircleSection_domain z)).symm.trans
    (hh.trans (loopCircleCoordinates.right_inv (loopHandleRotation_domain hy hd 1)))

theorem loopHandleRotation_inverse_norm {y : ModelSpace}
    (hy : y ∈ loopActualHandleChart.source) (hd : loopActualHandleChart y ∈ loopCircleDomain) :
    ‖(loopActualHandleChart.symm (loopCircleSection
      (loopCircleProjection ⟨loopActualHandleChart y, hd⟩))).1‖ = ‖y.1‖ := by
  rw [loopHandleRotation_section hy hd]
  have hh := loopActualHandleChart.left_inv (loopHandleRotation_source hy 1)
  change loopActualHandleChart.symm (loopActualHandleChart (loopHandleRotation y 1)) = _ at hh
  rw [hh, loopHandleRotation_norm]

theorem loopHandleRotation_inverse_time {y : ModelSpace}
    (hy : y ∈ loopActualHandleChart.source) (hd : loopActualHandleChart y ∈ loopCircleDomain) :
    (loopActualHandleChart.symm (loopCircleSection
      (loopCircleProjection ⟨loopActualHandleChart y, hd⟩))).2 = y.2 := by
  rw [loopHandleRotation_section hy hd]
  have hh := loopActualHandleChart.left_inv (loopHandleRotation_source hy 1)
  change loopActualHandleChart.symm (loopActualHandleChart (loopHandleRotation y 1)) = _ at hh
  rw [hh]
  rfl

end GC.GraphManifold.Assembly
