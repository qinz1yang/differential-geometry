import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopBallDefining
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopBallLatitude

/-!
The genuine first-circle action preserves the original ball chart radial coordinate.
The actual global circle section therefore recovers the same ball defining radius.
-/

set_option autoImplicit false
noncomputable section
open Set Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

private theorem ballOrbit_chart (x : EuclideanSpace ℝ (Fin 3)) :
    loopActualBallChart x = modelSphere.{0} 1 (ballMap (1 / 16) 0 x) := by
  rw [loopActualBallChart, modelBallChart_apply]
  have hb : modelBase (0 : Fin 1) = 0 := by norm_num [modelBase]
  rw [hb, ballSphere]

private theorem ballOrbit_model_bound {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ loopActualBallChart.source) : ‖(ballMap (1 / 16) 0 x).1‖ ^ 2 ≤ 2 := by
  rw [loopActualBallChart_source, mem_ball_zero_iff] at hx
  have hm := ballMap_mem_modelSlab (by norm_num : 0 < (1 / 16 : ℝ))
    (by norm_num : (1 / 16 : ℝ) ≤ 1 / 8) (by norm_num : 0 < (1 : ℕ)) 0 hx
  have hn := norm_nonneg (ballMap (1 / 16) 0 x).1
  nlinarith [hm.1]

private theorem ballOrbit_plane (θ : Circle) : modelPlaneComplex (planeOfCircle θ) = θ := by
  rw [modelPlaneComplex, planeOfCircle, LinearIsometryEquiv.symm_apply_apply]

def loopBallRotation (x : EuclideanSpace ℝ (Fin 3)) (θ : Circle) :
    EuclideanSpace ℝ (Fin 3) := loopBallCoordinates.symm
      (‖(ballCoord x).1‖ • planeOfCircle θ, (ballCoord x).2)

theorem loopBallRotation_coordinates (x : EuclideanSpace ℝ (Fin 3)) (θ : Circle) :
    ballCoord (loopBallRotation x θ) =
      (‖(ballCoord x).1‖ • planeOfCircle θ, (ballCoord x).2) :=
  loopBallCoordinates.apply_symm_apply _

theorem loopBallRotation_norm (x : EuclideanSpace ℝ (Fin 3)) (θ : Circle) :
    ‖loopBallRotation x θ‖ = ‖x‖ := by
  have hθ : ‖planeOfCircle θ‖ = 1 := by simp [planeOfCircle]
  have hq := norm_sq_ballCoord (loopBallRotation x θ)
  rw [loopBallRotation_coordinates, norm_smul, hθ, mul_one,
    Real.norm_of_nonneg (norm_nonneg _)] at hq
  have hx := norm_sq_ballCoord x
  nlinarith [norm_nonneg (loopBallRotation x θ), norm_nonneg x]

theorem loopBallRotation_source {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ loopActualBallChart.source) (θ : Circle) :
    loopBallRotation x θ ∈ loopActualBallChart.source := by
  rw [loopActualBallChart_source, mem_ball_zero_iff] at hx ⊢
  rwa [loopBallRotation_norm]

private def ballOrbitAmplitude (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (Real.sqrt 2)⁻¹ * ballRatioSq (1 / 16) (‖(ballCoord x).1‖ ^ 2) (ballCoord x).2 *
    ‖(ballCoord x).1‖

private theorem ballOrbit_coord_nonzero {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ loopActualBallChart.source) (hd : loopActualBallChart x ∈ loopCircleDomain) :
    (ballCoord x).1 ≠ 0 := by
  intro he
  apply hd
  rw [ballOrbit_chart, sphereFirst_modelSphere 1 (ballOrbit_model_bound hx), ballMap_apply]
  simp [he, modelFirst, modelPlaneComplex]

private theorem ballOrbit_amplitude_pos {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ loopActualBallChart.source) (hd : loopActualBallChart x ∈ loopCircleDomain) :
    0 < ballOrbitAmplitude x := by
  exact mul_pos (mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num)))
    (ballRatioSq_pos (by norm_num) (by norm_num) _ _))
    (norm_pos_iff.mpr (ballOrbit_coord_nonzero hx hd))

theorem loopBallRotation_first {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ loopActualBallChart.source) (θ : Circle) :
    sphereFirst (loopActualBallChart (loopBallRotation x θ)) =
      ballOrbitAmplitude x • (θ : ℂ) := by
  rw [ballOrbit_chart, sphereFirst_modelSphere 1
    (ballOrbit_model_bound (loopBallRotation_source hx θ)), ballMap_apply,
    loopBallRotation_coordinates]
  have hθ : ‖planeOfCircle θ‖ = 1 := by simp [planeOfCircle]
  simp only [norm_smul, hθ, mul_one,
    Real.norm_of_nonneg (norm_nonneg _)]
  rw [modelFirst, map_smul, map_smul, ballOrbit_plane, smul_smul, smul_smul]
  rfl

theorem loopBallRotation_second {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ loopActualBallChart.source) (θ : Circle) :
    sphereSecond (loopActualBallChart (loopBallRotation x θ)) =
      sphereSecond (loopActualBallChart x) := by
  rw [ballOrbit_chart, ballOrbit_chart,
    sphereSecond_modelSphere 1 (ballOrbit_model_bound (loopBallRotation_source hx θ)),
    sphereSecond_modelSphere 1 (ballOrbit_model_bound hx)]
  have hn : ‖(ballMap (1 / 16) 0 (loopBallRotation x θ)).1‖ =
      ‖(ballMap (1 / 16) 0 x).1‖ := by
    rw [norm_ballMap_fst (by norm_num) (by norm_num),
      norm_ballMap_fst (by norm_num) (by norm_num), loopBallRotation_coordinates]
    have hθ : ‖planeOfCircle θ‖ = 1 := by simp [planeOfCircle]
    simp only [norm_smul, hθ, mul_one, Real.norm_of_nonneg (norm_nonneg _)]
  have hh : (ballMap (1 / 16) 0 (loopBallRotation x θ)).2 =
      (ballMap (1 / 16) 0 x).2 := by
    rw [ballMap_snd, ballMap_snd, loopBallRotation_coordinates]
  simp only [modelSecond, hn, hh]

theorem loopBallRotation_domain {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ loopActualBallChart.source) (hd : loopActualBallChart x ∈ loopCircleDomain)
    (θ : Circle) : loopActualBallChart (loopBallRotation x θ) ∈ loopCircleDomain := by
  change sphereFirst _ ≠ 0
  rw [loopBallRotation_first hx θ]
  exact smul_ne_zero (ballOrbit_amplitude_pos hx hd).ne' (Circle.coe_ne_zero θ)

theorem loopBallRotation_section {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ loopActualBallChart.source) (hd : loopActualBallChart x ∈ loopCircleDomain) :
    loopCircleSection (loopCircleProjection ⟨loopActualBallChart x, hd⟩) =
      loopActualBallChart (loopBallRotation x 1) := by
  let z := loopCircleProjection ⟨loopActualBallChart x, hd⟩
  have he : loopCircleCoordinates.symm (loopActualBallChart (loopBallRotation x 1)) =
      (z.val, (1 : Circle)) := by
    rw [loopCircleCoordinates_inverse]
    apply Prod.ext
    · rw [loopBallRotation_second hx 1]
      exact (loopCircleProjection_val ⟨loopActualBallChart x, hd⟩).symm
    · rw [loopBallRotation_first hx 1, unitOf_smul (ballOrbit_amplitude_pos hx hd)]
  have hs := loopCircleSection_inverse z
  have hh := congrArg loopCircleCoordinates (hs.trans he.symm)
  exact (loopCircleCoordinates.right_inv (loopCircleSection_domain z)).symm.trans
    (hh.trans (loopCircleCoordinates.right_inv (loopBallRotation_domain hx hd 1)))

theorem loopBallRotation_inverse_norm {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ loopActualBallChart.source) (hd : loopActualBallChart x ∈ loopCircleDomain) :
    ‖loopActualBallChart.symm (loopCircleSection
      (loopCircleProjection ⟨loopActualBallChart x, hd⟩))‖ = ‖x‖ := by
  rw [loopBallRotation_section hx hd]
  have hh := loopActualBallChart.left_inv (loopBallRotation_source hx 1)
  change loopActualBallChart.symm (loopActualBallChart (loopBallRotation x 1)) = _ at hh
  rw [hh, loopBallRotation_norm]

end GC.GraphManifold.Assembly
