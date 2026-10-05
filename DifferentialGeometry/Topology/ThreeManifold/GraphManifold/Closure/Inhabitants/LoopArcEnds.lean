import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopArcOrbit
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopHandleRimInverse

/-!
The actual ball annulus ends are the original two rim circles with their whole first-circle angle.
Its actual base arc endpoints are exactly the two prescribed corner centers.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

private theorem arcEnd_radius (b : Bool) :
    loopBallArcImageRadius (iccEnd b) = neckRadius (1/16) 1 0 := by
  change ballRadius (1/16) (Real.sqrt (1-loopBallArcHeight (iccEnd b)^2))
    (loopBallArcHeight (iccEnd b)) = _
  have hh : 1/4 ≤ |loopBallArcHeight (iccEnd b)| := by
    cases b <;> norm_num [loopBallArcHeight,iccEnd]
  have hu : |loopBallArcHeight (iccEnd b)| ≤ 1 := by
    cases b <;> norm_num [loopBallArcHeight,iccEnd]
  rw [(ballRadius_sphere (by norm_num) (by norm_num) hh hu).1]
  congr 1
  cases b <;> norm_num [loopBallArcHeight,iccEnd,Real.sqrt_eq_iff_eq_sq]

private theorem arcEnd_rimModel (b : Bool) (θ : Circle) :
    standardLoopBallHandleCycle.rimChart ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (θ,(0,0)) =
    modelSphere.{0} 1 (neckRadius (1/16) 1 0 • planeOfCircle θ, if b then 4-3/5 else 3/5) := by
  have hθ : ‖planeOfCircle θ‖ = 1 := by simp [planeOfCircle]
  have hq : neckRim (1/16) (θ,(0,0)) = (planeOfCircle θ,0) := by
    simp [neckRim]
  have hd : (planeOfCircle θ,0) ∈ neckDomain (1/16) := by
    constructor
    · change ‖planeOfCircle θ‖ < 1+2*(1/16 : ℝ)
      rw [hθ]
      norm_num
    · change |(0 : ℝ)| < 2*(1/16 : ℝ)
      norm_num
  change modelNeck.{0} (len := 1) (ε := (1/16))
    (by norm_num) (by norm_num) (by norm_num) 0 b (neckRim (1/16) (θ,(0,0))) = _
  rw [hq,modelNeck_apply]
  change modelSphere.{0} 1 (zoneChartMap (1/16) (modelBase (0 : Fin 1))
    (neckFlip b (planeOfCircle θ,0))) = _
  rw [zoneChartMap_neckFlip (by norm_num) (by norm_num) _ b hd]
  rw [hθ]
  have hb : modelBase (0 : Fin 1) = 0 := by norm_num [modelBase]
  rw [hb]
  have hr : neckRatio (1/16) 1 0 = neckRadius (1/16) 1 0 := by
    have he := neckRatio_mul (ε := (1/16 : ℝ)) (τ := 0) (by norm_num : (1 : ℝ) ≠ 0)
    simpa using he
  rw [hr]
  cases b <;> norm_num [capCos]

theorem loopBallAnnulus_end (b : Bool) (θ : Circle) :
    loopBallAnnulus (θ,iccEnd b) =
    standardLoopBallHandleCycle.rimChart ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (θ,(0,0)) := by
  rw [loopBallAnnulus_model,arcEnd_radius,arcEnd_rimModel]
  cases b
  · congr 1
    norm_num [loopBallArcHeight,iccEnd]
  · have hp := modelSphere_add_period.{0} (by norm_num : 0 < 1)
      (neckRadius (1/16) 1 0 • planeOfCircle θ,(-3/5 : ℝ)) (1 : ℤ)
    have he : -loopBallArcHeight (iccEnd true) = (-3/5 : ℝ) := by
      norm_num [loopBallArcHeight,iccEnd]
    rw [he]
    convert hp.symm using 1
    all_goals norm_num

theorem loopBallArcBase_end (b : Bool) : loopBallArcBase (iccEnd b) = loopBaseCorner b (0,0) := by
  have hs : (0,0) ∈ rimBox 2 := by constructor <;> norm_num
  have hp := loopBallAnnulus_projection 1 (iccEnd b)
  have he : (⟨loopBallAnnulus (1,iccEnd b), loopBallAnnulus_domain 1 (iccEnd b)⟩
      : loopCircleDomain) =
      ⟨standardLoopBallHandleCycle.rimChart ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (1,(0,0)),
        loopRegionRim_domain b 1 (0,0) hs⟩ := Subtype.ext (loopBallAnnulus_end b 1)
  rw [he] at hp
  exact hp.symm.trans (loopRegionRim_projection b 1 (0,0) hs)

end GC.GraphManifold.Assembly
