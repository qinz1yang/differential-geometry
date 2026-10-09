import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopArcOrbit

/-!
The actual original annulus projects to a smooth base arc through both endpoints.
Its unwrapped second-coordinate phase recovers height and proves injectivity.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

theorem loopBallArcHeight_smooth : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ loopBallArcHeight :=
  contMDiff_const.add (contMDiff_const.mul contMDiff_subtypeVal_Icc)

private def arcSmoothRadius (t : Set.Icc (0 : ℝ) 1) : ℝ :=
  Real.sqrt (1 - loopBallArcHeight t ^ 2)

private theorem arcSmoothRadius_pos (t : Set.Icc (0 : ℝ) 1) : 0 < arcSmoothRadius t := by
  apply Real.sqrt_pos.mpr
  have ht := loopBallArcHeight_bounds t
  nlinarith [mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ht.2)]

private theorem arcSmoothRadius_smooth : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ arcSmoothRadius := by
  intro t
  have hp : 0 < 1 - loopBallArcHeight t ^ 2 := by
    have ht := loopBallArcHeight_bounds t
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ht.2)]
  exact (Real.contDiffAt_sqrt hp.ne').contMDiffAt.comp t
    (contMDiff_const.sub (loopBallArcHeight_smooth.pow 2)).contMDiffAt

theorem loopBallArcImageRadius_smooth : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞
    loopBallArcImageRadius := by
  have hp : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun t : Set.Icc (0 : ℝ) 1 => (arcSmoothRadius t ^ 2, loopBallArcHeight t)) :=
    (arcSmoothRadius_smooth.pow 2).prodMk_space loopBallArcHeight_smooth
  have hr := (contDiff_ballRatioSq (by norm_num : (0 : ℝ) < 1 / 16)
    (by norm_num : (1 / 16 : ℝ) ≤ 1 / 8)).contMDiff.comp hp
  exact arcSmoothRadius_smooth.mul hr

private def arcSlabChart : PartialDiffeomorph 𝓘(ℝ, ModelSpace) (𝓡 3)
    ModelSpace SphereCarrier.{0} ∞ := modelSphereChart (by norm_num : 0 < 1) (-2)

private theorem arcSlabSource (t : Set.Icc (0 : ℝ) 1) :
    (loopBallArcImageRadius t • planeOfCircle 1, -loopBallArcHeight t) ∈ arcSlabChart.source := by
  rw [arcSlabChart, modelSphereChart_source]
  dsimp only [modelSlab, mem_ofPred_eq, Prod.fst, Prod.snd]
  simp only [Nat.cast_one]
  have ht := loopBallArcHeight_bounds t
  constructor
  · rw [norm_smul, Real.norm_of_nonneg (loopBallArcImageRadius_pos t).le, planeOfCircle,
      LinearIsometryEquiv.norm_map, Circle.norm_coe, mul_one]
    linarith [loopBallArcImageRadius_le t]
  · constructor <;> linarith [ht.1, ht.2]

private theorem arcModel_smooth : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ModelSpace) ∞
    (fun t : Set.Icc (0 : ℝ) 1 =>
      (loopBallArcImageRadius t • planeOfCircle 1, -loopBallArcHeight t)) := by
  have hp : ContMDiff (𝓡∂ 1) (𝓡 2) ∞
      (fun _ : Set.Icc (0 : ℝ) 1 => planeOfCircle 1) := contMDiff_const
  exact (loopBallArcImageRadius_smooth.smul hp).prodMk_space loopBallArcHeight_smooth.neg

theorem loopBallAnnulus_one_smooth : ContMDiff (𝓡∂ 1) (𝓡 3) ∞
    (fun t : Set.Icc (0 : ℝ) 1 => loopBallAnnulus (1, t)) := by
  have hf : ContMDiff (𝓡∂ 1) (𝓡 3) ∞
      (fun t : Set.Icc (0 : ℝ) 1 => arcSlabChart
        (loopBallArcImageRadius t • planeOfCircle 1, -loopBallArcHeight t)) := by
    intro t
    exact (arcSlabChart.contMDiffOn_toFun.contMDiffAt
      (arcSlabChart.open_source.mem_nhds (arcSlabSource t))).comp t arcModel_smooth.contMDiffAt
  apply hf.congr
  intro t
  exact loopBallAnnulus_model 1 t

theorem loopBallArcBase_smooth : ContMDiff (𝓡∂ 1) (𝓡 2) ∞ loopBallArcBase := by
  have hd : ContMDiff (𝓡∂ 1) (𝓡 3) ∞ (fun t : Set.Icc (0 : ℝ) 1 =>
      (⟨loopBallAnnulus (1, t), loopBallAnnulus_domain 1 t⟩ : loopCircleDomain)) :=
    (ContMDiff.subtypeVal_comp_iff loopCircleDomain _).mp loopBallAnnulus_one_smooth
  exact loopCircleProjection_smooth.comp hd

theorem loopBallArcBase_arg (t : Set.Icc (0 : ℝ) 1) :
    Complex.arg (modelPlaneComplex (loopBallArcBase t).val) =
      -modelAngleScale 1 * loopBallArcHeight t := by
  have hs := arcSlabSource t
  have ha := arg_modelSecond_mul_exp (by norm_num : 0 < 1)
    (a := -2) (p := (loopBallArcImageRadius t • planeOfCircle 1, -loopBallArcHeight t)) hs
  have hangle : modelSlabAngle 1 (-2) = 0 := by norm_num [modelSlabAngle]
  rw [hangle, neg_zero, Circle.exp_zero, Circle.coe_one, mul_one, sub_zero] at ha
  have hn : ‖loopBallArcImageRadius t • planeOfCircle 1‖ ^ 2 ≤ 2 := by
    rw [norm_smul, Real.norm_of_nonneg (loopBallArcImageRadius_pos t).le, planeOfCircle,
      LinearIsometryEquiv.norm_map, Circle.norm_coe, mul_one]
    nlinarith [loopBallArcImageRadius_pos t, loopBallArcImageRadius_le t]
  change Complex.arg (modelPlaneComplex
    (loopCircleProjection ⟨loopBallAnnulus (1, t), loopBallAnnulus_domain 1 t⟩).val) = _
  rw [loopCircleProjection_val, modelPlaneComplex.apply_symm_apply]
  change Complex.arg (sphereSecond (loopBallAnnulus (1, t))) = _
  rw [loopBallAnnulus_model]
  have he := sphereSecond_modelSphere.{0} 1
    (p := (loopBallArcImageRadius t • planeOfCircle 1, -loopBallArcHeight t)) hn
  rw [he, ha]
  ring

theorem loopBallArcBase_slit (t : Set.Icc (0 : ℝ) 1) :
    modelPlaneComplex (loopBallArcBase t).val ∈ Complex.slitPlane := by
  have ht := arcSlabChart.map_source (arcSlabSource t)
  have he : arcSlabChart
      (loopBallArcImageRadius t • planeOfCircle 1, -loopBallArcHeight t) =
      loopBallAnnulus (1, t) := (loopBallAnnulus_model 1 t).symm
  rw [he] at ht
  change _ ∧ sphereSecond (loopBallAnnulus (1, t)) *
    (Circle.exp (-modelSlabAngle 1 (-2)) : ℂ) ∈ Complex.slitPlane at ht
  have hangle : modelSlabAngle 1 (-2) = 0 := by norm_num [modelSlabAngle]
  rw [hangle, neg_zero, Circle.exp_zero, Circle.coe_one, mul_one] at ht
  change modelPlaneComplex
    (loopCircleProjection ⟨loopBallAnnulus (1, t), loopBallAnnulus_domain 1 t⟩).val ∈ _
  rw [loopCircleProjection_val, modelPlaneComplex.apply_symm_apply]
  exact ht.2

theorem loopBallArcBase_injective : Function.Injective loopBallArcBase := by
  intro t s he
  have hh := congrArg (fun z : loopCircleBase => Complex.arg (modelPlaneComplex z.val)) he
  rw [loopBallArcBase_arg, loopBallArcBase_arg] at hh
  have hk := modelAngleScale_pos (by norm_num : 0 < 1)
  have hheight : loopBallArcHeight t = loopBallArcHeight s := by nlinarith
  apply Subtype.ext
  unfold loopBallArcHeight at hheight
  linarith

end GC.GraphManifold.Assembly
