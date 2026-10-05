import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopBallFace

/-!
The deep core torus is exactly the complete circle-fibre family over its genuine embedded base loop.
The true base loop belongs to the compact cornered base and to the common rounding zero set.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

private def coreBaseRadius : ℝ := Real.sqrt (1 / 8)

private theorem coreBaseRadius_pos : 0 < coreBaseRadius := Real.sqrt_pos.mpr (by norm_num)

private theorem coreBaseRadius_sq : coreBaseRadius ^ 2 = 1 / 8 :=
  Real.sq_sqrt (by norm_num)

def loopCoreBaseCircle (θ : Circle) : loopCircleBase :=
  ⟨coreBaseRadius • planeOfCircle θ, by
    change ‖coreBaseRadius • planeOfCircle θ‖ < 1
    rw [norm_smul, Real.norm_of_nonneg coreBaseRadius_pos.le, planeOfCircle,
      LinearIsometryEquiv.norm_map, Circle.norm_coe, mul_one]
    nlinarith [coreBaseRadius_sq]⟩

private def coreBaseInverse (z : loopCircleBase) : Circle :=
  unitOf (modelPlaneComplex z.val)

theorem loopCoreBaseCircle_norm (θ : Circle) : ‖(loopCoreBaseCircle θ).val‖ ^ 2 = 1 / 8 := by
  change ‖coreBaseRadius • planeOfCircle θ‖ ^ 2 = 1 / 8
  rw [norm_smul, Real.norm_of_nonneg coreBaseRadius_pos.le, planeOfCircle,
    LinearIsometryEquiv.norm_map, Circle.norm_coe, mul_one, coreBaseRadius_sq]

theorem loopCoreBaseCircle_smooth : ContMDiff (𝓡 1) (𝓡 2) ∞ loopCoreBaseCircle := by
  apply (ContMDiff.subtypeVal_comp_iff loopCircleBase _).mp
  change ContMDiff (𝓡 1) (𝓡 2) ∞ (fun θ : Circle => coreBaseRadius • planeOfCircle θ)
  have hr : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ (fun _ : Circle => coreBaseRadius) :=
    contMDiff_const
  exact hr.smul
    (modelPlaneComplex.symm.toContinuousLinearEquiv.contDiff.contMDiff.comp
      contMDiff_circle_coe)

theorem loopCoreBaseCircle_embedding : IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ loopCoreBaseCircle := by
  have hi (θ : Circle) : coreBaseInverse (loopCoreBaseCircle θ) = θ := by
    change unitOf (modelPlaneComplex (coreBaseRadius • planeOfCircle θ)) = θ
    rw [map_smul, modelPlaneComplex, planeOfCircle, LinearIsometryEquiv.symm_apply_apply]
    exact unitOf_smul coreBaseRadius_pos θ
  have hc : coreBaseInverse ∘ loopCoreBaseCircle = id := funext hi
  have hinj : Injective loopCoreBaseCircle := by
    intro θ θ' h
    have hh := congrArg coreBaseInverse h
    rwa [hi, hi] at hh
  refine ⟨DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv
    (by simp) loopCoreBaseCircle_smooth ?_,
    loopCoreBaseCircle_smooth.continuous.isClosedEmbedding hinj |>.isEmbedding⟩
  intro θ
  have hne : modelPlaneComplex (loopCoreBaseCircle θ).val ≠ 0 := by
    rw [← modelPlaneComplex.map_zero]
    apply modelPlaneComplex.injective.ne
    have hn := loopCoreBaseCircle_norm θ
    intro hz
    rw [hz, norm_zero] at hn
    norm_num at hn
  have hzSmooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℂ) ∞
      (fun z : loopCircleBase => modelPlaneComplex z.val) :=
    modelPlaneComplex.toContinuousLinearEquiv.contDiff.contMDiff.comp contMDiff_subtype_val
  have hd : ContMDiffAt (𝓡 2) (𝓡 1) ∞ coreBaseInverse (loopCoreBaseCircle θ) :=
    (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hne)).comp
      (loopCoreBaseCircle θ) hzSmooth.contMDiffAt
  have he := mfderiv_comp θ (hd.mdifferentiableAt (by simp))
    (loopCoreBaseCircle_smooth.mdifferentiableAt (by simp))
  rw [hc, mfderiv_id] at he
  intro v w hvw
  have hh := congrArg (mfderiv (𝓡 2) (𝓡 1) coreBaseInverse (loopCoreBaseCircle θ)) hvw
  rw [← ContinuousLinearMap.comp_apply, ← he, ← ContinuousLinearMap.comp_apply, ← he] at hh
  exact hh

theorem loopCoreBaseCircle_image : Subtype.val '' Set.range loopCoreBaseCircle =
    {z : EuclideanSpace ℝ (Fin 2) | ‖z‖ ^ 2 = 1 / 8} := by
  ext z
  constructor
  · rintro ⟨w, ⟨θ, rfl⟩, rfl⟩
    exact loopCoreBaseCircle_norm θ
  · intro hz
    have hn : ‖z‖ = coreBaseRadius := by
      have hr := coreBaseRadius_pos
      have hs := coreBaseRadius_sq
      change ‖z‖ ^ 2 = 1 / 8 at hz
      nlinarith [norm_nonneg z]
    refine ⟨loopCoreBaseCircle (unitOf (modelPlaneComplex z)), mem_range_self _, ?_⟩
    change coreBaseRadius • planeOfCircle (unitOf (modelPlaneComplex z)) = z
    apply modelPlaneComplex.injective
    rw [map_smul, modelPlaneComplex, planeOfCircle, LinearIsometryEquiv.symm_apply_apply]
    rw [← hn, ← modelPlaneComplex.norm_map]
    exact norm_smul_unitOf (modelPlaneComplex z)

theorem loopComplementFace_projection :
    loopComplementFace = loopCircleLift (Set.range loopCoreBaseCircle) := by
  rw [loopCircleLift_orbits, loopCoreBaseCircle_image, loopComplementFace_height]
  ext p
  constructor
  · intro hp
    have hne : sphereFirst p ≠ 0 := by
      have hh := norm_sphereFirst_sq_eq p
      rw [hp] at hh
      intro hz
      rw [hz, norm_zero] at hh
      norm_num at hh
    refine ⟨loopCircleCoordinates.symm p, ⟨?_, trivial⟩,
      loopCircleCoordinates.right_inv hne⟩
    rw [loopCircleCoordinates_inverse]
    change ‖modelPlaneComplex.symm (sphereSecond p)‖ ^ 2 = 1 / 8
    rw [modelPlaneComplex.symm.norm_map, norm_sphereSecond_sq_eq, hp]
    norm_num
  · rintro ⟨⟨z, θ⟩, hz, rfl⟩
    have hnorm : ‖z‖ ^ 2 = 1 / 8 := hz.1
    have hs : ‖z‖ < 1 := by nlinarith [norm_nonneg z]
    have hh := norm_sphereSecond_sq_eq (loopCircleCoordinates (z, θ))
    rw [loopCircleCoordinates_second (p := (z, θ)) hs, modelPlaneComplex.norm_map] at hh
    change cliffordHeight (loopCircleCoordinates (z, θ)) = 3 / 4
    dsimp only [Prod.fst] at hh
    linarith

theorem loopCoreBaseCircle_rounding (θ : Circle) :
    loopCircleBaseRounding (loopCoreBaseCircle θ) = 0 :=
  loopShellRounding_zero_iff.mpr (Or.inr (loopCoreBaseCircle_norm θ))

theorem loopCoreBaseCircle_cornerBase (θ : Circle) :
    loopCoreBaseCircle θ ∈ loopCircleCornerBase := by
  left
  exact (loopCoreBaseCircle_rounding θ).le

theorem loopComplementFace_closed : IsClosed loopComplementFace := by
  rw [loopComplementFace_height]
  exact isClosed_eq contMDiff_cliffordHeight.continuous continuous_const

theorem loopComplementFace_nonempty : loopComplementFace.Nonempty := by
  rw [← loopComplementFaceMap_range]
  exact Set.range_nonempty _

end GC.GraphManifold.Assembly
