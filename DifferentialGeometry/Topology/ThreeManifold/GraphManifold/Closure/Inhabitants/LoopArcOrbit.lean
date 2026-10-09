import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopBallLatitude

/-!
The actual original ball annulus retains the true complete first-Clifford circle at every time.
Its genuine base arc is the native projection, with no missing angles or substituted action.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

def loopBallArcHeight (t : Set.Icc (0 : ℝ) 1) : ℝ := -3 / 5 + (6 / 5) * t.val

theorem loopBallArcHeight_bounds (t : Set.Icc (0 : ℝ) 1) :
    -3 / 5 ≤ loopBallArcHeight t ∧ loopBallArcHeight t ≤ 3 / 5 := by
  have ht := t.property
  unfold loopBallArcHeight
  constructor <;> linarith [ht.1, ht.2]

private def arcPlaneRadius (t : Set.Icc (0 : ℝ) 1) : ℝ :=
  Real.sqrt (1 - loopBallArcHeight t ^ 2)

private theorem arcPlaneRadius_pos (t : Set.Icc (0 : ℝ) 1) : 0 < arcPlaneRadius t := by
  apply Real.sqrt_pos.mpr
  have ht := loopBallArcHeight_bounds t
  nlinarith [mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ht.2)]

private theorem arcPlaneRadius_sq (t : Set.Icc (0 : ℝ) 1) :
    arcPlaneRadius t ^ 2 = 1 - loopBallArcHeight t ^ 2 := by
  apply Real.sq_sqrt
  have ht := loopBallArcHeight_bounds t
  nlinarith [mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ht.2)]

private theorem arcPlane_norm (θ : Circle) : ‖planeOfCircle θ‖ = 1 := by
  rw [planeOfCircle, LinearIsometryEquiv.norm_map, Circle.norm_coe]

private theorem arcPlaneComplex (θ : Circle) :
    modelPlaneComplex (planeOfCircle θ) = (θ : ℂ) := by
  change Complex.orthonormalBasisOneI.repr.symm
    (Complex.orthonormalBasisOneI.repr (θ : ℂ)) = (θ : ℂ)
  exact LinearIsometryEquiv.symm_apply_apply _ _

private theorem latitudeCoord (θ : Circle) (t : Set.Icc (0 : ℝ) 1) :
    ballCoord (loopBallLatitudePoint θ t).val =
      (arcPlaneRadius t • planeOfCircle θ, loopBallArcHeight t) :=
  loopBallLatitudePoint_coordinates θ t

def loopBallArcImageRadius (t : Set.Icc (0 : ℝ) 1) : ℝ :=
  ballRadius (1 / 16) (arcPlaneRadius t) (loopBallArcHeight t)

theorem loopBallArcImageRadius_pos (t : Set.Icc (0 : ℝ) 1) : 0 < loopBallArcImageRadius t :=
  mul_pos (arcPlaneRadius_pos t) (ballRatioSq_pos (by norm_num) (by norm_num) _ _)

theorem loopBallArcImageRadius_le (t : Set.Icc (0 : ℝ) 1) : loopBallArcImageRadius t ≤ 1 := by
  have hb := (ballMap_range (by norm_num : (0 : ℝ) < 1 / 16)
    (by norm_num : (1 / 16 : ℝ) ≤ 1 / 8) 0 (loopBallLatitudePoint 1 t)).1
  have hn : ‖arcPlaneRadius t • planeOfCircle 1‖ = arcPlaneRadius t := by
    rw [norm_smul, Real.norm_of_nonneg (arcPlaneRadius_pos t).le, arcPlane_norm, mul_one]
  rw [ballMap_apply, latitudeCoord] at hb
  dsimp only [Prod.fst, Prod.snd] at hb
  rw [hn, norm_smul, Real.norm_of_nonneg
    (ballRatioSq_pos (by norm_num) (by norm_num) _ _).le, hn] at hb
  simpa only [loopBallArcImageRadius, ballRadius, mul_comm] using hb

theorem loopBallAnnulus_model (θ : Circle) (t : Set.Icc (0 : ℝ) 1) :
    loopBallAnnulus (θ, t) =
      modelSphere.{0} 1 (loopBallArcImageRadius t • planeOfCircle θ, -loopBallArcHeight t) := by
  change modelSphere.{0} 1
    (ballMap (1 / 16) (modelBase (0 : Fin 1)) (loopBallLatitudePoint θ t).val) = _
  have hb : modelBase (0 : Fin 1) = 0 := by norm_num [modelBase]
  rw [hb, ballMap_apply, latitudeCoord]
  dsimp only [Prod.fst, Prod.snd]
  have hn : ‖arcPlaneRadius t • planeOfCircle θ‖ = arcPlaneRadius t := by
    rw [norm_smul, Real.norm_of_nonneg (arcPlaneRadius_pos t).le, arcPlane_norm, mul_one]
  rw [hn, smul_smul]
  congr 1
  apply Prod.ext
  · change (ballRatioSq (1 / 16) (arcPlaneRadius t ^ 2) (loopBallArcHeight t) *
      arcPlaneRadius t) • planeOfCircle θ = loopBallArcImageRadius t • planeOfCircle θ
    rw [loopBallArcImageRadius, ballRadius, mul_comm]
  · ring

theorem loopBallAnnulus_domain (θ : Circle) (t : Set.Icc (0 : ℝ) 1) :
    loopBallAnnulus (θ, t) ∈ loopCircleDomain := by
  have hn : ‖loopBallArcImageRadius t • planeOfCircle θ‖ = loopBallArcImageRadius t := by
    rw [norm_smul, Real.norm_of_nonneg (loopBallArcImageRadius_pos t).le,
      arcPlane_norm, mul_one]
  have hs : ‖loopBallArcImageRadius t • planeOfCircle θ‖ ^ 2 ≤ 2 := by
    rw [hn]
    nlinarith [loopBallArcImageRadius_pos t, loopBallArcImageRadius_le t]
  change sphereFirst (loopBallAnnulus (θ, t)) ≠ 0
  rw [loopBallAnnulus_model]
  have hf := sphereFirst_modelSphere.{0} 1
    (p := (loopBallArcImageRadius t • planeOfCircle θ, -loopBallArcHeight t)) hs
  rw [hf, modelFirst]
  apply smul_ne_zero (by positivity)
  rw [← modelPlaneComplex.map_zero]
  apply modelPlaneComplex.injective.ne
  apply smul_ne_zero (loopBallArcImageRadius_pos t).ne'
  exact norm_ne_zero_iff.mp (by rw [arcPlane_norm]; norm_num)

def loopBallArcBase (t : Set.Icc (0 : ℝ) 1) : loopCircleBase :=
  loopCircleProjection ⟨loopBallAnnulus (1, t), loopBallAnnulus_domain 1 t⟩

theorem loopBallAnnulus_orbit_inverse (θ : Circle) (t : Set.Icc (0 : ℝ) 1) :
    loopCircleCoordinates.symm (loopBallAnnulus (θ, t)) = ((loopBallArcBase t).val, θ) := by
  have hn (θ' : Circle) : ‖loopBallArcImageRadius t • planeOfCircle θ'‖ =
      loopBallArcImageRadius t := by
    rw [norm_smul, Real.norm_of_nonneg (loopBallArcImageRadius_pos t).le,
      arcPlane_norm, mul_one]
  have hs (θ' : Circle) : ‖loopBallArcImageRadius t • planeOfCircle θ'‖ ^ 2 ≤ 2 := by
    rw [hn]
    nlinarith [loopBallArcImageRadius_pos t, loopBallArcImageRadius_le t]
  rw [loopCircleCoordinates_inverse]
  apply Prod.ext
  · change modelPlaneComplex.symm (sphereSecond (loopBallAnnulus (θ, t))) =
      (loopBallArcBase t).val
    change modelPlaneComplex.symm (sphereSecond (loopBallAnnulus (θ, t))) =
      (loopCircleProjection ⟨loopBallAnnulus (1, t), loopBallAnnulus_domain 1 t⟩).val
    rw [loopCircleProjection_val]
    change modelPlaneComplex.symm (sphereSecond (loopBallAnnulus (θ, t))) =
      modelPlaneComplex.symm (sphereSecond (loopBallAnnulus (1, t)))
    rw [loopBallAnnulus_model θ t, loopBallAnnulus_model 1 t]
    have hfθ := sphereSecond_modelSphere.{0} 1
      (p := (loopBallArcImageRadius t • planeOfCircle θ, -loopBallArcHeight t)) (hs θ)
    have hf1 := sphereSecond_modelSphere.{0} 1
      (p := (loopBallArcImageRadius t • planeOfCircle 1, -loopBallArcHeight t)) (hs 1)
    rw [hfθ, hf1]
    simp only [modelSecond, hn]
  · change unitOf (sphereFirst (loopBallAnnulus (θ, t))) = θ
    rw [loopBallAnnulus_model]
    have hf := sphereFirst_modelSphere.{0} 1
      (p := (loopBallArcImageRadius t • planeOfCircle θ, -loopBallArcHeight t)) (hs θ)
    rw [hf, modelFirst, map_smul, arcPlaneComplex, smul_smul]
    have hk : 0 < (Real.sqrt (2 : ℝ))⁻¹ := by positivity
    exact unitOf_smul (mul_pos hk (loopBallArcImageRadius_pos t)) θ

theorem loopBallAnnulus_projection (θ : Circle) (t : Set.Icc (0 : ℝ) 1) :
    loopCircleProjection ⟨loopBallAnnulus (θ, t), loopBallAnnulus_domain θ t⟩ =
      loopBallArcBase t := by
  apply Subtype.ext
  change (loopCircleCoordinates.symm (loopBallAnnulus (θ, t))).1 = (loopBallArcBase t).val
  rw [loopBallAnnulus_orbit_inverse]

theorem loopBallAnnulus_fibre (t : Set.Icc (0 : ℝ) 1) :
    loopBallAnnulus '' (Set.univ ×ˢ {t}) = loopCircleLift {loopBallArcBase t} := by
  rw [loopCircleLift, loopCircleProjection_fibre]
  ext p
  constructor
  · rintro ⟨⟨θ, s⟩, hs, rfl⟩
    have ht : s = t := hs.2
    subst s
    refine ⟨((loopBallArcBase t).val, θ), ⟨rfl, trivial⟩, ?_⟩
    exact (congrArg loopCircleCoordinates (loopBallAnnulus_orbit_inverse θ t)).symm.trans
      (loopCircleCoordinates.right_inv (loopBallAnnulus_domain θ t))
  · rintro ⟨⟨z, θ⟩, hz, rfl⟩
    have he : z = (loopBallArcBase t).val := hz.1
    subst z
    refine ⟨(θ, t), ⟨trivial, rfl⟩, ?_⟩
    exact (loopCircleCoordinates.right_inv (loopBallAnnulus_domain θ t)).symm.trans
      (congrArg loopCircleCoordinates (loopBallAnnulus_orbit_inverse θ t))

end GC.GraphManifold.Assembly
