import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopBallFace

/-!
The actual original ball sphere contains a genuine full-circle latitude annulus.
The native coordinate inverse constructs each point and proves continuous injective parametrization.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

private local instance latitudeBallCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

private local instance latitudeBallSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

private def latitudeHeight (t : Set.Icc (0 : ℝ) 1) : ℝ := -3 / 5 + (6 / 5) * t.val

private theorem latitudeHeight_bounds (t : Set.Icc (0 : ℝ) 1) :
    -3 / 5 ≤ latitudeHeight t ∧ latitudeHeight t ≤ 3 / 5 := by
  have ht := t.property
  unfold latitudeHeight
  constructor <;> linarith [ht.1, ht.2]

private def latitudeRadius (t : Set.Icc (0 : ℝ) 1) : ℝ :=
  Real.sqrt (1 - latitudeHeight t ^ 2)

private theorem latitudeRadius_pos (t : Set.Icc (0 : ℝ) 1) : 0 < latitudeRadius t := by
  apply Real.sqrt_pos.mpr
  have ht := latitudeHeight_bounds t
  nlinarith [sq_nonneg (latitudeHeight t + 3 / 5), sq_nonneg (latitudeHeight t - 3 / 5)]

private theorem latitudeRadius_sq (t : Set.Icc (0 : ℝ) 1) :
    latitudeRadius t ^ 2 = 1 - latitudeHeight t ^ 2 := by
  apply Real.sq_sqrt
  have ht := latitudeHeight_bounds t
  nlinarith [sq_nonneg (latitudeHeight t + 3 / 5), sq_nonneg (latitudeHeight t - 3 / 5)]

def loopBallCoordinates : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] ModelSpace :=
  (ballCoord.toLinearMap.linearEquivOfInjective ballCoord_injective
    (by simp)).toContinuousLinearEquiv

theorem loopBallCoordinates_norm (x : EuclideanSpace ℝ (Fin 3)) :
    ‖(loopBallCoordinates x).1‖ ^ 2 + (loopBallCoordinates x).2 ^ 2 = ‖x‖ ^ 2 :=
  norm_sq_ballCoord x

def loopBallLatitudePoint (θ : Circle) (t : Set.Icc (0 : ℝ) 1) : ClosedCell 3 :=
  ⟨loopBallCoordinates.symm (latitudeRadius t • planeOfCircle θ, latitudeHeight t), by
    have hn := loopBallCoordinates_norm
      (loopBallCoordinates.symm (latitudeRadius t • planeOfCircle θ, latitudeHeight t))
    rw [loopBallCoordinates.apply_symm_apply] at hn
    dsimp only [Prod.fst, Prod.snd] at hn
    have hθ : ‖planeOfCircle θ‖ = 1 := by
      rw [planeOfCircle, LinearIsometryEquiv.norm_map, Circle.norm_coe]
    rw [norm_smul, Real.norm_of_nonneg (latitudeRadius_pos t).le, hθ,
      mul_one, latitudeRadius_sq] at hn
    have hr := norm_nonneg
      (loopBallCoordinates.symm (latitudeRadius t • planeOfCircle θ, latitudeHeight t))
    nlinarith⟩

theorem loopBallLatitudePoint_coordinates (θ : Circle) (t : Set.Icc (0 : ℝ) 1) :
    loopBallCoordinates (loopBallLatitudePoint θ t).val =
      (latitudeRadius t • planeOfCircle θ, latitudeHeight t) :=
  loopBallCoordinates.apply_symm_apply _

theorem loopBallLatitudePoint_norm (θ : Circle) (t : Set.Icc (0 : ℝ) 1) :
    ‖(loopBallLatitudePoint θ t).val‖ = 1 := by
  have hn := loopBallCoordinates_norm (loopBallLatitudePoint θ t).val
  rw [loopBallLatitudePoint_coordinates] at hn
  dsimp only [Prod.fst, Prod.snd] at hn
  have hθ : ‖planeOfCircle θ‖ = 1 := by
    rw [planeOfCircle, LinearIsometryEquiv.norm_map, Circle.norm_coe]
  rw [norm_smul, Real.norm_of_nonneg (latitudeRadius_pos t).le, hθ,
    mul_one, latitudeRadius_sq] at hn
  nlinarith [norm_nonneg (loopBallLatitudePoint θ t).val]

theorem loopBallLatitudePoint_continuous : Continuous
    (fun q : Circle × Set.Icc (0 : ℝ) 1 => loopBallLatitudePoint q.1 q.2) := by
  have hh : Continuous latitudeHeight := continuous_const.add
    (continuous_const.mul continuous_subtype_val)
  have hr : Continuous latitudeRadius := Real.continuous_sqrt.comp
    (continuous_const.sub (hh.pow 2))
  have hc : Continuous planeOfCircle :=
    Complex.orthonormalBasisOneI.repr.continuous.comp contMDiff_circle_coe.continuous
  apply Continuous.subtype_mk
  exact loopBallCoordinates.symm.continuous.comp
    (((hr.comp continuous_snd).smul (hc.comp continuous_fst)).prodMk
      (hh.comp continuous_snd))

def loopBallAnnulus (q : Circle × Set.Icc (0 : ℝ) 1) : SphereCarrier.{0} :=
  (standardLoopBallHandleCycle.ball ⟨0, standardLoopBallHandleCycle.len_pos⟩).map
    ((standardLoopBallHandleCycle.ballModel ⟨0, standardLoopBallHandleCycle.len_pos⟩).symm
      (loopBallLatitudePoint q.1 q.2))

theorem loopBallAnnulus_continuous : Continuous loopBallAnnulus :=
  ((standardLoopBallHandleCycle.ball _).continuous_map.comp
    (standardLoopBallHandleCycle.ballModel _).symm.continuous).comp
      loopBallLatitudePoint_continuous

theorem loopBallAnnulus_injective : Function.Injective loopBallAnnulus := by
  rintro ⟨θ, t⟩ ⟨θ', t'⟩ he
  have hx := (standardLoopBallHandleCycle.ballModel
    ⟨0, standardLoopBallHandleCycle.len_pos⟩).symm.injective
      ((standardLoopBallHandleCycle.ball _).injective he)
  have hc := congrArg (fun x : ClosedCell 3 => loopBallCoordinates x.val) hx
  rw [loopBallLatitudePoint_coordinates, loopBallLatitudePoint_coordinates] at hc
  have ht := congrArg Prod.snd hc
  dsimp only [Prod.snd] at ht
  have htv : t.val = t'.val := by unfold latitudeHeight at ht; linarith
  have hti : t = t' := Subtype.ext htv
  subst t'
  have hw := congrArg Prod.fst hc
  dsimp only [Prod.fst] at hw
  have hθ : θ = θ' := by
    apply Circle.ext
    apply Complex.orthonormalBasisOneI.repr.injective
    exact smul_right_injective _ (latitudeRadius_pos t).ne' hw
  subst θ'
  rfl

theorem loopBallAnnulus_face : Set.range loopBallAnnulus ⊆ loopBallWholeFace := by
  rintro p ⟨q, rfl⟩
  refine ⟨(standardLoopBallHandleCycle.ballModel
    ⟨0, standardLoopBallHandleCycle.len_pos⟩).symm (loopBallLatitudePoint q.1 q.2), ?_, rfl⟩
  rw [← (standardLoopBallHandleCycle.ballModel
    ⟨0, standardLoopBallHandleCycle.len_pos⟩).preimage_boundary (by simp)]
  change (standardLoopBallHandleCycle.ballModel
    ⟨0, standardLoopBallHandleCycle.len_pos⟩)
    ((standardLoopBallHandleCycle.ballModel
      ⟨0, standardLoopBallHandleCycle.len_pos⟩).symm (loopBallLatitudePoint q.1 q.2)) ∈
    (𝓡∂ 3).boundary (ClosedCell 3)
  rw [Diffeomorph.apply_symm_apply,
    DifferentialGeometry.Topology.Manifold.closedCell_boundary_eq_sphere 2]
  exact loopBallLatitudePoint_norm q.1 q.2

end GC.GraphManifold.Assembly
