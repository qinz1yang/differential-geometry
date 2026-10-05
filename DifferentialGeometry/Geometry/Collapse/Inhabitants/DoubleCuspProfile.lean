import DifferentialGeometry.Geometry.Collapse.Inhabitants.CuspTruncation
import DifferentialGeometry.Analysis.Calculus.Cutoff.IntervalProfiles

/-!
A fixed smooth height profile has two exact inward exponential ends. Its positive warped
metric pulls back to the original compact annulus circle carrier at physical height 240.
-/

set_option autoImplicit false

noncomputable section

open Set Function DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Manifold.Interval
open GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

def doubleCuspLogProfile (r : ℝ) : ℝ :=
  -r / 2 + (r - 120) * (1 - Analysis.descendingIntervalProfile 119 121 r)

theorem doubleCuspLogProfile_smooth : ContDiff ℝ ∞ doubleCuspLogProfile :=
  (contDiff_id.neg.div_const 2).add ((contDiff_id.sub contDiff_const).mul
    (contDiff_const.sub (Analysis.contDiff_descendingIntervalProfile 119 121)))

theorem doubleCuspLogProfile_left {r : ℝ} (hr : r ≤ 119) :
    doubleCuspLogProfile r = -r / 2 := by
  rw [doubleCuspLogProfile, Analysis.descendingIntervalProfile_one (by norm_num) hr]
  ring

theorem doubleCuspLogProfile_right {r : ℝ} (hr : 121 ≤ r) :
    doubleCuspLogProfile r = -(240 - r) / 2 := by
  rw [doubleCuspLogProfile, Analysis.descendingIntervalProfile_zero (by norm_num) hr]
  ring

def doubleCuspWarp (a r : ℝ) : ℝ := a * Real.exp (doubleCuspLogProfile r)

theorem doubleCuspWarp_smooth (a : ℝ) : ContDiff ℝ ∞ (doubleCuspWarp a) :=
  contDiff_const.mul (Real.contDiff_exp.comp doubleCuspLogProfile_smooth)

theorem doubleCuspWarp_pos {a : ℝ} (ha : 0 < a) (r : ℝ) : 0 < doubleCuspWarp a r :=
  mul_pos ha (Real.exp_pos (doubleCuspLogProfile r))

def doubleCuspRealMetric (a : ℝ) (ha : 0 < a) :
    SmoothRiemannianMetric (𝓘(ℝ, ℝ).prod torusModel) (ℝ × Torus) :=
  (DifferentialGeometry.euclideanMetric (E := ℝ)).warpedProduct standardCuspTorusMetric
    (doubleCuspWarp a) (doubleCuspWarp_smooth a).contMDiff (doubleCuspWarp_pos ha)

def doubleCuspHeight (r : unitInterval) : ℝ := 240 * r.val

theorem doubleCuspHeight_smooth : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ doubleCuspHeight :=
  contMDiff_const.mul contMDiff_subtypeVal_Icc

theorem doubleCuspHeight_derivative (r : unitInterval) :
    mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) doubleCuspHeight r =
      (240 : ℝ) • mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : unitInterval → ℝ) r :=
  (((contMDiff_subtypeVal_Icc (n := ∞)).mdifferentiableAt
    (by simp)).hasMFDerivAt.const_smul (240 : ℝ)).mfderiv

theorem doubleCuspHeight_immersion (r : unitInterval) :
    Injective (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) doubleCuspHeight r) := by
  rw [doubleCuspHeight_derivative]
  intro v w h
  apply (tangentCoordinateIcc r).injective
  rw [tangentCoordinateIcc_apply, tangentCoordinateIcc_apply]
  apply congrArg (NormedSpace.fromTangentSpace (r : ℝ))
  exact (smul_right_injective _ (by norm_num : (240 : ℝ) ≠ 0)) h

def doubleCuspCylinderCoordinate (p : Torus × unitInterval) : ℝ × Torus :=
  (doubleCuspHeight p.2, p.1)

theorem doubleCuspCylinderCoordinate_smooth :
    ContMDiff torusMonodromyCylinderModel (𝓘(ℝ, ℝ).prod torusModel) ∞
      doubleCuspCylinderCoordinate :=
  (doubleCuspHeight_smooth.comp contMDiff_snd).prodMk contMDiff_fst

theorem doubleCuspCylinderCoordinate_immersion (p : Torus × unitInterval) :
    Injective (mfderiv torusMonodromyCylinderModel (𝓘(ℝ, ℝ).prod torusModel)
      doubleCuspCylinderCoordinate p) := by
  rw [show doubleCuspCylinderCoordinate =
    (fun p : Torus × unitInterval => (doubleCuspHeight p.2, p.1)) from rfl]
  have hd := mfderiv_prodMk (I := torusMonodromyCylinderModel)
    ((doubleCuspHeight_smooth.comp contMDiff_snd).mdifferentiableAt (by simp))
    ((contMDiff_fst (n := ∞)).mdifferentiableAt (by simp)) (x := p)
  change mfderiv torusMonodromyCylinderModel (𝓘(ℝ, ℝ).prod torusModel)
    (fun p : Torus × unitInterval => (doubleCuspHeight p.2, p.1)) p = _ at hd
  rw [hd]
  rw [mfderiv_comp p (doubleCuspHeight_smooth.mdifferentiableAt (by simp))
    mdifferentiableAt_snd, mfderiv_snd, mfderiv_fst]
  intro v w h
  exact Prod.ext (congrArg Prod.snd h)
    (doubleCuspHeight_immersion p.2 (congrArg Prod.fst h))

def doubleCuspCoordinate : (productSet.{u} 2) → ℝ × Torus :=
  doubleCuspCylinderCoordinate ∘ torusMonodromyPolarDiffeomorph.{u}

theorem doubleCuspCoordinate_smooth :
    ContMDiff (𝓡∂ 3) (𝓘(ℝ, ℝ).prod torusModel) ∞ doubleCuspCoordinate.{u} :=
  doubleCuspCylinderCoordinate_smooth.comp torusMonodromyPolarDiffeomorph.{u}.contMDiff

theorem doubleCuspCoordinate_immersion (p : (productSet.{u} 2)) :
    Injective (mfderiv (𝓡∂ 3) (𝓘(ℝ, ℝ).prod torusModel) doubleCuspCoordinate.{u} p) := by
  rw [doubleCuspCoordinate, mfderiv_comp p
    (doubleCuspCylinderCoordinate_smooth.mdifferentiableAt (by simp))
    (torusMonodromyPolarDiffeomorph.{u}.contMDiff.mdifferentiableAt (by simp))]
  apply (doubleCuspCylinderCoordinate_immersion _).comp
  rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe
    torusMonodromyPolarDiffeomorph.{u} (by simp)]
  exact (torusMonodromyPolarDiffeomorph.{u}.mfderivToContinuousLinearEquiv
    (by simp) p).injective

def doubleCuspMetric (a : ℝ) (ha : 0 < a) :
    SmoothRiemannianMetric (𝓡∂ 3) (productSet.{u} 2) :=
  (doubleCuspRealMetric a ha).pullback doubleCuspCoordinate.{u}
    doubleCuspCoordinate_smooth.{u} doubleCuspCoordinate_immersion.{u}

end DifferentialGeometry.Geometry.Collapse
