import DifferentialGeometry.Geometry.Metric.Sphere.Round.GreatCircle
import DifferentialGeometry.Topology.ProjectiveSpace.CylinderQuotientSmoothModels
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Set Metric Module
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology RealInnerProductSpace

local notation "V" => EuclideanSpace ℝ (Fin 3)
local notation "S" => Metric.sphere (0 : V) 1
local notation "T" => EuclideanSpace ℝ (Fin 2)

private local instance halfTurnDimension : Fact (Module.finrank ℝ V = 2 + 1) := ⟨by simp⟩

private def axis (i : Fin 3) : V := EuclideanSpace.basisFun (Fin 3) ℝ i

private theorem axis_norm (i : Fin 3) : ‖axis i‖ = 1 :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.norm_eq_one i

private theorem axis_inner {i j : Fin 3} (h : i ≠ j) : ⟪axis i, axis j⟫ = 0 :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.inner_eq_zero h

private def equatorStart : S := ⟨axis 0, by
  rw [mem_sphere_zero_iff_norm]
  exact axis_norm 0⟩

def sphereEquator : ℝ → S :=
  greatCircle equatorStart (axis 1) (axis_norm 1) (axis_inner (by decide))

theorem sphereEquator_smooth : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ sphereEquator :=
  greatCircle_smooth equatorStart (axis 1) (axis_norm 1) (axis_inner (by decide))

theorem sphereEquator_pi : sphereEquator Real.pi = -sphereEquator 0 := by
  apply Subtype.ext
  simp [sphereEquator, greatCircle_val, equatorStart]

private def equatorVelocity (t : ℝ) : TangentSpace (𝓡 2) (sphereEquator t) :=
  mfderiv 𝓘(ℝ, ℝ) (𝓡 2) sphereEquator t (constantModelVectorField (𝕜 := ℝ) 1 t)

private def heightGradient (x : S) : TangentSpace (𝓡 2) x :=
  gradFun (I := 𝓡 2) (roundMetric (E := V) (n := 2))
    (innerCoordFun (E := V) (n := 2) (axis 2)) x

private theorem equatorVelocity_ambient (t : ℝ) :
    dIncl (n := 2) (sphereEquator t) (equatorVelocity t) =
      -Real.sin t • axis 0 + Real.cos t • axis 1 :=
  greatCircle_velocity equatorStart (axis 1) (axis_norm 1) (axis_inner (by decide)) t

private theorem heightGradient_ambient_of_orthogonal (x : S)
    (hx : ⟪(x : V), axis 2⟫ = 0) :
    dIncl (n := 2) x (heightGradient x) = axis 2 := by
  have hrange : axis 2 ∈ (mvfderiv (𝓡 2) (Subtype.val : S → V) x).range := by
    rw [range_mvfderiv_subtypeVal]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hx
  obtain ⟨v, hv⟩ := hrange
  have hgrad : v = heightGradient x := by
    apply gradFun_unique
    intro w
    rw [roundMetric_inner, mfderiv_innerCoordFun]
    change ⟪dIncl (n := 2) x v, dIncl (n := 2) x w⟫ = ⟪axis 2, dIncl (n := 2) x w⟫
    exact congrArg (fun u : V => ⟪u, dIncl (n := 2) x w⟫) hv
  rw [← hgrad]
  exact hv

private theorem heightGradient_ambient (t : ℝ) :
    dIncl (n := 2) (sphereEquator t) (heightGradient (sphereEquator t)) = axis 2 := by
  apply heightGradient_ambient_of_orthogonal
  change ⟪Real.cos t • axis 0 + Real.sin t • axis 1, axis 2⟫ = 0
  simp only [inner_add_left, real_inner_smul_left,
    axis_inner (i := 0) (j := 2) (by decide),
    axis_inner (i := 1) (j := 2) (by decide), mul_zero, add_zero]

private theorem equatorVelocity_ne_zero (t : ℝ) : equatorVelocity t ≠ 0 := by
  intro h
  have hs := greatCircle_speed (n := 2) equatorStart (axis 1)
    (axis_norm 1) (axis_inner (by decide)) t
  change (roundMetric (E := V) (n := 2)).inner (sphereEquator t)
    (equatorVelocity t) (equatorVelocity t) = 1 at hs
  simp [h] at hs

private theorem equatorFrame_independent (t : ℝ) :
    LinearIndependent ℝ ![equatorVelocity t, heightGradient (sphereEquator t)] := by
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have ha := congrArg (dIncl (n := 2) (sphereEquator t)) h
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, heightGradient_ambient, map_zero] at ha
    have hn := axis_norm 2
    rw [ha, norm_zero] at hn
    norm_num at hn
  · intro a h
    have ham := congrArg (dIncl (n := 2) (sphereEquator t)) h
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, map_smul,
      heightGradient_ambient, equatorVelocity_ambient] at ham
    have hi := congrArg (fun z : V => ⟪axis 2, z⟫) ham
    have ha : a = 0 := by
      simpa only [inner_add_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, axis_norm, one_pow,
        axis_inner (i := 2) (j := 0) (by decide),
        axis_inner (i := 2) (j := 1) (by decide), mul_one, mul_zero, add_zero] using hi
    apply equatorVelocity_ne_zero t
    simpa only [ha, zero_smul, Matrix.cons_val_zero] using h.symm

private theorem equatorVelocity_continuous :
    Continuous (fun t => TotalSpace.mk' T (E := TangentSpace (𝓡 2))
      (sphereEquator t) (equatorVelocity t)) := by
  have hconst : Continuous (fun t : ℝ => TotalSpace.mk' ℝ
      (E := TangentSpace 𝓘(ℝ, ℝ)) t (constantModelVectorField (𝕜 := ℝ) 1 t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    rw [FiberBundle.continuousAt_totalSpace]
    simp only [trivializationAt_model_space_apply]
    exact ⟨continuousAt_id, continuousAt_const⟩
  have hmap : Continuous (tangentMap 𝓘(ℝ, ℝ) (𝓡 2) sphereEquator) :=
    sphereEquator_smooth.continuous_tangentMap (by simp)
  simpa only [Function.comp_def, tangentMap, equatorVelocity] using hmap.comp hconst

private theorem heightGradient_equator_continuous :
    Continuous (fun t => TotalSpace.mk' T (E := TangentSpace (𝓡 2))
      (sphereEquator t) (heightGradient (sphereEquator t))) := by
  have hg : Continuous (fun x : S => TotalSpace.mk' T (E := TangentSpace (𝓡 2))
      x (heightGradient x)) :=
    (gradFun_contMDiff_total_section (I := 𝓡 2)
      (roundMetric (E := V) (n := 2))
      (innerCoordFun (E := V) (n := 2) (axis 2)).contMDiff).continuous
  exact hg.comp sphereEquator_smooth.continuous

def sphereHalfTurnBasis (t : ℝ) : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) (sphereEquator t)) :=
  basisOfLinearIndependentOfCardEqFinrank (equatorFrame_independent t) (by
    change Fintype.card (Fin 2) = Module.finrank ℝ T
    simp)

private theorem sphereHalfTurnBasis_zero (t : ℝ) :
    sphereHalfTurnBasis t 0 = equatorVelocity t := by
  simp only [sphereHalfTurnBasis, coe_basisOfLinearIndependentOfCardEqFinrank,
    Matrix.cons_val_zero]

private theorem sphereHalfTurnBasis_one (t : ℝ) :
    sphereHalfTurnBasis t 1 = heightGradient (sphereEquator t) := by
  simp only [sphereHalfTurnBasis, coe_basisOfLinearIndependentOfCardEqFinrank,
    Matrix.cons_val_one, Matrix.cons_val_zero]

theorem sphereHalfTurnBasis_continuous (i : Fin 2) :
    Continuous (fun t => TotalSpace.mk' T (E := TangentSpace (𝓡 2))
      (sphereEquator t) (sphereHalfTurnBasis t i)) := by
  fin_cases i
  · apply equatorVelocity_continuous.congr
    intro t
    exact congrArg (TotalSpace.mk' T (E := TangentSpace (𝓡 2)) (sphereEquator t))
      (sphereHalfTurnBasis_zero t).symm
  · apply heightGradient_equator_continuous.congr
    intro t
    exact congrArg (TotalSpace.mk' T (E := TangentSpace (𝓡 2)) (sphereEquator t))
      (sphereHalfTurnBasis_one t).symm

theorem dIncl_antipodal_derivative (x : S) (v : TangentSpace (𝓡 2) x) :
    dIncl (n := 2) (-x)
        (mfderiv (𝓡 2) (𝓡 2) sphereAntipodalDiffeomorph x v) =
      -dIncl (n := 2) x v := by
  have hc := mfderiv_comp_apply (x := x)
    ((contMDiff_coe_sphere (n := 2) (m := ∞)).mdifferentiableAt (by simp))
    (sphereAntipodalDiffeomorph.contMDiff.mdifferentiableAt (by simp)) v
  have hfun : (Subtype.val : S → V) ∘ sphereAntipodalDiffeomorph =
      -(Subtype.val : S → V) := rfl
  rw [hfun, mfderiv_neg] at hc
  exact hc.symm

theorem sphereHalfTurnBasis_pi_first :
    sphereHalfTurnBasis Real.pi 0 =
      mfderiv (𝓡 2) (𝓡 2) sphereAntipodalDiffeomorph (sphereEquator 0)
        (sphereHalfTurnBasis 0 0) := by
  apply injective_mvfderiv_subtypeVal_sphere (sphereEquator Real.pi)
  change dIncl (n := 2) (sphereEquator Real.pi) _ = dIncl (n := 2) (sphereEquator Real.pi) _
  rw [sphereHalfTurnBasis_zero, equatorVelocity_ambient]
  rw [sphereEquator_pi, dIncl_antipodal_derivative, sphereHalfTurnBasis_zero,
    equatorVelocity_ambient]
  simp

theorem sphereHalfTurnBasis_pi_second :
    sphereHalfTurnBasis Real.pi 1 =
      -(mfderiv (𝓡 2) (𝓡 2) sphereAntipodalDiffeomorph (sphereEquator 0)
        (sphereHalfTurnBasis 0 1)) := by
  apply injective_mvfderiv_subtypeVal_sphere (sphereEquator Real.pi)
  change dIncl (n := 2) (sphereEquator Real.pi) _ = dIncl (n := 2) (sphereEquator Real.pi) _
  rw [sphereHalfTurnBasis_one, heightGradient_ambient]
  rw [sphereEquator_pi]
  let v : TangentSpace (𝓡 2) (-sphereEquator 0) :=
    mfderiv (𝓡 2) (𝓡 2) sphereAntipodalDiffeomorph (sphereEquator 0) (sphereHalfTurnBasis 0 1)
  change axis 2 = dIncl (n := 2) (-sphereEquator 0) (-v)
  rw [map_neg]
  have hd := dIncl_antipodal_derivative (sphereEquator 0) (sphereHalfTurnBasis 0 1)
  change dIncl (n := 2) (-sphereEquator 0) v =
    -dIncl (n := 2) (sphereEquator 0) (sphereHalfTurnBasis 0 1) at hd
  rw [hd, sphereHalfTurnBasis_one, heightGradient_ambient, neg_neg]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
