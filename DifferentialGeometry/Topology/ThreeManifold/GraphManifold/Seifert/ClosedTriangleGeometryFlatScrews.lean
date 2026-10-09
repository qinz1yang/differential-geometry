import DifferentialGeometry.Geometry.Thurston.ScrewLift

/-!
# Screws and fibre translations of the flat connection models in plane coordinates

Lane B3 (design `docs/geometrization/handoffs/20261004-design-b3-closed-triangle-assembly.md`,
§2.1). For the two connection models with flat base (`E³` and `Nil`, connection curvature `c`),
X14's recentering is affine, `recentre v x = x + v + (0, 0, -c (v × x)/2)` with
`v × x = v₀ x₁ - v₁ x₀` (`recentre_flat_apply`), so the clockwise screw about the fibre over `v`
is, in the plane coordinate `z = x₀ + i x₁`, `z ↦ v + e^{-2πi/p} (z - v)` with fibre component
`t ↦ t - ℓ q/p - c (v × (e^{-2πi/p} (z - v) - (z - v)))/2` (`planeOf_screwAt_flat`,
`screwAt_flat_two`). Fibre translations are isometries of every cone profile
(`fibreTranslation_isometry`) and act by `t ↦ t + s` (`fibreTranslation_apply'`).
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry
open scoped Manifold ContDiff

namespace GC.Geometry

def planeCrossC (v w : ℂ) : ℝ := v.re * w.im - v.im * w.re

theorem screwDiffeomorph_apply' (θ s : ℝ) (x : ModelCoordinates) :
    screwDiffeomorph θ s x = planeRotation θ x + fibreShift s := by
  change (⟨1⟩ : ScrewGroup θ s) • x = _
  rw [ScrewGroup.smul_def]
  simp [ScrewGroup.linearPart, ScrewGroup.translationPart]

theorem fibreTranslation_apply' (s : ℝ) (x : ModelCoordinates) :
    fibreTranslation s x = x + fibreShift s := by
  change screwDiffeomorph 0 s x = _
  rw [screwDiffeomorph_apply']
  congr 1
  ext i
  fin_cases i <;> simp

theorem screwDiffeomorph_isometry' (P : RadialProfile) (θ s : ℝ) :
    Diffeomorph.pullbackMetric P.metric (screwDiffeomorph θ s) = P.metric := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hfun : (screwDiffeomorph θ s : ModelCoordinates → ModelCoordinates) =
      fun y => planeRotation θ y + fibreShift s :=
    funext (screwDiffeomorph_apply' θ s)
  have hder : mfderiv (𝓡 3) (𝓡 3) (screwDiffeomorph θ s) x =
      (planeRotation θ : ModelCoordinates →L[ℝ] ModelCoordinates) := by
    rw [mfderiv_eq_fderiv, hfun]
    exact ((planeRotation θ).toContinuousLinearEquiv.hasFDerivAt.add_const _).fderiv
  rw [Diffeomorph.pullbackMetric_inner, hder, hfun]
  exact P.inner_rotation θ s x v w

theorem fibreTranslation_isometry (m : ConnectionModel) (s : ℝ) :
    Diffeomorph.pullbackMetric m.coneProfile.metric (fibreTranslation s) =
      m.coneProfile.metric :=
  screwDiffeomorph_isometry' _ 0 s

theorem recentre_flat_apply (m : ConnectionModel) (hm : m.baseCurvature ≤ 0)
    (hflat : m.baseCurvature = 0) (v x : ModelCoordinates) :
    recentre m hm v x =
      x + v + fibreShift (-m.connectionCurvature * (v 0 * x 1 - v 1 * x 0) / 2) ∧
    (recentre m hm v).symm x =
      x - v - fibreShift (-m.connectionCurvature * (v 0 * x 1 - v 1 * x 0) / 2) := by
  cases m
  · constructor
    · change shearMap 0 (shearMap (-0) x + (shearMap (-0) v - shearMap (-0) 0)) = _
      ext i; fin_cases i <;> simp [shearMap, ConnectionModel.connectionCurvature]
    · change shearMap 0 (shearMap (-0) x - (shearMap (-0) v - shearMap (-0) 0)) = _
      ext i; fin_cases i <;> simp [shearMap, ConnectionModel.connectionCurvature]
  · norm_num [ConnectionModel.baseCurvature] at hflat
  · norm_num [ConnectionModel.baseCurvature] at hflat
  · constructor
    · change shearMap 1 (coordinateShift .nil (shearMap (-1) 0) (shearMap (-1) v)
        (shearMap (-1) x)) = _
      ext i; fin_cases i <;>
        simp [shearMap, coordinateShift, coordinateShiftLinear,
          ConnectionModel.connectionCurvature] <;> ring
    · change shearMap 1 (coordinateShift .nil (shearMap (-1) v) (shearMap (-1) 0)
        (shearMap (-1) x)) = _
      ext i; fin_cases i <;>
        simp [shearMap, coordinateShift, coordinateShiftLinear,
          ConnectionModel.connectionCurvature]
      ring
  · norm_num [ConnectionModel.baseCurvature] at hflat
  · norm_num [ConnectionModel.baseCurvature] at hflat

theorem screwAt_flat_apply (m : ConnectionModel) (hm : m.baseCurvature ≤ 0)
    (hflat : m.baseCurvature = 0) (v : ModelCoordinates) (p : ℕ+) (q : ℤ) (ℓ : ℝ)
    (x : ModelCoordinates) :
    screwAt m hm v p q ℓ x =
      !₂[v 0 + Real.cos (-2 * Real.pi / p) * (x 0 - v 0) -
          Real.sin (-2 * Real.pi / p) * (x 1 - v 1),
        v 1 + Real.sin (-2 * Real.pi / p) * (x 0 - v 0) + Real.cos (-2 * Real.pi / p) * (x 1 - v 1),
        x 2 + -ℓ * q / p - m.connectionCurvature *
          (v 0 * (Real.sin (-2 * Real.pi / p) * (x 0 - v 0) +
              Real.cos (-2 * Real.pi / p) * (x 1 - v 1) - (x 1 - v 1)) -
            v 1 * (Real.cos (-2 * Real.pi / p) * (x 0 - v 0) -
              Real.sin (-2 * Real.pi / p) * (x 1 - v 1) - (x 0 - v 0))) / 2] := by
  change recentre m hm v (screwDiffeomorph (-2 * Real.pi / p) (-ℓ * q / p)
    ((recentre m hm v).symm x)) = _
  rw [(recentre_flat_apply m hm hflat v x).2, screwDiffeomorph_apply',
    (recentre_flat_apply m hm hflat v _).1]
  ext i
  fin_cases i <;> simp [fibreShift] <;> ring

theorem planeOf_screwAt_flat (m : ConnectionModel) (hm : m.baseCurvature ≤ 0)
    (hflat : m.baseCurvature = 0) (v : ModelCoordinates) (p : ℕ+) (q : ℤ) (ℓ : ℝ)
    (x : ModelCoordinates) :
    planeOf (screwAt m hm v p q ℓ x) =
      planeOf v + (Circle.exp (-2 * Real.pi / p) : ℂ) * (planeOf x - planeOf v) := by
  have hre : (Circle.exp (-2 * Real.pi / p) : ℂ).re = Real.cos (-2 * Real.pi / p) := by
    rw [Circle.coe_exp]; exact Complex.exp_ofReal_mul_I_re _
  have him : (Circle.exp (-2 * Real.pi / p) : ℂ).im = Real.sin (-2 * Real.pi / p) := by
    rw [Circle.coe_exp]; exact Complex.exp_ofReal_mul_I_im _
  rw [screwAt_flat_apply m hm hflat]
  apply Complex.ext <;>
    simp only [planeOf_re, planeOf_im, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.sub_re, Complex.sub_im, hre, him] <;> simp <;> ring

theorem screwAt_flat_two (m : ConnectionModel) (hm : m.baseCurvature ≤ 0)
    (hflat : m.baseCurvature = 0) (v : ModelCoordinates) (p : ℕ+) (q : ℤ) (ℓ : ℝ)
    (x : ModelCoordinates) :
    screwAt m hm v p q ℓ x 2 =
      x 2 - ℓ * q / p - m.connectionCurvature *
        planeCrossC (planeOf v) ((Circle.exp (-2 * Real.pi / p) : ℂ) * (planeOf x - planeOf v) -
          (planeOf x - planeOf v)) / 2 := by
  have hre : (Circle.exp (-2 * Real.pi / p) : ℂ).re = Real.cos (-2 * Real.pi / p) := by
    rw [Circle.coe_exp]; exact Complex.exp_ofReal_mul_I_re _
  have him : (Circle.exp (-2 * Real.pi / p) : ℂ).im = Real.sin (-2 * Real.pi / p) := by
    rw [Circle.coe_exp]; exact Complex.exp_ofReal_mul_I_im _
  rw [screwAt_flat_apply m hm hflat]
  simp only [planeCrossC, planeOf_re, planeOf_im, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, hre, him]
  simp
  ring

theorem planeOf_fibreTranslation (s : ℝ) (x : ModelCoordinates) :
    planeOf (fibreTranslation s x) = planeOf x := by
  rw [fibreTranslation_apply', planeOf_add_fibreShift]

theorem fibreTranslation_two (s : ℝ) (x : ModelCoordinates) :
    fibreTranslation s x 2 = x 2 + s := by
  rw [fibreTranslation_apply']
  simp [fibreShift]

end GC.Geometry
