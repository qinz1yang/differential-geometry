import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkerModelMasses
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticShrinkerNormalization
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (ThreeSpace)

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

set_option backward.isDefEq.respectTransparency false in
private theorem scalarOneShrinkingCylinderMetric_zero_eq_roundShrinker :
    scalarOneShrinkingCylinderMetric 0 (by norm_num) = roundThreeCylinderShrinkerMetric := by
  apply SmoothRiemannianMetric.ext_inner
  rintro ⟨y, z⟩ ⟨v, a⟩ ⟨w, b⟩
  rw [scalarOneShrinkingCylinderMetric_inner]
  simp [roundThreeCylinderShrinkerMetric, roundTwoSphereShrinkerMetric,
    roundSphereShrinkerMetric, SmoothRiemannianMetric.prod_inner,
    scaleMetric_inner, euclideanMetric_inner, mul_comm]

theorem normalizedShrinkerMass_eq_of_ordinary_cylinder
    (P : PointedRiemannianManifold (𝓡 3)) (g : SmoothRiemannianMetric (𝓡 3) P.M)
    (f : C^∞⟮(𝓡 3), P.M; ℝ⟯)
    (d : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, (𝓡 3)⟯ P.M)
    (hmetric : Diffeomorph.pullbackMetricCross g d = scalarOneShrinkingCylinderMetric 0 (by norm_num))
    (hpotential : ∀ z : SpatialNeckCylinder, f (d z) = 1 + z.2 ^ 2 / 4) :
    normalizedShrinkerMass g f = ENNReal.ofReal (2 * Real.exp (-1)) := by
  rw [normalizedShrinkerMass_pullbackMetricCross (L := P) (by simp) g f d,
    hmetric, scalarOneShrinkingCylinderMetric_zero_eq_roundShrinker]
  convert normalizedShrinkerMass_roundThreeCylinderShrinker using 2
  funext z
  simpa only [roundThreeCylinderShrinkerPotential_apply] using hpotential z

theorem one_half_lt_asymptoticReducedVolume_of_ordinary_cylinder
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold (𝓡 3) ∞ M] [T2Space M] [SigmaCompactSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := (𝓡 3)) (M := M) D) (b : ℝ) (p : M)
    (P : PointedRiemannianManifold (𝓡 3)) (g : SmoothRiemannianMetric (𝓡 3) P.M)
    (f : C^∞⟮(𝓡 3), P.M; ℝ⟯)
    (d : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, (𝓡 3)⟯ P.M)
    (hmetric : Diffeomorph.pullbackMetricCross g d = scalarOneShrinkingCylinderMetric 0 (by norm_num))
    (hpotential : ∀ z : SpatialNeckCylinder, f (d z) = 1 + z.2 ^ 2 / 4)
    (hmass : normalizedShrinkerMass g f = asymptoticReducedVolume S b p) :
    (1 / 2 : ℝ≥0∞) < asymptoticReducedVolume S b p := by
  rw [← hmass, normalizedShrinkerMass_eq_of_ordinary_cylinder P g f d hmetric hpotential]
  have h : (1 / 2 : ℝ) < 2 * Real.exp (-1) := by
    rw [Real.exp_neg]
    have he : 0 < Real.exp (1 : ℝ) := Real.exp_pos 1
    have hinv : (1 / 4 : ℝ) < (Real.exp 1)⁻¹ := by
      have hh := one_div_lt_one_div_of_lt (show (0 : ℝ) < Real.exp 1 from he)
        (show Real.exp 1 < 4 from Real.exp_one_lt_three.trans (by norm_num))
      simpa only [one_div] using hh
    linarith
  have ho := ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 2 * Real.exp (-1)) |>.2 h
  norm_num only [ENNReal.ofReal_div_of_pos, ENNReal.ofReal_one, ENNReal.ofReal_ofNat] at ho
  exact ho

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
