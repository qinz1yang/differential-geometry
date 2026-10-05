import DifferentialGeometry.Geometry.Collapse.LocalExport.ZeroModelBall
import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.BufferedRadialFunctionAtScale
import DifferentialGeometry.Geometry.Measure.Area.ManifoldEuclidean
import DifferentialGeometry.Geometry.Metric.InnerProductRadialCone
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# A Euclidean inhabitant of the zero-model ball certificate

The unit-radius model uses the actual Euclidean metric and identity cone approximation.
The buffered radial function is the existing scaled LC30 and LC31 producer. Each model chart
is the smooth inverse of the standard whole-space-to-ball partial homeomorphism.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry Set Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local instance euclideanZero_modelMetric : (b : Unit) → MetricSpace (Function.const Unit E3 b) :=
  fun _b => inferInstanceAs (MetricSpace E3)

local instance euclideanZero_modelChart : (b : Unit) → ChartedSpace E3 (Function.const Unit E3 b) :=
  fun _b => inferInstanceAs (ChartedSpace E3 E3)

local instance euclideanZero_nonzero : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

private def euclideanZeroConeMap {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    @KleinerLottApprox E3 E3 ((inferInstance : MetricSpace E3).rescale (1 : ℝ)⁻¹
      (by norm_num)) inferInstance 0 0 δ := by
  refine @KleinerLottApprox.mk E3 E3
    ((inferInstance : MetricSpace E3).rescale (1 : ℝ)⁻¹ (by norm_num))
    (inferInstance : MetricSpace E3) 0 0 δ hδ hδ1 id rfl ?_ ?_
  · intro x _hx y _hy
    change |dist x y - (1 : ℝ)⁻¹ * dist x y| ≤ δ
    simpa using hδ.le
  · intro y hy
    have hm : y ∈ id '' @Metric.ball E3
        ((inferInstance : MetricSpace E3).rescale (1 : ℝ)⁻¹ (by norm_num)).toPseudoMetricSpace
        0 δ⁻¹ := by
      refine ⟨y, ?_, rfl⟩
      change (1 : ℝ)⁻¹ * dist y 0 < δ⁻¹
      simpa only [inv_one, one_mul] using (by linarith : dist y 0 < δ⁻¹)
    rw [infDist_zero_of_mem hm]
    exact hδ.le

private def euclideanZeroBallChart (r : ℝ) (hr : 0 < r) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ where
  toPartialEquiv := (OpenPartialHomeomorph.univBall (0 : E3) r).symm.toPartialEquiv
  open_source := (OpenPartialHomeomorph.univBall (0 : E3) r).open_target
  open_target := (OpenPartialHomeomorph.univBall (0 : E3) r).open_source
  contMDiffOn_toFun := by
    rw [OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.univBall_target 0 hr]
    exact OpenPartialHomeomorph.contDiffOn_univBall_symm.contMDiffOn
  contMDiffOn_invFun := OpenPartialHomeomorph.contDiff_univBall.contDiffOn.contMDiffOn

private theorem euclideanZero_metric (x y : E3) :
    riemannianEDistOf (euclideanMetric (E := E3)) x y = ENNReal.ofReal (dist x y) := by
  rw [show euclideanMetric (E := E3) = standardEuclideanMetric E3 from rfl,
    riemannianEDistOf_standardEuclideanMetric, edist_dist]

private theorem euclideanZero_sectional (x : E3) :
    SectionalBoundedBelowAt (euclideanMetric (E := E3)) x 0 := by
  intro v w
  simp only [zero_mul, metricRm04StandardAt_apply, euclideanMetric_metricRm04At_eq_zero,
    zero_apply, le_refl]

theorem exists_euclideanZeroModelBall {ε e : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (he : 0 < e) (he1 : e < 1 / 40) :
    ∃ δ : ℝ, 0 < δ ∧
      ∃ z : ZeroModelBall (𝓡 3) E3 (euclideanMetric (E := E3))
        (Function.const Unit E3) (Function.const Unit E3) (Function.const Unit (0 : E3)) δ ε e,
        z.center = 0 ∧ z.radius = 1 := by
  have hrs : 0 < radialSmoothingConeError (ε / 4) :=
    radialSmoothingConeError_pos (by positivity)
  let δ := min (1 / 2 : ℝ) (radialSmoothingConeError (ε / 4) / 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hδs : δ < radialSmoothingConeError (ε / 4) := by
    have hh := min_le_right (1 / 2 : ℝ) (radialSmoothingConeError (ε / 4) / 2)
    dsimp [δ]
    linarith
  let φ := euclideanZeroConeMap hδ hδ1
  obtain ⟨radial, hradial⟩ := exists_buffered_radial_cutoff_at_scale
    (euclideanMetric (E := E3)) euclideanZero_metric (R := 1) (by norm_num) φ
    (RadialConeData.ofInnerProductSpace E3)
    (fun y _hy => (euclideanZero_sectional y).mono (by norm_num)) hε hε1 hδs he he1
  let z : ZeroModelBall (𝓡 3) E3 (euclideanMetric (E := E3))
      (Function.const Unit E3) (Function.const Unit E3) (Function.const Unit (0 : E3)) δ ε e :=
    { center := 0
      radius := 1
      radius_pos := by norm_num
      model := ()
      coneMap := φ
      radial := radial
      radial_spec := hradial
      modelChart := fun r hr => euclideanZeroBallChart r (by linarith [hr.1])
      modelChart_source := fun r hr => by
        change (OpenPartialHomeomorph.univBall (0 : E3) r).target = ball 0 (r * 1)
        simpa only [mul_one] using OpenPartialHomeomorph.univBall_target 0
          (by linarith [hr.1])
      modelChart_target := fun r _hr => OpenPartialHomeomorph.univBall_source 0 r }
  exact ⟨δ, hδ, z, rfl, rfl⟩

end DifferentialGeometry.Geometry.Collapse
