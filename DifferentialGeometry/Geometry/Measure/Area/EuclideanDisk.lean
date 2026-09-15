import DifferentialGeometry.Analysis.Integration.BallBoundary
import DifferentialGeometry.Geometry.Measure.Area.Euclidean
import DifferentialGeometry.Geometry.Metric.ConvexProjection
import DifferentialGeometry.Topology.LoopSpace.SpanningDisk
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar













noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter ContinuousMap Metric
open DifferentialGeometry.Topology
open scoped NNReal Topology

namespace DifferentialGeometry.Geometry


def diskRetraction : ℂ → closedDisk :=
  convexProjection ⟨0, by simp⟩ isClosed_closedBall.isComplete (convex_closedBall (0 : ℂ) 1)

theorem diskRetraction_lipschitz : LipschitzWith 1 diskRetraction :=
  convexProjection_lipschitz _ _ _

@[simp] theorem diskRetraction_coe (z : closedDisk) : diskRetraction z = z :=
  convexProjection_of_mem _ _ _ z


def diskExtension {Q : Type*} (u : closedDisk → Q) : ℂ → Q := u ∘ diskRetraction

@[simp] theorem diskExtension_coe {Q : Type*} (u : closedDisk → Q) (z : closedDisk) :
    diskExtension u z = u z := by simp [diskExtension]

theorem diskExtension_lipschitz {Q : Type*} [PseudoMetricSpace Q]
    {u : closedDisk → Q} {C : ℝ≥0} (hu : LipschitzWith C u) : LipschitzWith C (diskExtension u) := by
  simpa [diskExtension] using hu.comp diskRetraction_lipschitz


theorem ae_disk_interior : ∀ᵐ z ∂volume.restrict (Metric.closedBall (0 : ℂ) 1),
    z ∈ Metric.ball (0 : ℂ) 1 :=
  ae_mem_ball_of_measure_sphere_eq_zero (addHaar_sphere volume (0 : ℂ) 1)


variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]


def euclideanDiskArea (u : closedDisk → E) : ℝ :=
  euclideanArea (diskExtension u) (Metric.closedBall 0 1)



theorem euclideanDiskArea_eq_of_extension (u : closedDisk → E) (U : ℂ → E)
    (hU : ∀ z : closedDisk, U z = u z) :
    euclideanDiskArea u = euclideanArea U (Metric.closedBall 0 1) := by
  apply integral_congr_ae
  filter_upwards [ae_disk_interior] with z hz
  have heq : diskExtension u =ᶠ[𝓝 z] U := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    have hw' := Metric.ball_subset_closedBall hw
    exact (diskExtension_coe u ⟨w, hw'⟩).trans (hU ⟨w, hw'⟩).symm
  simp only [euclideanAreaDensity, heq.fderiv_eq]

theorem euclideanDiskArea_nonneg (u : closedDisk → E) : 0 ≤ euclideanDiskArea u :=
  euclideanArea_nonneg _ _

@[simp] theorem euclideanDiskArea_const (q : E) : euclideanDiskArea (fun _ => q) = 0 :=
  euclideanArea_const q _

theorem euclideanDiskArea_smul (u : closedDisk → E) (c : ℝ) :
    euclideanDiskArea (c • u) = c ^ 2 * euclideanDiskArea u :=
  euclideanArea_smul (diskExtension u) c _

section FiniteDimensional

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

local instance : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : ℂ) 1)) :=
  isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne

theorem integrable_euclideanDiskAreaDensity {u : closedDisk → E} {C : ℝ≥0}
    (hu : LipschitzWith C u) :
    IntegrableOn (euclideanAreaDensity (diskExtension u)) (Metric.closedBall 0 1) :=
  integrableOn_euclideanAreaDensity (diskExtension_lipschitz hu) _


theorem euclideanDiskArea_comp_le {u : closedDisk → E} {f : E → F} {C L : ℝ≥0}
    (hu : LipschitzWith C u) (hf : LipschitzWith L f) :
    euclideanDiskArea (f ∘ u) ≤ (L : ℝ) ^ 2 * euclideanDiskArea u :=
  euclideanArea_comp_le (diskExtension_lipschitz hu) hf _

end FiniteDimensional

end DifferentialGeometry.Geometry
