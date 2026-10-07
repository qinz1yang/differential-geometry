import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.RegularSlice
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Integral.Measure
open scoped ENNReal Manifold
universe u
namespace GC.LongTime.Ch12

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {T : ObservationTower P g}

/-- Total Riemannian volume of the (post-surgery) slice stage in the physical metric `g(t)`. -/
def sliceTotalVolume_S10 (s : GC.LongTime.RegularSlice T) : ℝ≥0∞ :=
  riemannianVolumeMeasure ThreeModel s.stage.Carrier s.metric univ

/-- Total volume in the Ch12 normalisation `\bar g_t = t⁻¹ g(t)` (no `4t`). -/
def normalizedTotalVolume (s : GC.LongTime.RegularSlice T) : ℝ≥0∞ :=
  riemannianVolumeMeasure ThreeModel s.stage.Carrier s.normalizedMetric univ

theorem normalizedTotalVolume_eq_S10 (s : GC.LongTime.RegularSlice T) :
    normalizedTotalVolume s =
      ENNReal.ofReal (Real.sqrt s.time⁻¹) ^ 3 * sliceTotalVolume_S10 s := by
  have h := volume_scale_apply (I := ThreeModel) (M := s.stage.Carrier) s.time⁻¹
    (inv_pos.mpr s.positive) s.metric univ
  have hr : Module.finrank ℝ ThreeSpace = 3 := by simp
  rw [hr] at h
  exact h

/-- Pure assembly step: a chain of event steps `v (i+1) · w i ≤ v i · w (i+1)` telescopes. -/
theorem chain_telescope_S10 (v w : ℕ → ℝ≥0∞) (hw0 : ∀ i, w i ≠ 0) (hwt : ∀ i, w i ≠ ⊤)
    (h : ∀ i, v (i + 1) * w i ≤ v i * w (i + 1)) (n : ℕ) :
    v n * w 0 ≤ v 0 * w n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have h1 : v (n + 1) * w 0 * w n ≤ v 0 * w (n + 1) * w n := by
      calc v (n + 1) * w 0 * w n = (v (n + 1) * w n) * w 0 := by ring
        _ ≤ (v n * w (n + 1)) * w 0 := mul_le_mul_left (h n) _
        _ = (v n * w 0) * w (n + 1) := by ring
        _ ≤ (v 0 * w n) * w (n + 1) := by gcongr
        _ = v 0 * w (n + 1) * w n := by ring
    exact (ENNReal.mul_le_mul_iff_left (hw0 n) (hwt n)).mp h1

end GC.LongTime.Ch12
