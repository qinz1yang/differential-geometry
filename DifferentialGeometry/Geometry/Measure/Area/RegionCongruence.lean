import DifferentialGeometry.Geometry.Measure.Area.Manifold



noncomputable section

open Manifold Set DifferentialGeometry MeasureTheory Filter Metric
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]



theorem riemannianArea_congr_on_open (g : SmoothRiemannianMetric I M)
    {u v : ℂ → M} {s : Set ℂ} (hs : IsOpen s) (huv : EqOn u v s) :
    riemannianArea g u s = riemannianArea g v s := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hs.measurableSet] with z hz
  exact riemannianAreaDensity_congr g (huv.eventuallyEq_of_mem (hs.mem_nhds hz))


theorem riemannianArea_closedBall_eq_ball (g : SmoothRiemannianMetric I M)
    (u : ℂ → M) (z : ℂ) (r : ℝ) :
    riemannianArea g u (closedBall z r) = riemannianArea g u (ball z r) := by
  unfold riemannianArea
  apply setIntegral_congr_set
  have hs : ∀ᵐ w : ℂ ∂volume, w ∉ sphere z r := by
    rw [ae_iff]
    convert MeasureTheory.Measure.addHaar_sphere volume z r using 1
    congr 1
    ext w
    simp
  filter_upwards [hs] with w hw
  exact propext (by
    change dist w z ≤ r ↔ dist w z < r
    exact ⟨fun h => lt_of_le_of_ne h hw, le_of_lt⟩)



theorem riemannianArea_congr_on_closedBall (g : SmoothRiemannianMetric I M)
    {u v : ℂ → M} {z : ℂ} {r : ℝ} (huv : EqOn u v (closedBall z r)) :
    riemannianArea g u (closedBall z r) = riemannianArea g v (closedBall z r) := by
  rw [riemannianArea_closedBall_eq_ball, riemannianArea_closedBall_eq_ball]
  exact riemannianArea_congr_on_open g isOpen_ball (huv.mono ball_subset_closedBall)

end DifferentialGeometry.Geometry
