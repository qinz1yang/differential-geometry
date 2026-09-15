import DifferentialGeometry.Geometry.Metric.Comparison.CurveLengthPartition
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.InitialRampLength

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

theorem polygonVertex_distance_sum_le_loopLength (g : SmoothRiemannianMetric I Q)
    (γ : RegularLoop I Q) {N : ℕ} (hN : 0 < N) :
    (∑ i : Fin N, (riemannianEDistOf g (polygonVertex γ N i.val)
      (polygonVertex γ N (i.val + 1))).toReal) ≤ loopLength g γ.toContinuousLoop := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hmono : Monotone (fun i : ℕ => (i : ℝ) / N) := by
    intro i j hij
    exact div_le_div_of_nonneg_right (by exact_mod_cast hij) hNR.le
  have h := DifferentialGeometry.sum_toReal_riemannianEDistOf_le_arcLength g
    γ.contMDiff_lift (fun i : ℕ => (i : ℝ) / N) hmono N
  rw [Nat.cast_zero, zero_div, div_self hNR.ne'] at h
  have hlen : DifferentialGeometry.Geometry.Riemannian.Variation.arcLength g
      (fun t : ℝ => γ.toContinuousLoop (t : Surgery.Topology.Circle)) 0 1 =
      loopLength g γ.toContinuousLoop := by
    rw [loopLength, ← restrict_Ioc_eq_restrict_Icc,
      ← intervalIntegral.integral_of_le zero_le_one]
    rfl
  rw [hlen] at h
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => (riemannianEDistOf g (polygonVertex γ N (k : ℤ))
      (polygonVertex γ N ((k : ℤ) + 1))).toReal)]
  simpa only [polygonVertex, Int.cast_natCast, Int.cast_add, Int.cast_one,
    Nat.cast_add, Nat.cast_one] using h

variable [FiniteDimensional ℝ E] [T2Space Q] [I.Boundaryless]

theorem flatPolygon_loopLength_le (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile)
    {N : ℕ} (hN : 0 < N) (γ c : RegularLoop I Q)
    (hc : ∀ z, c z = flatPolygon g P N γ z)
    (hseg : ∀ i : ℤ, 0 ≤ i → i < N → IsShortSegment g (polygonVertex γ N i)
      (polygonVertex γ N (i + 1))
      (shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1)))) :
    loopLength g c.toContinuousLoop ≤ loopLength g γ.toContinuousLoop := by
  rw [flatPolygon_loopLength_eq_sum g P hN γ c hc hseg]
  exact polygonVertex_distance_sum_le_loopLength g γ hN

theorem initialRamp_flatPolygon_length_le (g : SmoothRiemannianMetric I Q)
    (P : FlatteningProfile) {N : ℕ} (hN : 0 < N) (γ c : RegularLoop I Q)
    (hc : ∀ z, c z = flatPolygon g P N γ z)
    (hseg : ∀ i : ℤ, 0 ≤ i → i < N → IsShortSegment g (polygonVertex γ N i)
      (polygonVertex γ N (i + 1))
      (shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))))
    (lambda t : ℝ) :
    (initialRamp c).length (fun _ => g) lambda t ≤
      loopLength g γ.toContinuousLoop + |lambda| :=
  (initialRamp_length_le g c lambda t).trans
    (add_le_add_left (flatPolygon_loopLength_le g P hN γ c hc hseg) _)

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
