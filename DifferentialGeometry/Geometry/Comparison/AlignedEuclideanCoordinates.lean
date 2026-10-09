import DifferentialGeometry.Geometry.Comparison.LineDistance
import DifferentialGeometry.Geometry.Metric.L2Product
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X Z : Type*} [MetricSpace X] [MetricSpace Z] {k : ℕ}

theorem lineCoordinate_eq_euclidean_coordinate_of_aligned_isometry
    (e : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Z))
    {γ : ℝ → X} {z : Z} {j : Fin k}
    (halign : ∀ t, e (γ t) = WithLp.toLp 2 (PiLp.single 2 j t, z)) (x : X) :
    lineCoordinate γ x = (e x).fst j := by
  have hd (t : ℝ) := WithLp.prod_dist_sq_eq_add_sq (e x) (e (γ t))
  have hzero := hd 0
  have hone := hd 1
  rw [e.dist_eq, halign] at hzero hone
  change dist x (γ 0) ^ 2 = dist (e x).fst (PiLp.single 2 j 0) ^ 2 + dist (e x).snd z ^ 2 at hzero
  change dist x (γ 1) ^ 2 = dist (e x).fst (PiLp.single 2 j 1) ^ 2 + dist (e x).snd z ^ 2 at hone
  rw [(PiLp.single_eq_zero_iff 2 j).mpr rfl, dist_zero_right] at hzero
  rw [dist_eq_norm, norm_sub_sq_real] at hone
  have hinner : inner ℝ (e x).fst (PiLp.single 2 j (1 : ℝ)) = (e x).fst j := by
    simpa only [EuclideanSpace.single, one_mul, conj_trivial] using
      EuclideanSpace.inner_single_right j (1 : ℝ) (e x).fst
  rw [hinner, PiLp.norm_single, norm_one, one_pow] at hone
  unfold lineCoordinate
  linarith

end DifferentialGeometry.Geometry.Comparison.Toponogov
