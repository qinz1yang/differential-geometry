import DifferentialGeometry.Geometry.Collapse.LongTestValuesRiemannian

/-!
# Consumers of FC16 (Riemannian form)

* `abs_sub_le_along_unit_geodesic`: the direction-test integration along an actual unit-speed
  geodesic segment (the form used inside FC16).
* `norm_coordinate_value_sub_le_of_exact_long_tests_riemannian`: FC16 for an exact product map
  (`δ = 0`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Topology
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- Along a unit-speed geodesic segment `[0, ℓ]` avoiding `q`, the minimizing-direction test
bounds the change of `η + d_q` by `K ℓ`. -/
theorem abs_sub_le_along_unit_geodesic (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) {q p : M} {η : M → ℝ} {v : TangentSpace I p}
    (hv : g.inner p v v = 1) {ℓ K : ℝ} (hℓ : 0 ≤ ℓ)
    (hη : ∀ t ∈ Icc 0 ℓ, MDifferentiableAt I 𝓘(ℝ, ℝ) η (intrinsicGeodesic g hEnorm p v t))
    (hq : ∀ t ∈ Icc 0 ℓ, intrinsicGeodesic g hEnorm p v t ≠ q)
    (htest : ∀ t ∈ Icc 0 ℓ,
      ∀ w ∈ minimizingDirectionsTo g hEnorm {q} (intrinsicGeodesic g hEnorm p v t),
      ∀ X : TangentSpace I (intrinsicGeodesic g hEnorm p v t),
      |mvfderiv (I := I) η (intrinsicGeodesic g hEnorm p v t) X -
          g.inner (intrinsicGeodesic g hEnorm p v t) w X| ≤
        K * Real.sqrt (g.inner (intrinsicGeodesic g hEnorm p v t) X X)) :
    |(η (intrinsicGeodesic g hEnorm p v ℓ) + dist (intrinsicGeodesic g hEnorm p v ℓ) q) -
        (η p + dist p q)| ≤ K * ℓ := by
  have h := abs_sub_le_of_minimizingDirection_test g hEnorm (q := q) (η := η)
    (c := intrinsicGeodesic g hEnorm p v) hℓ
    (fun t _ => (intrinsicGeodesic_contMDiff g hEnorm p v).contMDiffAt.mdifferentiableAt
      (by simp))
    hη (fun t _ => by rw [intrinsicGeodesic_speedSq_eq, hv]) hq htest
  rwa [intrinsicGeodesic_zero, sub_zero] at h

/-- FC16 for an exact product map on `B(p, T)` (the row's `H`) (`δ = 0`). -/
theorem norm_coordinate_value_sub_le_of_exact_long_tests_riemannian (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) {k : ℕ} {Z : Type*} [MetricSpace Z]
    (u : M → EuclideanSpace ℝ (Fin k)) (z : M → Z) (η : M → EuclideanSpace ℝ (Fin k))
    {p : M} {z₀ : Z} {R s T α : ℝ} (hR : 0 < R) (hα : 0 ≤ α)
    (hs : 2 * R < s) (hH : s + R < T) (hup : u p = 0) (hzp : z p = z₀)
    (hdist : ∀ x ∈ ball p T, ∀ y ∈ ball p T,
      dist (WithLp.toLp 2 (u x, z x) : WithLp 2 (_ × Z)) (WithLp.toLp 2 (u y, z y)) = dist x y)
    (hcover : ∀ q : WithLp 2 (EuclideanSpace ℝ (Fin k) × Z),
      dist q (WithLp.toLp 2 (0, z₀)) < T → ∃ y ∈ ball p T, WithLp.toLp 2 (u y, z y) = q)
    (hη : ∀ a : Fin k, ∀ x ∈ ball p R, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => η y a) x)
    (hlip : ∀ a : Fin k, ∀ x ∈ ball p R, ∀ X : TangentSpace I x,
      |mvfderiv (I := I) (fun y => η y a) x X| ≤ (1 + α) * Real.sqrt (g.inner x X X))
    (htest : ∀ a : Fin k, ∀ x ∈ ball p R, ∀ y ∈ ball p T, R < dist x y →
      ∀ w : TangentSpace I x, g.inner x w w = 1 →
      intrinsicGeodesic g hEnorm x w (dist x y) = y →
      |mvfderiv (I := I) (fun y' => η y' a) x w - (u y a - u x a) / dist x y| ≤ α) :
    ∀ x ∈ ball p R, ‖η x - η p - u x‖ ≤
      Real.sqrt k * (R * Real.sqrt (4 * (α + 2 * R / (s - R)) + (α + 2 * R / (s - R)) ^ 2) +
        R ^ 2 / (2 * (s - R))) := by
  intro x hx
  have h := norm_coordinate_value_sub_le_of_long_tests_riemannian g hEnorm u z η
    (s := s) (T := T) (δ := 0) hR le_rfl hα (by linarith) (by linarith) hup hzp
    (fun x hx y hy => by rw [hdist x hx y hy, sub_self, abs_zero])
    (fun q hq => by
      obtain ⟨y, hy, hyq⟩ := hcover q (by linarith)
      exact ⟨y, hy, by rw [hyq, dist_self]⟩)
    hη hlip htest x hx
  simpa only [mul_zero, add_zero, sub_zero] using h

end DifferentialGeometry.Geometry.Collapse
