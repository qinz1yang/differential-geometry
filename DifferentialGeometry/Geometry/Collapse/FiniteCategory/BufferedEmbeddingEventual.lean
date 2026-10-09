import DifferentialGeometry.Geometry.Collapse.FiniteCategory.BufferedEmbeddingBinding
import DifferentialGeometry.Geometry.Collapse.FiniteCategory.EventualCurvatureBounds

/-!
# LFR10 under the eventual curvature bounds of LFR16

Blueprint 207A, LFR16 (`lem:collapse-finite-compact-factor`, A:26159–26203): with the curvature
bounds of orders `0, …, K` by `A(R)` on `B(q i, R)` holding only for `i ≥ i_R`, "the conclusions
of LFR14–LFR15 still hold". For the buffered-embedding conclusion (LFR10) this follows from
W4-F7b's reduction `GC.MetricGeometry.exists_uniform_curvature_bound_of_eventual` (a modified
bound function valid for every member) and the LFR10 row
`eventually_buffered_embedding_of_basepoint_volume`; only the order-`0` bound is used.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Metric Bundle
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse.FiniteCategory

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry (pullbackMetricCoefficients)
open DifferentialGeometry.Geometry.MetricSmoothing (chartCoeff)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **LFR10 under LFR16's eventual bounds.** The hypotheses of
`eventually_buffered_embedding_of_basepoint_volume`, with the curvature bound replaced by LFR16's
eventual version (orders `0, …, K` bounded by `A R` on `B(q i, R)` for `i ≥ i_R`). Then for
`r < R`, eventually `f i` restricts to a `C^m` diffeomorphism of `B(p, R)` onto its open image and
`B(q i, r) ⊆ f i (B(p, R))`. -/
theorem eventually_buffered_embedding_of_eventual_curvature_bounds (k : ℕ) (hk : 2 ≤ k)
    {N : Type*} [MetricSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin k)) N]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ N] [CompleteSpace N]
    {n : ℕ∞ω} (G : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) n
      (EuclideanSpace ℝ (Fin k)) (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) : N → Type _))
    (hn : (2 : ℕ∞ω) ≤ n)
    (hG : letI : RiemannianBundle
            (fun x : N => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) x) :=
          ⟨G.toRiemannianMetric⟩
      IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) N)
    {r₀ v₀ : ℝ} (hr₀ : 0 < r₀) (hv₀ : 0 < v₀)
    {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin k)) (X i)]
    [∀ i, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ (X i)]
    [∀ i, T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (X i))]
    [∀ i, SigmaCompactSpace (X i)] [∀ i, CompleteSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (q : ∀ i, X i) (hvol : ∀ i, ENNReal.ofReal v₀ ≤ ballVolume (g i) (q i) r₀)
    (K : ℕ) (A : ℝ → ℝ)
    (hev : letI : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin k))) :=
        ⟨by simpa using (show k ≠ 0 by omega)⟩
      ∀ R > 0, ∀ᶠ i in atTop, ∀ j ≤ K,
        ∀ y ∈ riemannianBallOf (g i) (q i) R, curvDerivNorm j (g i) y ≤ A R)
    (f : ∀ i, N → X i) (p : N) (hp : ∀ i, f i p = q i)
    (U : ℕ → Set N) (hUo : ∀ i, IsOpen (U i))
    (hUK : ∀ K : Set N, IsCompact K → ∀ᶠ i in atTop, K ⊆ U i)
    {m : ℕ} (hm : 3 ≤ m)
    (hf : ∀ i, ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) m
      (f i) (U i))
    (hconv : ∀ (z : N) (K : Set (EuclideanSpace ℝ (Fin k))), IsCompact K →
      K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) z).target →
      MapCPConvergenceOn K 2
        (fun i => pullbackMetricCoefficients (g i)
          (f i ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) z).symm))
        (chartCoeff G z))
    (hdist : ∀ S ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball p S, ∀ y ∈ ball p S,
      |dist (f i x) (f i y) - dist x y| < ε)
    {r R : ℝ} (hrR : r < R) :
    ∀ᶠ i in atTop,
      (∃ d : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
          N (X i) m,
        d.source = ball p R ∧ d.target = f i '' ball p R ∧ (d : N → X i) = f i) ∧
      ball (q i) r ⊆ f i '' ball p R := by
  have : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin k))) :=
    ⟨by simpa using (show k ≠ 0 by omega)⟩
  obtain ⟨A', hA'pos, -, hA'⟩ :=
    GC.MetricGeometry.exists_uniform_curvature_bound_of_eventual K g hmetric q A hev
  refine eventually_buffered_embedding_of_basepoint_volume k hk G hn hG hr₀ hv₀ g hmetric q hvol
    ?_ f p hp U hUo hUK hm hf hconv hdist hrR
  intro S
  have hS : (0 : ℝ) < max S 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨A' (max S 1), hA'pos _, fun i y hy => ?_⟩
  have hy' : y ∈ riemannianBallOf (g i) (q i) (max S 1) := by
    change riemannianEDistOf (g i) (q i) y < ENNReal.ofReal (max S 1)
    rw [hmetric, dist_comm]
    exact (ENNReal.ofReal_lt_ofReal_iff hS).2 (lt_of_lt_of_le (mem_ball.mp hy) (le_max_left _ _))
  exact hA' (max S 1) hS i 0 (Nat.zero_le K) y hy'

end DifferentialGeometry.Geometry.Collapse.FiniteCategory
