import DifferentialGeometry.Geometry.Collapse.FiniteCategory.BufferedEmbeddingBinding

/-!
# LFR10: closed balls and finitely many radii (consumer)

Blueprint 207A, LFR10 (A:25488–25555), the last two sentences: the comparison map is an
embedding on a neighbourhood of the closed `R`-ball if one starts with a larger buffer, and a
finite collection of radii has one common tail. Both follow from
`eventually_buffered_embedding_of_basepoint_volume` (applied with the radii `R < R + 1`) and
`Filter.eventually_all_finset`.
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

/-- **LFR10, closed balls, finitely many radii.** Under the hypotheses of
`eventually_buffered_embedding_of_basepoint_volume`, for every finite set `s` of radii, eventually,
for every `R ∈ s`, `f i` agrees with a `C^m` partial diffeomorphism whose (open) source contains
the closed ball `B̄(p, R)`, is injective on `B̄(p, R)`, and its image of that source contains
`B(q i, R)`. -/
theorem eventually_buffered_embedding_closedBall_finset (k : ℕ) (hk : 2 ≤ k)
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
    (hRm : letI : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin k))) :=
        ⟨by simpa using (show k ≠ 0 by omega)⟩
      ∀ S : ℝ, ∃ A : ℝ, 0 < A ∧ ∀ i, ∀ y ∈ ball (q i) S,
        Real.sqrt (Tensor0SBundle.normSq0S (g i) y 4 (metricRm04At (g i) y)) ≤ A)
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
    (s : Finset ℝ) :
    ∀ᶠ i in atTop, ∀ R ∈ s,
      ∃ d : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
          N (X i) m,
        closedBall p R ⊆ d.source ∧ (d : N → X i) = f i ∧ InjOn (f i) (closedBall p R) ∧
          ball (q i) R ⊆ f i '' d.source := by
  refine (Filter.eventually_all_finset s).2 fun R _ => ?_
  filter_upwards [eventually_buffered_embedding_of_basepoint_volume k hk G hn hG hr₀ hv₀ g
    hmetric q hvol hRm f p hp U hUo hUK hm hf hconv hdist (lt_add_one R)] with i hi
  obtain ⟨⟨d, hds, -, hdf⟩, hcont⟩ := hi
  have hsub : closedBall p R ⊆ d.source := hds ▸ closedBall_subset_ball (lt_add_one R)
  refine ⟨d, hsub, hdf, ?_, hds ▸ hcont⟩
  intro x hx y hy hxy
  rw [← hdf] at hxy
  exact d.toPartialEquiv.injOn (hsub hx) (hsub hy) hxy

end DifferentialGeometry.Geometry.Collapse.FiniteCategory
