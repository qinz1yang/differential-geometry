import DifferentialGeometry.Geometry.Geodesic.Convergence.FiniteMinimizingLimitBinding

/-!
# LC50′ consumers: the base-point form for T0's data (LFR49's shape)

LFR49 (A:29154–29158) uses LC50's minimizing-direction argument with the FIXED endpoint
`p_i = j_i q`, the base points of T0. With T0's pointing clause `j i q = p (φ i)`, minimizing
directions towards `p (φ i)` converge to minimizing `G`-directions towards `q`.

* `exists_subseq_basepoint_direction_limit_of_finite_cheeger_gromov`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

/-- **LC50′ towards the base points of T0.** For T0's data (`3 ≤ K`), minimizing
`g (φ i)`-unit directions from `j i (x i)` to the base point `p (φ i)` have, after extraction,
inverse lifts converging to a minimizing `G`-direction from `v.proj ∈ C` to `q`. -/
theorem exists_subseq_basepoint_direction_limit_of_finite_cheeger_gromov {n K : ℕ} (hK : 3 ≤ K)
    {X : ℕ → Type*} [∀ i, MetricSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (X i)]
    [∀ i, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (X i)] [∀ i, CompleteSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i) (φ : ℕ → ℕ)
    {N : Type*} [MetricSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N] [ProperSpace N]
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((K - 1 : ℕ) : ℕ∞ω)
      (EuclideanSpace ℝ (Fin n)) (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : N → Type _))
    (q : N)
    (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N (X (φ i)) K)
    (hRiem : letI : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
        ⟨G.toRiemannianMetric⟩
      IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N)
    (hpt : ∀ i, q ∈ (j i).source ∧ j i q = p (φ i))
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set (EuclideanSpace ℝ (Fin n))), IsCompact L →
      L ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).target →
      MapCPConvergenceOn L (K - 1)
        (fun i => pullbackMetricCoefficients (g (φ i))
          ((j i : N → X (φ i)) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hcover : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
      ball (p (φ i)) a ⊆ (j i : N → X (φ i)) '' ball q b)
    {C : Set N} (hC : IsCompact C) (x : ℕ → N) (hx : ∀ i, x i ∈ C)
    (w : ∀ i, TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (j i (x i)))
    (hw : ∀ i, w i ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g (φ i))
      {p (φ i)} (j i (x i))) :
    ∃ v : TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N, v.proj ∈ C ∧
      v.snd ∈ G.finiteMinimizingDirectionsTo {q} v.proj ∧
      (∀ s ∈ Icc 0 (dist v.proj q), ∀ t ∈ Icc 0 (dist v.proj q),
        dist (G.expMap (⟨v.proj, s • v.snd⟩ : TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N))
          (G.expMap (⟨v.proj, t • v.snd⟩ : TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N)) =
          |s - t|) ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (fun i => (⟨x (ψ i),
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          ((j (ψ i)).symm : X (φ (ψ i)) → N) (j (ψ i) (x (ψ i))) (w (ψ i))⟩ :
          TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N)) atTop (𝓝 v) :=
  exists_subseq_minimizing_direction_limit_of_finite_cheeger_gromov hK g hmetric p φ G q j hRiem
    hpt hexh hconv hdist hcover hC x hx (fun _ => q) tendsto_const_nhds w (fun i => by
      rw [(hpt i).2]
      exact hw i)

end DifferentialGeometry.Geometry.Riemannian.Geodesic
