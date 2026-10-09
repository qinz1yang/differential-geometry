import DifferentialGeometry.Geometry.Geodesic.Convergence.FiniteMinimizingLimit
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.CheegerGromovLimit

/-!
# LC50′ bound to T0 (LFR14's finite-order Cheeger–Gromov limit)

The data of T0 (`exists_finite_cheeger_gromov_limit`, CheegerGromovLimit.lean) for `3 ≤ K` are
LC50′-shaped: the limit metric `G` of class `C^{K-1}` is read as `C^{r+1}` with
`r = K - 2 ≥ 1`, the chart convergence of order `K - 1` is used at order one, the bundle norm of
`G.toRiemannianMetric` is the `G`-norm, and the coverage around `p (φ i) = j i q` is the coverage
around `j i q`.

* `exists_subseq_minimizing_direction_limit_of_finite_cheeger_gromov`: T0's output clauses (as
  hypotheses) give LC50′ with moving endpoints.
* `exists_finite_cheeger_gromov_limit_with_direction_limits`: the closed form, T0's hypotheses give
  T0's package together with LC50′ for every compact set of base points, endpoint sequence and
  minimizing directions. The oriented T1 has the same clauses, so the binding applies to it too.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Integral.Measure GC.MetricGeometry

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

universe u

/-- **LC50′ for T0's data.** T0's output clauses for `3 ≤ K` (the limit `(N, G, q)`, the maps
`j i : N → X (φ i)` pointed at `p (φ i)`, exhaustion, chart convergence of order `K - 1`,
distortion, coverage around `p (φ i)`, and `G` realising the distance) give the conclusion of
`exists_subseq_minimizing_direction_limit_finite`. -/
theorem exists_subseq_minimizing_direction_limit_of_finite_cheeger_gromov {n K : ℕ} (hK : 3 ≤ K)
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
    (y : ℕ → N) {yInf : N} (hy : Tendsto y atTop (𝓝 yInf))
    (w : ∀ i, TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (j i (x i)))
    (hw : ∀ i, w i ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g (φ i))
      {j i (y i)} (j i (x i))) :
    ∃ v : TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N, v.proj ∈ C ∧
      v.snd ∈ G.finiteMinimizingDirectionsTo {yInf} v.proj ∧
      (∀ s ∈ Icc 0 (dist v.proj yInf), ∀ t ∈ Icc 0 (dist v.proj yInf),
        dist (G.expMap (⟨v.proj, s • v.snd⟩ : TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N))
          (G.expMap (⟨v.proj, t • v.snd⟩ : TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N)) =
          |s - t|) ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (fun i => (⟨x (ψ i),
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          ((j (ψ i)).symm : X (φ (ψ i)) → N) (j (ψ i) (x (ψ i))) (w (ψ i))⟩ :
          TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N)) atTop (𝓝 v) := by
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 3 := ⟨K - 3, by omega⟩
  let hRB : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
    ⟨G.toRiemannianMetric⟩
  have hRM : IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N := hRiem
  have hGnorm : ∀ (z : N) (u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) z),
      ‖u‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner z u u)) := by
    intro z u
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  have hr : (1 : ℕ∞) ≤ ((m + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_add_left 1 m
  exact exists_subseq_minimizing_direction_limit_finite (M := fun i => X (φ i))
    (r := ((m + 1 : ℕ) : ℕ∞)) hr G hGnorm (fun i => g (φ i)) (fun i => hmetric (φ i))
    (by omega : 2 ≤ m + 3) q j hexh
    (fun z L hL hLt => (hconv z L hL hLt).mono_order (by omega)) hdist
    (fun a b ha hab => by
      filter_upwards [hcover a b ha hab] with i hi
      rw [(hpt i).2]
      exact hi)
    hC x hx y hy w hw

/-- **T0 with LC50′ (closed form).** Under T0's hypotheses with `3 ≤ K`, T0's package holds
together with LC50′: for every compact set `C` of base points, every endpoint sequence
`y i → yInf` and every choice of minimizing `g (φ i)`-unit directions `w i` from `j i (x i)` to
`j i (y i)`, a subsequence of the inverse lifts converges to a minimizing `G`-direction towards
`yInf` whose radial geodesic is a segment. -/
theorem exists_finite_cheeger_gromov_limit_with_direction_limits
    (n K : ℕ) (hn : 2 ≤ n) (hK : 3 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ) (hA : ∀ R > 0, 0 < A R)
    {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (X i)]
    [∀ i, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (X i)]
    [∀ i, SigmaCompactSpace (X i)]
    [∀ i, T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i))]
    [∀ i, CompleteSpace (X i)] [∀ i, ConnectedSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i)
    (hvol : ∀ i, ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (X i) (g i) (riemannianBallOf (g i) (p i) r))
    (hcurv : ∀ R > 0, ∀ i, ∀ k ≤ K, ∀ y ∈ riemannianBallOf (g i) (p i) R,
      curvDerivNorm k (g i) y ≤ A R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ (N : Type) (mN : MetricSpace N) (cN : ChartedSpace (EuclideanSpace ℝ (Fin n)) N),
      letI := mN
      letI := cN
      ∃ (_ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N)
        (G : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((K - 1 : ℕ) : ℕ∞ω)
          (EuclideanSpace ℝ (Fin n))
          (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : N → Type _))
        (q : N)
        (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N (X (φ i)) K),
        ProperSpace N ∧ ConnectedSpace N ∧
        (letI : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
          ⟨G.toRiemannianMetric⟩
         IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N) ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        (∀ i, q ∈ (j i).source ∧ j i q = p (φ i)) ∧
        (∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source) ∧
        (∀ (x : N) (L : Set (EuclideanSpace ℝ (Fin n))), IsCompact L →
          L ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).target →
          MapCPConvergenceOn L (K - 1)
            (fun i => pullbackMetricCoefficients (g (φ i))
              ((j i : N → X (φ i)) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm))
            (chartCoeff G x)) ∧
        (∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
          |dist (j i x) (j i y) - dist x y| < ε) ∧
        (∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
          ball (p (φ i)) a ⊆ (j i : N → X (φ i)) '' ball q b) ∧
        ∀ (C : Set N), IsCompact C → ∀ (x : ℕ → N), (∀ i, x i ∈ C) →
          ∀ (y : ℕ → N) (yInf : N), Tendsto y atTop (𝓝 yInf) →
          ∀ (w : ∀ i, TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (j i (x i))),
            (∀ i, w i ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g (φ i))
              {j i (y i)} (j i (x i))) →
          ∃ v : TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N, v.proj ∈ C ∧
            v.snd ∈ G.finiteMinimizingDirectionsTo {yInf} v.proj ∧
            (∀ s ∈ Icc 0 (dist v.proj yInf), ∀ t ∈ Icc 0 (dist v.proj yInf),
              dist (G.expMap (⟨v.proj, s • v.snd⟩ :
                  TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N))
                (G.expMap (⟨v.proj, t • v.snd⟩ :
                  TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N)) = |s - t|) ∧
            ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (fun i => (⟨x (ψ i),
              mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
                ((j (ψ i)).symm : X (φ (ψ i)) → N) (j (ψ i) (x (ψ i))) (w (ψ i))⟩ :
                TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N)) atTop (𝓝 v) := by
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist,
      hcov⟩ := exists_finite_cheeger_gromov_limit n K hn (by omega) hr hv A hA g hmetric p hvol hcurv
  let := mN
  let := cN
  have := hMN
  have := hprop
  refine ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist, hcov,
    fun C hC x hx y yInf hy w hw => ?_⟩
  exact exists_subseq_minimizing_direction_limit_of_finite_cheeger_gromov hK g hmetric p φ G q j
    hRiem hpt hexh hconv hdist hcov hC x hx y hy w hw

end DifferentialGeometry.Geometry.Riemannian.Geodesic
