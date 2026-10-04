import DifferentialGeometry.Geometry.Collapse.FiniteSurface.VerticalDirectionLimit
import DifferentialGeometry.Geometry.Geodesic.Convergence.FiniteMinimizingLimitBinding

/-!
# LFR18 for the data of T0 (LFR14's finite-order Cheeger–Gromov limit)

Consumer of `exists_vertical_field_eventually_inverse_directions_close`: T0's output clauses
(`exists_finite_cheeger_gromov_limit`, model `ℝⁿ`, `n ≥ 2`, order `K ≥ 4`) together with a metric
product structure `Φ : N ≃ᵢ ℓ²(ℝ × W)` of the limit (L-CONS (a) supplies one under a splitting
hypothesis) give LFR18: the vertical field `V` and the uniform convergence of EVERY inverse lift of a
source minimizing direction from `j i x` to `j i x⁺` to `V x`. The limit metric `G` of class `C^{K-1}`
is read as `C^{r+1}` with `r = K - 2 ≥ 2`.
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

/-- **LFR18 for T0's data.** T0's output clauses for `n ≥ 2`, `4 ≤ K`, and a metric product
structure `Φ` of the limit give the vertical field `V` of LFR18 with the uniform convergence of all
inverse lifts of source minimizing directions to `V`. -/
theorem exists_vertical_field_of_finite_cheeger_gromov {n K : ℕ} (hn : 2 ≤ n) (hK : 4 ≤ K)
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
    (hpt : ∀ i, j i q = p (φ i))
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
    {W : Type*} [MetricSpace W] (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {C : Set N} (hC : IsCompact C) :
    ∃ V : ∀ x : N, TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x,
      (∀ x, G.finiteMinimizingDirectionsTo
        {Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))} x = {V x}) ∧
      Continuous (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N)) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ C,
        ∀ w ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g (φ i))
          {j i (Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd)))} (j i x),
          let u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x :=
            mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
              ((j i).symm : X (φ i) → N) (j i x) w
          G.inner x (u - V x) (u - V x) < ε ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 4 := ⟨K - 4, by omega⟩
  let hRB : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
    ⟨G.toRiemannianMetric⟩
  have hRM : IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N := hRiem
  have hGnorm : ∀ (z : N) (u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) z),
      ‖u‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner z u u)) := by
    intro z u
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  have : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
    ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
  have hr : (2 : ℕ∞) ≤ ((m + 2 : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_add_left 2 m
  exact exists_vertical_field_eventually_inverse_directions_close (M := fun i => X (φ i))
    (r := ((m + 2 : ℕ) : ℕ∞)) hr G hGnorm (fun i => g (φ i)) (fun i => hmetric (φ i))
    (by omega : 2 ≤ m + 4) q j hexh
    (fun z L hL hLt => (hconv z L hL hLt).mono_order (by omega)) hdist
    (fun a b ha hab => by
      filter_upwards [hcover a b ha hab] with i hi
      rw [hpt i]
      exact hi)
    Φ hℓ hC

end DifferentialGeometry.Geometry.Riemannian.Geodesic
