import DifferentialGeometry.Geometry.Collapse.SublevelCore.FiniteCollarTransfer

/-!
# Consumer: LC51′ on T0's finite-order Cheeger–Gromov data

`exists_uniform_collar_of_finite_cheeger_gromov`: T0's output clauses
(`exists_finite_cheeger_gromov_limit`, the LFR14 producer) with `4 ≤ K` give LC51′'s uniform source
collar. The limit metric `G` of class `C^{K-1}` is read as `C^{r+1}` with `r = K - 2 ≥ 2`, the chart
convergence of order `K - 1` is used at order one, the bundle norm of `G.toRiemannianMetric` is
the `G`-norm, and the coverage around `p (φ i) = j i q` is the coverage around `j i q`; the same
conversions as LC50P's `exists_subseq_minimizing_direction_limit_of_finite_cheeger_gromov`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

/-- **LC51′ for T0's data.** -/
theorem exists_uniform_collar_of_finite_cheeger_gromov {n K : ℕ} (hK : 4 ≤ K)
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
    (o : N) {D : Set N} (hDc : IsCompact D) (hin : closedBall o (1 / 2) ⊆ interior D)
    (hout : D ⊆ ball o 2) {O : Set N} (hO : IsOpen O) (hDO : frontier D ⊆ O)
    (V : (x : N) → TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)
    (hV : ContinuousOn (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N)) O)
    (hneg : ∀ x ∈ frontier D, ∀ v ∈ G.finiteMinimizingDirectionsTo {o} x,
      G.inner x (V x) v < 0) :
    ∃ α B : ℝ, 0 < α ∧ 0 < B ∧ ∃ U : Set N, IsOpen U ∧ frontier D ⊆ U ∧
      IsCompact (closure U) ∧ closure U ⊆ (ball o 3 \ {o}) ∩ O ∧
      ∀ᶠ i in atTop, ∀ x ∈ closure U,
        (g (φ i)).inner (j i x)
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
              (j i : N → X (φ i)) x (V x))
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
              (j i : N → X (φ i)) x (V x)) ≤ (2 * B) ^ 2 ∧
        ∀ w ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g (φ i)) {j i o} (j i x),
          (g (φ i)).inner (j i x)
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
              (j i : N → X (φ i)) x (V x)) w ≤ -α := by
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 4 := ⟨K - 4, by omega⟩
  let hRB : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
    ⟨G.toRiemannianMetric⟩
  have hRM : IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N := hRiem
  have hGnorm : ∀ (z : N) (u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) z),
      ‖u‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner z u u)) := by
    intro z u
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  have hr : (2 : ℕ∞) ≤ ((m + 2 : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_add_left 2 m
  exact exists_uniform_collar_finite_limit (M := fun i => X (φ i))
    (r := ((m + 2 : ℕ) : ℕ∞)) hr G hGnorm (fun i => g (φ i)) (fun i => hmetric (φ i))
    (by omega : 2 ≤ m + 4) q j hexh
    (fun z L hL hLt => (hconv z L hL hLt).mono_order (by omega))
    hdist
    (fun a b ha hab => by
      filter_upwards [hcover a b ha hab] with i hi
      rw [(hpt i).2]
      exact hi)
    o hDc hin hout hO hDO V hV hneg

end DifferentialGeometry.Geometry.Collapse
