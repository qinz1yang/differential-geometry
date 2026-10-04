import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.CheegerGromovLimit
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.OrientedCheegerGromovLimit
import DifferentialGeometry.Geometry.Collapse.FiniteCategory.EventualCurvatureBounds

/-!
# LFR14 consumer adapters (b) and (c): eventual curvature bounds

The external review of the LFR14 design (`build-logs/inbox/review-lfr14.md` §2, items 5(b) and
5(c) of the dispositions) asks for the compact boundedness of `curvDerivNorm` with the
finite-prefix absorption (LFR16, A:26159), and for the eventual-bound form of LFR14 for ARBITRARY
sequences (LPA02, A:30349: "every sequence `αᵢ → ∞`, `pᵢ ∈ M^{αᵢ}` has a subsequence with the
finite package").

* `continuous_curvDerivNorm`, `exists_curvDerivNorm_bound_of_isCompact`: the two forms requested
  by the review (continuity; the weaker compact bound through order `K`).
* `exists_finite_cheeger_gromov_limit_of_eventual_curvature_bounds` (LFR16): T0 when the bounds
  `|∇^k Rm| ≤ A(R)` on `B(pᵢ,R)` hold only for `i ≥ i_R`; no positivity of `A` is needed. Route:
  W4-F7b's absorption `exists_uniform_curvature_bound_of_eventual` (prefix members are bounded on
  the compact closed balls), then T0 verbatim.
* `exists_finite_cheeger_gromov_limit_with_nonneg_sectional_of_eventual_bounds`: T0 + T2 when the
  volume, curvature-derivative and sectional bounds all hold only eventually (index shift past the
  volume and sectional thresholds, then absorption).
* `exists_finite_cheeger_gromov_limit_of_eventual_family` (LPA02): for a family `M a` over a filter
  `l` whose bounds hold eventually in `l` uniformly in the centre, EVERY sequence `αᵢ → l` with
  ANY centres `pᵢ ∈ M (αᵢ)` has the T0 + T2 package.
* `…oriented_with_nonneg_sectional_of_eventual_bounds`, `…oriented_of_eventual_family`: the same
  with orientation preservation on the whole sources (T1,
  `exists_finite_cheeger_gromov_limit_oriented`), the full finite package LPA02 asks of LFR14.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Integral.Measure GC.MetricGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature

universe u

section Norm

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- **Continuity of the curvature-derivative norm** of a smooth metric. -/
theorem continuous_curvDerivNorm (g : SmoothRiemannianMetric I M) (k : ℕ) :
    Continuous (fun y => curvDerivNorm k g y) := by
  have hfun : (fun y => curvDerivNorm k g y) = curvatureDerivativeNorm g k :=
    funext fun y => (curvatureDerivativeNorm_eq_curvDerivNorm g k y).symm
  rw [hfun]
  exact continuous_curvatureDerivativeNorm g k

/-- **Compact boundedness of the curvature-derivative norms** through order `K`. -/
theorem exists_curvDerivNorm_bound_of_isCompact (g : SmoothRiemannianMetric I M) (K : ℕ)
    {C : Set M} (hC : IsCompact C) :
    ∃ B : ℝ, ∀ k ≤ K, ∀ x ∈ C, curvDerivNorm k g x ≤ B := by
  have hb : ∀ k : ℕ, ∃ B : ℝ, ∀ x ∈ C, ‖curvDerivNorm k g x‖ ≤ B := fun k =>
    hC.exists_bound_of_continuousOn (continuous_curvDerivNorm g k).continuousOn
  choose B hB using hb
  refine ⟨∑ k ∈ Finset.range (K + 1), max (B k) 0, fun k hk x hx => ?_⟩
  have hkK : k ∈ Finset.range (K + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hk)
  have h1 : max (B k) 0 ≤ ∑ k' ∈ Finset.range (K + 1), max (B k') 0 :=
    Finset.single_le_sum (f := fun k' => max (B k') 0) (fun _ _ => le_max_right _ _) hkK
  have h2 := hB k x hx
  rw [Real.norm_eq_abs] at h2
  linarith [le_abs_self (curvDerivNorm k g x), le_max_left (B k) 0]

end Norm

/-- **LFR14 under eventual curvature bounds (LFR16, "the LFR14 conclusions still hold").** If
`|∇^k Rm_{gᵢ}| ≤ A(R)` on `B(pᵢ,R)` for `k ≤ K` holds only for `i` past a threshold depending on
`R`, the package of `exists_finite_cheeger_gromov_limit` holds verbatim. -/
theorem exists_finite_cheeger_gromov_limit_of_eventual_curvature_bounds
    (n K : ℕ) (hn : 2 ≤ n) (hK : 1 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ)
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
    (hcurv : ∀ R > 0, ∀ᶠ i in atTop, ∀ k ≤ K, ∀ y ∈ riemannianBallOf (g i) (p i) R,
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
          ball (p (φ i)) a ⊆ (j i : N → X (φ i)) '' ball q b) := by
  have : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
    ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
  obtain ⟨A', hA'pos, -, hA'⟩ := exists_uniform_curvature_bound_of_eventual K g hmetric p A hcurv
  exact exists_finite_cheeger_gromov_limit n K hn hK hr hv A' (fun R _ => hA'pos R) g hmetric p
    hvol hA'

/-- **LFR14 with the curvature sign under eventual bounds (T0 + T2).** If the basepoint volume
bound, the ballwise curvature-derivative bounds and the sectional bounds `sec ≥ -ηᵢ` on
`B(pᵢ, Lᵢ)` hold only eventually (the curvature-derivative threshold depending on the radius),
the package of `exists_finite_cheeger_gromov_limit_with_nonneg_sectional` holds. -/
theorem exists_finite_cheeger_gromov_limit_with_nonneg_sectional_of_eventual_bounds
    (n K : ℕ) (hn : 2 ≤ n) (hK : 3 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ)
    {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (X i)]
    [∀ i, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (X i)]
    [∀ i, SigmaCompactSpace (X i)]
    [∀ i, T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i))]
    [∀ i, CompleteSpace (X i)] [∀ i, ConnectedSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i)
    (hvol : ∀ᶠ i in atTop, ENNReal.ofReal v ≤ riemannianVolumeMeasure
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i) (g i) (riemannianBallOf (g i) (p i) r))
    (hcurv : ∀ R > 0, ∀ᶠ i in atTop, ∀ k ≤ K, ∀ y ∈ riemannianBallOf (g i) (p i) R,
      curvDerivNorm k (g i) y ≤ A R)
    {η L : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0)) (hL : Tendsto L atTop atTop)
    (hsec : ∀ᶠ i in atTop, ∀ y ∈ riemannianBallOf (g i) (p i) (L i),
      SectionalBoundedBelowAt (g i) y (-η i)) :
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
        (∀ (x : N) (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
          0 ≤ G.sectionalCurvature x v w) := by
  have : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
    ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
  obtain ⟨A', hA'pos, -, hA'⟩ := exists_uniform_curvature_bound_of_eventual K g hmetric p A hcurv
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hvol.and hsec)
  have hshift : Tendsto (fun i : ℕ => i + N₀) atTop atTop := tendsto_add_atTop_nat N₀
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist,
      hcov, hsecG⟩ := exists_finite_cheeger_gromov_limit_with_nonneg_sectional n K hn hK hr hv A'
    (fun R _ => hA'pos R) (X := fun i => X (i + N₀)) (fun i => g (i + N₀))
    (fun i => hmetric (i + N₀)) (fun i => p (i + N₀))
    (fun i => (hN₀ (i + N₀) (Nat.le_add_left N₀ i)).1)
    (fun R hR i => hA' R hR (i + N₀)) (hη.comp hshift) (hL.comp hshift)
    (fun i => (hN₀ (i + N₀) (Nat.le_add_left N₀ i)).2)
  exact ⟨fun i => φ i + N₀, fun a b hab => Nat.add_lt_add_right (hφ hab) N₀, N, mN, cN, hMN, G,
    q, j, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist, hcov, hsecG⟩

/-- **LFR14 oriented, with the curvature sign, under eventual bounds (T1 + T2).** The oriented
version of `exists_finite_cheeger_gromov_limit_with_nonneg_sectional_of_eventual_bounds`: for
oriented sources `o i`, there is moreover an orientation `oN` of the limit that every `j i`
eventually preserves on its whole source (T1). -/
theorem exists_finite_cheeger_gromov_limit_oriented_with_nonneg_sectional_of_eventual_bounds
    (n K : ℕ) (hn : 2 ≤ n) (hK : 3 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ)
    {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (X i)]
    [∀ i, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (X i)]
    [∀ i, SigmaCompactSpace (X i)]
    [∀ i, T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i))]
    [∀ i, CompleteSpace (X i)] [∀ i, ConnectedSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i)
    (o : ∀ i, ManifoldOrientation 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i) n)
    (hvol : ∀ᶠ i in atTop, ENNReal.ofReal v ≤ riemannianVolumeMeasure
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i) (g i) (riemannianBallOf (g i) (p i) r))
    (hcurv : ∀ R > 0, ∀ᶠ i in atTop, ∀ k ≤ K, ∀ y ∈ riemannianBallOf (g i) (p i) R,
      curvDerivNorm k (g i) y ≤ A R)
    {η L : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0)) (hL : Tendsto L atTop atTop)
    (hsec : ∀ᶠ i in atTop, ∀ y ∈ riemannianBallOf (g i) (p i) (L i),
      SectionalBoundedBelowAt (g i) y (-η i)) :
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
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N (X (φ i)) K)
        (oN : ManifoldOrientation 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N n),
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
        (∀ᶠ i in atTop, ∀ (x : N) (hx : x ∈ (j i).source),
          Orientation.map (Fin n)
            (((j i).isLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
                𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (K : ℕ∞ω) hx).mfderivToContinuousLinearEquiv
              (by exact_mod_cast (show K ≠ 0 by omega))).toLinearEquiv (oN.orientation x) =
            (o (φ i)).orientation (j i x)) ∧
        (∀ (x : N) (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
          0 ≤ G.sectionalCurvature x v w) := by
  have : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
    ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
  obtain ⟨A', hA'pos, -, hA'⟩ := exists_uniform_curvature_bound_of_eventual K g hmetric p A hcurv
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hvol.and hsec)
  have hshift : Tendsto (fun i : ℕ => i + N₀) atTop atTop := tendsto_add_atTop_nat N₀
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, oN, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist,
      hcov, hor⟩ := exists_finite_cheeger_gromov_limit_oriented n K hn (by omega) hr hv A'
    (fun R _ => hA'pos R) (X := fun i => X (i + N₀)) (fun i => g (i + N₀))
    (fun i => hmetric (i + N₀)) (fun i => p (i + N₀)) (fun i => o (i + N₀))
    (fun i => (hN₀ (i + N₀) (Nat.le_add_left N₀ i)).1)
    (fun R hR i => hA' R hR (i + N₀))
  let := mN
  let := cN
  have := hMN
  have hsecG := sectionalCurvature_nonneg_of_finite_comparison hK
    (X := fun i => X (φ i + N₀)) (fun i => g (φ i + N₀)) (fun i => hmetric (φ i + N₀))
    (fun i => p (φ i + N₀)) G q j hpt hexh hconv hdist
    ((hη.comp hshift).comp hφ.tendsto_atTop) ((hL.comp hshift).comp hφ.tendsto_atTop)
    (fun i => (hN₀ (φ i + N₀) (Nat.le_add_left N₀ (φ i))).2)
  exact ⟨fun i => φ i + N₀, fun a b hab => Nat.add_lt_add_right (hφ hab) N₀, N, mN, cN, hMN, G,
    q, j, oN, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist, hcov, hor, hsecG⟩

/-- **LPA02's extraction: eventual bounds give the finite package for EVERY sequence.** Let
`M a` (`a : ι`) be complete connected smooth pointed `n`-manifolds whose bounds hold eventually
along a filter `l`, uniformly in the centre: basepoint volume `≥ v` on every `r`-ball, the bounds
`|∇^k Rm| ≤ A(R)` on every `R`-ball (`k ≤ K`, threshold depending on `R`), and `sec ≥ -η a` on
every `H a`-ball with `η → 0`, `H → ∞` along `l`. Then for EVERY sequence `αᵢ → l` and ANY centres
`pᵢ ∈ M (αᵢ)` the T0 + T2 package holds for `(M (αᵢ), pᵢ)`. -/
theorem exists_finite_cheeger_gromov_limit_of_eventual_family
    (n K : ℕ) (hn : 2 ≤ n) (hK : 3 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ) {ι : Type*} {l : Filter ι}
    {M : ι → Type u} [∀ a, MetricSpace (M a)]
    [∀ a, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M a)]
    [∀ a, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (M a)]
    [∀ a, SigmaCompactSpace (M a)]
    [∀ a, T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M a))]
    [∀ a, CompleteSpace (M a)] [∀ a, ConnectedSpace (M a)]
    (gM : ∀ a, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M a))
    (hmetric : ∀ a x y, riemannianEDistOf (gM a) x y = ENNReal.ofReal (dist x y))
    (hvol : ∀ᶠ a in l, ∀ x : M a, ENNReal.ofReal v ≤
      riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M a) (gM a)
        (riemannianBallOf (gM a) x r))
    (hcurv : ∀ R > 0, ∀ᶠ a in l, ∀ x : M a, ∀ k ≤ K, ∀ y ∈ riemannianBallOf (gM a) x R,
      curvDerivNorm k (gM a) y ≤ A R)
    {η H : ι → ℝ} (hη : Tendsto η l (𝓝 0)) (hH : Tendsto H l atTop)
    (hsec : ∀ᶠ a in l, ∀ x : M a, ∀ y ∈ riemannianBallOf (gM a) x (H a),
      SectionalBoundedBelowAt (gM a) y (-η a))
    (α : ℕ → ι) (hα : Tendsto α atTop l) (p : ∀ i, M (α i)) :
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
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N (M (α (φ i))) K),
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
            (fun i => pullbackMetricCoefficients (gM (α (φ i)))
              ((j i : N → M (α (φ i))) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm))
            (chartCoeff G x)) ∧
        (∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
          |dist (j i x) (j i y) - dist x y| < ε) ∧
        (∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
          ball (p (φ i)) a ⊆ (j i : N → M (α (φ i))) '' ball q b) ∧
        (∀ (x : N) (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
          0 ≤ G.sectionalCurvature x v w) :=
  exists_finite_cheeger_gromov_limit_with_nonneg_sectional_of_eventual_bounds n K hn hK hr hv A
    (X := fun i => M (α i)) (fun i => gM (α i)) (fun i => hmetric (α i)) p
    ((hα.eventually hvol).mono fun i hi => hi (p i))
    (fun R hR => (hα.eventually (hcurv R hR)).mono fun i hi => hi (p i))
    (hη.comp hα) (hH.comp hα) ((hα.eventually hsec).mono fun i hi => hi (p i))

/-- **LPA02's extraction, oriented (T1 + T2 for every sequence).** The family form of
`exists_finite_cheeger_gromov_limit_oriented_with_nonneg_sectional_of_eventual_bounds`: for
oriented members `o a`, every sequence `αᵢ → l` with any centres has the T1 + T2 package. -/
theorem exists_finite_cheeger_gromov_limit_oriented_of_eventual_family
    (n K : ℕ) (hn : 2 ≤ n) (hK : 3 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ) {ι : Type*} {l : Filter ι}
    {M : ι → Type u} [∀ a, MetricSpace (M a)]
    [∀ a, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M a)]
    [∀ a, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (M a)]
    [∀ a, SigmaCompactSpace (M a)]
    [∀ a, T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M a))]
    [∀ a, CompleteSpace (M a)] [∀ a, ConnectedSpace (M a)]
    (gM : ∀ a, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M a))
    (hmetric : ∀ a x y, riemannianEDistOf (gM a) x y = ENNReal.ofReal (dist x y))
    (o : ∀ a, ManifoldOrientation 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M a) n)
    (hvol : ∀ᶠ a in l, ∀ x : M a, ENNReal.ofReal v ≤
      riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M a) (gM a)
        (riemannianBallOf (gM a) x r))
    (hcurv : ∀ R > 0, ∀ᶠ a in l, ∀ x : M a, ∀ k ≤ K, ∀ y ∈ riemannianBallOf (gM a) x R,
      curvDerivNorm k (gM a) y ≤ A R)
    {η H : ι → ℝ} (hη : Tendsto η l (𝓝 0)) (hH : Tendsto H l atTop)
    (hsec : ∀ᶠ a in l, ∀ x : M a, ∀ y ∈ riemannianBallOf (gM a) x (H a),
      SectionalBoundedBelowAt (gM a) y (-η a))
    (α : ℕ → ι) (hα : Tendsto α atTop l) (p : ∀ i, M (α i)) :
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
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N (M (α (φ i))) K)
        (oN : ManifoldOrientation 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N n),
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
            (fun i => pullbackMetricCoefficients (gM (α (φ i)))
              ((j i : N → M (α (φ i))) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm))
            (chartCoeff G x)) ∧
        (∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
          |dist (j i x) (j i y) - dist x y| < ε) ∧
        (∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
          ball (p (φ i)) a ⊆ (j i : N → M (α (φ i))) '' ball q b) ∧
        (∀ᶠ i in atTop, ∀ (x : N) (hx : x ∈ (j i).source),
          Orientation.map (Fin n)
            (((j i).isLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
                𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (K : ℕ∞ω) hx).mfderivToContinuousLinearEquiv
              (by exact_mod_cast (show K ≠ 0 by omega))).toLinearEquiv (oN.orientation x) =
            (o (α (φ i))).orientation (j i x)) ∧
        (∀ (x : N) (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
          0 ≤ G.sectionalCurvature x v w) :=
  exists_finite_cheeger_gromov_limit_oriented_with_nonneg_sectional_of_eventual_bounds n K hn hK
    hr hv A (X := fun i => M (α i)) (fun i => gM (α i)) (fun i => hmetric (α i)) p
    (fun i => o (α i)) ((hα.eventually hvol).mono fun i hi => hi (p i))
    (fun R hR => (hα.eventually (hcurv R hR)).mono fun i hi => hi (p i))
    (hη.comp hα) (hH.comp hα) ((hα.eventually hsec).mono fun i hi => hi (p i))

end DifferentialGeometry.CheegerGromovCompactness
