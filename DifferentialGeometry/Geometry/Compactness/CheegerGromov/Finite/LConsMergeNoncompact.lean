import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.QuasiInverse
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.EventualBounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.SplittingLimitMerge

/-!
# The L-CONS merge, noncompact (LFR28 blocker B1)

`lfr16_lcons_merge_Stmt` (build-logs/scratch/F7-LFR11b/LConsMergeStatement.lean) asks for ONE
subsequence and ONE finite Cheeger–Gromov limit carrying at once the L-CONS package (T0), the
curvature sign (T2), and an exact line splitting `e : N ≃ᵢ ℓ²(ℝ × W)` tracked by the SAME
comparison maps. The compact version also asked `W` compact of diameter `≤ D`; LFR28 needs the
NONCOMPACT variant, plus the source coverage of the comparison maps and, for oriented sources,
the limit orientation. Here:

* `exists_coordinate_subsequence_of_comparison_maps` (kernel): pointed comparison maps with
  eventual injectivity, distortion `→ 0` and strict-radius coverage, and Kleiner–Lott splittings
  `Φᵢ` of the targets with errors `δᵢ → 0`, have a subsequence along which the SAME maps track an
  exact product structure `e : N ≃ᵢ ℓ²(ℝ × W)` of the source (`W` proper complete):
  `(Φ ∘ j)_ℝ → e_ℝ` uniformly on bounded sets. Route: L-CONS's quasi-inverses
  (`exists_quasiInverse_of_comparison_maps`, index shift `T`) and
  `exists_product_limit_with_coordinate_pullback` (further subsequence `χ`); the subsequence is
  `χ i + T`.
* `exists_lcons_merge_noncompact`: F7-LFR11c's LFR15 merge
  (`exists_finite_cheeger_gromov_limit_with_nonneg_splitting`, which never assumes `W` compact),
  with the eventual bounds absorbed (`exists_uniform_curvature_bound_of_eventual`, index shift past
  the volume and sectional thresholds), plus the approximate source coverage
  `∀ R ε, ∀ᶠ i, ∀ y ∈ B(p_{φ i}, R), ∃ x ∈ B(q, R + 1), d(j i x, y) < ε`, derived from the exact
  strict-radius coverage `∀ a < b, ∀ᶠ i, B(p_{φ i}, a) ⊆ j i (B(q, b))` (both are in the conclusion).
* `exists_lcons_merge_noncompact_oriented`: the merge cannot be re-used here (its T0 run carries no
  orientation), so the oriented T0 + T2
  (`exists_finite_cheeger_gromov_limit_oriented_with_nonneg_sectional_of_eventual_bounds`) is
  re-indexed along the kernel's subsequence; `oN` is preserved by every late `j i` on its whole
  source (T1); both coverage clauses as above.

Strengthening (recorded): the volume and sectional hypotheses are only required eventually; the
verbatim `∀ i` form is `exists_lcons_merge_noncompact_of_forall_bounds` (Applications).
Compactness of `W` (the compact Stmt) is not used anywhere.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Integral.Measure GC.MetricGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry.Riemannian

universe u w

/-- **Coordinate tracking along a subsequence, for given comparison maps.** If `j i : N → Y i`
are pointed, eventually injective on every ball, with distortion `→ 0` and the strict-radius
coverage, and `Φ i` are Kleiner–Lott `δᵢ`-splittings of `(Y i, p i)` with `δᵢ → 0`, then along a
subsequence `ψ` the source `N` is an exact product `e : N ≃ᵢ ℓ²(ℝ × W)` (`W` proper complete,
`e q = (a, w)`) and `(Φ_{ψ i} ∘ j_{ψ i})_ℝ → e_ℝ` uniformly on bounded sets. -/
theorem exists_coordinate_subsequence_of_comparison_maps {N : Type} [MetricSpace N]
    [ProperSpace N] {Y : ℕ → Type u} [∀ i, MetricSpace (Y i)] (q : N) (p : ∀ i, Y i)
    (j : ∀ i, N → Y i) (hpt : ∀ i, j i q = p i)
    (hinj : ∀ b : ℝ, ∀ᶠ i in atTop, InjOn (j i) (ball q b))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hcov : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop, ball (p i) a ⊆ j i '' ball q b)
    {a : ℝ} {Z : ℕ → Type w} [∀ i, MetricSpace (Z i)] {b : ∀ i, Z i} {δ : ℕ → ℝ}
    (Φ : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 (a, b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ (W : Type) (m : MetricSpace W), letI := m
        ∃ (w : W), ProperSpace W ∧ CompleteSpace W ∧
          ∃ e : N ≃ᵢ WithLp 2 (ℝ × W), e q = WithLp.toLp 2 (a, w) ∧
            ∀ C : Set N, Bornology.IsBounded C →
              TendstoUniformlyOn (fun i x => ((Φ (ψ i)).toFun (j (ψ i) x)).fst)
                (fun x => (e x).fst) atTop C := by
  obtain ⟨T, R, ε, hR, hε, h, hdom, hinv⟩ :=
    exists_quasiInverse_of_comparison_maps q p j hpt hinj hdist hcov
  have hround : ∀ C : Set N, Bornology.IsBounded C →
      TendstoUniformlyOn (fun i x => (h i).extendToWholeSpace (j (i + T) x)) id atTop C := by
    intro C hC
    refine Metric.tendstoUniformlyOn_iff.mpr fun η hη => ?_
    filter_upwards [hinv C hC] with i hi x hx
    rw [hi x hx, id_eq, dist_self]
    exact hη
  obtain ⟨W, m, w, χ, hχ, hWp, hWc, -, -, e, he, hcoord, -⟩ :=
    exists_product_limit_with_coordinate_pullback h hR hε (fun i => Φ (i + T))
      (hδ.comp (tendsto_add_atTop_nat T)) (fun i => j (i + T)) hdom hround
  exact ⟨fun i => χ i + T, hχ.add_const T, W, m, w, hWp, hWc, e, he, hcoord⟩

/-- **B1 (unoriented).** `lfr16_lcons_merge_Stmt` without `CompactSpace W` and `dist ≤ D`, plus
the source coverage, on ONE subsequence; volume and sectional bounds only eventually. -/
theorem exists_lcons_merge_noncompact
    (K : ℕ) (hK : 4 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v) (A : ℝ → ℝ)
    {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (X i)]
    [∀ i, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (X i)]
    [∀ i, SigmaCompactSpace (X i)]
    [∀ i, T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (X i))]
    [∀ i, CompleteSpace (X i)] [∀ i, ConnectedSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i)
    (hvol : ∀ᶠ i in atTop, ENNReal.ofReal v ≤ riemannianVolumeMeasure
      𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (X i) (g i) (riemannianBallOf (g i) (p i) r))
    (hcurv : ∀ R > 0, ∀ᶠ i in atTop, ∀ k ≤ K, ∀ y ∈ riemannianBallOf (g i) (p i) R,
      curvDerivNorm k (g i) y ≤ A R)
    {η L : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0)) (hL : Tendsto L atTop atTop)
    (hsec : ∀ᶠ i in atTop, ∀ y ∈ riemannianBallOf (g i) (p i) (L i),
      SectionalBoundedBelowAt (g i) y (-η i))
    {a : ℝ} {Z : ℕ → Type w} [∀ i, MetricSpace (Z i)] {b : ∀ i, Z i} {δ : ℕ → ℝ}
    (Φ : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 (a, b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ (N : Type) (mN : MetricSpace N) (cN : ChartedSpace (EuclideanSpace ℝ (Fin 3)) N),
      letI := mN
      letI := cN
      ∃ (_ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ N)
        (G : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ((K - 1 : ℕ) : ℕ∞ω)
          (EuclideanSpace ℝ (Fin 3))
          (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) : N → Type _))
        (q : N)
        (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
          𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) N (X (φ i)) K),
        ProperSpace N ∧ ConnectedSpace N ∧
        (letI : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) x) :=
          ⟨G.toRiemannianMetric⟩
         IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) N) ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        (∀ i, q ∈ (j i).source ∧ j i q = p (φ i)) ∧
        (∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source) ∧
        (∀ (x : N) (L' : Set (EuclideanSpace ℝ (Fin 3))), IsCompact L' →
          L' ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) x).target →
          MapCPConvergenceOn L' (K - 1)
            (fun i => pullbackMetricCoefficients (g (φ i))
              ((j i : N → X (φ i)) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) x).symm))
            (chartCoeff G x)) ∧
        (∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
          |dist (j i x) (j i y) - dist x y| < ε) ∧
        (∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
          ball (p (φ i)) a ⊆ (j i : N → X (φ i)) '' ball q b) ∧
        (∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ y ∈ ball (p (φ i)) R,
          ∃ x ∈ ball q (R + 1), dist (j i x) y < ε) ∧
        (∀ (x : N) (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) x),
          0 ≤ G.sectionalCurvature x v w) ∧
        ∃ (W : Type) (m : MetricSpace W), letI := m
          ∃ (w : W), ProperSpace W ∧ CompleteSpace W ∧
            ∃ e : N ≃ᵢ WithLp 2 (ℝ × W), e q = WithLp.toLp 2 (a, w) ∧
              ∀ C : Set N, Bornology.IsBounded C →
                TendstoUniformlyOn (fun i x => ((Φ (φ i)).toFun (j i x)).fst)
                  (fun x => (e x).fst) atTop C := by
  have : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :=
    ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
  obtain ⟨A', hA'pos, -, hA'⟩ := exists_uniform_curvature_bound_of_eventual K g hmetric p A hcurv
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hvol.and hsec)
  have hshift : Tendsto (fun i : ℕ => i + N₀) atTop atTop := tendsto_add_atTop_nat N₀
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist,
      hcov, hsecG, W, m, w, hWp, hWc, -, e, he, hcoord⟩ :=
    exists_finite_cheeger_gromov_limit_with_nonneg_splitting 3 K (by norm_num) (by omega) hr hv
      A' (fun R _ => hA'pos R) (X := fun i => X (i + N₀)) (fun i => g (i + N₀))
      (fun i => hmetric (i + N₀)) (fun i => p (i + N₀))
      (fun i => (hN₀ (i + N₀) (Nat.le_add_left N₀ i)).1) (fun R hR i => hA' R hR (i + N₀))
      (hη.comp hshift) (hL.comp hshift) (fun i => (hN₀ (i + N₀) (Nat.le_add_left N₀ i)).2)
      (fun i => Φ (i + N₀)) (hδ.comp hshift)
  refine ⟨fun i => φ i + N₀, fun a b hab => Nat.add_lt_add_right (hφ hab) N₀, N, mN, cN, hMN, G,
    q, j, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist, hcov, ?_, hsecG, W, m, w, hWp, hWc,
    e, he, hcoord⟩
  intro R ε hε
  rcases le_or_gt R 0 with hR0 | hR0
  · refine Eventually.of_forall fun i y hy => ?_
    exact absurd (mem_ball.mp hy) (not_lt.mpr (hR0.trans dist_nonneg))
  · filter_upwards [hcov R (R + 1) hR0 (by linarith)] with i hi y hy
    obtain ⟨x, hx, hxy⟩ := hi hy
    exact ⟨x, hx, by rw [hxy, dist_self]; exact hε⟩

/-- **B1 (oriented).** The same for oriented sources: moreover an orientation `oN` of the limit
that every `j i` eventually preserves on its whole source. -/
theorem exists_lcons_merge_noncompact_oriented
    (K : ℕ) (hK : 4 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v) (A : ℝ → ℝ)
    {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (X i)]
    [∀ i, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (X i)]
    [∀ i, SigmaCompactSpace (X i)]
    [∀ i, T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (X i))]
    [∀ i, CompleteSpace (X i)] [∀ i, ConnectedSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i)
    (o : ∀ i, ManifoldOrientation (𝓡 3) (X i) 3)
    (hvol : ∀ᶠ i in atTop, ENNReal.ofReal v ≤ riemannianVolumeMeasure
      𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (X i) (g i) (riemannianBallOf (g i) (p i) r))
    (hcurv : ∀ R > 0, ∀ᶠ i in atTop, ∀ k ≤ K, ∀ y ∈ riemannianBallOf (g i) (p i) R,
      curvDerivNorm k (g i) y ≤ A R)
    {η L : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0)) (hL : Tendsto L atTop atTop)
    (hsec : ∀ᶠ i in atTop, ∀ y ∈ riemannianBallOf (g i) (p i) (L i),
      SectionalBoundedBelowAt (g i) y (-η i))
    {a : ℝ} {Z : ℕ → Type w} [∀ i, MetricSpace (Z i)] {b : ∀ i, Z i} {δ : ℕ → ℝ}
    (Φ : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 (a, b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ (N : Type) (mN : MetricSpace N) (cN : ChartedSpace (EuclideanSpace ℝ (Fin 3)) N),
      letI := mN
      letI := cN
      ∃ (_ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ N)
        (G : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ((K - 1 : ℕ) : ℕ∞ω)
          (EuclideanSpace ℝ (Fin 3))
          (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) : N → Type _))
        (q : N)
        (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
          𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) N (X (φ i)) K)
        (oN : ManifoldOrientation (𝓡 3) N 3),
        ProperSpace N ∧ ConnectedSpace N ∧
        (letI : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) x) :=
          ⟨G.toRiemannianMetric⟩
         IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) N) ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        (∀ i, q ∈ (j i).source ∧ j i q = p (φ i)) ∧
        (∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source) ∧
        (∀ (x : N) (L' : Set (EuclideanSpace ℝ (Fin 3))), IsCompact L' →
          L' ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) x).target →
          MapCPConvergenceOn L' (K - 1)
            (fun i => pullbackMetricCoefficients (g (φ i))
              ((j i : N → X (φ i)) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) x).symm))
            (chartCoeff G x)) ∧
        (∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
          |dist (j i x) (j i y) - dist x y| < ε) ∧
        (∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
          ball (p (φ i)) a ⊆ (j i : N → X (φ i)) '' ball q b) ∧
        (∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ y ∈ ball (p (φ i)) R,
          ∃ x ∈ ball q (R + 1), dist (j i x) y < ε) ∧
        (∀ᶠ i in atTop, ∀ (x : N) (hx : x ∈ (j i).source),
          Orientation.map (Fin 3)
            (((j i).isLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
                𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (K : ℕ∞ω) hx).mfderivToContinuousLinearEquiv
              (by exact_mod_cast (show K ≠ 0 by omega))).toLinearEquiv (oN.orientation x) =
            (o (φ i)).orientation (j i x)) ∧
        (∀ (x : N) (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) x),
          0 ≤ G.sectionalCurvature x v w) ∧
        ∃ (W : Type) (m : MetricSpace W), letI := m
          ∃ (w : W), ProperSpace W ∧ CompleteSpace W ∧
            ∃ e : N ≃ᵢ WithLp 2 (ℝ × W), e q = WithLp.toLp 2 (a, w) ∧
              ∀ C : Set N, Bornology.IsBounded C →
                TendstoUniformlyOn (fun i x => ((Φ (φ i)).toFun (j i x)).fst)
                  (fun x => (e x).fst) atTop C := by
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, oN, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist,
      hcov, hor, hsecG⟩ :=
    exists_finite_cheeger_gromov_limit_oriented_with_nonneg_sectional_of_eventual_bounds 3 K
      (by norm_num) (by omega) hr hv A g hmetric p o hvol hcurv hη hL hsec
  let := mN
  let := cN
  have := hprop
  have hinj : ∀ b : ℝ, ∀ᶠ i in atTop, InjOn (j i : N → X (φ i)) (ball q b) := fun b =>
    (hexh _ (isCompact_closedBall q b)).mono fun i hi =>
      (j i).toPartialEquiv.injOn.mono (ball_subset_closedBall.trans hi)
  obtain ⟨ψ, hψ, W, m, w, hWp, hWc, e, he, hcoord⟩ :=
    exists_coordinate_subsequence_of_comparison_maps q (fun i => p (φ i))
      (fun i => (j i : N → X (φ i))) (fun i => (hpt i).2) hinj hdist hcov (fun i => Φ (φ i))
      (hδ.comp hφ.tendsto_atTop)
  have hψt : Tendsto ψ atTop atTop := hψ.tendsto_atTop
  refine ⟨fun i => φ (ψ i), hφ.comp hψ, N, mN, cN, hMN, G, q, fun i => j (ψ i), oN, hprop,
    hconn, hRiem, hGH.subsequence hψ, fun i => hpt (ψ i), fun C hC => hψt.eventually (hexh C hC),
    fun x L' hL hLt => (hconv x L' hL hLt).comp_tendsto_atTop hψt,
    fun R ε hε => hψt.eventually (hdist R ε hε),
    fun a' b' ha hab => hψt.eventually (hcov a' b' ha hab), ?_, hψt.eventually hor, hsecG, W, m, w, hWp,
    hWc, e, he, hcoord⟩
  intro R ε hε
  rcases le_or_gt R 0 with hR0 | hR0
  · refine Eventually.of_forall fun i y hy => ?_
    exact absurd (mem_ball.mp hy) (not_lt.mpr (hR0.trans dist_nonneg))
  · filter_upwards [hψt.eventually (hcov R (R + 1) hR0 (by linarith))] with i hi y hy
    obtain ⟨x, hx, hxy⟩ := hi hy
    exact ⟨x, hx, by rw [hxy, dist_self]; exact hε⟩


end DifferentialGeometry.CheegerGromovCompactness
