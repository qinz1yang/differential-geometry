import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.SplittingLimitMerge

/-!
# The oriented L-CONS merge

The oriented case of LFR15 and LFR16 (oriented sources `o i`): the oriented limit of LFR14
(`exists_finite_cheeger_gromov_limit_oriented`: T0's package, an orientation `oN` of the limit and
eventual orientation preservation by the actual maps `jᵢ`) carries, on ONE further subsequence,
the exact product of LFR15's splittings with coordinate tracking, `sec ≥ 0`, and (for residual
diameter `≤ D`) a compact residual factor. Everything beyond the oriented T0 is post hoc:
* `exists_coordinate_pullback_of_comparison_maps`: for ANY comparison maps with pointedness,
  injectivity on balls, distortion `→ 0` and strict-radius coverage (T0's clauses), LFR15's
  splittings `Φᵢ` give an exact product `e : N ≃ᵢ F × W` with `(Φ ∘ j)_F → e_F` along a
  subsequence (the argument of `exists_finite_cheeger_gromov_limit_with_coordinate_pullback`,
  isolated from T0);
* `exists_finite_cheeger_gromov_limit_oriented_with_nonneg_splitting` (uniform bounds) and
  `exists_finite_cheeger_gromov_limit_oriented_with_compact_splitting` (eventual bounds,
  residual diameter `≤ D`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Integral.Measure GC.MetricGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry.Riemannian

universe u v w

/-- **Coordinate pullback for arbitrary comparison maps.** -/
theorem exists_coordinate_pullback_of_comparison_maps {N : Type} [MetricSpace N] [ProperSpace N]
    {Y : ℕ → Type u} [∀ i, MetricSpace (Y i)] (q : N) (p : ∀ i, Y i) (j : ∀ i, N → Y i)
    (hpt : ∀ i, j i q = p i)
    (hinj : ∀ b : ℝ, ∀ᶠ i in atTop, InjOn (j i) (ball q b))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hcov : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop, ball (p i) a ⊆ j i '' ball q b)
    {F : Type v} [MetricSpace F] [ProperSpace F] {a : F} {Z : ℕ → Type w}
    [∀ i, MetricSpace (Z i)] {b : ∀ i, Z i} {δ : ℕ → ℝ}
    (Φ : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 (a, b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    ∃ χ : ℕ → ℕ, StrictMono χ ∧
      ∃ (W : Type) (m : MetricSpace W), letI := m
        ∃ (w : W), ProperSpace W ∧ CompleteSpace W ∧
          PointedGHConverges (fun i => b (χ i)) w ∧
          ∃ e : N ≃ᵢ WithLp 2 (F × W), e q = WithLp.toLp 2 (a, w) ∧
            ∀ C : Set N, Bornology.IsBounded C →
              TendstoUniformlyOn (fun i x => ((Φ (χ i)).toFun (j (χ i) x)).fst)
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
  obtain ⟨W, m, w, χ, hχ, hWp, hWc, hzW, -, e, he, hcoord, -⟩ :=
    exists_product_limit_with_coordinate_pullback h hR hε (fun i => Φ (i + T))
      (hδ.comp (tendsto_add_atTop_nat T)) (fun i => j (i + T)) hdom hround
  exact ⟨fun i => χ i + T, hχ.add_const T, W, m, w, hWp, hWc, hzW, e, he, hcoord⟩

/-- **The oriented LFR15 merge.** As `exists_finite_cheeger_gromov_limit_with_nonneg_splitting`, for
oriented sources: the limit carries an orientation `oN` preserved eventually by the actual maps. -/
theorem exists_finite_cheeger_gromov_limit_oriented_with_nonneg_splitting
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
    (o : ∀ i, ManifoldOrientation 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i) n)
    (hvol : ∀ i, ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (X i) (g i) (riemannianBallOf (g i) (p i) r))
    (hcurv : ∀ R > 0, ∀ i, ∀ k ≤ K, ∀ y ∈ riemannianBallOf (g i) (p i) R,
      curvDerivNorm k (g i) y ≤ A R)
    {η L : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0)) (hL : Tendsto L atTop atTop)
    (hsec : ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i) (L i),
      SectionalBoundedBelowAt (g i) y (-η i))
    {F : Type v} [MetricSpace F] [ProperSpace F] {a : F} {Z : ℕ → Type w}
    [∀ i, MetricSpace (Z i)] {b : ∀ i, Z i} {δ : ℕ → ℝ}
    (Φ : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 (a, b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) :
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
        (∀ (x : N) (L' : Set (EuclideanSpace ℝ (Fin n))), IsCompact L' →
          L' ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).target →
          MapCPConvergenceOn L' (K - 1)
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
          0 ≤ G.sectionalCurvature x v w) ∧
        ∃ (W : Type) (m : MetricSpace W), letI := m
          ∃ (w : W), ProperSpace W ∧ CompleteSpace W ∧
            PointedGHConverges (fun i => b (φ i)) w ∧
            ∃ e : N ≃ᵢ WithLp 2 (F × W), e q = WithLp.toLp 2 (a, w) ∧
              ∀ C : Set N, Bornology.IsBounded C →
                TendstoUniformlyOn (fun i x => ((Φ (φ i)).toFun (j i x)).fst)
                  (fun x => (e x).fst) atTop C := by
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, oN, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist,
      hcov, hor⟩ :=
    exists_finite_cheeger_gromov_limit_oriented n K hn (by omega) hr hv A hA g hmetric p o hvol
      hcurv
  let := mN
  let := cN
  have := hMN
  have := hprop
  have hinj : ∀ b : ℝ, ∀ᶠ i in atTop, InjOn (j i : N → X (φ i)) (ball q b) := fun b =>
    (hexh _ (isCompact_closedBall q b)).mono fun i hi =>
      (j i).toPartialEquiv.injOn.mono (ball_subset_closedBall.trans hi)
  obtain ⟨χ, hχ, W, m, w, hWp, hWc, hzW, e, he, hcoord⟩ :=
    exists_coordinate_pullback_of_comparison_maps q (fun i => p (φ i))
      (fun i => (j i : N → X (φ i))) (fun i => (hpt i).2) hinj hdist hcov (fun i => Φ (φ i))
      (hδ.comp hφ.tendsto_atTop)
  have hsecG := sectionalCurvature_nonneg_of_finite_comparison hK (X := fun i => X (φ i))
    (fun i => g (φ i)) (fun i => hmetric (φ i)) (fun i => p (φ i)) G q j hpt hexh hconv hdist
    (hη.comp hφ.tendsto_atTop) (hL.comp hφ.tendsto_atTop) (fun i => hsec (φ i))
  have hT : Tendsto χ atTop atTop := hχ.tendsto_atTop
  exact ⟨fun i => φ (χ i), hφ.comp hχ, N, mN, cN, hMN, G, q, fun i => j (χ i), oN, hprop, hconn,
    hRiem, hGH.subsequence hχ, fun i => hpt (χ i), fun C hC => hT.eventually (hexh C hC),
    fun x L' hL' hL't => (hconv x L' hL' hL't).comp_tendsto_atTop hT,
    fun R ε hε => hT.eventually (hdist R ε hε), fun a b ha hab => hT.eventually (hcov a b ha hab),
    hT.eventually hor, hsecG, W, m, w, hWp, hWc, hzW, e, he, hcoord⟩

/-- **The oriented LFR16 merge.** As `exists_finite_cheeger_gromov_limit_with_compact_splitting`, for
oriented sources: the limit carries an orientation `oN` preserved eventually by the actual maps. -/
theorem exists_finite_cheeger_gromov_limit_oriented_with_compact_splitting
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
    (hvol : ∀ i, ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (X i) (g i) (riemannianBallOf (g i) (p i) r))
    (hcurv : ∀ R > 0, ∀ᶠ i in atTop, ∀ k ≤ K, ∀ y ∈ riemannianBallOf (g i) (p i) R,
      curvDerivNorm k (g i) y ≤ A R)
    {η L : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0)) (hL : Tendsto L atTop atTop)
    (hsec : ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i) (L i),
      SectionalBoundedBelowAt (g i) y (-η i))
    {F : Type v} [MetricSpace F] [ProperSpace F] {a : F} {Z : ℕ → Type w}
    [∀ i, MetricSpace (Z i)] {b : ∀ i, Z i} {δ : ℕ → ℝ}
    (Φ : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 (a, b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) {D : ℝ} (hD : ∀ i, ∀ x y : Z i, dist x y ≤ D) :
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
        (∀ (x : N) (L' : Set (EuclideanSpace ℝ (Fin n))), IsCompact L' →
          L' ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).target →
          MapCPConvergenceOn L' (K - 1)
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
          0 ≤ G.sectionalCurvature x v w) ∧
        ∃ (W : Type) (m : MetricSpace W), letI := m
          ∃ (w : W), ProperSpace W ∧ CompactSpace W ∧ (∀ x y : W, dist x y ≤ D) ∧
            PointedGHConverges (fun i => b (φ i)) w ∧
            ∃ e : N ≃ᵢ WithLp 2 (F × W), e q = WithLp.toLp 2 (a, w) ∧
              ∀ C : Set N, Bornology.IsBounded C →
                TendstoUniformlyOn (fun i x => ((Φ (φ i)).toFun (j i x)).fst)
                  (fun x => (e x).fst) atTop C := by
  have : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
    ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
  obtain ⟨A', hA'pos, -, hA'⟩ := exists_uniform_curvature_bound_of_eventual K g hmetric p A hcurv
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, oN, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist,
      hcov, hor, hsecG, W, m, w, hWp, hWc, hzW, e, he, hcoord⟩ :=
    exists_finite_cheeger_gromov_limit_oriented_with_nonneg_splitting n K hn hK hr hv A'
      (fun R _ => hA'pos R) g hmetric p o hvol hA' hη hL hsec Φ hδ
  let := m
  have hdiam : ∀ x y : W, dist x y ≤ D := hzW.dist_le_of_uniform_bound (fun i => hD (φ i))
  have hcpt : CompactSpace W := hzW.compactSpace_of_uniform_bound (fun i => hD (φ i))
  exact ⟨φ, hφ, N, mN, cN, hMN, G, q, j, oN, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist,
    hcov, hor, hsecG, W, m, w, hWp, hcpt, hdiam, hzW, e, he, hcoord⟩

end DifferentialGeometry.CheegerGromovCompactness
