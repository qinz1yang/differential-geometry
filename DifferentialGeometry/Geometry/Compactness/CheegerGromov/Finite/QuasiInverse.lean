import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.CheegerGromovLimit
import DifferentialGeometry.Geometry.Metric.Approximation.ProductCoordinatePullback
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Composition
import DifferentialGeometry.Topology.Sequences.EventualDiagonal

/-!
# LFR14 consumer adapter (a): a quasi-inverse of the SAME comparison maps

The external review of the LFR14 design (`build-logs/inbox/review-lfr14.md` §2 on LFR15, item 5(a)
of the dispositions): the coordinate tracking of LFR15 (A:26086) must use approximations paired with
the ACTUAL maps `jᵢ` of LFR14, not an unrelated family taken from `PointedGHConverges`. T0 hides
its own approximations, so they are rebuilt from T0's clauses: pointedness, distortion `→ 0`,
injectivity on the sources and the strict-radius coverage give, on buffer balls, an EXACT left
inverse `hᵢ` of `jᵢ`, which is a pointed ball approximation `X_{φ i} ⊇ B(pᵢ,Rᵢ) → N` with
`Rᵢ → ∞`, `εᵢ → 0`.

* `exists_pointedBallApprox_of_injOn_of_distortion`: one map; the inverse of an injective map with
  distortion `< ε` on `B(q,b)` whose image covers `B̄(p,R)` is a pointed ball approximation.
* `exists_quasiInverse_of_comparison_maps`: a sequence; after a finite index shift `T` (for early
  indices no pointed ball approximation need exist at any scale) the inverses form a sequence with
  `Rᵢ → ∞`, `εᵢ → 0`, `jᵢ` maps bounded sets into the balls, and `hᵢ ∘ jᵢ = id` eventually on every
  bounded set. Diagonal: `Filter.exists_tendsto_atTop_eventually_diagonal`.
* `exists_finite_cheeger_gromov_limit_with_quasiInverse`: T0 (re-indexed by the shift) together with
  such quasi-inverses of its own maps `j i`.
* `exists_finite_cheeger_gromov_limit_with_coordinate_pullback` (LFR15, coordinate clause): T0's
  limit `N` with LFR15's splittings `Φᵢ` of the sources is an exact product `F × W`, and
  `(Φᵢ ∘ jᵢ)_F → e_F` uniformly on bounded sets for the SAME `jᵢ`. This removes the DATA arguments
  (`f`, `j`, `hdom`, `hround`) of `exists_product_limit_with_coordinate_pullback`.
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

/-- **Inverse of an almost isometric injective map.** If `f q = p`, `f` is injective with
distortion `< ε` on `B(q,b)` and `f (B(q,b)) ⊇ B̄(p,R)`, with `0 < ε < R` and `R + ε ≤ b`, then the
inverse of `f` on `B̄(p,R)` is a pointed ball approximation `B̄(p,R) → (N,q)` with error `ε`, and it
is an exact left inverse of `f` on `B(q,b)`. -/
theorem exists_pointedBallApprox_of_injOn_of_distortion
    {N Y : Type*} [MetricSpace N] [MetricSpace Y] {q : N} {p : Y} {f : N → Y} (hfq : f q = p)
    {R ε b : ℝ} (hε : 0 < ε) (hεR : ε < R) (hRb : R + ε ≤ b)
    (hinj : InjOn f (ball q b))
    (hdist : ∀ x ∈ ball q b, ∀ y ∈ ball q b, |dist (f x) (f y) - dist x y| < ε)
    (hcov : closedBall p R ⊆ f '' ball q b) :
    ∃ h : PointedBallApprox p q R ε,
      ∀ x ∈ ball q b, ∀ hx : dist (f x) p ≤ R, h.toFun ⟨f x, hx⟩ = x := by
  have hpre : ∀ y : BallCarrier p R, ∃ x ∈ ball q b, f x = y.val := fun y =>
    hcov (mem_closedBall.mpr y.2)
  choose s hs hfs using hpre
  have hqb : q ∈ ball q b := mem_ball_self (by linarith)
  have hspec : ∀ x ∈ ball q b, ∀ hx : dist (f x) p ≤ R, s ⟨f x, hx⟩ = x := fun x hx hfx =>
    hinj (hs _) hx (hfs _)
  have hfqR : dist (f q) p ≤ R := by rw [hfq, dist_self]; linarith
  refine ⟨⟨hε, hεR, s, ?_, ?_, ?_⟩, hspec⟩
  · calc s _ = s ⟨f q, hfqR⟩ := congrArg s (Subtype.ext hfq.symm)
      _ = q := hspec q hqb hfqR
  · intro y y'
    have h := hdist (s y) (hs y) (s y') (hs y')
    rw [hfs, hfs] at h
    rw [abs_sub_comm]
    exact h
  · intro z hz
    have hzb : z ∈ ball q b := mem_ball.mpr (by linarith)
    have hfz : dist (f z) p ≤ R := by
      have h := hdist z hzb q hqb
      rw [hfq] at h
      linarith [(abs_lt.mp h).2]
    refine ⟨⟨f z, hfz⟩, ?_⟩
    rw [hspec z hzb hfz, dist_self]
    exact hε

/-- **Quasi-inverses of comparison maps.** Let `j i : N → Y i` be pointed (`j i q = p i`),
eventually injective on every ball `B(q,b)`, with distortion `→ 0` on every ball and the
strict-radius coverage `B(pᵢ,a) ⊆ jᵢ(B(q,b))` (`a < b`) eventually. Then after an index shift `T`
there are pointed ball approximations `h i : B̄(p_{i+T}, Rᵢ) → (N,q)` with `Rᵢ → ∞`, `εᵢ → 0`,
such that on every bounded set eventually `j_{i+T}` lands in `B̄(p_{i+T}, Rᵢ)` and
`hᵢ ∘ j_{i+T} = id`. -/
theorem exists_quasiInverse_of_comparison_maps
    {N : Type*} [MetricSpace N] {Y : ℕ → Type*} [∀ i, MetricSpace (Y i)]
    (q : N) (p : ∀ i, Y i) (j : ∀ i, N → Y i) (hpt : ∀ i, j i q = p i)
    (hinj : ∀ b : ℝ, ∀ᶠ i in atTop, InjOn (j i) (ball q b))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hcov : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop, ball (p i) a ⊆ j i '' ball q b) :
    ∃ T : ℕ, ∃ R ε : ℕ → ℝ, Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
      ∃ h : ∀ i, PointedBallApprox (p (i + T)) q (R i) (ε i),
        (∀ K : Set N, Bornology.IsBounded K →
          ∀ᶠ i in atTop, ∀ x ∈ K, dist (j (i + T) x) (p (i + T)) ≤ R i) ∧
        (∀ K : Set N, Bornology.IsBounded K →
          ∀ᶠ i in atTop, ∀ x ∈ K, (h i).extendToWholeSpace (j (i + T) x) = x) := by
  -- the stage predicate at level `m`
  let P : ℕ → ℕ → Prop := fun m i =>
    InjOn (j i) (ball q ((m : ℝ) + 3)) ∧
    (∀ x ∈ ball q ((m : ℝ) + 3), ∀ y ∈ ball q ((m : ℝ) + 3),
      |dist (j i x) (j i y) - dist x y| < 1 / ((m : ℝ) + 2)) ∧
    ball (p i) ((m : ℝ) + 2) ⊆ j i '' ball q ((m : ℝ) + 3)
  have hP : ∀ m, ∀ᶠ i in atTop, P m i := fun m =>
    (hinj _).and ((hdist _ _ (by positivity)).and (hcov _ _ (by positivity) (by linarith)))
  obtain ⟨s, hs, hPs⟩ := Filter.exists_tendsto_atTop_eventually_diagonal hP
  obtain ⟨T, hT⟩ := eventually_atTop.mp hPs
  have hPi : ∀ i, P (s (i + T)) (i + T) := fun i => hT (i + T) (Nat.le_add_left T i)
  have hst : Tendsto (fun i => s (i + T)) atTop atTop := hs.comp (tendsto_add_atTop_nat T)
  let m : ℕ → ℝ := fun i => (s (i + T) : ℝ)
  have hm0 : ∀ i, 0 ≤ m i := fun i => Nat.cast_nonneg _
  have hex : ∀ i, ∃ h : PointedBallApprox (p (i + T)) q (m i + 1) (1 / (m i + 2)),
      ∀ x ∈ ball q (m i + 3), ∀ hx : dist (j (i + T) x) (p (i + T)) ≤ m i + 1,
        h.toFun ⟨j (i + T) x, hx⟩ = x := by
    intro i
    obtain ⟨hi1, hi2, hi3⟩ := hPi i
    have hm := hm0 i
    have hlt : 1 / (m i + 2) < m i + 1 := by
      rw [div_lt_iff₀ (by linarith)]
      nlinarith
    have hle : 1 / (m i + 2) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    exact exists_pointedBallApprox_of_injOn_of_distortion (hpt (i + T)) (by positivity) hlt
      (by linarith) hi1 hi2 ((closedBall_subset_ball (by linarith)).trans hi3)
  choose h hh using hex
  have hmt : Tendsto m atTop atTop := tendsto_natCast_atTop_atTop.comp hst
  refine ⟨T, fun i => m i + 1, fun i => 1 / (m i + 2), tendsto_atTop_add_const_right _ 1 hmt,
    ?_, h, ?_⟩
  · have h2 : Tendsto (fun i => m i + 2) atTop atTop := tendsto_atTop_add_const_right _ 2 hmt
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp h2
  -- the common good tail on a bounded set
  have hgood : ∀ K : Set N, Bornology.IsBounded K → ∀ᶠ i in atTop, ∀ x ∈ K,
      x ∈ ball q (m i + 3) ∧ dist (j (i + T) x) (p (i + T)) ≤ m i + 1 := by
    intro K hK
    obtain ⟨C, hC⟩ := hK.subset_closedBall q
    filter_upwards [hmt.eventually_ge_atTop (C + 1)] with i hi x hx
    have hxq : dist x q ≤ C := mem_closedBall.mp (hC hx)
    have hm := hm0 i
    have hxb : x ∈ ball q (m i + 3) := mem_ball.mpr (by linarith)
    have hqb : q ∈ ball q (m i + 3) := mem_ball_self (by linarith)
    refine ⟨hxb, ?_⟩
    have hd := (hPi i).2.1 x hxb q hqb
    rw [hpt (i + T)] at hd
    have hle : 1 / (m i + 2) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    linarith [(abs_lt.mp hd).2]
  refine ⟨fun K hK => (hgood K hK).mono fun i hi x hx => (hi x hx).2, fun K hK => ?_⟩
  filter_upwards [hgood K hK] with i hi x hx
  rw [(h i).extendToWholeSpace_apply _ (hi x hx).2]
  exact hh i x (hi x hx).1 (hi x hx).2

/-- **LFR14 with quasi-inverses of its own maps (T0 + (c5′)).** The package of
`exists_finite_cheeger_gromov_limit` (for a subsequence `φ`) together with pointed ball
approximations `h i : B̄(p_{φ i}, Rᵢ) → (N, q)`, `Rᵢ → ∞`, `εᵢ → 0`, such that on every bounded
set eventually `j i` lands in `B̄(p_{φ i}, Rᵢ)` and `hᵢ ∘ jᵢ = id`. -/
theorem exists_finite_cheeger_gromov_limit_with_quasiInverse
    (n K : ℕ) (hn : 2 ≤ n) (hK : 1 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
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
        ∃ R ε : ℕ → ℝ, Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
          ∃ h : ∀ i, PointedBallApprox (p (φ i)) q (R i) (ε i),
            (∀ C : Set N, Bornology.IsBounded C →
              ∀ᶠ i in atTop, ∀ x ∈ C, dist (j i x) (p (φ i)) ≤ R i) ∧
            (∀ C : Set N, Bornology.IsBounded C →
              ∀ᶠ i in atTop, ∀ x ∈ C, (h i).extendToWholeSpace (j i x) = x) := by
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist,
      hcov⟩ := exists_finite_cheeger_gromov_limit n K hn hK hr hv A hA g hmetric p hvol hcurv
  let := mN
  let := cN
  have hinj : ∀ b : ℝ, ∀ᶠ i in atTop, InjOn (j i : N → X (φ i)) (ball q b) := fun b =>
    (hexh _ (isCompact_closedBall q b)).mono fun i hi =>
      (j i).toPartialEquiv.injOn.mono (ball_subset_closedBall.trans hi)
  obtain ⟨T, R, ε, hR, hε, h, hdom, hinv⟩ := exists_quasiInverse_of_comparison_maps q
    (fun i => p (φ i)) (fun i => (j i : N → X (φ i))) (fun i => (hpt i).2) hinj hdist hcov
  have hT : Tendsto (fun i : ℕ => i + T) atTop atTop := tendsto_add_atTop_nat T
  refine ⟨fun i => φ (i + T), hφ.comp (strictMono_id.add_const T), N, mN, cN, hMN, G, q,
    fun i => j (i + T), hprop, hconn, hRiem,
    hGH.subsequence (φ := fun i => i + T) (strictMono_id.add_const T), fun i => hpt (i + T),
    fun C hC => hT.eventually (hexh C hC),
    fun x L hL hLt => (hconv x L hL hLt).comp_tendsto_atTop hT,
    fun R' ε' hε' => hT.eventually (hdist R' ε' hε'),
    fun a b ha hab => hT.eventually (hcov a b ha hab), R, ε, hR, hε, h, hdom, hinv⟩

/-- **LFR15, coordinate clause, for LFR14's own maps.** Under the hypotheses of T0 and LFR15's
splittings `Φᵢ : X i → F × Zᵢ` (Kleiner–Lott approximations with errors `δᵢ → 0`), the package of
T0 holds, and the SAME limit `N` is an exact product `e : N ≃ᵢ F × W` (`W` proper complete, the
pointed limit of the factors along a further subsequence `χ`) with `(Φ ∘ j)_F → e_F` uniformly on
bounded sets, for the SAME maps `j`. -/
theorem exists_finite_cheeger_gromov_limit_with_coordinate_pullback
    (n K : ℕ) (hn : 2 ≤ n) (hK : 1 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
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
      curvDerivNorm k (g i) y ≤ A R)
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
        ∃ (W : Type) (m : MetricSpace W), letI := m
          ∃ (w : W) (χ : ℕ → ℕ), StrictMono χ ∧ ProperSpace W ∧ CompleteSpace W ∧
            PointedGHConverges (fun i => b (φ (χ i))) w ∧
            ∃ e : N ≃ᵢ WithLp 2 (F × W), e q = WithLp.toLp 2 (a, w) ∧
              ∀ C : Set N, Bornology.IsBounded C →
                TendstoUniformlyOn (fun i x => ((Φ (φ (χ i))).toFun (j (χ i) x)).fst)
                  (fun x => (e x).fst) atTop C := by
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist,
      hcov, R, ε, hR, hε, h, hdom, hinv⟩ :=
    exists_finite_cheeger_gromov_limit_with_quasiInverse n K hn hK hr hv A hA g hmetric p hvol
      hcurv
  let := mN
  let := cN
  have := hprop
  have hround : ∀ C : Set N, Bornology.IsBounded C →
      TendstoUniformlyOn (fun i x => (h i).extendToWholeSpace (j i x)) id atTop C := by
    intro C hC
    refine Metric.tendstoUniformlyOn_iff.mpr fun η hη => ?_
    filter_upwards [hinv C hC] with i hi x hx
    rw [hi x hx, id_eq, dist_self]
    exact hη
  obtain ⟨W, m, w, χ, hχ, hWp, hWc, hzW, -, e, he, hcoord, -⟩ :=
    exists_product_limit_with_coordinate_pullback h hR hε (fun i => Φ (φ i))
      (hδ.comp hφ.tendsto_atTop) (fun i => (j i : N → X (φ i))) hdom hround
  exact ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist, hcov,
    W, m, w, χ, hχ, hWp, hWc, hzW, e, he, hcoord⟩

end DifferentialGeometry.CheegerGromovCompactness
