import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.QuasiInverse
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.EventualBounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.CurvatureScaleBinding
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.ArbitraryCharts

/-!
# Consumers of the LFR14 consumer adapters (lane L-CONS)

* `exists_pointedBallApprox_id`, `exists_quasiInverse_id` (adapter (a)): the identity maps of a
  metric space have themselves as quasi-inverses, at one scale and along a sequence.
* `exists_curvDerivNorm_bound_of_compactSpace` (adapter (b)): on a compact manifold the
  curvature-derivative norms through order `K` are bounded.
* `exists_finite_cheeger_gromov_limit_of_real_family` (adapter (c)): LPA02's phrasing — a family
  over `α ∈ ℝ` whose bounds hold for `α` past radius-dependent thresholds; every sequence
  `αᵢ → ∞` with any centres has the T0 + T2 package.
* `exists_curvature_scale_of_ball_lower_bounds_tendsto` (adapter (d)): LFR49's curvature scale
  for lower bounds `sec ≥ κᵢ`, `κᵢ → 0`, of any sign (e.g. positive curvature).
* `exists_finite_cheeger_gromov_limit_C1_in_charts` (adapter (e)): LFR18's input — for `K ≥ 2`,
  `C¹` convergence of `jᵢ^* gᵢ` in every `C^K` chart of the limit.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Integral.Measure GC.MetricGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry.Riemannian

universe u

/-- Adapter (a), one map: the identity is its own pointed ball approximation. -/
theorem exists_pointedBallApprox_id {N : Type*} [MetricSpace N] (q : N) {R ε : ℝ}
    (hε : 0 < ε) (hεR : ε < R) :
    ∃ h : PointedBallApprox q q R ε, ∀ x : BallCarrier q R, h.toFun x = x.val := by
  obtain ⟨h, hh⟩ := exists_pointedBallApprox_of_injOn_of_distortion (f := id) (q := q) rfl hε
    hεR le_rfl (injOn_id _) (fun x _ y _ => by simpa only [id_eq, sub_self, abs_zero] using hε)
    (fun y hy => ⟨y, mem_ball.mpr (by have h := mem_closedBall.mp hy; rw [id_eq] at h; linarith),
      rfl⟩)
  exact ⟨h, fun x => hh x.val (mem_ball.mpr (by linarith [x.2])) x.2⟩

/-- Adapter (a), sequence: constant identity maps have quasi-inverses that are eventually the
identity on every bounded set. -/
theorem exists_quasiInverse_id {N : Type*} [MetricSpace N] (q : N) :
    ∃ R ε : ℕ → ℝ, Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
      ∃ h : ∀ i, PointedBallApprox q q (R i) (ε i),
        ∀ K : Set N, Bornology.IsBounded K →
          ∀ᶠ i in atTop, ∀ x ∈ K, (h i).extendToWholeSpace x = x := by
  obtain ⟨-, R, ε, hR, hε, h, -, hinv⟩ := exists_quasiInverse_of_comparison_maps
    (Y := fun _ => N) q (fun _ => q) (fun _ => id) (fun _ => rfl)
    (fun _ => Eventually.of_forall fun _ => injOn_id _)
    (fun _ _ hε => Eventually.of_forall fun _ _ _ _ _ => by
      simpa only [id_eq, sub_self, abs_zero] using hε)
    (fun _ _ _ hab => Eventually.of_forall fun _ y hy =>
      ⟨y, mem_ball.mpr (lt_trans (mem_ball.mp hy) hab), rfl⟩)
  exact ⟨R, ε, hR, hε, h, hinv⟩

/-- Adapter (b): on a compact manifold the curvature-derivative norms through order `K` are
bounded. -/
theorem exists_curvDerivNorm_bound_of_compactSpace
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [CompactSpace M] (g : SmoothRiemannianMetric I M) (K : ℕ) :
    ∃ B : ℝ, ∀ k ≤ K, ∀ x : M, curvDerivNorm k g x ≤ B := by
  obtain ⟨B, hB⟩ := exists_curvDerivNorm_bound_of_isCompact g K isCompact_univ
  exact ⟨B, fun k hk x => hB k hk x (mem_univ x)⟩

/-- Adapter (c), LPA02's phrasing: a family `M α`, `α ∈ ℝ`, whose volume, curvature-derivative
(threshold depending on the radius) and sectional bounds hold for all `α` past thresholds, with
`η α → 0`, `H α → ∞`. Then EVERY sequence `αᵢ → ∞` with ANY centres has the T0 + T2 package. -/
theorem exists_finite_cheeger_gromov_limit_of_real_family
    (n K : ℕ) (hn : 2 ≤ n) (hK : 3 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ)
    {M : ℝ → Type u} [∀ a, MetricSpace (M a)]
    [∀ a, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M a)]
    [∀ a, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (M a)]
    [∀ a, SigmaCompactSpace (M a)]
    [∀ a, T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M a))]
    [∀ a, CompleteSpace (M a)] [∀ a, ConnectedSpace (M a)]
    (gM : ∀ a, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M a))
    (hmetric : ∀ a x y, riemannianEDistOf (gM a) x y = ENNReal.ofReal (dist x y))
    (α₀ : ℝ) (hvol : ∀ a ≥ α₀, ∀ x : M a, ENNReal.ofReal v ≤
      riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M a) (gM a)
        (riemannianBallOf (gM a) x r))
    (αR : ℝ → ℝ) (hcurv : ∀ R > 0, ∀ a ≥ αR R, ∀ x : M a, ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (gM a) x R, curvDerivNorm k (gM a) y ≤ A R)
    {η H : ℝ → ℝ} (hη : Tendsto η atTop (𝓝 0)) (hH : Tendsto H atTop atTop)
    (hsec : ∀ a ≥ α₀, ∀ x : M a, ∀ y ∈ riemannianBallOf (gM a) x (H a),
      SectionalBoundedBelowAt (gM a) y (-η a))
    (α : ℕ → ℝ) (hα : Tendsto α atTop atTop) (p : ∀ i, M (α i)) :
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
  exists_finite_cheeger_gromov_limit_of_eventual_family n K hn hK hr hv A gM hmetric
    (eventually_atTop.mpr ⟨α₀, hvol⟩)
    (fun R hR => eventually_atTop.mpr ⟨αR R, hcurv R hR⟩) hη hH
    (eventually_atTop.mpr ⟨α₀, hsec⟩) α hα p

/-- Adapter (d): LFR49's curvature scale for lower bounds `sec ≥ κᵢ` with `κᵢ → 0` of any sign
(for instance positive curvature, which the nonnegative-error form does not accept). -/
theorem exists_curvature_scale_of_ball_lower_bounds_tendsto
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {X : ℕ → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, ChartedSpace H (X i)]
    [∀ i, IsManifold I ∞ (X i)]
    (g : ∀ i, SmoothRiemannianMetric I (X i)) (p : ∀ i, X i) {L κ : ℕ → ℝ}
    (hL : Tendsto L atTop atTop) (hκ : Tendsto κ atTop (𝓝 0))
    (hsec : ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i) (L i),
      SectionalBoundedBelowAt (g i) y (κ i)) :
    ∃ Hs : ℕ → ℝ, Tendsto Hs atTop atTop ∧ (∀ i, Hs i ≤ L i) ∧
      ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i) (Hs i),
        SectionalBoundedBelowAt (g i) y (-(Hs i ^ 2)⁻¹) :=
  exists_curvature_scale_of_signed_ball_lower_bounds g p (η := fun i => -κ i) hL
    (by simpa only [neg_zero] using hκ.neg)
    (fun i y hy => by simpa only [neg_neg] using hsec i y hy)

/-- Adapter (e), LFR18's input: for `K ≥ 2`, the comparison maps of LFR14 have `C¹` metric
convergence in every `C^K` chart parametrization of the limit. -/
theorem exists_finite_cheeger_gromov_limit_C1_in_charts
    (n K : ℕ) (hn : 2 ≤ n) (hK : 2 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
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
        (∀ i, q ∈ (j i).source ∧ j i q = p (φ i)) ∧
        ∀ (ψ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            (EuclideanSpace ℝ (Fin n)) N K) (L : Set (EuclideanSpace ℝ (Fin n))),
          IsCompact L → L ⊆ ψ.source →
          MapCPConvergenceOn L 1
            (fun i => pullbackMetricCoefficients (g (φ i)) ((j i : N → X (φ i)) ∘ ψ))
            (fun u => (G.inner (ψ u) : EuclideanSpace ℝ (Fin n) →L[ℝ]
                EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).bilinearComp
              (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ψ u :
                EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
              (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ψ u :
                EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, -, -, -, -, hpt, -, -, -, -, hcharts⟩ :=
    exists_finite_cheeger_gromov_limit_in_charts n K hn (by omega) hr hv A hA g hmetric p hvol
      hcurv
  exact ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hpt, fun ψ L hL hLψ =>
    (hcharts ψ L hL hLψ).mono_order (by omega)⟩

end DifferentialGeometry.CheegerGromovCompactness
