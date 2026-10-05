import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.QuasiInverse
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.EventualBounds
import DifferentialGeometry.Geometry.Metric.Approximation.BoundedDiameterLimit

/-!
# The L-CONS merge: one subsequence, one limit, curvature sign and exact splitting

LFR15 (A:26086) and LFR16 (A:26159) need the conclusions of the L-CONS adapters (a) (coordinate
pullback of the splittings `Φᵢ`), (b) (eventual curvature-derivative bounds) and (c) (`sec ≥ 0`
from expanding-ball lower bounds) on ONE subsequence and ONE limit. No re-run of T0 is needed:
* (a) already produces T0's package, the product `e : N ≃ᵢ F × W` and the coordinate convergence,
  the latter along a further subsequence `χ`; T0's clauses are re-indexed by `χ`;
* `sec ≥ 0` is a property of the limit metric, proved post hoc on T0's package
  (`sectionalCurvature_nonneg_of_finite_comparison`);
* eventual bounds become uniform ones (`exists_uniform_curvature_bound_of_eventual`);
* a uniform diameter bound `D` on the residual factors passes to the factor limit `W`
  (`PointedGHConverges.dist_le_of_uniform_bound`), which is then compact.

* `exists_finite_cheeger_gromov_limit_with_nonneg_splitting` — the LFR15 merge (uniform bounds);
* `exists_finite_cheeger_gromov_limit_with_compact_splitting` — the LFR16 merge (eventual bounds,
  residual diameter `≤ D`; `W` compact with `diam W ≤ D`).
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

/-- **The LFR15 merge.** Under T0's hypotheses (uniform curvature-derivative bounds), the
expanding-ball sectional lower bounds `sec ≥ -ηᵢ` on `B(pᵢ, Lᵢ)` (`ηᵢ → 0`, `Lᵢ → ∞`) and LFR15's
splittings `Φᵢ` of the sources (errors `δᵢ → 0`), ONE subsequence `φ` and ONE limit `(N, G, q, j)`
carry T0's package, `sec_G ≥ 0`, an exact product `e : N ≃ᵢ F × W` with `W` the pointed limit of
the residual factors, and `(Φ_{φ i} ∘ jᵢ)_F → e_F` uniformly on bounded sets. -/
theorem exists_finite_cheeger_gromov_limit_with_nonneg_splitting
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
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N (X (φ i)) K),
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
        (∀ (x : N) (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
          0 ≤ G.sectionalCurvature x v w) ∧
        ∃ (W : Type) (m : MetricSpace W), letI := m
          ∃ (w : W), ProperSpace W ∧ CompleteSpace W ∧
            PointedGHConverges (fun i => b (φ i)) w ∧
            ∃ e : N ≃ᵢ WithLp 2 (F × W), e q = WithLp.toLp 2 (a, w) ∧
              ∀ C : Set N, Bornology.IsBounded C →
                TendstoUniformlyOn (fun i x => ((Φ (φ i)).toFun (j i x)).fst)
                  (fun x => (e x).fst) atTop C := by
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist,
      hcov, W, m, w, χ, hχ, hWp, hWc, hzW, e, he, hcoord⟩ :=
    exists_finite_cheeger_gromov_limit_with_coordinate_pullback n K hn (by omega) hr hv A hA g
      hmetric p hvol hcurv Φ hδ
  let := mN
  let := cN
  have := hMN
  have hsecG := sectionalCurvature_nonneg_of_finite_comparison hK (X := fun i => X (φ i))
    (fun i => g (φ i)) (fun i => hmetric (φ i)) (fun i => p (φ i)) G q j hpt hexh hconv hdist
    (hη.comp hφ.tendsto_atTop) (hL.comp hφ.tendsto_atTop) (fun i => hsec (φ i))
  have hT : Tendsto χ atTop atTop := hχ.tendsto_atTop
  exact ⟨fun i => φ (χ i), hφ.comp hχ, N, mN, cN, hMN, G, q, fun i => j (χ i), hprop, hconn,
    hRiem, hGH.subsequence hχ, fun i => hpt (χ i), fun C hC => hT.eventually (hexh C hC),
    fun x L' hL' hL't => (hconv x L' hL' hL't).comp_tendsto_atTop hT,
    fun R ε hε => hT.eventually (hdist R ε hε), fun a b ha hab => hT.eventually (hcov a b ha hab),
    hsecG, W, m, w, hWp, hWc, hzW, e, he, hcoord⟩

/-- **The LFR16 merge.** Under T0's hypotheses with EVENTUAL ballwise curvature-derivative bounds,
the expanding-ball lower bounds and LFR15's splittings with residual factors of diameter `≤ D`,
ONE subsequence and ONE limit carry T0's package, `sec_G ≥ 0`, and an exact product
`e : N ≃ᵢ F × W` with `W` COMPACT of diameter `≤ D`, tracked by the actual comparison maps. -/
theorem exists_finite_cheeger_gromov_limit_with_compact_splitting
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
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N (X (φ i)) K),
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
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist,
      hcov, hsecG, W, m, w, hWp, hWc, hzW, e, he, hcoord⟩ :=
    exists_finite_cheeger_gromov_limit_with_nonneg_splitting n K hn hK hr hv A'
      (fun R _ => hA'pos R) g hmetric p hvol hA' hη hL hsec Φ hδ
  let := m
  have hdiam : ∀ x y : W, dist x y ≤ D := hzW.dist_le_of_uniform_bound (fun i => hD (φ i))
  have hcpt : CompactSpace W := hzW.compactSpace_of_uniform_bound (fun i => hD (φ i))
  exact ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist,
    hcov, hsecG, W, m, w, hWp, hcpt, hdiam, hzW, e, he, hcoord⟩

end DifferentialGeometry.CheegerGromovCompactness
