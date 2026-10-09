import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimModelEmbeddingThreshold
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.BufferComparison

/-!
# LFR20, last paragraph: the model embedding with prescribed comparison tolerances

Blueprint LFR20 (master207A:26358), last paragraph (A:26404–26406): "The model embedding can
additionally meet any prescribed positive finite-buffer `C^{K-1}` metric and pointed-distance
comparison tolerance, by decreasing `β₀` after that tolerance is fixed"; proof step 5
(A:26516–26525). Lane LFR20-CMP, packet 1 (review 43, row LFR20 (i)).

`slimChart_model_comparison_threshold`: the tolerance `ε > 0` and a buffer radius `R` are fixed
BEFORE `β₀`. For every slim chart there is an LC81 product model `P : SlimProductModel c K` (item 3,
`SlimProductModel` unchanged) such that, for the SAME `P.j`, `P.G`, `P.e`, on the compact buffer
`{|t| ≤ 19L/20} ∪ B̄(q, R)` (`L = 10⁶Δ`):
* the buffer lies in the source of `P.j`;
* pointed distances are preserved up to `ε`: `|d(j x, j y) − d(x, y)| < ε`;
* the `C^{K-1}` metric comparison in the tree's own LFR14 form: a finite family of compact chart
  patches `L x ⊆ (extChartAt x).target` (`x ∈ S`), whose interiors cover the buffer, with
  `mapDerivNorm k (pullbackMetricCoefficients g (j ∘ (extChartAt x)⁻¹)) (chartCoeff P.G x) ≤ ε` on
  `L x` for `k ≤ K - 1` (the finite-tolerance version of `MapCPConvergenceOn L' (K - 1)`);
* moreover `P.N` carries an orientation `oN` that `P.j` maps to the given source orientation `o` at
  every point of its source (LFR16's eventual orientation preservation, used by packet 2).

Proof: the contradiction argument of `slimChart_model_embedding_threshold` with the stronger
negation; the merge's chart convergence, distortion and orientation clauses (discarded there) give
the extra clauses on one further tail (`eventually_buffer_chart_comparison`,
`eventually_abs_dist_sub_lt_of_isBounded`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric WithLp Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry
open DifferentialGeometry.Integral.Measure

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] SlimProductModel.instMetricN SlimProductModel.instChartedN
  SlimProductModel.instManifoldN SlimProductModel.instProperN SlimProductModel.instConnectedN
  SlimProductModel.instBundleN SlimProductModel.instRiemannianN SlimProductModel.instMetricW
  SlimProductModel.instCompactW

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local instance nezero_finrank_euclidean_three_cmpThreshold_LFR20CMP :
    NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

universe u w

/-- The threshold statement with its conclusion packed as a nonempty subtype (so that the
contradiction argument negates it as one `IsEmpty`). -/
private theorem slimChart_model_comparison_threshold_aux {Δ σ : ℝ} (hΔ : 1 ≤ Δ) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1 / 100) (K : ℕ) (hK : 5 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, 0 < β → β < β₀ →
      ∀ (M : Type u) [MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
        [SigmaCompactSpace M] [T2Space (TangentBundle 𝓘(ℝ, E3) M)] [CompleteSpace M]
        [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        [IsRiemannianManifold 𝓘(ℝ, E3) M]
        [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        (g : SmoothRiemannianMetric 𝓘(ℝ, E3) M) (hEnorm : IsMetricNorm g),
        ∀ o : ManifoldOrientation (𝓡 3) M 3, ∀ p : M,
        ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, E3) M g (ball p r) →
        (∀ R, 0 < R → R < β⁻¹ → ∀ k ≤ K, ∀ y ∈ ball p R, curvDerivNorm k g y ≤ A R) →
        (∀ y ∈ ball p β⁻¹, SectionalBoundedBelowAt g y (-β ^ 2)) →
        ∀ (Y : Type w) [MetricSpace Y] (y₀ : Y)
          (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β),
        (∀ y z : Y, dist y z ≤ 10 ^ 3 * Δ) →
        ∀ c : SlimChart g hEnorm Δ σ α, Nonempty {P : SlimProductModel c K //
          (∃ oN : ManifoldOrientation (𝓡 3) P.N 3, ∀ (x : P.N) (hx : x ∈ P.j.source),
            Orientation.map (Fin 3)
              ((P.j.isLocalDiffeomorphAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) (K : ℕ∞ω) hx).mfderivToContinuousLinearEquiv
                (by exact_mod_cast (show K ≠ 0 by omega))).toLinearEquiv (oN.orientation x) =
              o.orientation (P.j x)) ∧
          closedBall P.q R ⊆ P.j.source ∧
          (∀ x y : P.N, (|(P.e x).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) ∨ dist x P.q ≤ R) →
            (|(P.e y).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) ∨ dist y P.q ≤ R) →
            |dist (P.j x) (P.j y) - dist x y| < ε) ∧
          ∃ (S : Finset P.N) (L : P.N → Set E3),
            (∀ x ∈ S, IsCompact (L x) ∧ L x ⊆ (extChartAt 𝓘(ℝ, E3) x).target ∧
              (extChartAt 𝓘(ℝ, E3) x).symm '' L x ⊆ P.j.source ∧
              ∀ k ≤ K - 1, ∀ y ∈ L x, mapDerivNorm k
                (pullbackMetricCoefficients g ((P.j : P.N → M) ∘ (extChartAt 𝓘(ℝ, E3) x).symm))
                (chartCoeff P.G x) y ≤ ε) ∧
            ∀ x : P.N, (|(P.e x).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) ∨ dist x P.q ≤ R) →
              ∃ x' ∈ S, x ∈ (extChartAt 𝓘(ℝ, E3) x').source ∧
                extChartAt 𝓘(ℝ, E3) x' x ∈ interior (L x')} := by
  by_contra hcon
  have hK4 : 4 ≤ K := by omega
  push Not at hcon
  choose β hβ0 hβlt M iMet iCh iMan iSig iT2 iCo iCon iRB iRM iCRB g hEnorm o p hvol hcurv hsec
    Y iY y₀ α hD c hneg using fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  have hβ : Tendsto β atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun n => (hβ0 n).le)
      (Eventually.of_forall fun n => (hβlt n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  have hmetric : ∀ n a b, riemannianEDistOf (g n) a b = ENNReal.ofReal (dist a b) :=
    fun n => riemannianEDistOf_eq_ofReal_dist (g n) (hEnorm n)
  have hball : ∀ n R, riemannianBallOf (g n) (p n) R = ball (p n) R :=
    fun n R => DifferentialGeometry.Geometry.Metric.riemannianBallOf_eq_ball_of_isMetricNorm (g n) (hEnorm n) (p n) R
  have hL : Tendsto (fun n => (β n)⁻¹) atTop atTop :=
    (tendsto_nhdsWithin_iff.mpr ⟨hβ, Eventually.of_forall hβ0⟩).inv_tendsto_nhdsGT_zero
  have hη : Tendsto (fun n => β n ^ 2) atTop (𝓝 0) := by
    simpa using hβ.pow 2
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, oN, hprop, hconn, hRiem, -, hbase, hexh, hconv, hdist,
      hcov, -, hor, hsecG, W, mW, w, hWp, -, e, he, hU⟩ :=
    exists_lcons_merge_noncompact_oriented K hK4 hr hv A g hmetric p o
      (Eventually.of_forall fun n => by rw [hball]; exact hvol n)
      (fun R hR => by
        filter_upwards [hL.eventually (eventually_gt_atTop R)] with n hn k hk y hy
        rw [hball] at hy
        exact hcurv n R hR hn k hk y hy)
      hη hL (Eventually.of_forall fun n y hy => by rw [hball] at hy; exact hsec n y hy) α hβ
  let _ := mN
  let _ := cN
  have _ := hMN
  have _ := hprop
  have _ := hconn
  let _ : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x) := ⟨G.toRiemannianMetric⟩
  have _ : IsRiemannianManifold 𝓘(ℝ, E3) N := hRiem
  let _ := mW
  have _ := hWp
  have _ : Nonempty W := ⟨w⟩
  have hpt : ∀ i, j i q = p (φ i) := fun i => (hbase i).2
  have hU' : ∀ C : Set N, IsCompact C →
      TendstoUniformlyOn (fun i x => ((α (φ i)).toFun (j i x)).fst) (fun x => (e x).fst) atTop C :=
    fun C hC => hU C hC.isBounded
  have hβφ : Tendsto (fun i => β (φ i)) atTop (𝓝 0) := hβ.comp hφ.tendsto_atTop
  have hcompW : CompactSpace W := compactSpace_splitting_factor_of_limit q
    (fun i => (j i : N → M (φ i))) (fun i => p (φ i)) hpt hdist (fun i => α (φ i)) hβφ
    (fun i => hD (φ i)) e hU'
  have hDW : ∀ a b : W, dist a b ≤ 10 ^ 3 * Δ := splitting_factor_dist_le_of_limit q
    (fun i => (j i : N → M (φ i))) (fun i => p (φ i)) hpt hdist (fun i => α (φ i)) hβφ
    (fun i => hD (φ i)) e hU'
  have hcover : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
      ball (j i q) a ⊆ (j i : N → M (φ i)) '' ball q b := by
    intro a b ha hab
    filter_upwards [hcov a b ha hab] with i hi
    rw [hpt i]
    exact hi
  have he0 : (e q).fst = 0 := by rw [he]; rfl
  obtain ⟨V, hVdir, hdt, hev⟩ := eventually_slimChart_model_embedding (two_le_reindex K hK4)
    (finiteMetricReindex K hK4 G) (finiteMetricReindex_enorm K hK4 G) (fun i => g (φ i))
    (fun i => hEnorm (φ i)) (fun i => hmetric (φ i)) (by omega : 2 ≤ K) q j hexh
    (fun x L hL hLt => (hconv x L hL hLt).mono_order (by omega)) hdist hcover e hΔ hσ hσ1 hDW
    (fun i => α (φ i)) (fun i => c (φ i)) hpt hU'
  -- the compact buffer `{|t| ≤ 19L/20} ∪ B̄(q, R)`
  let B : Set N := {x | |(e x).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) ∨ dist x q ≤ R}
  have hB : IsCompact B :=
    (isCompact_splitting_cylinder e (95 / 100 * (10 ^ 6 * Δ))).union (isCompact_closedBall q R)
  obtain ⟨S, Lp, hLp, hLcov, hcmp⟩ := eventually_buffer_chart_comparison (fun i => g (φ i)) G j
    hexh hconv hB hε
  have hdB := eventually_abs_dist_sub_lt_of_isBounded (fun i => (j i : N → M (φ i))) q hdist
    hB.isBounded hε
  obtain ⟨i, ⟨⟨⟨⟨hcl, hfib⟩, hsrc⟩, hcmpi⟩, hdBi⟩, hori⟩ :=
    ((((hev.and (hexh _ (isCompact_splitting_cylinder e (95 / 100 * (10 ^ 6 * Δ))))).and
      hcmp).and hdB).and hor).exists
  let P : SlimProductModel (c (φ i)) K :=
    { N := N
      instMetricN := mN
      instChartedN := cN
      instManifoldN := hMN
      instProperN := hprop
      instConnectedN := hconn
      instBundleN := ⟨G.toRiemannianMetric⟩
      instRiemannianN := hRiem
      G := finiteMetricReindex K hK4 G
      enorm := finiteMetricReindex_enorm K hK4 G
      sectional_nonneg := fun x v w => hsecG x v w
      W := W
      instMetricW := mW
      instCompactW := hcompW
      factor_dist := hDW
      e := e
      V := V
      vertical := hVdir
      dt_vertical := hdt
      j := j i
      q := q
      q_mem := (hbase i).1
      j_q := (hbase i).2
      t_q := he0
      cylinder_subset := hsrc
      cylinder := hcl
      fibres := hfib }
  exact (hneg (φ i)).false ⟨P, ⟨oN, hori⟩, fun x hx => hcmpi.1 (Or.inr hx),
    fun x y hx hy => hdBi x hx y hy, S, Lp,
    fun x hx => ⟨(hLp x hx).1, (hLp x hx).2, (hcmpi.2 x hx).1, (hcmpi.2 x hx).2⟩, hLcov⟩

/-- **LFR20, last paragraph, threshold form.** For a comparison tolerance `ε > 0` and a buffer
radius `R` fixed BEFORE `β₀`: every slim chart has an LC81 product model whose SAME embedding
`P.j` is `ε`-close to an isometry on the buffer `{|t| ≤ 19L/20} ∪ B̄(q, R)`, whose pulled-back
metric is `ε`-close to `P.G` in `C^{K-1}` on a finite atlas of compact chart patches covering that
buffer (LFR14's predicate at fixed tolerance), and whose model carries an orientation mapped by
`P.j` to the source orientation. -/
theorem slimChart_model_comparison_threshold {Δ σ : ℝ} (hΔ : 1 ≤ Δ) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1 / 100) (K : ℕ) (hK : 5 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, 0 < β → β < β₀ →
      ∀ (M : Type u) [MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
        [SigmaCompactSpace M] [T2Space (TangentBundle 𝓘(ℝ, E3) M)] [CompleteSpace M]
        [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        [IsRiemannianManifold 𝓘(ℝ, E3) M]
        [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        (g : SmoothRiemannianMetric 𝓘(ℝ, E3) M) (hEnorm : IsMetricNorm g),
        ∀ o : ManifoldOrientation (𝓡 3) M 3, ∀ p : M,
        ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, E3) M g (ball p r) →
        (∀ R, 0 < R → R < β⁻¹ → ∀ k ≤ K, ∀ y ∈ ball p R, curvDerivNorm k g y ≤ A R) →
        (∀ y ∈ ball p β⁻¹, SectionalBoundedBelowAt g y (-β ^ 2)) →
        ∀ (Y : Type w) [MetricSpace Y] (y₀ : Y)
          (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β),
        (∀ y z : Y, dist y z ≤ 10 ^ 3 * Δ) →
        ∀ c : SlimChart g hEnorm Δ σ α, ∃ P : SlimProductModel c K,
          (∃ oN : ManifoldOrientation (𝓡 3) P.N 3, ∀ (x : P.N) (hx : x ∈ P.j.source),
            Orientation.map (Fin 3)
              ((P.j.isLocalDiffeomorphAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) (K : ℕ∞ω) hx).mfderivToContinuousLinearEquiv
                (by exact_mod_cast (show K ≠ 0 by omega))).toLinearEquiv (oN.orientation x) =
              o.orientation (P.j x)) ∧
          closedBall P.q R ⊆ P.j.source ∧
          (∀ x y : P.N, (|(P.e x).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) ∨ dist x P.q ≤ R) →
            (|(P.e y).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) ∨ dist y P.q ≤ R) →
            |dist (P.j x) (P.j y) - dist x y| < ε) ∧
          ∃ (S : Finset P.N) (L : P.N → Set E3),
            (∀ x ∈ S, IsCompact (L x) ∧ L x ⊆ (extChartAt 𝓘(ℝ, E3) x).target ∧
              (extChartAt 𝓘(ℝ, E3) x).symm '' L x ⊆ P.j.source ∧
              ∀ k ≤ K - 1, ∀ y ∈ L x, mapDerivNorm k
                (pullbackMetricCoefficients g ((P.j : P.N → M) ∘ (extChartAt 𝓘(ℝ, E3) x).symm))
                (chartCoeff P.G x) y ≤ ε) ∧
            ∀ x : P.N, (|(P.e x).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) ∨ dist x P.q ≤ R) →
              ∃ x' ∈ S, x ∈ (extChartAt 𝓘(ℝ, E3) x').source ∧
                extChartAt 𝓘(ℝ, E3) x' x ∈ interior (L x') := by
  obtain ⟨β₀, hβ₀, h⟩ :=
    slimChart_model_comparison_threshold_aux.{u, w} hΔ hσ hσ1 K hK hr hv A hε R
  refine ⟨β₀, hβ₀, fun β hβ hββ₀ M _ _ _ _ _ _ _ _ _ _ g hEnorm o p hvol hcurv hsec Y _ y₀ α hD c => ?_⟩
  obtain ⟨⟨P, hP⟩⟩ := h β hβ hββ₀ M g hEnorm o p hvol hcurv hsec Y y₀ α hD c
  exact ⟨P, hP⟩

end DifferentialGeometry.Geometry.Collapse
