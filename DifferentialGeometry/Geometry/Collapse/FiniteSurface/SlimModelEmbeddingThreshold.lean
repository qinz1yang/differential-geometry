import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.LConsMergeNoncompact
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimThresholdInputs
import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimPacketApplications
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimModelEmbedding
import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimProductModel
import DifferentialGeometry.Geometry.Metric.Approximation.RiemannianHausdorffVolume
import DifferentialGeometry.Geometry.Collapse.SublevelCore.ScaledMinimizingDirections

/-!
# LFR20 item 3, threshold form

Blueprint LFR20 (master207A:26358), item 3, under LFR20's hypotheses (as in
`slimChart_zeroLevel_sphere_or_torus_threshold`, oriented): for EVERY slim chart `c` (coordinate
`η`) there is a complete finite model `N` (proper, connected, Riemannian for a `C^{K-1}` metric `G`
with `sec ≥ 0`) with an exact splitting `e : N ≃ᵢ ℓ²(ℝ × W)`, `W` compact of diameter `≤ 10³Δ`,
LFR18's vertical field `V` (`dt(V) = 1`), and an actual `C^K` embedding `j` (a partial
diffeomorphism) of a neighbourhood of the cylinder `{|t| ≤ b}`, `b = 19L/20`, into `M` with
`j(t = 0 factor) ∋ j q = p`, such that on the cylinder `j` lands in `B(p, L)`, `|η ∘ j - t| < 2e`,
`∂_t(η ∘ j) > 3/4`, every interpolation `(1 - u) t + u (η ∘ j)` is transverse along `V` with
inverse images of `[-a, a]` inside `{|t| < a + 2e}`, and EVERY source fibre over `[-a, a]` in
`B(p, L)` lies in `j({|t| < 0.93L})` (`slimChart_model_embedding_threshold`).
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

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local instance nezero_finrank_euclidean_three_embThreshold_F7LFR20b :
    NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

universe u w

/-- **LFR20 item 3, threshold form.** Every slim chart has an LC81 product model. -/
theorem slimChart_model_embedding_threshold {Δ σ : ℝ} (hΔ : 1 ≤ Δ) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1 / 100) (K : ℕ) (hK : 5 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, 0 < β → β < β₀ →
      ∀ (M : Type u) [MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
        [SigmaCompactSpace M] [T2Space (TangentBundle 𝓘(ℝ, E3) M)] [CompleteSpace M]
        [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        [IsRiemannianManifold 𝓘(ℝ, E3) M]
        [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        (g : SmoothRiemannianMetric 𝓘(ℝ, E3) M) (hEnorm : IsMetricNorm g),
        ManifoldOrientation (𝓡 3) M 3 → ∀ p : M,
        ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, E3) M g (ball p r) →
        (∀ R, 0 < R → R < β⁻¹ → ∀ k ≤ K, ∀ y ∈ ball p R, curvDerivNorm k g y ≤ A R) →
        (∀ y ∈ ball p β⁻¹, SectionalBoundedBelowAt g y (-β ^ 2)) →
        ∀ (Y : Type w) [MetricSpace Y] (y₀ : Y)
          (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β),
        (∀ y z : Y, dist y z ≤ 10 ^ 3 * Δ) →
        ∀ c : SlimChart g hEnorm Δ σ α, Nonempty (SlimProductModel c K) := by
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
      hcov, -, -, hsecG, W, mW, w, hWp, -, e, he, hU⟩ :=
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
  obtain ⟨i, ⟨hcl, hfib⟩, hsrc⟩ :=
    (hev.and (hexh _ (isCompact_splitting_cylinder e (95 / 100 * (10 ^ 6 * Δ))))).exists
  exact (hneg (φ i)).false
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

end DifferentialGeometry.Geometry.Collapse
