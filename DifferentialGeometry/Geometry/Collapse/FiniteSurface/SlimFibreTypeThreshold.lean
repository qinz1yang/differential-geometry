import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.LConsMergeNoncompact
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimThresholdInputs
import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimPacketApplications
import DifferentialGeometry.Geometry.Metric.Approximation.RiemannianHausdorffVolume
import DifferentialGeometry.Geometry.Collapse.SublevelCore.ScaledMinimizingDirections

/-!
# LFR20 item 2, the fibre type, threshold form

Blueprint LFR20 (master207A:26358), the compactness-contradiction frame of its proof. For `Δ ≥ 1`,
`0 < σ ≤ 1/100`, `K ≥ 5`, `r, v > 0` and `A` there is `β₀ > 0` such that for every `β < β₀`, every
complete connected ORIENTED smooth three-manifold with `Vol B(p, r) ≥ v`, `|∇^k Rm| ≤ A(R)` on
`B(p, R)` (`k ≤ K`, `R < β⁻¹`), `sec ≥ -β²` on `B(p, β⁻¹)`, every normalized `(1, β)`-splitting
`α` with factor diameter `≤ 10³Δ` and EVERY slim chart `c` of `α` (LFR19/LFR20's coordinate):
the ENTIRE zero fibre `{x ∈ B(p, 10⁶Δ) | η x = 0}` is connected and homeomorphic to `S²` or `T²`
(`slimChart_zeroLevel_sphere_or_torus_threshold`).

Proof: a sequence of counterexamples with `β_n → 0`; the L-CONS merge (B1, oriented:
`exists_lcons_merge_noncompact_oriented`) gives one subsequence, an oriented limit `N` with
`sec ≥ 0`, an exact splitting `e : N ≃ᵢ ℓ²(ℝ × W)` tracked by `u_n ∘ j_n → t` and LFR14's comparison
data; the factor `W` is compact of diameter `≤ 10³Δ` (`compactSpace_splitting_factor_of_limit`);
then `exists_sphere_or_torus_eventually_slimChart_zeroLevel` contradicts.

The orientation is used only to orient the limit and its surface factor (LFR17 is for oriented
surfaces); without it `RP²` and the Klein bottle occur (e.g. `RP² × ℝ`).

LC85's producer in threshold form, `exists_slimPacket_threshold`, is in
`SlimFibreTypeThresholdApplications.lean`.
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

local instance nezero_finrank_euclidean_three_threshold_F7LFR20b :
    NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

universe u w

/-- **LFR20, fibre type, threshold form.** -/
theorem slimChart_zeroLevel_sphere_or_torus_threshold {Δ σ : ℝ} (hΔ : 1 ≤ Δ) (hσ : 0 < σ)
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
        ∀ c : SlimChart g hEnorm Δ σ α,
          ConnectedSpace {x // x ∈ ball p (10 ^ 6 * Δ) ∧ c.coord x = 0} ∧
          (Nonempty ({x // x ∈ ball p (10 ^ 6 * Δ) ∧ c.coord x = 0} ≃ₜ
              Metric.sphere (0 : E3) 1) ∨
            Nonempty ({x // x ∈ ball p (10 ^ 6 * Δ) ∧ c.coord x = 0} ≃ₜ
              (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))) := by
  by_contra hcon
  push Not at hcon
  have hK4 : 4 ≤ K := by omega
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
      hcov, -, -, hsecG, W, mW, w, hWp, -, e, -, hU⟩ :=
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
  have _ : CompactSpace W := compactSpace_splitting_factor_of_limit q
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
  obtain ⟨S, mS, cS, iS, -, hconnS, -, htype, hev⟩ :=
    exists_sphere_or_torus_eventually_slimChart_zeroLevel (two_le_reindex K hK4)
      (finiteMetricReindex K hK4 G) (finiteMetricReindex_enorm K hK4 G)
      (fun x v w => hsecG x v w) oN (fun i => g (φ i)) (fun i => hEnorm (φ i))
      (fun i => hmetric (φ i)) (by omega : 2 ≤ K) q j hexh
      (fun x L hL hLt => (hconv x L hL hLt).mono_order (by omega)) hdist hcover e hΔ hσ hσ1 hDW
      (fun i => α (φ i)) (fun i => c (φ i)) hpt hU'
  obtain ⟨i, ⟨ψ⟩⟩ := hev.exists
  have hconnZ := ψ.connectedSpace_iff.mpr hconnS
  have hni := hneg (φ i) hconnZ
  rcases htype with hs | ht
  · obtain ⟨d⟩ := hs
    exact hni.1.false (ψ.trans d.toHomeomorph)
  · obtain ⟨d⟩ := ht
    exact hni.2.false (ψ.trans d.toHomeomorph)

end DifferentialGeometry.Geometry.Collapse
