import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeProductModel
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.BufferComparison
import DifferentialGeometry.Geometry.Collapse.EdgeRowThresholdHpreserving
import DifferentialGeometry.Geometry.Collapse.EdgeSourceCutoff

/-!
# LC84 item 4: the packet together with its LC81 comparison with `ℝ × Z`

Blueprint LC84 (`def:collapse-edge-packet`, master207A:30874) item 4, and LFR28
(`thm:collapse-finite-source-edge-packet`, A:27223): "There is one complete nonnegative `C^{K-1}`
product model `ℝ × Z` and an actual `C^K` embedding of the whole buffered model domain from LFR24,
containing the ENTIRE source closed slab ... Any prescribed positive finite-buffer metric/distance
comparison tolerance may be imposed by further reducing `β`." LC81 items 1–2 (whole buffered
embedding; the SAME approximate splitting with the map-comparison estimates).

* `edgeChart_productModel_threshold`: for a tolerance `δ > 0` and a buffer radius `R` fixed before
  `b₀`, every edge chart (with the coarse-border, smoothing-value and scale data of LFR28) at an
  oriented point with the noncollapse and curvature data has an `EdgeProductModel` whose SAME
  embedding `j` (i) maps an orientation of `N` to the source orientation, and on the buffer
  `B̄(Θ(0, s₀), R)`: (ii) lies in its source, (iii) is `δ`-close to an isometry, (iv) has first
  coordinate of the chart's splitting `δ`-close to the model `t`, (v) is `δ`-close to `G` in
  `C^{K-1}` on a finite atlas of compact chart patches covering the buffer (LFR14's predicate at
  fixed tolerance, as in `slimChart_model_comparison_threshold`).
* `exists_edgeDiskPacket_comparison_threshold` (**LC84 item 4, companion of the packet**): the
  binders of `exists_edgeDiskPacket_threshold` with `δ`, `R` before the threshold; the conclusion is
  `∃ P : EdgeDiskPacket …, P.toEdgeChart = c ∧ ∃ Z : EdgeProductModel c K, (i) ∧ … ∧ (v)`.

Proof of the first: the compactness frame of `edgeSourceSlab_disk_bundle_threshold` with the
L-CONS merge `exists_lcons_merge_noncompact_oriented`, the surface factor and product chart of
`edgeRowModelChart_of_carrier`, the slab enclosure `eventually_edgeSourceSlab_mem_image` (B5) and
`eventually_buffer_chart_comparison` / `eventually_abs_dist_sub_lt_of_isBounded` (lane LFR20-CMP).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Function Filter Metric Manifold WithLp
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Topology
open DifferentialGeometry.Manifold DifferentialGeometry.Manifold.RegularLevel
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open GC.MetricGeometry

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

local instance nezero_finrank_euclidean_three_cmp_LFR28ROW2 : NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

attribute [local instance] EdgeProductModel.instMetricN EdgeProductModel.instChartedN
  EdgeProductModel.instManifoldN EdgeProductModel.instProperN EdgeProductModel.instConnectedN
  EdgeProductModel.instBundleN EdgeProductModel.instRiemannianN EdgeProductModel.instMetricS
  EdgeProductModel.instChartedS EdgeProductModel.instManifoldS EdgeProductModel.instBundleS
  EdgeProductModel.instRiemannianS EdgeChart.instY

/-- **LFR28's model comparison, threshold form** (the LC84 item 4 half of
`exists_edgeDiskPacket_comparison_threshold`). The tolerance `δ` and the buffer radius `R` are fixed
before the threshold; the threshold does not depend on `σ`, `γ`, `β`. -/
theorem edgeChart_productModel_threshold {Δ μ τ : ℝ} {Λ : ℝ≥0} (hΔ : 1 ≤ Δ) (hμ1 : μ ≤ 1 / 10 ^ 8)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 10 ^ 30) (hΛ : 100 * Δ * Λ ≤ 1 / 10 ^ 8) (K : ℕ) (hK : 5 ≤ K)
    {r v : ℝ} (hr : 0 < r) (hv : 0 < v) (A : ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) (R : ℝ) :
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b < b₀ →
      ∀ (M : Type) [MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
        [SigmaCompactSpace M] [T2Space (TangentBundle 𝓘(ℝ, E3) M)] [CompleteSpace M]
        [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        [IsRiemannianManifold 𝓘(ℝ, E3) M]
        [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        (g : SmoothRiemannianMetric 𝓘(ℝ, E3) M) (hEnorm : IsMetricNorm g),
        ∀ o : ManifoldOrientation (𝓡 3) M 3, ∀ p : M,
        ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, E3) M g (ball p r) →
        (∀ R, 0 < R → R < b⁻¹ → ∀ k ≤ K, ∀ y ∈ ball p R, curvDerivNorm k g y ≤ A R) →
        (∀ y ∈ ball p b⁻¹, SectionalBoundedBelowAt g y (-b ^ 2)) →
        ∀ (σ γ β : ℝ) (E : Set M) (ρ F : M → ℝ) (c : EdgeChart g hEnorm Δ σ μ b γ β E ρ F),
        c.center = p → c.Qn p = 0 →
        (∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
          |dist (c.Qn x) (c.Qn y) - dist x y| ≤ τ * Δ) →
        (∀ x ∈ ball p (200 * Δ), 0 ≤ (c.Qn x).snd) →
        (∀ a ∈ E ∩ ball p (190 * Δ), (c.Qn a).snd ≤ τ * Δ) →
        (∀ t : ℝ, |t| ≤ 100 * Δ →
          ∃ a ∈ E ∩ ball p (190 * Δ), dist (c.Qn a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ) →
        (∀ x, |F x - infDist x E| < μ * Δ) → LipschitzWith Λ ρ →
        ∃ Z : EdgeProductModel c K,
          (∃ oN : ManifoldOrientation (𝓡 3) Z.N 3, ∀ (x : Z.N) (hx : x ∈ Z.j.source),
            Orientation.map (Fin 3)
              ((Z.j.isLocalDiffeomorphAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) (K : ℕ∞ω) hx).mfderivToContinuousLinearEquiv
                (by exact_mod_cast (show K ≠ 0 by omega))).toLinearEquiv (oN.orientation x) =
              o.orientation (Z.j x)) ∧
          closedBall (Z.Θ (0, Z.s₀)) R ⊆ Z.j.source ∧
          (∀ x ∈ closedBall (Z.Θ (0, Z.s₀)) R, ∀ y ∈ closedBall (Z.Θ (0, Z.s₀)) R,
            |dist (Z.j x) (Z.j y) - dist x y| < δ) ∧
          (∀ x ∈ closedBall (Z.Θ (0, Z.s₀)) R,
            |(c.split.toFun (Z.j x)).fst - (Z.Θ.symm x).1| < δ) ∧
          ∃ (T : Finset Z.N) (L : Z.N → Set E3),
            (∀ x ∈ T, IsCompact (L x) ∧ L x ⊆ (extChartAt 𝓘(ℝ, E3) x).target ∧
              (extChartAt 𝓘(ℝ, E3) x).symm '' L x ⊆ Z.j.source ∧
              ∀ k ≤ K - 1, ∀ y ∈ L x, mapDerivNorm k
                (pullbackMetricCoefficients g ((Z.j : Z.N → M) ∘ (extChartAt 𝓘(ℝ, E3) x).symm))
                (chartCoeff Z.G x) y ≤ δ) ∧
            ∀ x ∈ closedBall (Z.Θ (0, Z.s₀)) R, ∃ x' ∈ T, x ∈ (extChartAt 𝓘(ℝ, E3) x').source ∧
              extChartAt 𝓘(ℝ, E3) x' x ∈ interior (L x') := by
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 2 := ⟨K - 2, by omega⟩
  have hk : 3 ≤ k := by omega
  refine exists_threshold_of_sequence (c := 1) one_pos fun bs hb0 hbs _ hneg => ?_
  choose M hn0 using fun n => not_forall.mp (hneg n)
  choose iMet hn1 using fun n => not_forall.mp (hn0 n)
  choose iCh hn2 using fun n => not_forall.mp (hn1 n)
  choose iMan hn3 using fun n => not_forall.mp (hn2 n)
  choose iSig hn4 using fun n => not_forall.mp (hn3 n)
  choose iT2 hn5 using fun n => not_forall.mp (hn4 n)
  choose iCo hn6 using fun n => not_forall.mp (hn5 n)
  choose iCon hn7 using fun n => not_forall.mp (hn6 n)
  choose iRB hn8 using fun n => not_forall.mp (hn7 n)
  choose iRM hn9 using fun n => not_forall.mp (hn8 n)
  choose iCRB hn10 using fun n => not_forall.mp (hn9 n)
  choose g hn11 using fun n => not_forall.mp (hn10 n)
  choose hEnorm hn12 using fun n => not_forall.mp (hn11 n)
  choose o hn13 using fun n => not_forall.mp (hn12 n)
  choose p hn14 using fun n => not_forall.mp (hn13 n)
  choose hvol hn15 using fun n => not_forall.mp (hn14 n)
  choose hcurv hn16 using fun n => not_forall.mp (hn15 n)
  choose hsec hn17 using fun n => not_forall.mp (hn16 n)
  choose σ hn18 using fun n => not_forall.mp (hn17 n)
  choose γ hn19 using fun n => not_forall.mp (hn18 n)
  choose β hn20 using fun n => not_forall.mp (hn19 n)
  choose E hn21 using fun n => not_forall.mp (hn20 n)
  choose ρ hn22 using fun n => not_forall.mp (hn21 n)
  choose F hn23 using fun n => not_forall.mp (hn22 n)
  choose c hn24 using fun n => not_forall.mp (hn23 n)
  choose hcp hn25 using fun n => not_forall.mp (hn24 n)
  choose hQp hn26 using fun n => not_forall.mp (hn25 n)
  choose hQdist hn27 using fun n => not_forall.mp (hn26 n)
  choose hheight hn28 using fun n => not_forall.mp (hn27 n)
  choose hborder hn29 using fun n => not_forall.mp (hn28 n)
  choose hbordercover hn30 using fun n => not_forall.mp (hn29 n)
  choose hF hn31 using fun n => not_forall.mp (hn30 n)
  choose hρL hC using fun n => not_forall.mp (hn31 n)
  have hmetric : ∀ n a b, riemannianEDistOf (g n) a b = ENNReal.ofReal (dist a b) :=
    fun n => riemannianEDistOf_eq_ofReal_dist (g n) (hEnorm n)
  have hball : ∀ n R, riemannianBallOf (g n) ((c n).center) R = ball ((c n).center) R :=
    fun n R => DifferentialGeometry.Geometry.Metric.riemannianBallOf_eq_ball_of_isMetricNorm
      (g n) (hEnorm n) _ R
  have hL : Tendsto (fun n => (bs n)⁻¹) atTop atTop :=
    (tendsto_nhdsWithin_iff.mpr ⟨hbs, Eventually.of_forall hb0⟩).inv_tendsto_nhdsGT_zero
  have hη : Tendsto (fun n => bs n ^ 2) atTop (𝓝 0) := by
    simpa using hbs.pow 2
  let _ : ∀ n, MetricSpace (c n).Y := fun n => (c n).instY
  obtain ⟨φ, -, N, mN, cN, hMN, G, q, j, oN, hprop, hconn, hRiem, -, hbase, hexh, hconv, hdist,
      hcover, -, hor, hsecG, W, mW, w, -, -, e, he, hU⟩ :=
    exists_lcons_merge_noncompact_oriented (k + 2) (by omega) hr hv A g hmetric
      (fun n => (c n).center) o
      (Eventually.of_forall fun n => by
        beta_reduce
        rw [hball, hcp n]
        exact hvol n)
      (fun R hR => by
        filter_upwards [hL.eventually (eventually_gt_atTop R)] with n hn k' hk' y hy
        rw [hball, hcp n] at hy
        exact hcurv n R hR hn k' hk' y hy)
      hη hL (Eventually.of_forall fun n y hy => by
        rw [hball, hcp n] at hy
        exact hsec n y hy)
      (fun n => (c n).split) hbs
  let _ := mN
  let _ := cN
  have _ := hMN
  have _ := hprop
  have _ := hconn
  let _ : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x) := ⟨G.toRiemannianMetric⟩
  have _ : IsRiemannianManifold 𝓘(ℝ, E3) N := hRiem
  let _ := mW
  have _ : CompleteSpace N := complete_of_proper
  have _ : SecondCountableTopology N := secondCountable_of_proper
  let G' : ContMDiffRiemannianMetric 𝓘(ℝ, E3) (((k : ℕ∞) : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _) :=
    { G with contMDiff := by rw [withTop_natCast_add_one]; exact G.contMDiff }
  have hGnorm : ∀ (x : N) (u : TangentSpace 𝓘(ℝ, E3) x),
      ‖u‖ₑ = ENNReal.ofReal (Real.sqrt (G'.inner x u u)) := by
    intro x u
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  have hk2 : (2 : ℕ∞) ≤ (k : ℕ∞) := by exact_mod_cast (show 2 ≤ k by omega)
  -- the surface factor and the product chart (stage 1)
  obtain ⟨S, mS, cS, iS, ψ, κ0, Θ, -, -, ⟨oS⟩, hsecS, hRS, heΘ, hpull, -⟩ :=
    edgeRowModelChart_of_carrier G' hk2 hGnorm (fun x u w => hsecG x u w) oN e
  let _ := mS
  let _ := cS
  have _ := iS
  let _ : RiemannianBundle (fun x : S => TangentSpace (𝓡 2) x) := ⟨κ0.toRiemannianMetric⟩
  obtain ⟨hRiemS, hκnorm⟩ := hRS
  have hΘx : ∀ x : N, e x = WithLp.toLp 2 ((Θ.symm x).1, ψ (Θ.symm x).2) := fun x => by
    rw [← heΘ, Θ.apply_symm_apply]
  have hΘq : Θ (0, ψ.symm w) = q := by
    apply e.injective
    rw [heΘ, he, IsometryEquiv.apply_symm_apply]
  have hdistΘ : ∀ a b : ℝ × S, dist (Θ a) (Θ b) = dist (WithLp.toLp 2 a) (WithLp.toLp 2 b) := by
    intro a b
    have h2 : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
    rw [← e.dist_eq, heΘ, heΘ, WithLp.prod_dist_eq_add h2, WithLp.prod_dist_eq_add h2]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, ψ.dist_eq]
  have hpt : ∀ i, j i q = (c (φ i)).center := fun i => (hbase i).2
  -- the tail estimates
  have hB : IsCompact (closedBall q R) := isCompact_closedBall q R
  obtain ⟨T, Lp, hLp, hLcov, hcmp⟩ := eventually_buffer_chart_comparison (fun i => g (φ i)) G j
    hexh hconv hB hδ
  have hdB := eventually_abs_dist_sub_lt_of_isBounded (fun i => (j i : N → M (φ i))) q hdist
    hB.isBounded hδ
  have hsp := Metric.tendstoUniformlyOn_iff.mp (hU _ hB.isBounded) δ hδ
  have hcoord : TendstoUniformlyOn (fun i x => ((c (φ i)).Qn (j i x)).fst) (fun x => (e x).fst)
      atTop (closedBall q (100 * Δ)) :=
    (hU _ isBounded_closedBall).congr
      (Eventually.of_forall fun i x _ => ((c (φ i)).Qn_fst _).symm)
  have hτ' : τ ≤ 1 / 10000 := hτ1.trans (by norm_num)
  have hh : 20 * Real.sqrt τ < 1 / 10 := by
    have h1 : Real.sqrt τ < 1 / 200 := (Real.sqrt_lt' (by norm_num)).mpr (by
      have : (1 / 10 ^ 30 : ℝ) < (1 / 200) ^ 2 := by norm_num
      linarith)
    linarith
  have hB5 := eventually_edgeSourceSlab_mem_image (fun i => (j i : N → M (φ i))) q hdist
    (fun a b' ha hab => by
      filter_upwards [hcover a b' ha hab] with i hi
      rw [hpt i]
      exact hi)
    e he hΔ0 (by linarith : μ ≤ 1 / 1000) hτ.le hτ' (le_refl (1 / 1000 : ℝ)) hh (by norm_num)
    (hΛ.trans (by norm_num)) (fun i => (c (φ i)).Qn) (fun i => E (φ i)) (fun i => F (φ i))
    (fun i => (c (φ i)).coord) (fun i => ρ (φ i))
    (fun i => by rw [hpt i, hcp]; exact hQp (φ i))
    (fun i => by rw [hpt i, hcp]; exact hQdist (φ i))
    (fun i => by rw [hpt i, hcp]; exact hheight (φ i))
    hcoord
    (fun i => by rw [hpt i]; exact (c (φ i)).center_mem)
    (fun i => by rw [hpt i, hcp]; exact hborder (φ i))
    (fun i => by rw [hpt i, hcp]; exact hbordercover (φ i))
    (fun i x => (hF (φ i) x).le)
    (fun i x hx => by
      rw [hpt i] at hx
      rw [(c (φ i)).Qn_fst]
      exact ((c (φ i)).value x hx).le)
    (fun i => hρL (φ i)) (fun i => by rw [hpt i]; exact (c (φ i)).rho_center)
  obtain ⟨i, ⟨⟨⟨⟨⟨⟨hsrcB, hpatch⟩, hdBi⟩, hspi⟩, hori⟩, hB5i⟩, hsrc7⟩⟩ :=
    (((((hcmp.and hdB).and hsp).and hor).and hB5).and
      (hexh _ (isCompact_closedBall q (7 * Δ)))).exists
  let Z : EdgeProductModel (c (φ i)) (k + 2) :=
    { N := N
      instMetricN := mN
      instChartedN := cN
      instManifoldN := hMN
      instProperN := hprop
      instConnectedN := hconn
      instBundleN := ⟨G.toRiemannianMetric⟩
      instRiemannianN := hRiem
      G := G
      enorm := hGnorm
      sectional_nonneg := hsecG
      S := S
      instMetricS := mS
      instChartedS := cS
      instManifoldS := iS
      instBundleS := ⟨κ0.toRiemannianMetric⟩
      instRiemannianS := hRiemS
      κ := κ0
      enormS := hκnorm
      sectional_nonnegS := hsecS
      orientationS := oS
      Θ := Θ
      dist_Θ := hdistΘ
      product_metric := hpull
      j := j i
      s₀ := ψ.symm w
      base_mem := by rw [hΘq]; exact (hbase i).1
      j_base := by rw [hΘq]; exact hpt i
      slab := fun y hy hfy hHy => by
        have hy' : y ∈ ball (j i q) (100 * Δ) := by rw [hpt i]; exact hy
        obtain ⟨x, hxq, hjx, ht, hs⟩ := hB5i y hy' hfy ((edgeRowHeight_le_iff hΔ0).mp hHy)
        rw [hΘx x] at ht hs
        refine ⟨Θ.symm x, ht, ?_, ?_, ?_⟩
        · rw [← ψ.dist_eq, IsometryEquiv.apply_symm_apply]
          exact hs
        · rw [Θ.apply_symm_apply]
          exact hsrc7 (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
            hxq)
        · rw [Θ.apply_symm_apply]
          exact hjx }
  have hZq : Z.Θ (0, Z.s₀) = q := hΘq
  apply hC (φ i)
  refine ⟨Z, ⟨oN, hori⟩, ?_, ?_, ?_, T, Lp, ?_, ?_⟩
  · rw [hZq]
    exact hsrcB
  · rw [hZq]
    exact hdBi
  · rw [hZq]
    intro x hx
    have h1 := hspi x hx
    rw [dist_comm, Real.dist_eq, hΘx x] at h1
    exact h1
  · intro x hx
    exact ⟨(hLp x hx).1, (hLp x hx).2, (hpatch x hx).1, (hpatch x hx).2⟩
  · rw [hZq]
    exact hLcov

/-- **LC84 item 4, the companion of the packet.** For `b` below the threshold, every edge chart
with LFR28's data extends to an edge disk packet AND has an LC81 product model `ℝ × Z` whose
embedding meets the comparison tolerance `δ` on the buffer of radius `R` (both fixed before the
threshold). -/
theorem exists_edgeDiskPacket_comparison_threshold {Δ σ ε μ τ : ℝ} {Λ : ℝ≥0} (hΔ : 1 ≤ Δ)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 10 ^ 10) (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 10 ^ 8) (hμ : 0 < μ)
    (hμ1 : μ ≤ 1 / 10 ^ 8) (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 10 ^ 30)
    (hΛ : 100 * Δ * Λ ≤ 1 / 10 ^ 8) (K : ℕ) (hK : 5 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) (R : ℝ) :
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b < b₀ →
      ∀ (M : Type) [MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
        [SigmaCompactSpace M] [T2Space (TangentBundle 𝓘(ℝ, E3) M)] [CompleteSpace M]
        [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        [IsRiemannianManifold 𝓘(ℝ, E3) M]
        [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        (g : SmoothRiemannianMetric 𝓘(ℝ, E3) M) (hEnorm : IsMetricNorm g),
        ∀ o : ManifoldOrientation (𝓡 3) M 3, ∀ p : M,
        ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, E3) M g (ball p r) →
        (∀ R, 0 < R → R < b⁻¹ → ∀ k ≤ K, ∀ y ∈ ball p R, curvDerivNorm k g y ≤ A R) →
        (∀ y ∈ ball p b⁻¹, SectionalBoundedBelowAt g y (-b ^ 2)) →
        ∀ (γ β : ℝ) (E : Set M) (ρ F : M → ℝ) (c : EdgeChart g hEnorm Δ σ μ b γ β E ρ F)
          (OF : Set M), c.center = p → c.Qn p = 0 →
        (∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
          |dist (c.Qn x) (c.Qn y) - dist x y| ≤ τ * Δ) →
        (∀ x ∈ ball p (200 * Δ), 0 ≤ (c.Qn x).snd) →
        (∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
          ∃ x ∈ ball p (200 * Δ), dist (c.Qn x) z ≤ τ * Δ) →
        IsClosed E →
        (∀ a ∈ E ∩ ball p (190 * Δ), (c.Qn a).snd ≤ τ * Δ) →
        (∀ t : ℝ, |t| ≤ 100 * Δ →
          ∃ a ∈ E ∩ ball p (190 * Δ), dist (c.Qn a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ) →
        (∀ x, |F x - infDist x E| < μ * Δ) →
        IsOpen OF →
        closedBall p (20 * Δ) ∩ {y | 3 / 4 * Δ ≤ infDist y E ∧ infDist y E ≤ 21 / 2 * Δ} ⊆ OF →
        ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ F OF →
        (∀ y ∈ closedBall p (20 * Δ) ∩ {y | 3 / 4 * Δ ≤ infDist y E ∧ infDist y E ≤ 21 / 2 * Δ},
          ∀ u ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo g E y,
            Real.sqrt (g.inner y (gradFun g F y + u) (gradFun g F y + u)) < ε) →
        (∀ y ∈ closedBall p (20 * Δ) ∩ {y | 3 / 4 * Δ ≤ infDist y E ∧ infDist y E ≤ 21 / 2 * Δ},
          Real.sqrt (g.inner y (gradFun g (fun z => F z / ρ z) y - gradFun g F y)
            (gradFun g (fun z => F z / ρ z) y - gradFun g F y)) ≤ 100 * Δ * Λ) →
        (∀ x ∈ ball p (20 * Δ), infDist x E < 41 / 4 * Δ →
          ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (edgeRowHeight Δ F ρ) x) →
        LipschitzWith Λ ρ → ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ ρ (ball p (100 * Δ)) →
        ∃ P : EdgeDiskPacket g hEnorm Δ σ μ b γ β E ρ F, P.toEdgeChart = c ∧
        ∃ Z : EdgeProductModel c K,
          (∃ oN : ManifoldOrientation (𝓡 3) Z.N 3, ∀ (x : Z.N) (hx : x ∈ Z.j.source),
            Orientation.map (Fin 3)
              ((Z.j.isLocalDiffeomorphAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) (K : ℕ∞ω) hx).mfderivToContinuousLinearEquiv
                (by exact_mod_cast (show K ≠ 0 by omega))).toLinearEquiv (oN.orientation x) =
              o.orientation (Z.j x)) ∧
          closedBall (Z.Θ (0, Z.s₀)) R ⊆ Z.j.source ∧
          (∀ x ∈ closedBall (Z.Θ (0, Z.s₀)) R, ∀ y ∈ closedBall (Z.Θ (0, Z.s₀)) R,
            |dist (Z.j x) (Z.j y) - dist x y| < δ) ∧
          (∀ x ∈ closedBall (Z.Θ (0, Z.s₀)) R,
            |(c.split.toFun (Z.j x)).fst - (Z.Θ.symm x).1| < δ) ∧
          ∃ (T : Finset Z.N) (L : Z.N → Set E3),
            (∀ x ∈ T, IsCompact (L x) ∧ L x ⊆ (extChartAt 𝓘(ℝ, E3) x).target ∧
              (extChartAt 𝓘(ℝ, E3) x).symm '' L x ⊆ Z.j.source ∧
              ∀ k ≤ K - 1, ∀ y ∈ L x, mapDerivNorm k
                (pullbackMetricCoefficients g ((Z.j : Z.N → M) ∘ (extChartAt 𝓘(ℝ, E3) x).symm))
                (chartCoeff Z.G x) y ≤ δ) ∧
            ∀ x ∈ closedBall (Z.Θ (0, Z.s₀)) R, ∃ x' ∈ T, x ∈ (extChartAt 𝓘(ℝ, E3) x').source ∧
              extChartAt 𝓘(ℝ, E3) x' x ∈ interior (L x') := by
  obtain ⟨bd₀, hbd₀, hpk⟩ := exists_edgeDiskPacket_threshold hΔ hσ hσ1 hε hε1 hμ hμ1 hτ hτ1 hΛ K hK
    hr hv A
  obtain ⟨bc₀, hbc₀, hcm⟩ := edgeChart_productModel_threshold hΔ hμ1 hτ hτ1 hΛ K hK hr hv A hδ R
  refine ⟨min bd₀ bc₀, lt_min hbd₀ hbc₀, fun b hb hbb M _ _ _ _ _ _ _ _ _ _ g hEnorm o p hvol hcurv
    hsec γ β E ρ F c OF hcp hQp hQdist hheight hQcover hEc hborder hbordercover hF hOF hCO hFs hFgrad
    hquot hHs hρL hρs => ?_⟩
  obtain ⟨P, hP⟩ := hpk b hb (hbb.trans_le (min_le_left _ _)) M g hEnorm o p hvol hcurv hsec γ β E ρ
    F c OF hcp hQp hQdist hheight hQcover hEc hborder hbordercover hF hOF hCO hFs hFgrad hquot hHs
    hρL hρs
  exact ⟨P, hP, hcm b hb (hbb.trans_le (min_le_right _ _)) M g hEnorm o p hvol hcurv hsec σ γ β E ρ
    F c hcp hQp hQdist hheight hborder hbordercover hF hρL⟩

end DifferentialGeometry.Geometry.Collapse
