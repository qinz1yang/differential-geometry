import DifferentialGeometry.Geometry.Collapse.EdgeRowThreshold
import DifferentialGeometry.Geometry.Collapse.EdgeRowCoreSection

/-!
# The core-line section of the edge coordinate, threshold form (EGP05 / CGP03)

`edgeSourceSlab_core_section_threshold` (statement frozen by lane C14-KA,
build-logs/scratch/C14-KA/EdgeSectionTargets.lean; blueprint 207B EGP05 B:5042–5085, CGP03 edge case
B:4029–4053): binders and parameter order of `edgeSourceSlab_disk_bundle_threshold`; the conclusion
is the continuous section `sec : (-8.5Δ, 8.5Δ) → M` of the LFR19 coordinate `f` with
`F/ρ < Δ/100` and `d(sec a, p) < 10Δ`.

Proof: the compactness-contradiction frame of `edgeSourceSlab_disk_bundle_threshold`
(`exists_threshold_of_sequence`, the L-CONS merge `exists_lcons_merge_noncompact_oriented`) with
the sequence form `eventually_edgeSourceSlab_core_section`. The counterexamples are taken below
`min(1/(1000Δ), b₁)`, `b₁` the threshold of `edgeSourceSlab_disk_bundle_threshold` for the same
data, so the threshold produced here also works for the slab bundle (the two consumers take one
`b₀`).
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

local instance nezero_finrank_euclidean_three_secthr_LFR28ROW2 :
    NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

/-- **Augmented LFR28 (core-line section), threshold form** — consumed by EGP05 (`(−8.5Δ, 8.5Δ)`)
and CGP03 (`[−23Δ/4, 23Δ/4]`, by restriction). -/
theorem edgeSourceSlab_core_section_threshold {Δ σ ε μ τ : ℝ} {Λ : ℝ≥0} (hΔ : 1 ≤ Δ)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 10 ^ 10) (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 10 ^ 8) (hμ : 0 < μ)
    (hμ1 : μ ≤ 1 / 10 ^ 8) (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 10 ^ 30)
    (hΛ : 100 * Δ * Λ ≤ 1 / 10 ^ 8) (K : ℕ) (hK : 5 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ) :
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b < b₀ →
      ∀ (M : Type) [MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
        [SigmaCompactSpace M] [T2Space (TangentBundle 𝓘(ℝ, E3) M)] [CompleteSpace M]
        [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        [IsRiemannianManifold 𝓘(ℝ, E3) M]
        [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        (g : SmoothRiemannianMetric 𝓘(ℝ, E3) M) (hEnorm : IsMetricNorm g),
        ManifoldOrientation (𝓡 3) M 3 → ∀ p : M,
        ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, E3) M g (ball p r) →
        (∀ R, 0 < R → R < b⁻¹ → ∀ k ≤ K, ∀ y ∈ ball p R, curvDerivNorm k g y ≤ A R) →
        (∀ y ∈ ball p b⁻¹, SectionalBoundedBelowAt g y (-b ^ 2)) →
        ∀ (Y : Type) [MetricSpace Y] (y₀ : Y)
          (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) b)
          (Q : M → WithLp 2 (ℝ × ℝ)) (E : Set M) (F f ρ : M → ℝ) (OF Of : Set M),
        (∀ z, (Q z).fst = (α.toFun z).fst) → Q p = 0 →
        (∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
          |dist (Q x) (Q y) - dist x y| ≤ τ * Δ) →
        (∀ x ∈ ball p (200 * Δ), 0 ≤ (Q x).snd) →
        (∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
          ∃ x ∈ ball p (200 * Δ), dist (Q x) z ≤ τ * Δ) →
        IsClosed E → p ∈ E →
        (∀ a ∈ E ∩ ball p (190 * Δ), (Q a).snd ≤ τ * Δ) →
        (∀ t : ℝ, |t| ≤ 100 * Δ →
          ∃ a ∈ E ∩ ball p (190 * Δ), dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ) →
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
        LipschitzWith Λ ρ → ρ p = 1 → ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ ρ (ball p (100 * Δ)) →
        IsOpen Of → closedBall p (100 * Δ) ⊆ Of → ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ f Of →
        LipschitzWith (Real.toNNReal (1 + σ)) f →
        (∀ x ∈ ball p (100 * Δ), |f x - (α.toFun x).fst| < μ * Δ) →
        (∀ x ∈ ball p (100 * Δ), ∀ x' ∈ ball p (1000 * Δ), 100 * Δ < dist x x' →
          ∀ w : TangentSpace 𝓘(ℝ, E3) x, g.inner x w w = 1 →
          intrinsicGeodesic g hEnorm x w (dist x x') = x' →
          |mvfderiv 𝓘(ℝ, E3) f x w - ((α.toFun x').fst - (α.toFun x).fst) / dist x x'| < σ) →
        ∃ sec : Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ) → M, Continuous sec ∧
          ∀ a : Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ),
            f (sec a) = a ∧ F (sec a) / ρ (sec a) < Δ / 100 ∧ dist (sec a) p < 10 * Δ := by
  obtain ⟨b₁, hb₁, -⟩ := edgeSourceSlab_disk_bundle_threshold hΔ hσ hσ1 hε hε1 hμ hμ1 hτ hτ1 hΛ K hK
    hr hv A
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 2 := ⟨K - 2, by omega⟩
  have hk : 3 ≤ k := by omega
  refine exists_threshold_of_sequence (c := min (1 / (1000 * Δ)) b₁) (lt_min (by positivity) hb₁)
    fun β hβ0 hβ hβc hneg => ?_
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
  choose Y hn18 using fun n => not_forall.mp (hn17 n)
  choose iY hn19 using fun n => not_forall.mp (hn18 n)
  choose y₀ hn20 using fun n => not_forall.mp (hn19 n)
  choose α hn21 using fun n => not_forall.mp (hn20 n)
  choose Q hn22 using fun n => not_forall.mp (hn21 n)
  choose E hn23 using fun n => not_forall.mp (hn22 n)
  choose F hn24 using fun n => not_forall.mp (hn23 n)
  choose f hn25 using fun n => not_forall.mp (hn24 n)
  choose ρ hn26 using fun n => not_forall.mp (hn25 n)
  choose OF hn27 using fun n => not_forall.mp (hn26 n)
  choose Of hn28 using fun n => not_forall.mp (hn27 n)
  choose hQU hn29 using fun n => not_forall.mp (hn28 n)
  choose hQp hn30 using fun n => not_forall.mp (hn29 n)
  choose hQdist hn31 using fun n => not_forall.mp (hn30 n)
  choose hheight hn32 using fun n => not_forall.mp (hn31 n)
  choose hQcover hn33 using fun n => not_forall.mp (hn32 n)
  choose hEc hn34 using fun n => not_forall.mp (hn33 n)
  choose hpE hn35 using fun n => not_forall.mp (hn34 n)
  choose hborder hn36 using fun n => not_forall.mp (hn35 n)
  choose hbordercover hn37 using fun n => not_forall.mp (hn36 n)
  choose hF hn38 using fun n => not_forall.mp (hn37 n)
  choose hOF hn39 using fun n => not_forall.mp (hn38 n)
  choose hCO hn40 using fun n => not_forall.mp (hn39 n)
  choose hFs hn41 using fun n => not_forall.mp (hn40 n)
  choose hFgrad hn42 using fun n => not_forall.mp (hn41 n)
  choose hquot hn43 using fun n => not_forall.mp (hn42 n)
  choose hHs hn44 using fun n => not_forall.mp (hn43 n)
  choose hρ hn45 using fun n => not_forall.mp (hn44 n)
  choose hρp hn46 using fun n => not_forall.mp (hn45 n)
  choose hρs hn47 using fun n => not_forall.mp (hn46 n)
  choose hOf hn48 using fun n => not_forall.mp (hn47 n)
  choose hOfb hn49 using fun n => not_forall.mp (hn48 n)
  choose hfs hn50 using fun n => not_forall.mp (hn49 n)
  choose hflip hn51 using fun n => not_forall.mp (hn50 n)
  choose hfval hn52 using fun n => not_forall.mp (hn51 n)
  choose hftest hC using fun n => not_forall.mp (hn52 n)
  have hmetric : ∀ n a b, riemannianEDistOf (g n) a b = ENNReal.ofReal (dist a b) :=
    fun n => riemannianEDistOf_eq_ofReal_dist (g n) (hEnorm n)
  have hball : ∀ n R, riemannianBallOf (g n) (p n) R = ball (p n) R :=
    fun n R => DifferentialGeometry.Geometry.Metric.riemannianBallOf_eq_ball_of_isMetricNorm
      (g n) (hEnorm n) (p n) R
  have hL : Tendsto (fun n => (β n)⁻¹) atTop atTop :=
    (tendsto_nhdsWithin_iff.mpr ⟨hβ, Eventually.of_forall hβ0⟩).inv_tendsto_nhdsGT_zero
  have hη : Tendsto (fun n => β n ^ 2) atTop (𝓝 0) := by
    simpa using hβ.pow 2
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, oN, hprop, hconn, hRiem, -, hbase, hexh, hconv, hdist,
      hcover, hcov, -, hsecG, W, mW, w, -, -, e, he, hU⟩ :=
    exists_lcons_merge_noncompact_oriented (k + 2) (by omega) hr hv A g hmetric p o
      (Eventually.of_forall fun n => by rw [hball]; exact hvol n)
      (fun R hR => by
        filter_upwards [hL.eventually (eventually_gt_atTop R)] with n hn k' hk' y hy
        rw [hball] at hy
        exact hcurv n R hR hn k' hk' y hy)
      hη hL (Eventually.of_forall fun n y hy => by rw [hball] at hy; exact hsec n y hy) α hβ
  let _ := mN
  let _ := cN
  have _ := hMN
  have _ := hprop
  have _ := hconn
  let _ : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x) := ⟨G.toRiemannianMetric⟩
  have _ : IsRiemannianManifold 𝓘(ℝ, E3) N := hRiem
  let _ := mW
  let G' : ContMDiffRiemannianMetric 𝓘(ℝ, E3) (((k : ℕ∞) : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _) :=
    { G with contMDiff := by rw [withTop_natCast_add_one]; exact G.contMDiff }
  have hGnorm : ∀ (x : N) (u : TangentSpace 𝓘(ℝ, E3) x),
      ‖u‖ₑ = ENNReal.ofReal (Real.sqrt (G'.inner x u u)) := by
    intro x u
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  have hpt : ∀ i, j i q = p (φ i) := fun i => (hbase i).2
  have hpt : ∀ i, j i q = p (φ i) := fun i => (hbase i).2
  have hEv := eventually_edgeSourceSlab_core_section (M := fun i => M (φ i)) (by omega : 2 ≤ k) G'
    hGnorm (fun i => g (φ i)) (fun i => hEnorm (φ i)) (fun i => hmetric (φ i)) q j hexh
    (fun x L hL hLt => (hconv x L hL hLt).mono_order (by omega)) hdist
    (fun a b ha hab => by
      filter_upwards [hcover a b ha hab] with i hi
      rw [hpt i]
      exact hi)
    e he hΔ hσ (hσ1.trans (by norm_num)) (hμ1.trans (by norm_num)) hτ (hτ1.trans (by norm_num))
    (hΛ.trans (by norm_num)) (fun i => Q (φ i)) (fun i => E (φ i))
    (fun i z => ((α (φ i)).toFun z).fst) (fun i => F (φ i)) (fun i => f (φ i))
    (fun i => ρ (φ i)) (fun C hC => hU C hC.isBounded) (fun i => hQU (φ i))
    (fun i => by rw [hpt i]; exact hQp (φ i)) (fun i => by rw [hpt i]; exact hQdist (φ i))
    (fun i => by rw [hpt i]; exact hheight (φ i)) (fun i => by rw [hpt i]; exact hpE (φ i))
    (fun i => by rw [hpt i]; exact hborder (φ i))
    (fun i => by rw [hpt i]; exact hbordercover (φ i)) (fun i => hF (φ i))
    (fun i => hρ (φ i)) (fun i => by rw [hpt i]; exact hρp (φ i)) (fun i => Of (φ i))
    (fun i => hOf (φ i)) (fun i => by rw [hpt i]; exact hOfb (φ i)) (fun i => hfs (φ i))
    (fun i => hflip (φ i)) (fun i => by rw [hpt i]; exact hfval (φ i))
    (fun i => by rw [hpt i]; exact hftest (φ i))
  obtain ⟨i, hi⟩ := hEv.exists
  rw [hpt i] at hi
  exact hC (φ i) hi

end DifferentialGeometry.Geometry.Collapse
