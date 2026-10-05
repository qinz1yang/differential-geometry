import DifferentialGeometry.Geometry.Collapse.EdgeRowSequenceApplications
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.LConsMergeNoncompact
import DifferentialGeometry.Geometry.Metric.Approximation.RiemannianHausdorffVolume
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound
import DifferentialGeometry.Geometry.Collapse.SublevelCore.ScaledMinimizingDirections

/-!
# LFR28 row, threshold form

Blueprint 207A, LFR28 (`thm:collapse-finite-source-edge-packet`, A:27223): "These choices precede
`K ≥ 5`, noncollapse data `r₀, v > 0` and finite derivative bounds `A(R) > 0`. For all
sufficiently small `β > 0`, depending also on these later data, ..." and the compactness frame of
its proof ("If the claimed uniform `β` threshold fails, take counterexamples `β_i → 0` ...").

`edgeSourceSlab_disk_bundle_threshold`: the universal tolerances `Δ ≥ 1`, `σ ≤ 10⁻¹⁰`,
`ε, μ ≤ 10⁻⁸`, `τ ≤ 10⁻³⁰`, `100ΔΛ ≤ 10⁻⁸` come first; then `K ≥ 5`, `r, v > 0`, `A`; then
`∃ b₀ > 0` such that for every `b < b₀`, every complete connected ORIENTED smooth `3`-manifold
`(M, g)` with `Vol B(p, r) ≥ v`, `|∇^k Rm| ≤ A(R)` on `B(p, R)` (`k ≤ K`, `R < b⁻¹`),
`sec ≥ -b²` on `B(p, b⁻¹)`, every ACTUAL `(1, b)`-splitting `α` whose first coordinate is that of a
coarse-border chart `Q` of a closed set `E ∋ p` (tolerance `τΔ`), every LFR27 output `F` of `d_E`
with scale `ρ` (value, gradient, quotient and smooth-core clauses), and EVERY LFR19 coordinate `f`
(smooth near `B̄(p, 100Δ)`, `(1+σ)`-Lipschitz, value error `μΔ` against `α`, the (LFR19.1) test
on `B(p, 100Δ) × B(p, 1000Δ)`): with `H = Δψ(F/(ρΔ))` there is an open `O ⊆ B(p, 20Δ)` containing
the whole closed slab `{y ∈ B(p, 100Δ) : |f y| ≤ 4Δ, H y ≤ 4Δ}` such that for every
`-4Δ < a₀ < 0 < b₀' < 4Δ` (F8-LPA3's clauses (1)–(3)):
(1) the fibre `S₀ = {f = 0, H ≤ 4Δ}` of `O` (regular sublevel of `(f, 4Δ - H)`, `O` charted on
    `ModelProd ℝ E2` along `E3 ≃ ℝ × E2`) is diffeomorphic to `ClosedCell 2`, compact, connected;
(2) `Θ' : S₀ × (a₀, b₀') → O` smooth, `f ∘ Θ' = pr₂`, `H ≤ 4Δ`, `Θ'(x, 0) = x`, injective, onto
    `{a₀ < f < b₀', H ≤ 4Δ}` with a smooth retraction on an open neighbourhood;
(3) the boundary points of `S₀` are exactly `{H = 4Δ}`.

Proof: a sequence of counterexamples with `b_n → 0` (and `b_n < 1/(1000Δ)`); the L-CONS merge
(`exists_lcons_merge_noncompact_oriented`) gives one subsequence with an oriented nonnegatively
curved limit and an exact splitting tracked by the first coordinates of the `α_n`; the sequence
form `eventually_edgeSourceSlab_disk_bundle` (curvature bound `κs = 1/(100Δ)` on `B(p, 1000Δ)`)
contradicts.
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

local instance nezero_finrank_euclidean_three_threshold_LFR28ROW2 :
    NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

/-- The compactness-contradiction frame: if no sequence `β_n → 0` (`0 < β_n < c`) has
`¬ P (β_n)` for every `n`, then `P b` holds for every sufficiently small `b > 0`. -/
theorem exists_threshold_of_sequence {P : ℝ → Prop} {c : ℝ} (hc : 0 < c)
    (h : ∀ β : ℕ → ℝ, (∀ n, 0 < β n) → Tendsto β atTop (𝓝 0) → (∀ n, β n < c) →
      (∀ n, ¬ P (β n)) → False) :
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b < b₀ → P b := by
  by_contra hcon
  push Not at hcon
  have hn : ∀ n : ℕ, ∃ b, 0 < b ∧ b < min (1 / ((n : ℝ) + 1)) c ∧ ¬ P b := fun n =>
    hcon _ (lt_min (by positivity) hc)
  choose β hβ0 hβlt hβP using hn
  refine h β hβ0 ?_ (fun n => (hβlt n).trans_le (min_le_right _ _)) hβP
  exact squeeze_zero' (Eventually.of_forall fun n => (hβ0 n).le)
    (Eventually.of_forall fun n => ((hβlt n).trans_le (min_le_left _ _)).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- **LFR28 (the whole source edge disk bundle), threshold form.** See the module docstring. -/
theorem edgeSourceSlab_disk_bundle_threshold {Δ σ ε μ τ : ℝ} {Λ : ℝ≥0} (hΔ : 1 ≤ Δ)
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
        ∃ O : TopologicalSpace.Opens M,
        (O : Set M) ⊆ ball p (20 * Δ) ∧
        (∀ y ∈ ball p (100 * Δ), |f y| ≤ 4 * Δ → edgeRowHeight Δ F ρ y ≤ 4 * Δ → y ∈ O) ∧
        ∀ (a₀ b₀ : ℝ), -(4 * Δ) < a₀ → ∀ (h0 : (0 : ℝ) ∈ Ioo a₀ b₀), b₀ < 4 * Δ →
        letI := chartedSpaceTransHomeomorph (M := O) euclideanThreeProdHomeomorph
        letI : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ O := edgeSource_isManifold
        ∃ (hΨ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ (fun y : O => f y))
          (hB : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
            (fun y : O => 4 * Δ - edgeRowHeight Δ F ρ y))
          (hreg : ∀ y : O, f y = 0 → 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y →
            Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) (fun y : O => f y) y))
          (hregb : ∀ y : O, f y = 0 → 4 * Δ - edgeRowHeight Δ F ρ y = 0 →
            Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
              (fun y : O => ((f y, 4 * Δ - edgeRowHeight Δ F ρ y) : ℝ × ℝ)) y)),
          letI := regularSublevelChartedSpace finrank_real_prod_euclideanTwo hΨ hB hreg hregb
          let Q₀ : TopologicalSpace.Opens ℝ := ⟨Ioo a₀ b₀, isOpen_Ioo⟩
          Nonempty (ClosedCell 2 ≃ₘ⟮𝓡∂ (1 + 1), 𝓡∂ (1 + 1)⟯
            {y : O // f y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y}) ∧
          CompactSpace {y : O // f y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y} ∧
          ConnectedSpace {y : O // f y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y} ∧
          (∃ Θ' : {y : O // f y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y} × Q₀ → O,
            ContMDiff ((𝓡∂ (1 + 1)).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ Θ' ∧
            (∀ p, f (Θ' p) = p.2 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ (Θ' p)) ∧
            (∀ x, Θ' (x, ⟨0, h0⟩) = x) ∧ Injective Θ' ∧
            ∃ O' : Set O, IsOpen O' ∧
              (∀ y : O, f y ∈ Ioo a₀ b₀ → 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y → y ∈ O') ∧
              ∃ R : O → O, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ R O' ∧
                ∀ (y : O) (hy : f y ∈ Ioo a₀ b₀),
                  0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y →
                  ∃ hR : f (R y) = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ (R y),
                    Θ' (⟨R y, hR⟩, ⟨f y, hy⟩) = y) ∧
          ∀ y : {y : O // f y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y},
            (𝓡∂ (1 + 1)).IsBoundaryPoint y ↔ edgeRowHeight Δ F ρ y = 4 * Δ := by
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 2 := ⟨K - 2, by omega⟩
  have hk : 3 ≤ k := by omega
  refine exists_threshold_of_sequence (c := 1 / (1000 * Δ)) (by positivity)
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
  have hβφ : ∀ i, β (φ i) ≤ 1 / (1000 * Δ) := fun i => (hβc (φ i)).le
  -- the curvature bound `κs = 1/(100Δ)` on `B(p, 1000Δ)`
  have hsec' : ∀ i, ∀ z ∈ ball (j i q) (1000 * Δ),
      SectionalBoundedBelowAt (g (φ i)) z (-(1 / (100 * Δ)) ^ 2) := by
    intro i z hz
    rw [hpt i] at hz
    have hb0 := hβ0 (φ i)
    have hbinv : 1000 * Δ ≤ (β (φ i))⁻¹ := by
      rw [le_inv_comm₀ (by positivity) hb0, inv_eq_one_div]
      exact hβφ i
    have hz' : z ∈ ball (p (φ i)) (β (φ i))⁻¹ := ball_subset_ball hbinv hz
    refine (hsec (φ i) z hz').mono ?_
    have h1 : β (φ i) ≤ 1 / (100 * Δ) := (hβφ i).trans (by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith)
    have h2 : β (φ i) ^ 2 ≤ (1 / (100 * Δ)) ^ 2 := pow_le_pow_left₀ hb0.le h1 2
    linarith
  have hκsΔ : 1 / (100 * Δ) * Δ ≤ 1 / 100 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hEv := eventually_edgeSourceSlab_disk_bundle (M := fun i => M (φ i)) hk G' hGnorm
    (fun x u w => hsecG x u w) oN (fun i => g (φ i)) (fun i => hEnorm (φ i))
    (fun i => hmetric (φ i)) q j hexh
    (fun x L hL hLt => (hconv x L hL hLt).mono_order (by omega)) hdist
    (fun a b ha hab => by
      filter_upwards [hcover a b ha hab] with i hi
      rw [hpt i]
      exact hi)
    (fun R ε' hε' => by
      filter_upwards [hcov R ε' hε'] with i hi
      rw [hpt i]
      exact hi)
    e he hΔ hσ hσ1 hε hε1 hμ hμ1 hτ hτ1 hΛ (by positivity : (0 : ℝ) < 1 / (100 * Δ)) hκsΔ
    (fun i => Q (φ i)) (fun i => E (φ i)) (fun i z => ((α (φ i)).toFun z).fst)
    (fun i => F (φ i)) (fun i => f (φ i)) (fun i => ρ (φ i))
    (fun C hC => hU C hC.isBounded) (fun i => hQU (φ i))
    (fun i => by rw [hpt i]; exact hQp (φ i)) (fun i => by rw [hpt i]; exact hQdist (φ i))
    (fun i => by rw [hpt i]; exact hheight (φ i)) (fun i => by rw [hpt i]; exact hQcover (φ i))
    (fun i => hEc (φ i)) (fun i => by rw [hpt i]; exact hpE (φ i))
    (fun i => by rw [hpt i]; exact hborder (φ i))
    (fun i => by rw [hpt i]; exact hbordercover (φ i)) hsec' (fun i => hF (φ i))
    (fun i => OF (φ i)) (fun i => hOF (φ i)) (fun i => by rw [hpt i]; exact hCO (φ i))
    (fun i => hFs (φ i)) (fun i => by rw [hpt i]; exact hFgrad (φ i))
    (fun i => by rw [hpt i]; exact hquot (φ i)) (fun i => by rw [hpt i]; exact hHs (φ i))
    (fun i => hρ (φ i)) (fun i => by rw [hpt i]; exact hρp (φ i))
    (fun i => by rw [hpt i]; exact hρs (φ i)) (fun i => Of (φ i)) (fun i => hOf (φ i))
    (fun i => by rw [hpt i]; exact hOfb (φ i)) (fun i => hfs (φ i)) (fun i => hflip (φ i))
    (fun i => by rw [hpt i]; exact hfval (φ i)) (fun i => by rw [hpt i]; exact hftest (φ i))
  obtain ⟨i, hi⟩ := hEv.exists
  rw [hpt i] at hi
  exact hC (φ i) hi

end DifferentialGeometry.Geometry.Collapse
