import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamily
import DifferentialGeometry.Geometry.Collapse.SimultaneousSlimFibreTypeReordered

/-!
# LC87 items 2–3: the producer of the local chart family on the reordered LPA04 tail

`eventually_nonempty_localChartFamily`: with the standing data `σs, K ≥ 5, A` fixed first and then
EXACTLY the parameter order of `eventually_simultaneous_slim_packets_with_models_reordered`
(LPA04's order, master207A:30447–30547; order table in `build-logs/resume/state-F8-LPA3.md`), on ONE
late tail of a sequence of closed oriented Riemannian three-manifolds there is ONE scale `ρ` with
LC02's bounds and

* a `LocalChartFamily` for `ρ` and this single assignment: the circle family (LPA03/LPA06), the slim
  family with the LC85 packet and the LC81 product model at every slim centre (LFR20 at
  `r = 1`, `v = v_*`, `𝒜`), the strong-edge family with ONE shared smoothing and an LC84 `EdgeChart`
  (items 1–3) at every edge centre, and the stratum exhaustion; and
* on the SAME tail and the SAME `ρ`, the tail's zero conjunct in its LPA05-input form (for every
  radius function `r ∈ [Tρ, Vρ]` and every choice of zero witnesses there is a finite `r`-disjoint
  selection whose tenth balls cover the zero stratum and whose LC31 cutoffs are as in LC80 as soon as
  the witnesses satisfy their clauses at the selected centres).

The proof re-chains `eventually_simultaneous_local_cover_with_edge_coordinates_reordered` (the last
reordered tail that still carries the circle family and the zero conjunct) with LPA01's analytic data
(`eventually_simultaneous_analytic_data`) and the per-centre producers `exists_slimChart_at_centre`,
`exists_slimPacket_threshold`, `slimChart_model_embedding_threshold` (as in
`eventually_simultaneous_slim_packets_with_models_reordered`) and, at the edge centres, the tail's
collar block with `exists_physical_coarse_border_chart` (as in `exists_edgeCharts_of_strong_edge_family`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Topology.Ehresmann
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u v

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- `140 √τ < ε²/20` with `ε < 1/100` forces `τ < 1/10⁴` (the coarse-border threshold). -/
theorem lt_of_sqrt_budget_LC87 {ε τ : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 100) (hτ : 0 ≤ τ)
    (hθ : 140 * Real.sqrt τ < ε ^ 2 / 20) : τ < 1 / 10000 := by
  have hs0 : 0 ≤ Real.sqrt τ := Real.sqrt_nonneg τ
  have hε2 : ε ^ 2 < 1 / 10000 := by nlinarith
  have hs : Real.sqrt τ < 1 / 100 := by nlinarith
  have hsq : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ
  nlinarith

/-- **Producer of the LC87 local chart family on the reordered tail.** See the module docstring. -/
theorem eventually_nonempty_localChartFamily
    {σs : ℝ} (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100) (K : ℕ) (hK : 5 ≤ K) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ σ₀ → σc < 1 → 0 < ε → ε < 1 / 100 → 0 < μ → μ ≤ 1 / 1000000 →
        0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{u, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{u, 0} →
      ∀ ζ : ℝ, β 1 < ζ → ζ < 1 →
      ∃ εz δ' Λ' : ℝ, 0 < εz ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T V : ℝ, ∀ hT : 0 < T, 20 * Λ' ≤ T → T ≤ V →
      ∀ (X : ℕ → Type u) [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
        [∀ i, IsManifold 𝓘(ℝ, E3) ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E3) (X i))
        (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
        (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
        (∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
          ∀ C, 0 < C → C < α i → ∀ k ≤ K,
          ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
            curvatureDerivativeNorm (g i) k y ≤
              A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹) →
        (∀ i, ManifoldOrientation (𝓡 3) (X i) 3) →
      ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        (∀ p, firstVolumeScale (g i) p w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
        Nonempty (LocalChartFamily (X i) (g i) (hmetric i) ρ hρpos Λ β Δ σs K
          σc μ b s b' s' ε γc βc) ∧
            ∀ r : X i → ℝ, ∀ hlower : ∀ p, T * ρ p ≤ r p, (∀ p, r p ≤ V * ρ p) →
            ∀ (N C : X i → Type v) [mN : ∀ j, MetricSpace (N j)] [∀ j, ProperSpace (N j)]
              [mC : ∀ j, MetricSpace (C j)] [∀ j, ProperSpace (C j)]
              (n₀ : ∀ j, N j) (o : ∀ j, C j), (∀ j, RadialConeData (o j)) →
            ∀ (δ : X i → ℝ) (η : X i → X i → ℝ) (O : X i → Set (X i)) {e : ℝ}, e < 1 / 40 →
            ∃ J₀ : Set (X i), J₀.Finite ∧ J₀.PairwiseDisjoint (fun j => ball j (r j)) ∧
              ((∀ j ∈ J₀,
              fourPointComparison 0 (univ : Set (N j)) ∧
              (∀ x y : N j, ∃ f : Icc (0 : ℝ) 1 → N j,
                Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
                ∀ s t, dist (f s) (f t) = dist x y * dist s t) ∧
              (∀ δ₁ : ℝ, 0 < δ₁ → δ₁ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ,
                R₀ ≤ R → ∀ hR : 0 < R, Nonempty (@KleinerLottApprox (N j) (C j)
                  ((mN j).rescale R⁻¹ (inv_pos.mpr hR)) (mC j) (n₀ j) (o j) δ₁)) ∧
              δ j < δ' ∧
              Nonempty (@KleinerLottApprox (X i) (C j)
                ((mX i).rescale (r j)⁻¹ (inv_pos.mpr ((mul_pos hT (hρpos j)).trans_le (hlower j))))
                (mC j) j (o j) (δ j)) ∧
              ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (η j)
                {x | 3 / 40 ≤ (r j)⁻¹ * dist x j ∧ (r j)⁻¹ * dist x j ≤ 11} ∧
              (∀ x y, |(η j x - (r j)⁻¹ * dist j x) - (η j y - (r j)⁻¹ * dist j y)| ≤
                εz * ((r j)⁻¹ * dist x y)) ∧
              Continuous (η j) ∧ IsOpen (O j) ∧ ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (η j) (O j) ∧
              η j ⁻¹' Icc (1 / 5 : ℝ) (9 / 10) ⊆ O j ∧
              (∀ x, |η j x - (r j)⁻¹ * dist x j| < e) ∧
              ∀ q ∈ η j ⁻¹' Icc (1 / 5 : ℝ) (9 / 10),
                Real.sqrt ((scaleMetric ((r j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr
                  ((mul_pos hT (hρpos j)).trans_le (hlower j))) 2) (g i)).inner q
                  (gradFun (scaleMetric ((r j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr
                    ((mul_pos hT (hρpos j)).trans_le (hlower j))) 2) (g i)) (η j) q)
                  (gradFun (scaleMetric ((r j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr
                    ((mul_pos hT (hρpos j)).trans_le (hlower j))) 2) (g i)) (η j) q)) ≤ 1 + εz) →
                scaledSplittingStratum.{u, 0} ρ hρpos β 0 ⊆ ⋃ j ∈ J₀, ball j (r j / 10) ∧
                ∃ L : ℝ, 0 ≤ L ∧
              (∀ j ∈ J₀,
                let ζi : X i → ℝ := fun x => annularCutoff cutoffProfile (η j x)
                let gr := scaleMetric ((r j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr
                  ((mul_pos hT (hρpos j)).trans_le (hlower j))) 2) (g i)
                ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ ζi ∧ (∀ x, ζi x ∈ Icc (0 : ℝ) 1) ∧
                (∀ x, η j x ∈ Icc (3 / 10 : ℝ) (4 / 5) → ζi x = 1) ∧
                tsupport ζi ⊆
                  {x | (1 / 5 - e) * r j < dist x j ∧ dist x j < (9 / 10 + e) * r j} ∧
                tsupport ζi ⊆ ball j (r j) ∧ HasCompactSupport ζi ∧
                (∀ q, Real.sqrt (gr.inner q (gradFun gr ζi q) (gradFun gr ζi q)) ≤ L * (1 + εz)) ∧
                ball j (r j / 10) ⊆ {x | η j x < 1 / 5}) ∧
            J₀.PairwiseDisjoint fun j =>
              tsupport fun x => annularCutoff cutoffProfile (η j x)) := by
  classical
  have hdim : Module.finrank ℝ E3 = 3 := finrank_euclideanSpace_fin
  obtain ⟨a₂, ha₂, h⟩ :=
    eventually_simultaneous_local_cover_with_edge_coordinates_reordered.{0, 0, u, v}
      (E := E3) (H := E3) (I := 𝓘(ℝ, E3)) hdim
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, h⟩ := h βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  have hΔ1 : 1 ≤ Δ := by
    have h100 : 100 < 100 / β₂ := (lt_div_iff₀ hβ₂).mpr (by linarith)
    linarith
  have hΔpos : 0 < Δ := by linarith
  obtain ⟨βs₀, hβs₀, hslimc⟩ :=
    exists_slimChart_at_centre.{0, 0, u, 0} (E := E3) (H := E3) (I := 𝓘(ℝ, E3)) hΔ1 hσs hσs1
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, h⟩ := h β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ s b' s' hs
    hssmall hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  have hτsmall : τ < 1 / 10000 := lt_of_sqrt_budget_LC87 hε hε1 hτ.le hθ
  obtain ⟨a₀, b₁, ha₀, hb₁, h⟩ := h σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ s b' s' hs
    hssmall hsb' hss' hb'd hs'd hb'e hs'e
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend => ?_⟩
  obtain ⟨w₀, hw₀, h⟩ := h σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend
  refine ⟨w₀, hw₀, fun w hw hww hwc b hb hbs hbc hbb₁ hsource => ?_⟩
  -- LPA01's `v_*` and `𝒜` for this `w`, fixed BEFORE `b₀`
  have hden : 1 < 2 * (1 + 2 * Λ⁻¹) ^ 3 := by
    have h := one_le_pow₀ (show 1 ≤ 1 + 2 * Λ⁻¹ by linarith [inv_pos.mpr hΛ]) (n := 3)
    linarith
  have hI : 0 < ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2 := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      ((Real.continuous_sinh.pow 2).intervalIntegrable _ _) (fun x hx => ?_) zero_lt_one
    exact pow_pos (Real.sinh_pos_iff.mpr hx.1) 2
  have hv : 0 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) :=
    div_pos (div_pos hw (by linarith)) (by positivity)
  obtain ⟨βf, hβf, hfib⟩ := exists_slimPacket_threshold.{u, 0} hΔ1 hσs hσs1 K hK one_pos hv
    (fun R => 2 ^ (K + 2) * A (2 * R + 2) (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)))
  obtain ⟨βm, hβm, hmod⟩ := slimChart_model_embedding_threshold.{u, 0} hΔ1 hσs hσs1 K hK one_pos
    hv (fun R => 2 ^ (K + 2) * A (2 * R + 2) (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)))
  obtain ⟨b₀, hb₀, h⟩ := h w hw hww hwc b hb hbs hbc hbb₁ hsource
  refine ⟨min b₀ (min βs₀ (min βf βm)), lt_min hb₀ (lt_min hβs₀ (lt_min hβf hβm)),
    fun β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone => ?_⟩
  have hβ1s : β 1 < βs₀ := hβ1b.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hβf1 : β 1 < βf :=
    hβ1b.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hβm1 : β 1 < βm :=
    hβ1b.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨εz, δ', Λ', hεz, hδ', hΛ', h⟩ :=
    h β hβ2 hβ1 (hβ1b.trans_le (min_le_left _ _)) hβone hβ3 ζ hβζ hζone
  refine ⟨εz, δ', Λ', hεz, hδ', hΛ',
    fun T V hT hTΛ hTV X mX _ _ _ g hmetric α hα hstand hder o => ?_⟩
  filter_upwards [h T V hT hTΛ hTV X g hmetric α hα hstand,
    eventually_simultaneous_analytic_data hdim g hmetric hα hstand K A hA hder hΛ hw hwc,
    hα.eventually_gt_atTop (4 * (β 1)⁻¹ + 4)] with i hi han hαβ
  obtain ⟨ρ, hρpos, hρsm, hρlip, hρb, hsecL, -, -, -, -, hcirc, J, hJfin, hJS, hJdisj, hJcov,
    hJmult, Js, Je, hJsfin, hJsS, hJsdisj, hJscov, hJsmult, hJefin, hJeE, hJedisj, hJecovE, hns,
    hJemult, hcollar, hexh, hzero⟩ := hi
  obtain ⟨-, -, -, hdata⟩ := han
  refine ⟨ρ, hρpos, hρb, ?_, hzero⟩
  have hβinv : 0 < (β 1)⁻¹ := inv_pos.mpr hβ1
  -- the circle family (as in `eventually_nonempty_circleFamily`)
  have hcdata : ∀ j ∈ J, ∃ c : (letI := (mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j));
      CircleChart 𝓘(ℝ, E3) (X i)), ∃ ζc : X i → ℝ,
      (letI := (mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j));
        c.center = j ∧ (∀ x ∈ ball j 200, ‖c.coord x‖ ≤ 8 → ζc x = 1) ∧
        (∀ x, ζc x ≠ 0 → x ∈ ball j 200 ∧ ‖c.coord x‖ < 9) ∧
        tsupport ζc ⊆ (diskPreimageOpens (ball c.center 200) isOpen_ball c.coord
          c.contMDiffOn_coord.continuousOn 100 : Set (X i))) ∧
      ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ ζc ∧ (∀ x, ζc x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ ball j (2 * ρ j), ζc x = 1) ∧ tsupport ζc ⊆ ball j (200 * ρ j) := by
    intro j hj
    obtain ⟨C, mC, c, -, -, -, -, -, Y, mY, a, F, η, hη, hrank, hp0, hlip2, -, h102, h2, -,
      hbundle, -, ζc, hζ, -, hζ01, hplat8, hne, -, hdom, hball, hphys⟩ := hcirc j (hJS hj)
    obtain ⟨-, -, hprop, hsurj, hfib', htriv⟩ := hbundle
    let _ := (mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
    exact ⟨{
      center := j
      coord := η
      contMDiffOn_coord := hη
      rank := hrank
      lipschitz := hlip2
      coord_center := hp0
      enclosure := h102
      zero_enclosure := h2
      isProperMap := hprop
      surjective := hsurj
      fibres := hfib'
      trivial := htriv }, ζc, ⟨rfl, hplat8, hne, hdom⟩, hζ, hζ01, fun x hx => (hball hx).2, hphys⟩
  choose cc ζc hcc using hcdata
  let circle : CircleFamily 𝓘(ℝ, E3) (X i) ρ hρpos β :=
    { centres := J
      finite_centres := hJfin
      centres_subset := hJS
      disjoint_centres := hJdisj
      covers := hJcov
      chart := cc
      chart_center := fun j hj => (hcc j hj).1.1
      cutoff := fun j => if hj : j ∈ J then ζc j hj else 0
      contMDiff_cutoff := fun j hj => by rw [dite_eq_left hj]; exact (hcc j hj).2.1
      cutoff_mem_Icc := fun j hj => by rw [dite_eq_left hj]; exact (hcc j hj).2.2.1
      cutoff_eq_one := fun j hj => by rw [dite_eq_left hj]; exact (hcc j hj).1.2.1
      coord_lt_of_cutoff_ne_zero := fun j hj => by rw [dite_eq_left hj]; exact (hcc j hj).1.2.2.1
      tsupport_subset_domain := fun j hj => by rw [dite_eq_left hj]; exact (hcc j hj).1.2.2.2
      plateau := fun j hj => by rw [dite_eq_left hj]; exact (hcc j hj).2.2.2.1
      tsupport_subset_ball := fun j hj => by rw [dite_eq_left hj]; exact (hcc j hj).2.2.2.2
      multiplicity := fun x => by
        refine le_trans ?_ (hJmult x)
        have hsub : J ∩ {j | x ∈ tsupport (if hj : j ∈ J then ζc j hj else 0)} ⊆
            J ∩ {j | x ∈ ball j (2000000 * ρ j)} := by
          rintro j ⟨hj, hx⟩
          rw [mem_ofPred_eq, dite_eq_left hj] at hx
          refine ⟨hj, ball_subset_ball ?_ ((hcc j hj).2.2.2.2 hx)⟩
          linarith [hρpos j]
        exact_mod_cast Set.ncard_le_ncard hsub (hJfin.subset inter_subset_left) }
  -- the slim centres (as in `eventually_simultaneous_slim_packets_with_models_reordered`)
  have hscent : ∀ j ∈ Js,
      Nonempty (SlimCentre (X i) (g i) (hmetric i) ρ hρpos (β 1) Δ σs K j) := by
    intro j hj
    obtain ⟨-, Z, mZ, z, hbdd, hdiam, ⟨αs⟩⟩ := hJsS hj
    have hD : ∀ y y' : Z, dist y y' ≤ 10 ^ 3 * Δ := fun y y' =>
      (dist_le_diam_of_mem hbdd (mem_univ y) (mem_univ y')).trans (by linarith)
    have hsecj : ∀ x ∈ ball j ((β 1)⁻¹ * ρ j),
        SectionalBoundedBelowAt (g i) x (-(β 1 / ρ j) ^ 2) := by
      intro x hx
      have hs := hsecL (β 1)⁻¹ hβinv (by linarith) j x hx
      have he : -(((β 1)⁻¹ * ρ j) ^ 2)⁻¹ = -(β 1 / ρ j) ^ 2 := by
        rw [mul_pow, mul_inv, inv_pow, inv_inv, div_pow, div_eq_mul_inv, ← inv_pow]
      rwa [he] at hs
    obtain ⟨c, -, -, -, -⟩ :=
      hslimc (β 1) hβ1 hβ1s (X i) (g i) (hmetric i) (ρ j) (hρpos j) j Z z hD αs hsecj
    obtain ⟨-, hvol0, hsec0, hder0⟩ := hdata j (ρ j) (hρpos j) (hρb j).2.le
    have hconn0 : ConnectedSpace (X i) := connectedSpace_of_aligned_metric (g i) (hmetric i) j
    let hMc : CompleteSpace (X i) := complete_of_compact
    let mR : MetricSpace (X i) := (mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
    let bR := radialScaledBundle (g i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
    let cR : IsContinuousRiemannianBundle E3 (fun x : X i => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous (g i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
    let iR : IsRiemannianManifold 𝓘(ℝ, E3) (X i) :=
      radialScaledManifold (m := mX i) (g i) (hmetric i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
    let kR : CompleteSpace (X i) :=
      ((mX i).rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρpos j))).mpr hMc
    let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) (X i) :=
      scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos j)) 2) (g i)
    have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X i) gR := isMetricNorm_of_riemannianBundle gR
    have hconn : ConnectedSpace (X i) := hconn0
    have hmeq : normalizedCenterMetric (g i) (ρ j) (hρpos j) = gR := by
      have key : ∀ (c d : ℝ) (hc : 0 < c) (hd : 0 < d), c = d →
          scaleMetric c hc (g i) = scaleMetric d hd (g i) := by
        rintro c d hc hd rfl
        rfl
      exact key _ _ _ _ (inv_pow (ρ j) 2).symm
    have hball : ∀ r, riemannianBallOf gR j r = ball j r := fun r =>
      DifferentialGeometry.Geometry.Metric.riemannianBallOf_eq_ball_of_isMetricNorm gR hnR j r
    have hvol : ENNReal.ofReal (w / (2 * (1 + 2 * Λ⁻¹) ^ 3) /
        (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2)) ≤
        riemannianVolumeMeasure 𝓘(ℝ, E3) (X i) gR (ball j 1) := by
      rw [hmeq] at hvol0
      rw [← hball 1]
      exact (ENNReal.ofReal_le_ofReal hvol0).trans ENNReal.ofReal_toReal_le
    have hsec : ∀ y ∈ ball j (β 1)⁻¹, SectionalBoundedBelowAt gR y (-β 1 ^ 2) := by
      intro y hy
      have hq : (β 1)⁻¹ ≤ α i / 4 := by linarith
      have hy' : y ∈ riemannianBallOf (normalizedCenterMetric (g i) (ρ j) (hρpos j)) j
          (α i / 4) := by
        rw [hmeq, hball]
        exact ball_subset_ball hq hy
      have hs := hsec0 y hy'
      rw [hmeq] at hs
      refine hs.mono ?_
      rw [neg_le_neg_iff, ← inv_pow]
      have hα4 : 0 < α i / 4 := hβinv.trans_le hq
      have hinv : (α i / 4)⁻¹ ≤ β 1 := by
        rw [inv_le_comm₀ hα4 hβ1]
        exact hq
      exact pow_le_pow_left₀ (inv_pos.mpr hα4).le hinv 2
    have hcurv : ∀ R, 0 < R → R < (β 1)⁻¹ → ∀ k ≤ K, ∀ y ∈ ball j R,
        curvDerivNorm k gR y ≤ 2 ^ (K + 2) * A (2 * R + 2) (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)) := by
      intro R hR hRβ k hk y hy
      have hy' : y ∈ riemannianBallOf (normalizedCenterMetric (g i) (ρ j) (hρpos j)) j R := by
        rw [hmeq, hball]
        exact hy
      have hd := hder0 R hR (by linarith) k hk y hy'
      rw [hmeq, curvatureDerivativeNorm_eq_curvDerivNorm] at hd
      exact hd
    obtain ⟨-, hP⟩ := hfib (β 1) hβ1 hβf1 (X i) gR hnR (o i) j hvol hcurv hsec Z z αs hD
    have hM := hmod (β 1) hβ1 hβm1 (X i) gR hnR (o i) j hvol hcurv hsec Z z αs hD c
    obtain ⟨P, rfl⟩ := hP c
    obtain ⟨Mod⟩ := hM
    exact ⟨@SlimCentre.mk (X i) (mX i) _ _ _ (g i) (hmetric i) ρ hρpos (β 1) Δ σs K j Z mZ z hD αs
      P Mod⟩
  -- the edge charts (as in `exists_edgeCharts_of_strong_edge_family`)
  obtain ⟨F, hF0, hFL, hF⟩ := hcollar
  have hecent : ∀ j ∈ Je,
      let A : Set (X i) := closure
        {y | @isEdgePoint.{u, 0} (X i) ((mX i).rescale (ρ y)⁻¹ (inv_pos.mpr (hρpos y))) y Δ b' s'}
      let hMc : CompleteSpace (X i) := complete_of_compact
      letI := (mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
      letI := radialScaledBundle (g i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
      letI : IsContinuousRiemannianBundle E3 (fun x : X i => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous (g i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
      letI : IsRiemannianManifold 𝓘(ℝ, E3) (X i) :=
        radialScaledManifold (m := mX i) (g i) (hmetric i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
      letI : CompleteSpace (X i) :=
        ((mX i).rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρpos j))).mpr hMc
      let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) (X i) :=
        scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos j)) 2) (g i)
      have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X i) gR := isMetricNorm_of_riemannianBundle gR
      ∃ c : EdgeChart gR hnR Δ σc μ b γc βc A (fun x => ρ x / ρ j) (fun x => F x / ρ j),
        c.center = j := by
    intro j hj
    have hpA : j ∈ closure
        {y | @isEdgePoint.{u, 0} (X i) ((mX i).rescale (ρ y)⁻¹ (inv_pos.mpr (hρpos y))) y Δ b' s'} :=
      by
      obtain ⟨-, -, -, -, -, hmem, -⟩ := exists_physical_coarse_border_chart (X := X i)
        (Λ := Real.toNNReal Λ) hρlip hρpos hΔ1 hτ hτsmall
        (by rw [Real.coe_toNNReal _ hΛ.le]; exact hΛ44)
        (by rw [Real.coe_toNNReal _ hΛ.le]; exact hend) hb'd hs'd hb'e hs'e hsb' hss' hbs j
        (hJeE j hj)
      exact hmem
    obtain ⟨-, Y, mY, q, Fp, Qn, hQn, hall⟩ := hF j hj
    let hMc : CompleteSpace (X i) := complete_of_compact
    let mR : MetricSpace (X i) := (mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
    let bR := radialScaledBundle (g i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
    let cR : IsContinuousRiemannianBundle E3 (fun x : X i => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous (g i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
    let iR : IsRiemannianManifold 𝓘(ℝ, E3) (X i) :=
      radialScaledManifold (m := mX i) (g i) (hmetric i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
    let kR : CompleteSpace (X i) :=
      ((mX i).rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρpos j))).mpr hMc
    obtain ⟨⟨f, O, hO, hCO, hfs, hfp, hfL, hfv, hft⟩, hallf⟩ := hall
    have hcl := hallf f (hfs.mono (ball_subset_closedBall.trans hCO)) hfL
      (fun x hx => (hfv x hx).le) hft
    exact ⟨{ center := j
             rho_center := div_self (hρpos j).ne'
             center_mem := hpA
             Y := Y
             instY := mY
             q := q
             split := Fp
             Qn := Qn
             Qn_fst := hQn
             coord := f
             domain := O
             isOpen_domain := hO
             closedBall_subset_domain := hCO
             contMDiffOn_coord := hfs
             coord_center := hfp
             lipschitz := hfL
             value := hfv
             test := hft
             disk_subset := hcl.1.1
             cutoff_eq_one := hcl.1.2
             collar := hcl.2 }, rfl⟩
  choose ec hec using hecent
  exact ⟨{ contMDiff_scale := hρsm
           lipschitz_scale := hρlip
           circle := circle
           slim :=
             { centres := Js
               finite_centres := hJsfin
               centres_subset := hJsS
               disjoint_centres := hJsdisj
               covers := hJscov
               centre := fun j hj => (hscent j hj).some
               multiplicity := hJsmult }
           edge :=
             { centres := Je
               finite_centres := hJefin
               strong := hJeE
               disjoint_centres := hJedisj
               covers_strong := hJecovE
               covers_nonslim := hns
               multiplicity := hJemult
               smoothing := F
               smoothing_nonneg := hF0
               lipschitz_smoothing := hFL
               smoothing_value := fun p hp => (hF p hp).1
               chart := ec
               chart_center := hec }
           exhaustion := hexh }⟩

end DifferentialGeometry.Geometry.Collapse
