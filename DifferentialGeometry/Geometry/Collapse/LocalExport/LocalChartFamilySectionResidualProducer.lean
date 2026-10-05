import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsResidualProducer
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsDiskSectionProducer

/-!
# EADR with EGP05's edge sections (one construction for the final chapter-13 family)

Lane C14-FAM, register R9 of external review 48 (design `build-logs/resume/design-C14-FAM.md` (c)).
`eventually_nonempty_localChartFamilyEADRS_FAM`: C14-SGP2's / C14-ZERO's base family
`eventually_nonempty_localChartFamilyEADR` (circle charts with LFR07's residual enclosure, LC84 edge
disk packets) whose edge clause also carries C14-KC's EGP05 section (blueprint 207B, B:5042–5053:
"At the initial construction the common local packets may also be required to have a continuous
section `s_i : (-8.5Δ, 8.5Δ) → U_i`, `η_i s_i(a) = a`, `0 ≤ t s_i(a) < Δ/100` … The threshold for
this augmented conclusion has the same permitted dependencies as LFR28"). C14-KC's own augmented
producer `eventually_nonempty_localChartFamilyEADS` re-chains EAD (circle charts WITHOUT the
residual enclosure), so its family is not EADR's; this twin re-chains EADR with C14-KC's two edge
suppliers.
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **EADR with EGP05's sections** (C14-FAM, design (c) step 1): the statement of
`eventually_nonempty_localChartFamilyEADR` (same binders, same parameter order) whose edge clause
carries, next to the LC84 disk packet over the family's chart, C14-KC's continuous section of
the chart's coordinate over `(-8.5Δ, 8.5Δ)` (normalized at the centre). The proof is the proof of
EADR with the two edge suppliers replaced by C14-KC's
(`exists_edgeDiskPackets_sections_of_strong_edge_family`, `edgeDiskFamily_sections_on_tail_KC`): the
shared smoothing, the charts and the packets are the SAME objects as before, and the circle charts
keep LFR07's residual enclosure. -/
theorem eventually_nonempty_localChartFamilyEADRS_FAM
    {σs : ℝ} (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100) (K : ℕ) (hK : 5 ≤ K) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ σ₀ → σc < 1 → 0 < ε → ε < 1 / 100 → 0 < μ → μ ≤ 1 / 1000000 →
        0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 → ε ≤ 1 / 10 ^ 8 → μ ≤ 1 / 10 ^ 8 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{0, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) → 100 * Δ * Λ ≤ 1 / 10 ^ 8 →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 → ∃ bd₀ : ℝ, 0 < bd₀ ∧
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → b < bd₀ →
      ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
      ∀ Lmax : ℝ, 0 < Lmax →
      ∀ (X : ℕ → Type) [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
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
        ∃ L : LocalChartFamilyE (X i) (g i) (hmetric i) ρ hρpos Λ β Δ σs K
          σc μ b s b' s' ε γc βc Lmax τ,
          Nonempty (∀ j (hj : j ∈ L.circle.centres),
            CircleAdaptedCentre (X i) (g i) (hmetric i) ρ hρpos β γ L.circle j hj) ∧
          (∀ j (hj : j ∈ L.circle.centres),
            let c := L.circle.chart j hj
            letI := (mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
            ∀ x ∈ ball j 200, ‖c.coord x‖ ≤ 8 → x ∈ ball j 10) ∧
          ∀ j (hj : j ∈ L.edge.centres),
            let c := L.edge.chart j hj
            let Fs := L.edge.smoothing
            let A : Set (X i) := closure
              {y | @isEdgePoint.{0, 0} (X i) ((mX i).rescale (ρ y)⁻¹ (inv_pos.mpr (hρpos y))) y
                Δ b' s'}
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
            have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X i) gR :=
              isMetricNorm_of_riemannianBundle gR
            ∃ P : EdgeDiskPacket gR hnR Δ σc μ b γc βc A (fun x => ρ x / ρ j)
              (fun x => Fs x / ρ j), P.toEdgeChart = c ∧
              ∃ sec : Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ) → X i, Continuous sec ∧
                ∀ a : Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ), c.coord (sec a) = a ∧
                  Fs (sec a) / ρ j / (ρ (sec a) / ρ j) < Δ / 100 ∧ dist (sec a) j < 10 * Δ := by
  classical
  have hdim : Module.finrank ℝ E3 = 3 := finrank_euclideanSpace_fin
  obtain ⟨a₂, ha₂, h⟩ :=
    eventually_simultaneous_local_cover_with_edge_coordinates_reordered.{0, 0, 0, 0}
      (E := E3) (H := E3) (I := 𝓘(ℝ, E3)) hdim
  obtain ⟨a₂k, ha₂k, hK2⟩ := exists_circleChart_with_tests_residual_at_scale_LC87.{0}
  refine ⟨min a₂ a₂k, lt_min ha₂ ha₂k, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγ1
  obtain ⟨β₀k, hβ₀k, hβ₀ka, hK2⟩ := hK2 γ hγ hγ1
  refine ⟨min β₀ β₀k, lt_min hβ₀ hβ₀k, min_le_min hβ₀a hβ₀ka, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, h⟩ := h βc γc hβc hβγ hγc hγc1
  obtain ⟨σ₀e, hσ₀e, Δ₀e, hΔ₀e, hE⟩ :=
    exists_edgeDiskPackets_sections_of_strong_edge_family hβc hβγ hγc hγc1
  refine ⟨min σ₀ (min σ₀e (1 / 10 ^ 10)), lt_min hσ₀ (lt_min hσ₀e (by norm_num)), max Δ₀ Δ₀e,
    lt_max_of_lt_left hΔ₀,
    fun β₂ Δ hβ₂ hβ₂β₀' hβ₂small hΔ hΔ₀Δ' => ?_⟩
  have hβ₂β₀ : β₂ ≤ β₀ := hβ₂β₀'.trans (min_le_left _ _)
  have hβ₂k : β₂ ≤ β₀k := hβ₂β₀'.trans (min_le_right _ _)
  have hΔ₀Δ : Δ₀ ≤ Δ := (le_max_left _ _).trans hΔ₀Δ'
  have hΔ₀Δe : Δ₀e ≤ Δ := (le_max_right _ _).trans hΔ₀Δ'
  have hΔ1 : 1 ≤ Δ := by
    have h100 : 100 < 100 / β₂ := (lt_div_iff₀ hβ₂).mpr (by linarith)
    linarith
  have hΔpos : 0 < Δ := by linarith
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, h⟩ := h β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  obtain ⟨τ₀e, hτ₀e, κe, hκe, b₀e, hb₀e, hE⟩ := hE Δ hΔ₀Δe hΔ1
  refine ⟨min τ₀ (min τ₀e (1 / 10 ^ 30)), lt_min hτ₀ (lt_min hτ₀e (by norm_num)),
    min bc₀ b₀e, lt_min hbc₀ hb₀e,
    fun σc ε μ τ hσc hσcσ₀' hσc1 hε hε1 hμ hμ1 hτ hττ₀' hθ hε8 hμ8 s b' s' hs
    hssmall hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  have hσcσ₀ : σc ≤ σ₀ := hσcσ₀'.trans (min_le_left _ _)
  have hττ₀ : τ ≤ τ₀ := hττ₀'.trans (min_le_left _ _)
  obtain ⟨b₁e, hb₁e, hE⟩ := hE σc ε μ τ κe s b' s' hσc
    (hσcσ₀'.trans ((min_le_right _ _).trans (min_le_left _ _)))
    (hσcσ₀'.trans ((min_le_right _ _).trans (min_le_right _ _))) hε hε1 hε8 hμ hμ1 hμ8 hτ
    (hττ₀'.trans ((min_le_right _ _).trans (min_le_left _ _)))
    (hττ₀'.trans ((min_le_right _ _).trans (min_le_right _ _))) hθ hκe.le le_rfl hb'd hs'd hb'e
    hs'e hsb' hss'
  have hτsmall : τ < 1 / 10000 := lt_of_sqrt_budget_LC87 hε hε1 hτ.le hθ
  obtain ⟨a₀, b₁, ha₀, hb₁, h⟩ := h σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ s b' s' hs
    hssmall hsb' hss' hb'd hs'd hb'e hs'e
  refine ⟨a₀, min b₁ b₁e, ha₀, lt_min hb₁ hb₁e,
    fun σ hσ hσa' hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8 => ?_⟩
  have hσa : σ ≤ a₂ := hσa'.trans (min_le_left _ _)
  have hσk : σ ≤ a₂k := hσa'.trans (min_le_right _ _)
  have hΛc : ((Real.toNNReal Λ : NNReal) : ℝ) = Λ := Real.coe_toNNReal _ hΛ.le
  have hE := hE (Real.toNNReal Λ) (by rw [hΛc]; exact hlam) (by rw [hΛc]; exact hbudget)
    (by rw [hΛc]; exact hΛ44) (by rw [hΛc]; exact hend) (by rw [hΛc]; exact hΛ8)
  obtain ⟨w₀, hw₀, h⟩ := h σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend
  refine ⟨w₀, hw₀, fun w hw hww hwc => ?_⟩
  -- LPA01's `v_*` and `𝒜` for this `w`, fixed BEFORE `bd₀` and `b₀`
  have hden : 1 < 2 * (1 + 2 * Λ⁻¹) ^ 3 := by
    have h := one_le_pow₀ (show 1 ≤ 1 + 2 * Λ⁻¹ by linarith [inv_pos.mpr hΛ]) (n := 3)
    linarith
  have hI : 0 < ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2 := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      ((Real.continuous_sinh.pow 2).intervalIntegrable _ _) (fun x hx => ?_) zero_lt_one
    exact pow_pos (Real.sinh_pos_iff.mpr hx.1) 2
  have hv : 0 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) :=
    div_pos (div_pos hw (by linarith)) (by positivity)
  obtain ⟨bd₀, hbd₀, hE⟩ := hE K hK 1 _ one_pos hv
    (fun R => 2 ^ (K + 2) * A (2 * R + 2) (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)))
  refine ⟨bd₀, hbd₀, fun b hb hbs hbc' hbb₁' hsource hbd => ?_⟩
  have hbc : b < bc₀ := hbc'.trans_le (min_le_left _ _)
  have hbb₁ : b < b₁ := hbb₁'.trans_le (min_le_left _ _)
  have hb100 : b < 1 / 100 := by
    have h1 : 100 < b⁻¹ := lt_of_le_of_lt (by linarith) hsource
    have h2 := (lt_inv_comm₀ (by norm_num) hb).mp h1
    linarith
  have hE := hE b hb (hbc'.trans_le (min_le_right _ _)) (hbb₁'.trans_le (min_le_right _ _)) hbd
    hb100 hsource hbs
  obtain ⟨βS, hβS, hslim⟩ := exists_slimCentre_with_formula_threshold_LC87 hΔ1 hσs hσs1 K hK hv
    (fun R => 2 ^ (K + 2) * A (2 * R + 2) (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)))
  obtain ⟨b₀, hb₀, h⟩ := h w hw hww hwc b hb hbs hbc hbb₁ hsource
  refine ⟨min b₀ βS, lt_min hb₀ hβS,
    fun β hβ2 hβ1 hβ1b hβone hβ3 Lmax hLmax X mX _ _ _ g hmetric α hα hstand hder o => ?_⟩
  have hβS1 : β 1 < βS := hβ1b.trans_le (min_le_right _ _)
  obtain ⟨_εz, _δz, Λz, -, -, hΛz, h⟩ :=
    h β hβ2 hβ1 (hβ1b.trans_le (min_le_left _ _)) hβone hβ3 ((β 1 + 1) / 2) (by linarith)
      (by linarith)
  filter_upwards [h (20 * Λz) (20 * Λz) (by positivity) le_rfl le_rfl X g hmetric α hα hstand,
    eventually_simultaneous_analytic_data hdim g hmetric hα hstand K A hA hder hΛ hw hwc,
    hα.eventually_gt_atTop (4 * (β 1)⁻¹ + 4), hα.eventually_gt_atTop (2 * Lmax),
    hα.eventually_gt_atTop (2 * (10000 * Δ + κe⁻¹)), hα.eventually_gt_atTop (2 * b⁻¹),
    hα.eventually_gt_atTop (2 * (β 2)⁻¹), hα.eventually_gt_atTop (2 * b⁻¹ + 2)]
    with i hi han hαβ hαL hακ hαb hαβ2 hαbd
  obtain ⟨ρ, hρpos, hρsm, hρlip, hρb, hsecL, -, hmodt, -, -, hcirc, J, hJfin, hJS, hJdisj, hJcov,
    hJmult, Js, Je, hJsfin, hJsS, hJsdisj, hJscov, hJsmult, hJefin, hJeE, hJedisj, hJecovE, hns,
    hJemult, hcollar, hexh, -⟩ := hi
  obtain ⟨-, -, -, hdata⟩ := han
  refine ⟨ρ, hρpos, hρb, ?_⟩
  have hβinv : 0 < (β 1)⁻¹ := inv_pos.mpr hβ1
  -- the circle family: charts with their original tests, rebuilt at the tail's own centres
  have hβ2pos : 0 < β 2 := by rw [hβ2]; exact hβ₂
  have hcdata : ∀ j ∈ J, ∃ c : (letI := (mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j));
      CircleChart 𝓘(ℝ, E3) (X i)), ∃ ζc : X i → ℝ,
      (letI := (mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j));
        c.center = j ∧ (∀ x ∈ ball j 200, ‖c.coord x‖ ≤ 8 → ζc x = 1) ∧
        (∀ x, ζc x ≠ 0 → x ∈ ball j 200 ∧ ‖c.coord x‖ < 9) ∧
        tsupport ζc ⊆ (diskPreimageOpens (ball c.center 200) isOpen_ball c.coord
          c.contMDiffOn_coord.continuousOn 100 : Set (X i)) ∧ ζc = c.formulaCutoff ∧
        ∀ x ∈ ball j 200, ‖c.coord x‖ ≤ 8 → x ∈ ball j 10) ∧
      ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ ζc ∧ (∀ x, ζc x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ ball j (2 * ρ j), ζc x = 1) ∧ tsupport ζc ⊆ ball j (200 * ρ j) ∧
      ∃ (Y : Type) (mY : MetricSpace Y), letI := mY
        ∃ (a : Y) (F : @KleinerLottApprox (X i) (WithLp 2 (EuclideanSpace ℝ (Fin 2) × Y))
            ((mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))) _ j
            (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), a)) (β 2)),
        (letI := (mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          ∀ x ∈ ball j 200, ‖c.coord x - (F.toFun x).fst‖ < γ) ∧
        (letI := (mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j));
          LipschitzOnWith (Real.toNNReal (1 + γ)) c.coord (ball j 200)) ∧
        (let hMc : CompleteSpace (X i) := complete_of_compact
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
        ∀ x ∈ ball j 200, ∀ z ∈ ball j (201 * 10000), 201 < dist x z →
          ∀ w : TangentSpace 𝓘(ℝ, E3) x, gR.inner x w w = 1 →
          intrinsicGeodesic gR hnR x w (dist x z) = z →
          ‖mvfderiv (I := 𝓘(ℝ, E3)) c.coord x w -
            (dist x z)⁻¹ • ((F.toFun z).fst - (F.toFun x).fst)‖ < γ) := by
    intro j hj
    obtain ⟨-, -, -, -, -, -, -, -, Y, mY, a, F, -⟩ := hcirc j (hJS hj)
    have hsec1 : ∀ y ∈ ball j ((β 2)⁻¹ * ρ j),
        SectionalBoundedBelowAt (g i) y (-(β 2 ^ 2 * (ρ j)⁻¹ ^ 2)) := by
      intro y hy
      have h := hsecL (β 2)⁻¹ (inv_pos.mpr hβ2pos) hαβ2 j y hy
      have he : -(((β 2)⁻¹ * ρ j) ^ 2)⁻¹ = -(β 2 ^ 2 * (ρ j)⁻¹ ^ 2) := by
        rw [mul_pow, mul_inv, inv_pow, inv_inv, ← inv_pow]
      rwa [he] at h
    obtain ⟨c, ζc, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hK2 (X i) (g i) (hmetric i) j (ρ j)
      (hρpos j) hσk (show β 2 ≤ β₀k by rw [hβ2]; exact hβ₂k) (hmodt j) Y a F hsec1
    exact ⟨c, ζc, h1, h2, h3, h4, h5, Y, mY, a, F, h6, h7, h8⟩
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
      tsupport_subset_domain := fun j hj => by rw [dite_eq_left hj]; exact (hcc j hj).1.2.2.2.1
      plateau := fun j hj => by rw [dite_eq_left hj]; exact (hcc j hj).2.2.2.1
      tsupport_subset_ball := fun j hj => by rw [dite_eq_left hj]; exact (hcc j hj).2.2.2.2.1
      multiplicity := fun x => by
        refine le_trans ?_ (hJmult x)
        have hsub : J ∩ {j | x ∈ tsupport (if hj : j ∈ J then ζc j hj else 0)} ⊆
            J ∩ {j | x ∈ ball j (2000000 * ρ j)} := by
          rintro j ⟨hj, hx⟩
          rw [mem_ofPred_eq, dite_eq_left hj] at hx
          refine ⟨hj, ball_subset_ball ?_ ((hcc j hj).2.2.2.2.1 hx)⟩
          linarith [hρpos j]
        exact_mod_cast Set.ncard_le_ncard hsub (hJfin.subset inter_subset_left) }
  -- the slim centres (as in `eventually_simultaneous_slim_packets_with_models_reordered`)
  have hscent : ∀ j ∈ Js, ∃ S : SlimCentre (X i) (g i) (hmetric i) ρ hρpos (β 1) Δ σs K j,
      let P := S.packet
      letI := S.instZ
      let hMc : CompleteSpace (X i) := complete_of_compact
      letI := (mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
      letI := radialScaledBundle (g i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
      letI : IsContinuousRiemannianBundle E3 (fun x : X i => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous (g i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
      letI : IsRiemannianManifold 𝓘(ℝ, E3) (X i) :=
        radialScaledManifold (m := mX i) (g i) (hmetric i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
      letI : CompleteSpace (X i) :=
        ((mX i).rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρpos j))).mpr hMc
      P.cutoff = P.toSlimChart.formulaCutoff := by
    intro j hj
    have hsecj : ∀ x ∈ ball j ((β 1)⁻¹ * ρ j),
        SectionalBoundedBelowAt (g i) x (-(β 1 / ρ j) ^ 2) := by
      intro x hx
      have hs := hsecL (β 1)⁻¹ hβinv (by linarith) j x hx
      have he : -(((β 1)⁻¹ * ρ j) ^ 2)⁻¹ = -(β 1 / ρ j) ^ 2 := by
        rw [mul_pow, mul_inv, inv_pow, inv_inv, div_pow, div_eq_mul_inv, ← inv_pow]
      rwa [he] at hs
    exact hslim (β 1) hβ1 hβS1 (X i) (g i) (hmetric i) (o i) ρ hρpos j (α i) hαβ (hJsS hj).2 hsecj
      (hdata j (ρ j) (hρpos j) (hρb j).2.le)
  -- the edge family with the recorded coarse-border composite
  have hsecκ : ∀ p ∈ Je, ∀ z ∈ ball p (10000 * (Δ * ρ p)),
      SectionalBoundedBelowAt (g i) z (-(κe / ρ p) ^ 2) := by
    intro p _ z hz
    have hρp := hρpos p
    have hL : 0 < 10000 * Δ + κe⁻¹ := by positivity
    have hz' : z ∈ ball p ((10000 * Δ + κe⁻¹) * ρ p) := by
      refine ball_subset_ball ?_ hz
      rw [add_mul, mul_assoc]
      linarith [mul_pos (inv_pos.mpr hκe) hρp]
    refine (hsecL _ hL hακ p z hz').mono ?_
    rw [neg_le_neg_iff]
    have hκρ : (κe / ρ p) ^ 2 = ((ρ p / κe) ^ 2)⁻¹ := by rw [← inv_pow, inv_div]
    rw [hκρ]
    apply inv_anti₀ (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right (by linarith [inv_pos.mpr hκe]) hρp.le
  have hsecb : ∀ p ∈ Je, ∀ z ∈ ball p (b⁻¹ * ρ p),
      SectionalBoundedBelowAt (g i) z (-(b / ρ p) ^ 2) := by
    intro p _ z hz
    have h := hsecL b⁻¹ (inv_pos.mpr hb) hαb p z hz
    have he : -((b⁻¹ * ρ p) ^ 2)⁻¹ = -(b / ρ p) ^ 2 := by
      rw [mul_pow, mul_inv, inv_pow, inv_inv, div_pow, div_eq_mul_inv, ← inv_pow]
    rwa [he] at h
  obtain ⟨F, hF0, hFL, hF⟩ := edgeDiskFamily_sections_on_tail_KC _ hE (g i) (hmetric i) (o i) ρ
    hρpos
    hρsm hρlip hJefin hJeE hsecκ hsecb hαbd
    (fun p _ => (hdata p (ρ p) (hρpos p) (hρb p).2.le).2.1)
    (fun p _ => (hdata p (ρ p) (hρpos p) (hρb p).2.le).2.2.2)
  have hecent := fun j (hj : j ∈ Je) => (hF j hj).2
  choose ec hec using hecent
  choose sc hsc using hscent
  choose Yc mYc ac Fc hFc using fun j (hj : j ∈ J) => (hcc j hj).2.2.2.2.2
  exact ⟨{ contMDiff_scale := hρsm
           lipschitz_scale := hρlip
           circle := circle
           slim :=
             { centres := Js
               finite_centres := hJsfin
               centres_subset := hJsS
               disjoint_centres := hJsdisj
               covers := hJscov
               centre := sc
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
               chart_center := fun j hj => (hec j hj).1 }
           exhaustion := hexh
           circle_cutoff_eq := fun j hj => by
             change (if hj' : j ∈ J then ζc j hj' else 0) = _
             rw [dite_eq_left hj]
             exact (hcc j hj).1.2.2.2.2.1
           slim_cutoff_eq := hsc
           sectional_buffer := fun L hL hLL p y hy => hsecL L hL (by linarith) p y hy
           edge_coarse := fun j hj => (hec j hj).2.1 }, ⟨fun j hj =>
    { Y := Yc j hj
      instY := mYc j hj
      a := ac j hj
      split := Fc j hj
      adapted := (hFc j hj).1
      lipschitz := (hFc j hj).2.1
      test := (hFc j hj).2.2 }⟩, fun j hj => (hcc j hj).1.2.2.2.2.2, fun j hj => (hec j hj).2.2⟩

end DifferentialGeometry.Geometry.Collapse
