import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsValueProducer
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilySectionResidualProducer
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05LocalComparisonCapped

/-!
# Producer of the final chapter-13 family for chapter 14 (`LocalChartPacketsC14`)

Lane C14-FAM (design `build-logs/resume/design-C14-FAM.md` (c), (h); external review 48, register
R4, R6, R9; lead decisions T48-1, T48-2). ONE producer yields, on ONE tail, ONE family carrying
LFR19's slim value tolerance, LC73's zero shell clauses, LPA05's enlarged zero-ball curvature and
EGP05's edge sections, with the zero radial difference-Lipschitz constant below a REQUESTED cap.

* `eventually_nonempty_localChartFamilyEADRSV_FAM`: C14-SGP2's EADRV on the EADR-with-sections
  family `eventually_nonempty_localChartFamilyEADRS_FAM` (slim family rebuilt at the SAME centres,
  `σs, vs` after `Δ` and `b`).
* `eventually_nonempty_localChartPacketsC14`: the statement of
  `eventually_nonempty_localChartPacketsRVZ` with (1) a requested cap: `∀ ζ cap, β₁ < ζ < 1 →
  0 < cap → ∃ εr δ' Λ', … ∧ εr < cap ∧ …` (the cap enters LPA05 before the joint zero
  witness, `lpa05_selected_zero_packets_capped_FAM`); (2) `∀ Lmax` bound AFTER `∃ V, ∃ δ` (so
  that `Lmax ≥ 400V`, blueprint PBR01 PR24 "Include H_α > 400V", can be requested); (3)
  `LocalChartPacketsC14 … vs ζ Λ'`. Blueprint order kept: `β₂ → Δ`, `w → b → β₁`, joint zero
  output last.
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

/-- **EADRV with EGP05's sections** (C14-FAM, design (c) step 2): the statement of C14-SGP2's
`eventually_nonempty_localChartFamilyEADRV` (`σs, vs` chosen after `Δ` and `b`) whose edge clause
carries C14-KC's section next to the LC84 packet. Proof: C14-SGP2's proof on
`eventually_nonempty_localChartFamilyEADRS_FAM` (the slim family rebuilt at the SAME centres by
`exists_slimCentre_with_formula_threshold_vs`; the edge clause, which mentions no slim datum, is
passed through unchanged). -/
theorem eventually_nonempty_localChartFamilyEADRSV_FAM (K : ℕ) (hK : 5 ≤ K) (A : ℝ → ℝ → ℝ)
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
      ∀ σs vs : ℝ, 0 < σs → σs ≤ 1 / 100 → 0 < vs →
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
          (∀ j (hj : j ∈ L.edge.centres),
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
                  Fs (sec a) / ρ j / (ρ (sec a) / ρ j) < Δ / 100 ∧ dist (sec a) j < 10 * Δ) ∧
          ∀ j (hj : j ∈ L.slim.centres), ∀ x ∈ ball j (10 ^ 6 * Δ * ρ j),
            |(L.slim.centre j hj).coord x -
              (letI := (L.slim.centre j hj).instZ
               @KleinerLottApprox.toFun (X i) (WithLp 2 (ℝ × (L.slim.centre j hj).Z))
                ((mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))) _ j _ (β 1)
                (L.slim.centre j hj).split x).fst| < vs := by
  have hdim : Module.finrank ℝ E3 = 3 := finrank_euclideanSpace_fin
  obtain ⟨a₂, ha₂, h⟩ := eventually_nonempty_localChartFamilyEADRS_FAM (σs := 1 / 100)
    (by norm_num) le_rfl K hK A hA
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, h⟩ := h βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  have hΔ1 : 1 ≤ Δ := by
    have h100 : 100 < 100 / β₂ := (lt_div_iff₀ hβ₂).mpr (by linarith)
    linarith
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, h⟩ := h β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s b' s'
    hs hssmall hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, h⟩ := h σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s b'
    s' hs hssmall hsb' hss' hb'd hs'd hb'e hs'e
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8 => ?_⟩
  obtain ⟨w₀, hw₀, h⟩ := h σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8
  refine ⟨w₀, hw₀, fun w hw hww hwc => ?_⟩
  obtain ⟨bd₀, hbd₀, h⟩ := h w hw hww hwc
  refine ⟨bd₀, hbd₀, fun b hb hbs hbc hbb₁ hsource hbd σs vs hσs hσs1 hvs => ?_⟩
  obtain ⟨b₀, hb₀, h⟩ := h b hb hbs hbc hbb₁ hsource hbd
  -- LPA01's `v_*` and `𝒜` for this `w` (as in `eventually_nonempty_localChartFamilyEADR`)
  have hv := lpa01_volume_constant_pos_SGP2 hΛ hw
  obtain ⟨βS, hβS, hslim⟩ := exists_slimCentre_with_formula_threshold_vs hΔ1 hσs hσs1 hvs K hK hv
    (fun R => 2 ^ (K + 2) * A (2 * R + 2) (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)))
  refine ⟨min b₀ βS, lt_min hb₀ hβS,
    fun β hβ2 hβ1 hβ1b hβone hβ3 Lmax hLmax X mX _ _ _ g hmetric α hα hstand hder o => ?_⟩
  have hβS1 : β 1 < βS := hβ1b.trans_le (min_le_right _ _)
  have hβinv : 0 < (β 1)⁻¹ := inv_pos.mpr hβ1
  filter_upwards [h β hβ2 hβ1 (hβ1b.trans_le (min_le_left _ _)) hβone hβ3 (max Lmax (β 1)⁻¹)
      (lt_max_of_lt_left hLmax) X g hmetric α hα hstand hder o,
    eventually_simultaneous_analytic_data hdim g hmetric hα hstand K A hA hder hΛ hw hwc,
    hα.eventually_gt_atTop (4 * (β 1)⁻¹ + 4)] with i hi han hαβ
  obtain ⟨ρ, hρpos, hρb, L, hAd, hRes, hDisk⟩ := hi
  obtain ⟨-, -, -, hdata⟩ := han
  have hbuf := L.sectional_buffer
  have hsub := L.slim.centres_subset
  -- the slim centres again, now with LFR19's tolerance `vs` and the late quality `σs`
  have hscent : ∀ j ∈ L.slim.centres,
      ∃ S : SlimCentre (X i) (g i) (hmetric i) ρ hρpos (β 1) Δ σs K j,
        (let P := S.packet
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
        P.cutoff = P.toSlimChart.formulaCutoff) ∧
        ∀ x ∈ ball j (10 ^ 6 * Δ * ρ j), |S.coord x -
          (letI := S.instZ
           @KleinerLottApprox.toFun (X i) (WithLp 2 (ℝ × S.Z))
            ((mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))) _ j _ (β 1) S.split x).fst| < vs := by
    intro j hj
    have hsecj : ∀ x ∈ ball j ((β 1)⁻¹ * ρ j),
        SectionalBoundedBelowAt (g i) x (-(β 1 / ρ j) ^ 2) := by
      intro x hx
      have hs := hbuf (β 1)⁻¹ hβinv (le_max_right _ _) j x hx
      rwa [sectional_radius_eq_SGP2, inv_inv] at hs
    exact hslim (β 1) hβ1 hβS1 (X i) (g i) (hmetric i) (o i) ρ hρpos j (α i) hαβ (hsub hj).2 hsecj
      (hdata j (ρ j) (hρpos j) (hρb j).2.le)
  choose sc hsc hscv using hscent
  let L' : LocalChartFamilyE (X i) (g i) (hmetric i) ρ hρpos Λ β Δ σs K
      σc μ b s b' s' ε γc βc Lmax τ :=
    { L with
      slim := { L.slim with centre := sc }
      slim_cutoff_eq := hsc
      sectional_buffer := fun r hr hrL p y hy => hbuf r hr (hrL.trans (le_max_left _ _)) p y hy }
  exact ⟨ρ, hρpos, hρb, L', hAd, hRes, hDisk, hscv⟩

/-- **Producer of the final chapter-13 family for chapter 14.** On ONE tail, ONE family
`LocalChartPacketsC14 … vs ζ Λ'`: LFR19's separate slim value tolerance `vs`, LC73's zero shell
clauses of quality `ζ` (ratios `λ ≥ Λ'`), LPA05's enlarged zero-ball curvature and EGP05's edge
sections, with the zero radial difference-Lipschitz constant `εr` below the requested `cap`; `Lmax`
is chosen after `V`. See the module docstring. -/
theorem eventually_nonempty_localChartPacketsC14 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ → ℝ)
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
      ∀ σs vs : ℝ, 0 < σs → σs ≤ 1 / 100 → 0 < vs →
      ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
      ∀ ζ cap : ℝ, β 1 < ζ → ζ < 1 → 0 < cap →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ εr < cap ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
      ∀ (X : ℕ → Type) [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
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
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ Lmax : ℝ, 0 < Lmax → ∀ᶠ i in atTop,
        ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        (∀ p, firstVolumeScale (g i) p w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
        Nonempty (LocalChartPacketsC14 (X i) (g i) (hmetric i) ρ hρpos Λ β Δ σs K
          σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λ') := by
  obtain ⟨a₂, ha₂, h⟩ := eventually_nonempty_localChartFamilyEADRSV_FAM K (by omega) A hA
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, h⟩ := h βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, h⟩ := h β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s b' s'
    hs hssmall hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, h⟩ := h σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s b'
    s' hs hssmall hsb' hss' hb'd hs'd hb'e hs'e
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8 => ?_⟩
  obtain ⟨w₀, hw₀, h⟩ := h σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8
  refine ⟨w₀, hw₀, fun w hw hww hwc => ?_⟩
  obtain ⟨bd₀, hbd₀, h⟩ := h w hw hww hwc
  refine ⟨bd₀, hbd₀, fun b hb hbs hbc hbb₁ hsource hbd σs vs hσs hσs1 hvs => ?_⟩
  obtain ⟨b₀, hb₀, h⟩ := h b hb hbs hbc hbb₁ hsource hbd σs vs hσs hσs1 hvs
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβone hβ3 ζ cap hβζ hζone hcap => ?_⟩
  have hEA := h β hβ2 hβ1 hβ1b hβone hβ3
  obtain ⟨εr, δ', Λ5, hεr, hεr4, hεrcap, hδ', hΛ5, h5⟩ :=
    lpa05_selected_zero_packets_capped_FAM hβ1 hβone hβζ hζone hcap
  refine ⟨εr, δ', Λ5, hεr, hεr4, hεrcap, hδ', hΛ5,
    fun T hT hTΛ e he he1 X _ _ _ _ g hmetric α hα hstand hder hor => ?_⟩
  obtain ⟨V, hTV, δ, hδ0, hδδ', h5⟩ := h5 T hT hTΛ e he he1 X g hmetric
    α hα hstand K hK A hA hder Λ w hΛ hw hwc
  refine ⟨V, hTV, δ, hδ0, hδδ', fun Lmax hLmax => ?_⟩
  filter_upwards [hEA Lmax hLmax X g hmetric α hα hstand hder hor, h5] with i hi h5i
  obtain ⟨ρ, hρpos, hρb, L, ⟨hAd⟩, hRes, hDS, hVal⟩ := hi
  obtain ⟨N, C, mN, cN, -, mC, o, -, Z, hZloc, hZcurv, -, hsplit, hadapt, -⟩ :=
    h5i ρ hρpos L.contMDiff_scale.continuous (fun p => (hρb p).2.le)
  exact ⟨ρ, hρpos, hρb, ⟨{ L with
    circleAdapted := hAd
    N := N
    C := C
    instMetricN := mN
    instChartedN := cN
    instMetricC := mC
    o := o
    zero := Z
    edgeDisk := fun j hj => ⟨(hDS j hj).choose, (hDS j hj).choose_spec.1⟩
    circle_residual := hRes
    zero_local_comparison := hZloc
    slim_value := hVal
    zero_shell_split := hsplit
    zero_adapted := hadapt
    zero_curvature := hZcurv
    edge_section := fun j hj => (hDS j hj).choose_spec.2 }⟩⟩

end DifferentialGeometry.Geometry.Collapse
