import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ProducerWitness
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05LocalComparisonCappedTypes

/-!
# The C14 producer KEEPING the sublevel types of its zero family (lane C14-FAM-Z, layer 2)

External review 53, §4.1 (A-Z): the types of the actual radial sublevels of the SAME zero family,
kept at the joint zero selection and carried through the three layers that carry the zero family
(lane FC39-WIT): capped LPA05 → C14 producer → C14D producer.

`eventually_nonempty_localChartPacketsC14_FAMZ`: the statement of
`eventually_nonempty_localChartPacketsC14_WIT` (every clause verbatim, the same tail) with one more
clause on the returned family `P`: for every orientation `oX` of the member, every zero centre `c`
of `P` and every `a ∈ [1/5, 2]`, `{η_c ≤ a}` is `CompactModelSublevel oX ∨ PointSoulCoreSublevel ∨
CircleSoulCoreSublevel ∨ ProjectiveSoulCoreSublevel ∨ KleinSoulCoreSublevel` of its model. The proof
is the accepted one (generated from `LocalChartPacketsC14ProducerWitness.lean` by
`build-logs/scratch/C14-FAM-Z/gen_l23.py`) with `lpa05_selected_zero_packets_capped_FAMZ` in place
of `lpa05_selected_zero_packets_capped_WIT` and its type clause passed on (`P.zero := Z`).

Consumer: `eventually_nonempty_localChartPacketsC14_WIT_of_FAMZ` (the `_WIT` statement follows).
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

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

/-- **The C14 producer keeping the sublevel types of its zero family.** The statement of
`eventually_nonempty_localChartPacketsC14_WIT` (every clause verbatim, the same tail) with one more
clause on the returned family `P`: for every orientation `oX` of the member, every zero centre `c`
of `P` and every `a ∈ [1/5, 2]`, the actual sublevel `{η_c ≤ a}` is
`CompactModelSublevel oX ∨ PointSoulCoreSublevel ∨ CircleSoulCoreSublevel ∨
ProjectiveSoulCoreSublevel ∨ KleinSoulCoreSublevel` of its model (`P.zero` is LPA05's selected
family; the clause is kept from `lpa05_selected_zero_packets_capped_FAMZ`). -/
theorem eventually_nonempty_localChartPacketsC14_FAMZ (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ → ℝ)
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
        Lpa02WitnessV2 (g i) K Λ w εr e T V δ ∧
        ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        (∀ p, firstVolumeScale (g i) p w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
        ∃ P : LocalChartPacketsC14 (X i) (g i) (hmetric i) ρ hρpos Λ β Δ σs K
          σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λ',
          (∀ c (hc : c ∈ P.zero.centres), ∃ t ∈ Icc T V, ∃ ht : 0 < t,
            (P.zero.zero c hc).radius = t * ρ c ∧
              Lpa02WitnessAtV2 (g i) K εr e δ c (ρ c) t (hρpos c) ht) ∧
          ∀ oX : ManifoldOrientation (𝓡 3) (X i) 3, ∀ c (hc : c ∈ P.zero.centres),
            ∀ a ∈ Icc (1 / 5 : ℝ) 2,
            CompactModelSublevel oX (P.N (P.zero.zero c hc).model)
                {x | (P.zero.zero c hc).radial x ≤ a} ∨
              PointSoulCoreSublevel (P.N (P.zero.zero c hc).model)
                {x | (P.zero.zero c hc).radial x ≤ a} ∨
              CircleSoulCoreSublevel (P.N (P.zero.zero c hc).model)
                {x | (P.zero.zero c hc).radial x ≤ a} ∨
              ProjectiveSoulCoreSublevel (P.N (P.zero.zero c hc).model)
                {x | (P.zero.zero c hc).radial x ≤ a} ∨
              KleinSoulCoreSublevel (P.N (P.zero.zero c hc).model)
                {x | (P.zero.zero c hc).radial x ≤ a} := by
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
    lpa05_selected_zero_packets_capped_FAMZ hβ1 hβone hβζ hζone hcap
  refine ⟨εr, δ', Λ5, hεr, hεr4, hεrcap, hδ', hΛ5,
    fun T hT hTΛ e he he1 X _ _ _ _ g hmetric α hα hstand hder hor => ?_⟩
  obtain ⟨V, hTV, δ, hδ0, hδδ', h5⟩ := h5 T hT hTΛ e he he1 X g hmetric
    α hα hstand K hK A hA hder Λ w hΛ hw hwc
  refine ⟨V, hTV, δ, hδ0, hδδ', fun Lmax hLmax => ?_⟩
  filter_upwards [hEA Lmax hLmax X g hmetric α hα hstand hder hor, h5] with i hi h5i
  obtain ⟨hwit, h5i⟩ := h5i
  obtain ⟨ρ, hρpos, hρb, L, ⟨hAd⟩, hRes, hDS, hVal⟩ := hi
  obtain ⟨N, C, mN, cN, -, mC, o, -, Z, hsel, htyp, hZloc, hZcurv, -, hsplit, hadapt, -⟩ :=
    h5i ρ hρpos L.contMDiff_scale.continuous (fun p => (hρb p).2.le)
  exact ⟨hwit, ρ, hρpos, hρb, { L with
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
    edge_section := fun j hj => (hDS j hj).choose_spec.2 }, hsel, htyp⟩

/-- **Consumer: the `_WIT` statement follows.** `eventually_nonempty_localChartPacketsC14_FAMZ`
implies the statement of `eventually_nonempty_localChartPacketsC14_WIT` (drop the type clause). -/
theorem eventually_nonempty_localChartPacketsC14_WIT_of_FAMZ (K : ℕ) (hK : 10 ≤ K)
    (A : ℝ → ℝ → ℝ) (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) :
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
        Lpa02WitnessV2 (g i) K Λ w εr e T V δ ∧
        ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        (∀ p, firstVolumeScale (g i) p w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
        ∃ P : LocalChartPacketsC14 (X i) (g i) (hmetric i) ρ hρpos Λ β Δ σs K
          σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λ',
          ∀ c (hc : c ∈ P.zero.centres), ∃ t ∈ Icc T V, ∃ ht : 0 < t,
            (P.zero.zero c hc).radius = t * ρ c ∧
              Lpa02WitnessAtV2 (g i) K εr e δ c (ρ c) t (hρpos c) ht := by
  obtain ⟨a₂, ha₂, h⟩ := eventually_nonempty_localChartPacketsC14_FAMZ K hK A hA
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
  obtain ⟨εr, δ', Λ', hεr, hεr4, hεrcap, hδ', hΛ', h⟩ :=
    h β hβ2 hβ1 hβ1b hβone hβ3 ζ cap hβζ hζone hcap
  refine ⟨εr, δ', Λ', hεr, hεr4, hεrcap, hδ', hΛ',
    fun T hT hTΛ e he he1 X _ _ _ _ g hmetric α hα hstand hder hor => ?_⟩
  obtain ⟨V, hTV, δ, hδ0, hδδ', h⟩ := h T hT hTΛ e he he1 X g hmetric α hα hstand hder hor
  refine ⟨V, hTV, δ, hδ0, hδδ', fun Lmax hLmax => ?_⟩
  filter_upwards [h Lmax hLmax] with i hi
  obtain ⟨hwit, ρ, hρpos, hρb, P, hsel, -⟩ := hi
  exact ⟨hwit, ρ, hρpos, hρb, P, hsel⟩

end DifferentialGeometry.Geometry.Collapse
