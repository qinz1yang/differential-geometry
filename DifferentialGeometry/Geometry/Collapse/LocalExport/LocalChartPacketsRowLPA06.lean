import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsRowLPA04
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsDiskApplications

/-!
# Row LPA06: the simultaneous finite local cover with an early multiplicity bound

Frozen blueprint master207A, LPA06 (`thm:collapse-simultaneous-finite-local-cover`, A:30586): the
SAME late manifolds and assignment of LPA04 admit finite circle, strong-edge and slim families,
together with LPA05's zero family, whose actual domains cover the manifold; the circle, edge and slim
cutoffs equal one on their covering balls; all cutoffs have closed supports strictly within their
smooth domains; the edge family uses ONE distance smoothing for disks and collars; the nonzero
support multiplicity is bounded by one numerical constant chosen before `Δ, w'`; the zero cutoffs
have disjoint supports (LC87 items (1)–(3) for the closed carrier).

`lpa06_simultaneous_finite_local_cover` (consumer of `lpa04_simultaneous_interior_choice`, same
parameter order, same tail, same `LocalChartPacketsD`):
* every point lies in a zero tenth-radius ball or in the plateau (cutoff `= 1`) of a circle, slim or
  edge cutoff (`exhaustion_four_kinds`);
* at every point the active circle + slim + edge supports number at most a NUMERICAL constant
  (`support_multiplicity`; Bishop–Gromov volume ratios with the fixed constant `2·10⁶`);
* the closed supports lie strictly inside the chart domains: circle in `B(j, 200ρ(j))` (normalized
  domain `|η| < 100` is the structure field), slim in `B̄(j, 0.91·10⁶Δρ(j)) ⊂ B(j, 10⁶Δρ(j))`, edge in
  `B(j, 13Δρ(j)) ⊂ B(j, 100Δρ(j))` (LC84's disk-packet margin);
* the zero cutoffs (LC31 on the SAME radial functions) are smooth, supported in their selected
  balls, and pairwise disjoint.
The ONE shared edge smoothing is the field `edge.smoothing`, which is the `F` of every LFR28 disk
packet `edgeDisk` (by the structure).
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
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model metrics of the zero kind, as a local instance. -/
local instance instMetricN_LPA06_LPA02b {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
    [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
    (L : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (L.N a) :=
  L.instMetricN a

/-- The model charts of the zero kind, as a local instance. -/
local instance instChartedN_LPA06_LPA02b {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
    [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
    (L : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (L.N a) :=
  L.instChartedN a

/-- The cone metrics of the zero kind, as a local instance. -/
local instance instMetricC_LPA06_LPA02b {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
    [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
    (L : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (L.C a) :=
  L.instMetricC a
/-- **Row LPA06 (simultaneous finite local cover with an early multiplicity bound).** See the
module docstring. -/
theorem lpa06_simultaneous_finite_local_cover
    {σs : ℝ} (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100) (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ → ℝ)
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
      ∀ ζ : ℝ, β 1 < ζ → ζ < 1 →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
      ∀ Lmax : ℝ, 0 < Lmax →
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
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ i in atTop,
        ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        (∀ p, firstVolumeScale (g i) p w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
        ∃ P : LocalChartPacketsD (X i) (g i) (hmetric i) ρ hρpos Λ β Δ σs K
          σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V,
          (∀ x : X i, (∃ c, ∃ hc : c ∈ P.zero.centres, x ∈ ball c ((P.zero.zero c hc).radius / 10)) ∨
            (∃ j ∈ P.circle.centres, P.circle.cutoff j x = 1) ∨
            (∃ j ∈ P.slim.centres, P.slim.cutoff j x = 1) ∨
            ∃ j ∈ P.edge.centres, P.edge.cutoff j x = 1) ∧
          (∀ x : X i, ((P.circle.centres ∩ {j | x ∈ tsupport (P.circle.cutoff j)}).ncard : ℝ) +
            ((P.slim.centres ∩ {j | x ∈ tsupport (P.slim.cutoff j)}).ncard : ℝ) +
            ((P.edge.centres ∩ {j | x ∈ tsupport (P.edge.cutoff j)}).ncard : ℝ) ≤
              2 * (modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
                modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3)) +
              modelVolume (-((1 / (4 * (1 + 2 * 2000000 + 1 / 3)) : ℝ) ^ 2)) 3
                  (4 * (1 + 2 * 2000000 + 1 / 3)) /
                modelVolume (-((1 / (4 * (1 + 2 * 2000000 + 1 / 3)) : ℝ) ^ 2)) 3 (1 / 3)) ∧
          (∀ j ∈ P.circle.centres, tsupport (P.circle.cutoff j) ⊆ ball j (200 * ρ j)) ∧
          (∀ j ∈ P.slim.centres,
            tsupport (P.slim.cutoff j) ⊆ closedBall j (91 / 100 * (10 ^ 6 * Δ) * ρ j)) ∧
          (∀ j ∈ P.edge.centres, tsupport (P.edge.cutoff j) ⊆ ball j (13 * Δ * ρ j)) ∧
          (∀ c (hc : c ∈ P.zero.centres),
            ContMDiff I3 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile ((P.zero.zero c hc).radial x)) ∧
            tsupport (fun x => annularCutoff cutoffProfile ((P.zero.zero c hc).radial x)) ⊆
              ball c (P.zero.zero c hc).radius) ∧
          ∀ c (hc : c ∈ P.zero.centres) c' (hc' : c' ∈ P.zero.centres), c ≠ c' →
            Disjoint (tsupport fun x => annularCutoff cutoffProfile ((P.zero.zero c hc).radial x))
              (tsupport fun x => annularCutoff cutoffProfile ((P.zero.zero c' hc').radial x)) := by
  obtain ⟨a₂, ha₂, h⟩ := lpa04_simultaneous_interior_choice hσs hσs1 K hK A hA
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, h⟩ := h βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  have hΔpos : 0 < Δ := lt_trans (div_pos (by norm_num) hβ₂) hΔ
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, h⟩ := h β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s b' s'
    hs hssmall hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, h⟩ := h σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s b'
    s' hs hssmall hsb' hss' hb'd hs'd hb'e hs'e
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8 => ?_⟩
  obtain ⟨w₀, hw₀, h⟩ := h σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8
  refine ⟨w₀, hw₀, fun w hw hww hwc => ?_⟩
  obtain ⟨bd₀, hbd₀, h⟩ := h w hw hww hwc
  refine ⟨bd₀, hbd₀, fun b hb hbs hbc hbb₁ hsource hbd => ?_⟩
  obtain ⟨b₀, hb₀, h⟩ := h b hb hbs hbc hbb₁ hsource hbd
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone => ?_⟩
  obtain ⟨εr, δ', Λ5, hεr, hεr4, hδ', hΛ5, h⟩ := h β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone
  refine ⟨εr, δ', Λ5, hεr, hεr4, hδ', hΛ5,
    fun T hT hTΛ e he he1 Lmax hLmax X _ _ _ _ g hmetric α hα hstand hder hor => ?_⟩
  obtain ⟨V₀, hTV, δ₀, hδ0, hδδ', h⟩ := h T hT hTΛ e he he1 Lmax hLmax X g hmetric α hα hstand hder hor
  refine ⟨V₀, hTV, δ₀, hδ0, hδδ', h.mono fun i hi => ?_⟩
  obtain ⟨ρ, hρpos, hρb, P, -, -, -, -, L, -, hcut, hdisj⟩ := hi
  refine ⟨ρ, hρpos, hρb, P, fun x => ?_, fun x => ?_, fun j hj => P.circle.tsupport_subset_ball j hj,
    fun j hj => ?_, fun j hj => P.edge_tsupport_cutoff_subset_ball hΔpos hj,
    fun c hc => ⟨(hcut c hc).1, (hcut c hc).2.2.2.2.1⟩, hdisj⟩
  · exact P.toLocalChartPackets.exhaustion_four_kinds hΔpos hσs.le hσs1 x
  · exact P.toLocalChartFamily.support_multiplicity hΔpos x
  · unfold SlimFamily.cutoff
    rw [dite_eq_left hj]
    exact (P.slim.centre j hj).tsupport_cutoff_subset

end DifferentialGeometry.Geometry.Collapse
