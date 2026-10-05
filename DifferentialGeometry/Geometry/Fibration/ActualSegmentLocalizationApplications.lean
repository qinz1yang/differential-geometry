import DifferentialGeometry.Geometry.Fibration.ActualSegmentLocalization
import DifferentialGeometry.Geometry.Fibration.ActualZeroDomainEstimates
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14

/-!
# Consumers on the final family `LocalChartPacketsC14`: GAF06 cutoffs and ZSP02's localization

* `gaf06_circle_cutoff_one_C14`, `gaf06_slim_cutoff_one_C14`: GAF06's "for circles and slim charts
  its original cutoff is consequently one" (blueprint B:6021–6022), with the chart scales
  `ℓ = 1` (circle plateau `|η| ≤ 8`) and `ℓ = 10⁵Δ` (slim plateau `|η| ≤ 8·10⁵Δ`).
* `zsp02_zero_domain_localization_C14`: ZSP02's localization of the second set of (ZD)
  `{v ≥ .9R, u ≤ .4v}` and of the boundary set (ZF) `{v ≥ .9R, u = .4v}` in the original radial
  coordinate, for every map with (ZE), on the final family.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_GAF2
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_GAF2
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_GAF2
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **GAF06, circle charts** on the final family: (RP) on the segment with `ℓ = 1` forces the
original circle cutoff to be exactly one. -/
theorem gaf06_circle_cutoff_one_C14
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (hΔ : 1 ≤ Δ) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4)
    (E : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) {c₃ : ℝ}
    (hc₃ : c₃ < 1 / 1000) (j : P.circle.finite_centres.toFinset)
    (hAM0 : ∀ p, ∀ t ∈ Icc (0 : ℝ) 1, P.circle.cutoff j.1 p = 0 →
      |gafCircleMarker P.toLocalChartPackets j
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • E p)| ≤ ρ j.1 / 32)
    (hAE : ∀ p, ‖E p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ < c₃ * ρ p) :
    ∀ p, ∀ t ∈ Icc (0 : ℝ) 1,
      9 / 10 * ρ j.1 < gafCircleMarker P.toLocalChartPackets j
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • E p) →
      ‖gafCircleVector P.toLocalChartPackets j
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • E p)‖ ≤
        4 * gafCircleMarker P.toLocalChartPackets j
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • E p) →
      P.circle.cutoff j.1 p = 1 := by
  intro p t ht hmark hratio
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨hpos, hη⟩ := gaf06_segment_localization P.toLocalChartFamilyQ P.zero hΔ hσs hσs1 hΛ
    hsmall E hc₃ le_rfl (.inl j) hAM0 hAE p t ht hmark (by rw [mul_one]; exact hratio)
  have hp : p ∈ ball j.1 (200 * ρ j.1) :=
    cgpMarkerCutoff_ne_zero P.toLocalChartFamily hΔ0 (.inl j) p hpos.ne'
  have hη' : ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 401 / 100 * 1 := hη
  exact circle_cutoff_eq_one_of_coord_le_GAF P.toLocalChartFamilyQ P.zero j hp (by linarith)

/-- **GAF06, slim charts** on the final family: (RP) on the segment with `ℓ = 10⁵Δ` forces the
original slim cutoff to be exactly one. -/
theorem gaf06_slim_cutoff_one_C14
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (hΔ : 1 ≤ Δ) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4)
    (E : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) {c₃ : ℝ}
    (hc₃ : c₃ < 1 / 1000) (j : P.slim.finite_centres.toFinset)
    (hAM0 : ∀ p, ∀ t ∈ Icc (0 : ℝ) 1, P.slim.cutoff j.1 p = 0 →
      |blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl j))
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • E p)| ≤ ρ j.1 / 32)
    (hAE : ∀ p, ‖E p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ < c₃ * ρ p) :
    ∀ p, ∀ t ∈ Icc (0 : ℝ) 1,
      9 / 10 * ρ j.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inl j)) ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • E p) →
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl j))
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • E p)‖ ≤
        4 * (10 ^ 5 * Δ) * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inl j)) ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • E p) →
      P.slim.cutoff j.1 p = 1 := by
  intro p t ht hmark hratio
  have hΔ0 : 0 < Δ := by linarith
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hℓ : (1 : ℝ) ≤ 10 ^ 5 * Δ := by nlinarith
  obtain ⟨hpos, hη⟩ := gaf06_segment_localization P.toLocalChartFamilyQ P.zero hΔ hσs hσs1 hΛ
    hsmall E hc₃ hℓ (.inr (.inl j)) hAM0 hAE p t ht hmark hratio
  have hp : p ∈ ball j.1 (1000000 * Δ * ρ j.1) :=
    cgpMarkerCutoff_ne_zero P.toLocalChartFamily hΔ0 (.inr (.inl j)) p hpos.ne'
  change ‖planeAxis ((P.slim.centre j.1 hj).coord p)‖ < 401 / 100 * (10 ^ 5 * Δ) at hη
  rw [norm_planeAxis] at hη
  rw [slimFamily_cutoff_eq_KA2 P.toLocalChartFamily hj]
  refine (P.slim.centre j.1 hj).cutoff_eq_one_of_abs_coord_le ?_ ?_
  · convert hp using 2
    norm_num
  · nlinarith

/-- **ZSP02's localization** of the zero domain on the final family: for every map `f` with (ZE)
(`δ₀ < 1/1000`), the second set of (ZD) lies in `{ζ_k > .899, η_k < .402}`, the boundary set (ZF)
in `{.398 < η_k < .402}`, and the closed band `.3 ≤ η_k < .381` lies strictly inside the second set
(marker `> .999R_k`, ratio `< .4`). -/
theorem zsp02_zero_domain_localization_C14
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (k : P.zero.finite_centres.toFinset)
    (f : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) {δ₀ : ℝ}
    (hδ₀ : δ₀ < 1 / 1000)
    (hZE : ∀ p, ‖f p (.inr (.inr (.inr (.inl k)))) -
        cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl k))))‖ <
      δ₀ * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) :
    {p | 9 / 10 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius ≤
          (f p (.inr (.inr (.inr (.inl k))))).snd ∧
        ((f p (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 ≤
          4 / 10 * (f p (.inr (.inr (.inr (.inl k))))).snd} ⊆
      {p | 899 / 1000 < Calculus.annularCutoff Calculus.cutoffProfile
            ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p) ∧
        (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p < 402 / 1000} ∧
    {p | 9 / 10 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius ≤
          (f p (.inr (.inr (.inr (.inl k))))).snd ∧
        ((f p (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 =
          4 / 10 * (f p (.inr (.inr (.inr (.inl k))))).snd} ⊆
      {p | 398 / 1000 < (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p ∧
        (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p < 402 / 1000} ∧
    {p | 3 / 10 ≤ (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p ∧
        (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p < 381 / 1000} ⊆
      {p | 999 / 1000 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius <
          (f p (.inr (.inr (.inr (.inl k))))).snd ∧
        ((f p (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 <
          4 / 10 * (f p (.inr (.inr (.inr (.inl k))))).snd} := by
  have hR := zsp02_original_radial P.toLocalChartFamily P.zero k f hδ₀ hZE
  have hA := zsp02_original_annulus P.toLocalChartFamily P.zero k f hδ₀ hZE
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => (hA p hp.1 hp.2).2⟩
  · obtain ⟨h1, h2, -⟩ := hR p hp.1
    exact ⟨h1, h2 hp.2⟩
  · obtain ⟨-, -, h3⟩ := hR p hp.1
    have h := abs_lt.mp (h3 hp.2)
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

end DifferentialGeometry.Geometry.Collapse
