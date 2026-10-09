import DifferentialGeometry.Geometry.Fibration.ActualStageClouds
import DifferentialGeometry.Geometry.Metric.LargeCloudSmoothingRows
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14

/-!
# CFS12 and CFS13 on the three actual stage clouds

Blueprint `master207B.tex`, CFS12 (B:2513) and CFS13 (B:2571) under the standing hypotheses of
B:2425–2449 on the actual data: the stage clouds `S_st = π_st𝓔⁰(A_st) ⊆ S̃_st` of
`𝓔⁰ = cgpGlobalMap` on the final family `LocalChartPacketsC14` (FC07's parameter range), radius
`Σρ(sel x)` for ANY selection of preimages over `S̃_st`, at ANY buffer `b ≥ 1` with
`128bΣ ≤ 1/5`.

* `cfs1213_actual_inputs_CFSA`: every standing hypothesis but the (CS) tests on the actual stage
  clouds: `S ⊆ S̃`, `S` totally bounded, radius bounds, (MCb) on `S̃` at `128b` with `B = 5/3`
  (from `cfs14_stage_inputs_GAF2` at accuracy `b⁻¹`).
* Consumers (the rows applied to the actual stage clouds, (CS) at quality `δ ≤ δ₀` the rows' own
  hypothesis): `cfs12_actual_cover_CFSA` (`cfs12_row_CFSA`: the selection and the `8b`/`20b` tubes
  of CFS12's domain), `cfs13_actual_zero_set_CFSA` (`cfs13_row_CFSA`: the selection and its tube).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14L_CFSA {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14L_CFSA {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14L_CFSA {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **The standing hypotheses of CFS11–CFS14 on the actual stage clouds** (all but (CS)), at any
buffer `bb ≥ 1` and radius factor `0 < Σ` with `128 bb Σ ≤ 1/5`: `S_st ⊆ S̃_st`, `S_st` totally
bounded, `Σρ ∘ sel` bounded above and away from zero on `S_st`, and (MCb) on `S̃_st` at `128 bb`
with `B = 5/3`. -/
theorem cfs1213_actual_inputs_CFSA {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (he : e ≤ 1 / 8)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (st : Fin 3)
    (sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st)
        (sel x) = x)
    {bb sg : ℝ} (hbb : 1 ≤ bb) (hsg : 0 < sg) (hbsg : 128 * bb * sg ≤ 1 / 5) :
    gafCloud P.toLocalChartFamily P.zero st ⊆ gafCloudEnlarged P.toLocalChartFamily P.zero st ∧
      TotallyBounded (gafCloud P.toLocalChartFamily P.zero st) ∧
      (∃ rmin R : ℝ, 0 < rmin ∧ (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
          rmin ≤ sg * ρ (sel x)) ∧
        (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, sg * ρ (sel x) ≤ R)) ∧
      ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
        ∀ y ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
        dist y x ≤ 128 * bb * max (sg * ρ (sel y)) (sg * ρ (sel x)) →
        sg * ρ (sel x) / (5 / 3) ≤ sg * ρ (sel y) ∧
          sg * ρ (sel y) ≤ (5 / 3) * (sg * ρ (sel x)) := by
  have hb0 : 0 < bb := zero_lt_one.trans_le hbb
  have hmo : 128 * bb⁻¹⁻¹ * sg ≤ 1 / 5 := by rwa [inv_inv]
  have hin := cfs14_stage_inputs_GAF2 P.toLocalChartPackets hΛ hΔ hμ hτ he hLΛ st sel hsel
    (inv_pos.mpr hb0) hsg hmo
  refine ⟨hin.1, hin.2.1, hin.2.2.1, fun x hx y hy hd => hin.2.2.2 x hx y hy ?_⟩
  rwa [inv_inv]

/-- **Consumer: CFS12 on an actual stage cloud** (`B = 5/3`, any buffer `bb ≥ 1`, `128bbΣ ≤ 1/5`):
with the (CS) tests at quality `0 < δ ≤ δ₀`, CFS12's selection exists on `S_st` with the tube
`N_{8bb r}(S_st) ⊆ U_bb` — `cfs12_row_CFSA` applied to `cfs1213_actual_inputs_CFSA`. -/
theorem cfs12_actual_cover_CFSA (st : Fin 3) (bb : ℝ) (hbb : 1 ≤ bb) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        0 ≤ Λ → 1 ≤ Δ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → e ≤ 1 / 8 →
        1000000 * Δ * Λ < 1 / 100000 →
        ∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
        (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
          cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st)
            (sel x) = x) →
        ∀ sg : ℝ, 0 < sg → 128 * bb * sg ≤ 1 / 5 →
        ∀ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
          Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
          Module.finrank ℝ (plane x) = gafStageDim st) →
        ∀ δc : ℝ, 0 < δc → δc ≤ δ₀ →
        (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
          hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero st ∩
              ball x (sg * ρ (sel x) / δc))
            ((AffineSubspace.mk' x (plane x) :
                Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
              ball x (sg * ρ (sel x) / δc)) ≤ ENNReal.ofReal (δc * (sg * ρ (sel x)))) →
        ∃ I : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), I.Finite ∧
          I ⊆ gafCloud P.toLocalChartFamily P.zero st ∧
          (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero st, ball x (8 * bb * (sg * ρ (sel x)))) ⊆
            ⋃ i ∈ I, ball i (20 * bb * (sg * ρ (sel i))) := by
  obtain ⟨C, E, δ₀, hδ₀, hker⟩ := cfs12_row_CFSA.{0} (gafStageDim st) bb (5 / 3) hbb (by norm_num)
  refine ⟨δ₀, hδ₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hΛ hΔ hμ hτ he hLΛ sel hsel sg hsg hbsg plane hdim δc hδc hδcd hcloud
  have hin := cfs1213_actual_inputs_CFSA P hΛ hΔ hμ hτ he hLΛ st sel hsel hbb hsg hbsg
  have h3 := hin.2.2.1
  obtain ⟨rmin, h3'⟩ := h3
  obtain ⟨R, h3''⟩ := h3'
  have hk := hker (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (gafCloud P.toLocalChartFamily P.zero st) (gafCloudEnlarged P.toLocalChartFamily P.zero st)
    hin.1 hin.2.1 (fun x => sg * ρ (sel x)) plane hdim rmin R δc h3''.1 h3''.2.1 h3''.2.2 hδc hδcd
    (fun x hx y hy hd => hin.2.2.2 x (hin.1 hx) y (hin.1 hy) hd) hcloud
  exact hk.elim fun I hI => ⟨I, hI.1, hI.2.1, hI.2.2.2.2.1⟩

/-- **Consumer: CFS13 on an actual stage cloud** (`B = 5/3`, any buffer `bb ≥ 1`,
`128bbΣ ≤ 1/5`): with the (CS) tests at quality `0 < δ ≤ δ₀`, CFS13's selection exists on `S_st`
with the tube `N_{8bb r}(S_st) ⊆ U_bb` on which `W` lives — `cfs13_row_CFSA` applied to
`cfs1213_actual_inputs_CFSA`. -/
theorem cfs13_actual_zero_set_CFSA (st : Fin 3) (bb : ℝ) (hbb : 1 ≤ bb) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        0 ≤ Λ → 1 ≤ Δ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → e ≤ 1 / 8 →
        1000000 * Δ * Λ < 1 / 100000 →
        ∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
        (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
          cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st)
            (sel x) = x) →
        ∀ sg : ℝ, 0 < sg → 128 * bb * sg ≤ 1 / 5 →
        ∀ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
          Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
          Module.finrank ℝ (plane x) = gafStageDim st) →
        ∀ δc : ℝ, 0 < δc → δc ≤ δ₀ →
        (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
          hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero st ∩
              ball x (sg * ρ (sel x) / δc))
            ((AffineSubspace.mk' x (plane x) :
                Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
              ball x (sg * ρ (sel x) / δc)) ≤ ENNReal.ofReal (δc * (sg * ρ (sel x)))) →
        ∃ I : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), I.Finite ∧
          I ⊆ gafCloud P.toLocalChartFamily P.zero st ∧
          (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero st, ball x (8 * bb * (sg * ρ (sel x)))) ⊆
            ⋃ i ∈ I, ball i (20 * bb * (sg * ρ (sel i))) := by
  obtain ⟨F, -, δ₀, hδ₀, hker⟩ := cfs13_row_CFSA.{0} (gafStageDim st) bb (5 / 3) hbb (by norm_num)
  refine ⟨δ₀, hδ₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hΛ hΔ hμ hτ he hLΛ sel hsel sg hsg hbsg plane hdim δc hδc hδcd hcloud
  have hin := cfs1213_actual_inputs_CFSA P hΛ hΔ hμ hτ he hLΛ st sel hsel hbb hsg hbsg
  have h3 := hin.2.2.1
  obtain ⟨rmin, h3'⟩ := h3
  obtain ⟨R, h3''⟩ := h3'
  have hk := hker (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (gafCloud P.toLocalChartFamily P.zero st) (gafCloudEnlarged P.toLocalChartFamily P.zero st)
    hin.1 hin.2.1 (fun x => sg * ρ (sel x)) plane hdim rmin R δc h3''.1 h3''.2.1 h3''.2.2 hδc hδcd
    hin.2.2.2 hcloud
  exact hk.elim fun I hI => ⟨I, hI.1, hI.2.1, hI.2.2.2.2.1⟩

end DifferentialGeometry.Geometry.Collapse
