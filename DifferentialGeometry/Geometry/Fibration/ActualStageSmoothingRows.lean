import DifferentialGeometry.Geometry.Fibration.ActualStageClouds
import DifferentialGeometry.Geometry.Fibration.ActualCfs15StageOutputMean
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14

/-!
# CFS14 and CFS15 on the three actual stage clouds (whole rows)

Blueprint `master207B.tex`, CFS14 (`thm:fibration-cloud-controlled-global-smoothing`, B:2628–2709)
and CFS15 (`cor:fibration-cloud-marker-modulus`, B:2711–2748), with the standing hypotheses of
B:2425–2449. The actual data are the three stage clouds `S_st = π_st𝓔⁰(A_st) ⊆ S̃_st` of CGP01's
`𝓔⁰ = cgpGlobalMap` on the final family `LocalChartPacketsC14` (FC07's parameter range), the radius
`Σρ(sel x)` for ANY selection `sel` of preimages over `S̃_st` (FC04 at `st = 0`, FC26 at `st = 1, 2`)
and planes of the stage dimension `gafStageDim st`. The (CS) tests at quality `δ` are the rows' own
standing hypothesis (B:2429–2430, "the actual (CS) tests hold with quality `δ`"); boundedness, the
radius bounds and (MCb) at the buffer `128 ε⁻¹` are discharged (`cfs14_stage_inputs_GAF2`).

* `Cfs15StageOutput.cfs14_clauses_CFSA`: CFS14's listed conclusions (1)–(3) read off a native output.
* `cfs14_row_CFSA`: CFS14 — for `k = gafStageDim st`, jet order `K`, `0 < ε ≤ 1/10`: a threshold
  `d_* > 0` (before the data) such that every actual stage cloud with (CS) at quality `δ ≤ d_*`
  and `128 ε⁻¹ Σ ≤ 1/5` has a smoothing `W = O.Z` with (1)–(3).
* `cfs15_row_CFSA`: CFS15 — `θ₁ > 0`, `Ξ → 0`, and for `0 < Γ < θ₁`, `0 < Σ ≤ Ξ(Γ)/640` ((MO)) every
  actual stage cloud of quality `Γ` has a native output at accuracy `Ξ(Γ)` (CFS14's conclusions,
  explicit through `Cfs15StageOutput.cfs14_clauses_CFSA`).
* Consumers (the (CS) hypothesis supplied by the producer): `cfs15_firstStagePlanes_CFSA`,
  `cfs15_edgeStagePlanes_CFSA`, `cfs15_slimStagePlanes_CFSA` (FC27's `cloudy` field of the enhanced
  stage planes at their own radius selection `A.rsel x₀`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace GC.MetricGeometry.Cfs15StageOutput

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  {k K : ℕ} {ε cw : ℝ} {S T : Set H} {r : H → ℝ} {P : H → Submodule ℝ H}

/-- **CFS14's listed conclusions on a native output** `O` (the smoothing is `W = O.Z`):
(1) at every core centre the `r_x⁻¹`-rescaled enlarged cloud and `W` have truncated Hausdorff
error `≤ ε` on the closed and on the open radius-`ε⁻¹` ball, and `W ⊆ N_{εr}(S̃)` (radius at the
witness); (2) `W ∩ N_r(S)` is properly embedded in `N_r(S)` and the normal projectors on
`W ∩ B(x, r_x)` are `ε`-close to `P_x`; (3) the nearest-point map `p : N_r(S) → W` is a smooth
submersion onto its unique nearest points, with `|P − P_{A_x}| ≤ εr_x` and
`‖D^q(P − P_{A_x})‖ ≤ εr_x^{1−q}` (`1 ≤ q ≤ K`) on every `B(x, r_x)`, `P = O.ambient = ι ∘ p`. -/
theorem cfs14_clauses_CFSA (O : Cfs15StageOutput k K ε cw S T r P) :
    ((∀ x ∈ S,
      hausdorffEDist (((fun y => (r x)⁻¹ • (y - x)) '' T) ∩ closedBall 0 ε⁻¹)
          (((fun y => (r x)⁻¹ • (y - x)) '' O.Z) ∩ closedBall 0 ε⁻¹) ≤ ENNReal.ofReal ε ∧
        hausdorffEDist (((fun y => (r x)⁻¹ • (y - x)) '' T) ∩ ball 0 ε⁻¹)
          (((fun y => (r x)⁻¹ • (y - x)) '' O.Z) ∩ ball 0 ε⁻¹) ≤ ENNReal.ofReal ε) ∧
      O.Z ⊆ ⋃ q ∈ T, ball q (ε * r q)) ∧
    (IsProperMap (Subtype.val :
        {z : (⋃ x ∈ S, ball x (r x) : Set H) | (z : H) ∈ O.Z} → (⋃ x ∈ S, ball x (r x) : Set H)) ∧
      (let _ := O.cs
       ∀ x : S, ∀ z : O.Z, (z : H) ∈ ball (x : H) (r x) →
        ‖actualZeroSetNormalProjector k O.Z z - (P x)ᗮ.starProjection‖ ≤ ε)) ∧
    (let _ := O.cs
     _root_.Manifold.IsSubmersion 𝓘(ℝ, H) 𝓘(ℝ, Fin k → ℝ) ∞ O.p ∧
      (∀ z : cfs15Omega_C15 S r,
        IsMinOn (fun y => dist (z : H) y) O.Z (O.p z : H) ∧
          (∀ y ∈ O.Z, IsMinOn (fun w => dist (z : H) w) O.Z y → y = (O.p z : H))) ∧
      (∀ z : cfs15Omega_C15 S r, O.ambient z = O.p z) ∧
      ∀ x ∈ S, ∀ z ∈ ball x (r x),
        ‖O.ambient z - (x + (P x).starProjection (z - x))‖ ≤ ε * r x ∧
        ∀ q, 1 ≤ q → q ≤ K →
          ‖iteratedFDeriv ℝ q (fun y => O.ambient y - (x + (P x).starProjection (y - x))) z‖ ≤
            ε * r x * (r x)⁻¹ ^ q) := by
  have hε := O.eps_pos
  have h716 : ENNReal.ofReal (7 * ε / 16) ≤ ENNReal.ofReal ε :=
    ENNReal.ofReal_le_ofReal (by linarith)
  refine ⟨⟨fun x hx => ⟨(O.hausdorff x hx).1.trans h716, (O.hausdorff x hx).2.trans h716⟩,
    O.near_cloud⟩, ⟨O.proper_over, O.normal_proj⟩, O.submersion, O.nearest,
    fun z => O.ambient_eq z z.2, fun x hx z hz => ⟨(O.ambient_value_deriv hx hz).1, ?_⟩⟩
  intro q _ hqK
  have hrx := O.radius_pos x hx
  have hj := O.ambient_jets ⟨x, hx⟩ z hz q hqK
  have hnn : 0 ≤ r x * (r x)⁻¹ ^ q := by positivity
  calc ‖iteratedFDeriv ℝ q (fun y => O.ambient y - (x + (P x).starProjection (y - x))) z‖
      ≤ ε / 3 * r x * (r x)⁻¹ ^ q := hj
    _ = ε / 3 * (r x * (r x)⁻¹ ^ q) := by ring
    _ ≤ ε * (r x * (r x)⁻¹ ^ q) := mul_le_mul_of_nonneg_right (by linarith) hnn
    _ = ε * r x * (r x)⁻¹ ^ q := by ring

end GC.MetricGeometry.Cfs15StageOutput

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_CFSA {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_CFSA {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_CFSA {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **CFS14 on the actual stage clouds** (B:2628). Fix the stage `st` (model dimension
`k = gafStageDim st`), the jet order `K` and `0 < ε ≤ 1/10` (`b = ε⁻¹`). There are a threshold
`d_* > 0` and CFS12's early weight constant `c_w ≥ 0`, chosen before the data, such that for every
packet of the final family in FC07's range, every selection `sel` of preimages over `S̃_st`, every
`Σ > 0` with `128 ε⁻¹ Σ ≤ 1/5`, every plane field of the stage dimension, and every quality
`0 < δ ≤ d_*` of the actual (CS) tests, the native output `O` (smoothing `W = O.Z`, nearest map
`p`, `P = O.ambient`) exists and has all CFS14 conclusions (1)–(3). -/
theorem cfs14_row_CFSA (st : Fin 3) (Kj : ℕ) (εa : ℝ) (hεa : 0 < εa) (hεa10 : εa ≤ 1 / 10) :
    ∃ dstar : ℝ, 0 < dstar ∧ ∃ cw : ℝ, 0 ≤ cw ∧
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
        ∀ sg : ℝ, 0 < sg → 128 * εa⁻¹ * sg ≤ 1 / 5 →
        ∀ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
          Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
          Module.finrank ℝ (plane x) = gafStageDim st) →
        ∀ δc : ℝ, 0 < δc → δc ≤ dstar →
        (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
          hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero st ∩
              ball x (sg * ρ (sel x) / δc))
            ((AffineSubspace.mk' x (plane x) :
                Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
              ball x (sg * ρ (sel x) / δc)) ≤ ENNReal.ofReal (δc * (sg * ρ (sel x)))) →
        ∃ O : Cfs15StageOutput (gafStageDim st) Kj εa cw (gafCloud P.toLocalChartFamily P.zero st)
            (gafCloudEnlarged P.toLocalChartFamily P.zero st) (fun x => sg * ρ (sel x)) plane,
          ((∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
            hausdorffEDist (((fun y => (sg * ρ (sel x))⁻¹ • (y - x)) ''
                gafCloudEnlarged P.toLocalChartFamily P.zero st) ∩ closedBall 0 εa⁻¹)
              (((fun y => (sg * ρ (sel x))⁻¹ • (y - x)) '' O.Z) ∩ closedBall 0 εa⁻¹) ≤
              ENNReal.ofReal εa ∧
            hausdorffEDist (((fun y => (sg * ρ (sel x))⁻¹ • (y - x)) ''
                gafCloudEnlarged P.toLocalChartFamily P.zero st) ∩ ball 0 εa⁻¹)
              (((fun y => (sg * ρ (sel x))⁻¹ • (y - x)) '' O.Z) ∩ ball 0 εa⁻¹) ≤
              ENNReal.ofReal εa) ∧
            O.Z ⊆ ⋃ q ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
              ball q (εa * (sg * ρ (sel q)))) ∧
          (IsProperMap (Subtype.val :
              {z : (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero st, ball x (sg * ρ (sel x)) :
                  Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) |
                (z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∈ O.Z} →
              (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero st, ball x (sg * ρ (sel x)) :
                Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))) ∧
            (let _ := O.cs
             ∀ x : gafCloud P.toLocalChartFamily P.zero st, ∀ z : O.Z,
              (z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∈
                ball (x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
                  (sg * ρ (sel x)) →
              ‖actualZeroSetNormalProjector (gafStageDim st) O.Z z -
                (plane x)ᗮ.starProjection‖ ≤ εa)) ∧
          (let _ := O.cs
           _root_.Manifold.IsSubmersion
              𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
              𝓘(ℝ, Fin (gafStageDim st) → ℝ) ∞ O.p ∧
            (∀ z : cfs15Omega_C15 (gafCloud P.toLocalChartFamily P.zero st)
                (fun x => sg * ρ (sel x)),
              IsMinOn (fun y => dist (z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero =>
                ℝ²)) y) O.Z (O.p z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∧
                (∀ y ∈ O.Z, IsMinOn (fun w => dist (z : BlockSpace (fun _ : CGPTag
                  P.toLocalChartFamily P.zero => ℝ²)) w) O.Z y →
                  y = (O.p z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))) ∧
            (∀ z : cfs15Omega_C15 (gafCloud P.toLocalChartFamily P.zero st)
                (fun x => sg * ρ (sel x)),
              O.ambient z = O.p z) ∧
            ∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, ∀ z ∈ ball x (sg * ρ (sel x)),
              ‖O.ambient z - (x + (plane x).starProjection (z - x))‖ ≤ εa * (sg * ρ (sel x)) ∧
              ∀ q, 1 ≤ q → q ≤ Kj →
                ‖iteratedFDeriv ℝ q (fun y => O.ambient y - (x + (plane x).starProjection (y - x)))
                    z‖ ≤ εa * (sg * ρ (sel x)) * (sg * ρ (sel x))⁻¹ ^ q) := by
  obtain ⟨cw, hcw, δ₀, hδ₀, hker⟩ :=
    exists_cfs15StageOutput_C15.{0} (gafStageDim st) Kj (5 / 3) εa (by norm_num) hεa hεa10
  refine ⟨δ₀, hδ₀, cw, hcw, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hΛ hΔ hμ hτ he hLΛ sel hsel sg hsg hmo plane hdim δc hδc hδcd hcloud
  have hin := cfs14_stage_inputs_GAF2 P.toLocalChartPackets hΛ hΔ hμ hτ he hLΛ st sel hsel hεa hsg
    hmo
  have h3 := hin.2.2.1
  obtain ⟨rmin, h3'⟩ := h3
  obtain ⟨R, h3''⟩ := h3'
  have hO := hker (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (gafCloud P.toLocalChartFamily P.zero st) (gafCloudEnlarged P.toLocalChartFamily P.zero st)
    hin.1 hin.2.1 (fun x => sg * ρ (sel x)) plane hdim rmin R δc h3''.1 h3''.2.1 h3''.2.2 hδc hδcd hin.2.2.2
    hcloud
  exact hO.elim fun O => ⟨O, O.cfs14_clauses_CFSA⟩

/-- `(MO)`: `Σ ≤ Ξ/640` gives the buffer bound `128 Ξ⁻¹ Σ ≤ 1/5` of (MCb). -/
theorem mo_buffer_CFSA {Ξ sg : ℝ} (hΞ : 0 < Ξ) (hsg : sg ≤ Ξ / 640) :
    128 * Ξ⁻¹ * sg ≤ 1 / 5 := by
  have h1 : 128 * Ξ⁻¹ * sg ≤ 128 * Ξ⁻¹ * (Ξ / 640) :=
    mul_le_mul_of_nonneg_left hsg (by positivity)
  have h2 : 128 * Ξ⁻¹ * (Ξ / 640) = 1 / 5 := by
    field_simp
    norm_num
  linarith

/-- **CFS15 on the actual stage clouds** (B:2711). For the stage `st` (`k = gafStageDim st`) and the
jet order `K` there are `θ₁ > 0` and a modulus `Ξ` with `Ξ(Γ) → 0` as `Γ ↓ 0` such that: first
choose `0 < Γ < θ₁` (then `0 < Ξ(Γ) ≤ 1/10`, and CFS12's weight constant `c_w ≥ 0` is fixed), then
choose `0 < Σ ≤ Ξ(Γ)/640` ((MO)); every actual stage cloud of quality `Γ` (the (CS) tests at radius
`Σρ(sel x)`, any selection of preimages, FC04 / FC26 marker data of the final family) has a native
output `Cfs15StageOutput … (Ξ Γ) …`, i.e. all CFS14 conclusions (1)–(3) at accuracy `Ξ(Γ)` (read off
explicitly by `Cfs15StageOutput.cfs14_clauses_CFSA`). -/
theorem cfs15_row_CFSA (st : Fin 3) (Kj : ℕ) :
    ∃ θ₁ : ℝ, 0 < θ₁ ∧ ∃ Ξ : ℝ → ℝ, Tendsto Ξ (𝓝[>] 0) (𝓝 0) ∧
      ∀ Γ, 0 < Γ → Γ < θ₁ → 0 < Ξ Γ ∧ Ξ Γ ≤ 1 / 10 ∧ ∃ cw : ℝ, 0 ≤ cw ∧
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
        ∀ sg : ℝ, 0 < sg → sg ≤ Ξ Γ / 640 →
        ∀ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
          Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
          Module.finrank ℝ (plane x) = gafStageDim st) →
        (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
          hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero st ∩
              ball x (sg * ρ (sel x) / Γ))
            ((AffineSubspace.mk' x (plane x) :
                Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
              ball x (sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel x)))) →
        Nonempty (Cfs15StageOutput (gafStageDim st) Kj (Ξ Γ) cw
          (gafCloud P.toLocalChartFamily P.zero st)
          (gafCloudEnlarged P.toLocalChartFamily P.zero st) (fun x => sg * ρ (sel x)) plane) := by
  obtain ⟨θ₁, hθ₁, Ξ, hΞ, h⟩ := exists_cfs15StageOutput_with_mean (gafStageDim st) Kj
  refine ⟨θ₁, hθ₁, Ξ, hΞ, fun Γ hΓ hΓθ => ?_⟩
  have hh := h Γ hΓ hΓθ
  obtain ⟨m, hm⟩ := hh.1
  have hcwex := hh.2.2.2
  have hΞpos : 0 < Ξ Γ := by rw [hm]; positivity
  have hΞ10 : Ξ Γ ≤ 1 / 10 := by
    rw [hm]
    calc (1 / 2 : ℝ) ^ (m + 4) ≤ (1 / 2 : ℝ) ^ 4 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ ≤ 1 / 10 := by norm_num
  refine ⟨hΞpos, hΞ10, hcwex.choose, hcwex.choose_spec.1, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hΛ hΔ hμ hτ he hLΛ sel hsel sg hsg hsgΞ plane hdim hcloud
  have hin := cfs14_stage_inputs_GAF2 P.toLocalChartPackets hΛ hΔ hμ hτ he hLΛ st sel hsel hΞpos
    hsg (mo_buffer_CFSA hΞpos hsgΞ)
  have h3 := hin.2.2.1
  obtain ⟨rmin, h3'⟩ := h3
  obtain ⟨R, h3''⟩ := h3'
  have hO := hcwex.choose_spec.2 (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (gafCloud P.toLocalChartFamily P.zero st) (gafCloudEnlarged P.toLocalChartFamily P.zero st)
    hin.1 hin.2.1 (fun x => sg * ρ (sel x)) plane hdim rmin R h3''.1 h3''.2.1 h3''.2.2 hin.2.2.2 hcloud
  exact hO.elim fun O _ => ⟨O⟩

end DifferentialGeometry.Geometry.Collapse
