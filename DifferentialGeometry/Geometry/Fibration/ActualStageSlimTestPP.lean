import DifferentialGeometry.Geometry.Fibration.ActualStageSlimTestApplications
import DifferentialGeometry.Geometry.Fibration.ActualStageSmallMarkers

/-!
# FC27's slim test with the plane rule (PP) for small markers

Blueprint `master207B.tex`, FC27 (B:1658) slim case with CFS27's plane rule (PP) (B:3633–3680) in
the form used by CFS28/CFS31's `hnear` (`stage_small_marker_near_GAF4`): the slim test of
`fc27_slim_test_GAF3` re-assembled from SGP06's pointwise lemma, with the extra clause

  for every `x ∈ S₃`, every preimage `q` of `x` and every retained marker `a` with
  `ρ(c_a) < ρ(q)/5`: `plane x ≤ ker v_a`.

The plane at `x = π₃𝓔⁰(p)` is `im DΦ_i(η_i p)` for SGP04's explicit model `Φ_i = sgpFullGraph` at a
core witness `i`; (AS) at `q` with the full marker of `i` gives `ρ(q) ≤ 5ρ(i)/4`, hence
`ρ(c_a) < ρ(i)/4`, and such blocks are zero in the model (`sgpFullGraph_smallMarker_GAF4`).

* `slim_witness_scale_GAF4`, `slim_pp_point_GAF4`: the two steps at one witness.
* `fc27_slim_test_pp_GAF4` (RVZ) and `fc27_slim_test_pp_C14_GAF4` (C14).
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

section Model

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

/-- (AS) at a slim core witness: every preimage `q` of `π₃𝓔⁰(p)` (`p` in the slim core of `i`)
has `ρ(q) ≤ 5ρ(i)/4` (the slim marker of `i` is full at `p`). -/
theorem slim_witness_scale_GAF4 (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4)
    (i : L.slim.finite_centres.toFinset) {p : X} (hp : p ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1))
    (hη : |(L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤ 7 * 10 ^ 5 * Δ)
    {q : X} (hq : cgpProjMap L Z (cgpQ3Tags L Z) q = cgpProjMap L Z (cgpQ3Tags L Z) p) :
    ρ q ≤ 5 * ρ i.1 / 4 := by
  have hi := (Set.Finite.mem_toFinset _).mp i.2
  have hcut : L.slim.cutoff i.1 p = 1 := by
    rw [slimFamily_cutoff_eq_KA2 L hi]
    exact SlimCentre.cutoff_eq_one_of_abs_coord_le _ hp (by nlinarith)
  have hpos : 0 < cgpMarker L Z (.inr (.inl i)) (cgpProjMap L Z (cgpQ3Tags L Z) q) := by
    rw [hq, cgpMarker_projMap L Z (slim_mem_cgpQ3Tags L Z i), cgpMarker, ← blockMarkerCLM_apply,
      (cgpGlobalMap_markerBlock_GAF2 L Z (.inr (.inl i)) p).2]
    change 0 < ρ i.1 * L.slim.cutoff i.1 p
    rw [hcut, mul_one]
    exact hρ i.1
  exact ((fc27_slim_cloud_scale L Z hΔ hΛ hsmall).1 i q hpos).2

/-- **(PP) at a slim core witness**: for every preimage `q` of `π₃𝓔⁰(p)` and every retained marker
with `ρ(c_a) < ρ(q)/5`, the model plane `im DΦ_i(η_i p)` lies in `ker v_a`. -/
theorem slim_pp_point_GAF4 (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (i : L.slim.finite_centres.toFinset) (sgn c zsgn zc : X → ℝ) {p : X}
    (hp : p ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1))
    (hη : |(L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤ 7 * 10 ^ 5 * Δ) :
    ∀ q, cgpProjMap L Z (cgpQ3Tags L Z) q = cgpProjMap L Z (cgpQ3Tags L Z) p →
      ∀ a : CGPMarkerIndex L, ρ (cgpMarkerCentre L a) < ρ q / 5 →
        (fderiv ℝ (sgpFullGraph L Z i sgn c zsgn zc)
            ((L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p)).range ≤
          LinearMap.ker ((blockMarkerCLM (V := fun _ : CGPTag L Z => ℝ²) (cgpMarkerTag L Z a) :
            BlockSpace (fun _ : CGPTag L Z => ℝ²) →L[ℝ] ℝ) :
              BlockSpace (fun _ : CGPTag L Z => ℝ²) →ₗ[ℝ] ℝ) := by
  intro q hq a ha
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  have h1 := slim_witness_scale_GAF4 L Z hΔ hΛ hsmall i hp hη hq
  have hri := hρ i.1
  have ha' : ρ (cgpMarkerCentre L a) ≤ 99 / 100 * ρ i.1 := by linarith
  rintro _ ⟨h, rfl⟩
  exact LinearMap.mem_ker.mpr (sgpFullGraph_smallMarker_GAF4 L Z (by linarith) hΛ hLΛ i sgn c zsgn
    zc a ha' _ h)

end Model

section Row

/-- The model metrics of `LocalChartPacketsRVZ`, as a named local instance. -/
local instance instMetricNRVZ_GAF4s {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsRVZ`, as a named local instance. -/
local instance instChartedNRVZ_GAF4s {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsRVZ`, as a named local instance. -/
local instance instMetricCRVZ_GAF4s {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **FC27's slim test with (PP)** (`fc27_slim_test_GAF3` plus the small-marker plane rule). Same
thresholds, hypotheses and first three conclusions as `fc27_slim_test_GAF3`; in addition, for every
`x ∈ S₃`, every preimage `q` of `x` (`π₃𝓔⁰(q) = x`) and every retained marker `a` with
`ρ(c_a) < ρ(q)/5`, the plane at `x` lies in the kernel of the marker `v_a = (·)_{a}.snd`. -/
theorem fc27_slim_test_pp_GAF4 {Δ β₂ Γ sg eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1)
    (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg) (hsgΓ : sg < Γ / 200)
    (hsgC : sg < Γ ^ 3 / (100 * sgpGraphBound)) (heg : 0 < eg) (heg1 : eg < 1 / 100)
    (hegΓ : eg < Γ * sg / 100) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
        0 < σs → σs < θ ^ 2 / 10 ^ 6 → vs < θ / 100 →
        0 < ζ → ζ < θ ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
        εr < θ / (100 * (1000000 * Δ)) →
        ∃ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
            Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
          (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
            Module.finrank ℝ (plane x) = gafStageDim 2 ∧
              plane x ≤ gafStageQ P.toLocalChartFamily P.zero 2) ∧
          (∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
            (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 2,
              cgpProjMap P.toLocalChartFamily P.zero
                (gafStageTags P.toLocalChartFamily P.zero 2) (sel x) = x) →
            ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
              hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 2 ∩
                  ball x (sg * ρ (sel x) / Γ))
                ((AffineSubspace.mk' x (plane x) :
                    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
                  ball x (sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel x)))) ∧
          (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
            ∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
            ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q =
              x →
            let Pq := (plane x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)) q)
            Function.Surjective Pq ∧
            (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ3Tags P.toLocalChartFamily P.zero)) q v - (Pq v : BlockSpace _)‖ ≤
              eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
            (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
              1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
            ∀ v, ‖Pq v‖ ≤ 3 * sgpGraphBound * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
          ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2, ∀ q,
            cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) q =
              x →
            ∀ a : CGPMarkerIndex P.toLocalChartFamily,
              ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
              plane x ≤ LinearMap.ker ((blockMarkerCLM
                (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
                (cgpMarkerTag P.toLocalChartFamily P.zero a) :
                  BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
                BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ) := by
  obtain ⟨θ, hθ, hθ1, Lc, η₀, hLc, hη₀, hrow⟩ := sgp05_row hΔ hβ₂ hβ₂1 heg heg1
  have hθ2 : θ ^ 2 / 10 ^ 6 < 1 / 100 := by
    have : θ ^ 2 < 1 := by nlinarith
    rw [div_lt_iff₀ (by norm_num)]
    linarith
  refine ⟨θ, hθ, hθ1, Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hβ2 hβ1 hLmax hΛ hLΛ he hT hΛzT hσs hσθ hvθ hζ hζθ hζL hεr
  have hrowP := hrow X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε
    γc βc Lmax τ γ δ εr e T V vs ζ Λz P hβ2 hβ1 hLmax hΛ hLΛ he hT
    hΛzT hσs hσθ hvθ hζ hζθ hζL hεr
  have hσ1 : σs < 1 / 100 := hσθ.trans hθ2
  have hpt : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
      ∃ W : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (Module.finrank ℝ W = gafStageDim 2 ∧ W ≤ gafStageQ P.toLocalChartFamily P.zero 2) ∧
        (∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
          (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 2,
            cgpProjMap P.toLocalChartFamily P.zero
              (gafStageTags P.toLocalChartFamily P.zero 2) (sel x) = x) →
          hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 2 ∩
              ball x (sg * ρ (sel x) / Γ))
            ((AffineSubspace.mk' x W :
                Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
              ball x (sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel x)))) ∧
        (∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
        ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q =
          x →
        let Pq := W.orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
          (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)) q)
        Function.Surjective Pq ∧
        (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
            (cgpQ3Tags P.toLocalChartFamily P.zero)) q v - (Pq v : BlockSpace _)‖ ≤
          eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
        (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
          1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
        ∀ v, ‖Pq v‖ ≤ 3 * sgpGraphBound * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
        ∀ q, cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) q =
            x →
          ∀ a : CGPMarkerIndex P.toLocalChartFamily,
            ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
            W ≤ LinearMap.ker ((blockMarkerCLM
              (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
              (cgpMarkerTag P.toLocalChartFamily P.zero a) :
                BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ) := by
    intro x hx
    have hx' : x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) ''
        fc27SlimSet P.toLocalChartFamily 7 := hx
    obtain ⟨p, ⟨i, hp, hηp⟩, rfl⟩ := hx'
    have hi := (Set.Finite.mem_toFinset _).mp i.2
    have hηp' : |(P.slim.centre i.1 hi).coord p| ≤ 7 * (10 ^ 5 * Δ) := by
      rw [← mul_assoc]
      exact hηp
    have hrowi := hrowP i
    obtain ⟨sgn, c, zsgn, zc, hsgn, hzsgn, hSG, hrk⟩ := hrowi
    have hs01 := sgp01_row P.toLocalChartPacketsR hΛ hΔ hLΛ he hT hσs.le hσ1.le hi
    obtain ⟨-, -, -, huniq, hzero01, -⟩ := hs01
    have hs0 : ∀ k (hk : k ∈ P.zero.centres),
        sgpZeroMeets P.zero (Δ := Δ) (ρ := ρ) i.1 k hk → 1 ≤ (P.zero.zero k hk).radius / ρ i.1 :=
      fun k hk hm => (one_le_div_twenty_SGP4 hΔ hT).trans (hzero01 k hk hm).1
    have hpoint := sgp06_point_SGP5 P.toLocalChartFamily P.zero hΔ hΛ hLΛ i sgn c zsgn zc hsgn
      hzsgn hs0 huniq hΓ hΓ1 hsg hsgΓ hsgC heg hegΓ (fun y hy hyη => (hSG y hy hyη).1) hp hηp'
    obtain ⟨hfin, hcl⟩ := hpoint
    have hQ := range_fderiv_sgpFullGraph_le_GAF3 P.toLocalChartFamily P.zero i sgn c zsgn zc
      ((P.slim.centre i.1 hi).coord p)
    have hpp := slim_pp_point_GAF4 P.toLocalChartFamily P.zero hΔ hΛ hLΛ i sgn c zsgn zc hp hηp
    exact ⟨_, ⟨hfin, hQ⟩, hcl, ⟨i, hrk p hp hηp'⟩, hpp⟩
  choose! plane hplane using hpt
  exact ⟨plane, fun x hx => (hplane x hx).1, fun sel hsel x hx =>
    (hplane x hx).2.1 sel hsel, fun x hx => (hplane x hx).2.2.1, fun x hx => (hplane x hx).2.2.2⟩

end Row

end DifferentialGeometry.Geometry.Collapse
