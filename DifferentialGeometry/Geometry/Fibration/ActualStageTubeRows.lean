import DifferentialGeometry.Geometry.Fibration.ActualStageStepApplications
import DifferentialGeometry.Geometry.Metric.CloudSmoothInterpolant
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14

/-!
# CFS16 and CFS05 on the three actual stage clouds (whole rows)

Blueprint `master207B.tex`, CFS16 (`lem:fibration-original-cloud-tube`, B:2911–2938) and CFS05
(`prop:fibration-cloud-local-zero-set`, B:2008–2029, with the cloud convention (CS) of B:1766–1782
and the radius inequality after FC07). Actual data: the stage clouds `S_st = π_st𝓔⁰(A_st) ⊆ S̃_st`
of `𝓔⁰ = cgpGlobalMap` on the final family `LocalChartPacketsC14`, radius `Σρ(sel x)` for ANY
selection `sel` of preimages over `S̃_st` (FC04 at `st = 0`, FC26 at `st = 1, 2`).

* `cfs16_row_CFSA` (CFS16): for every original point `p` with `x = π_st𝓔⁰(p) ∈ S_st`, the chosen
  radius obeys `3/5 Σρ(p) ≤ r(x) ≤ 5/3 Σρ(p)` (equality `r(x) = Σρ(p)` at `st = 0`), and for every map
  `f` with `|f(p) − 𝓔⁰(p)| ≤ eρ(p)`, `e ≤ 3Σ/10`, the input `y = π_st f(p)` satisfies `|y − x| ≤ r(x)/2`,
  `B(y, r(x)/2) ⊆ B(x, r(x)) ⊆ N_r(S_st)` and `[x, y] ⊆ B(x, r(x))`. No descent of `ρ` is used.
* `gafCloud_radius_ineq_CFSA`: the radius inequality `|r(y) − r(x)| ≤ 2(|x − y| + r(x))` (`C = 2`) on
  every actual stage cloud for `0 ≤ Σ ≤ 1/2` (FC04's `Σ`-Lipschitz radius, FC26's selected radius).
* `cfs05_row_CFSA` (CFS05, the row in its own generality, as the accepted CFS02–CFS04 wrappers):
  `δ₀(k, C) > 0` and `F` with: the zero set of CFS04's section `η` on its buffered domain is a smooth
  embedded `k`-manifold, properly embedded there, and over every selected centre, in the cylinder
  of radius `λr_i/4`, it is exactly one graph `n = g_i(t)` with `‖D^q g_i‖ ≤ F_m δ r_i^{1−q}`.
* `cfs05_actual_CFSA`: CFS05 on the actual stage clouds (`C = 2`; boundedness, radius bounds and
  the radius inequality discharged; the (CS) tests at quality `δ ≤ δ₀` are the row's hypothesis).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped BigOperators ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry DifferentialGeometry.Analysis

namespace GC.MetricGeometry

universe u

/-- **CFS05** (`prop:fibration-cloud-local-zero-set`) in the row's own generality: for model
dimension `k` and radius-inequality constant `C ≥ 0` there are `δ₀ > 0` and constants `F_m ≥ 0`
such that every bounded cloud `S ⊆ S̃` with `k`-planes, radius bounded above and away from zero, the
radius inequality and (CS) at quality `0 < δ ≤ δ₀` has CFS02's selection `I` with: CFS04's section
`η` smooth on `Ω = ⋃ B(x_i, 6λr_i) ⊇ U = ⋃ B(x_i, 5λr_i)`, its zero set `Z ⊆ Ω` properly embedded in
`Ω` and a smooth embedded `k`-manifold, and over every selected centre `x_i` exactly one graph
`n = g_i(t)` in the cylinder `|t| < λr_i/4`, `|n| ≤ λr_i/4` (closed normal ball: strengthening), with
`‖D^q g_i‖ ≤ F_m δ r_i^{1−q}` for `q ≤ m`. -/
theorem cfs05_row_CFSA (k : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ F : ℕ → ℝ, (∀ m, 0 ≤ F m) ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        [FiniteDimensional ℝ H] (S T : Set H), S ⊆ T → TotallyBounded S →
        ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
        (∀ x ∈ S, Module.finrank ℝ (P x) = k) →
        ∀ rmin R δ : ℝ, 0 < rmin →
        (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
        0 < δ → δ ≤ δ₀ →
        (∀ x ∈ S, ∀ y ∈ S, |r y - r x| ≤ C * (dist x y + r x)) →
        (∀ x ∈ S, hausdorffEDist (T ∩ ball x (r x / δ))
          ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / δ)) ≤
            ENNReal.ofReal (δ * r x)) →
        let ℓ : ℝ := 1 / (100 * (C + 1))
        let α : ℝ := ℓ / 4
        ∃ (I : Set H) (hI : I.Finite), I ⊆ S ∧
          I.PairwiseDisjoint (fun i => ball i (ℓ * r i)) ∧
          ((⋃ x ∈ S, ball x (ℓ * r x)) ⊆ ⋃ i ∈ I, ball i (5 * ℓ * r i)) ∧
          let w : H → H → ℝ := fun i y =>
            ballCutoff i (10 * ℓ * r i) (2 * (10 * ℓ * r i)) y /
              (∑ a ∈ hI.toFinset, ballCutoff a (10 * ℓ * r a) (2 * (10 * ℓ * r a)) y)
          let Q : H → Submodule ℝ H := fun y =>
            ⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
              (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
          let η : H → H := fun y => (Q y).starProjection
            (y - ∑ i ∈ hI.toFinset, w i y • i)
          ContDiffOn ℝ ∞ η (⋃ i ∈ I, ball i (6 * ℓ * r i)) ∧
          let Ω : Set H := ⋃ i ∈ I, ball i (6 * ℓ * r i)
          let Z : Set H := {z | z ∈ Ω ∧ η z = 0}
          IsProperMap (fun z : Z => (⟨z.1, z.2.1⟩ : Ω)) ∧
          (∃ cs : ChartedSpace (Fin k → ℝ) Z,
            let _ := cs
            IsManifold 𝓘(ℝ, Fin k → ℝ) ∞ Z ∧
            Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞ (Subtype.val : Z → H)) ∧
          ∀ i ∈ I, ∃ g : P i → (P i)ᗮ,
            ContDiffOn ℝ ∞ g (ball 0 (α * r i)) ∧
            (∀ t ∈ ball 0 (α * r i), ‖g t‖ ≤ α * r i / 4 ∧
              η (i + orthogonalCoordinateSum (P i) (t, g t)) = 0) ∧
            (∀ t ∈ ball 0 (α * r i), ∀ n ∈ closedBall 0 (α * r i),
              η (i + orthogonalCoordinateSum (P i) (t, n)) = 0 ↔ n = g t) ∧
            ∀ m, ∀ t ∈ ball 0 (α * r i), ∀ j, j ≤ m →
              ‖iteratedFDeriv ℝ j g t‖ ≤ F m * δ * r i * ((r i)⁻¹) ^ j :=
  exists_uniform_cloud_smooth_interpolant.{u} k C hC

end GC.MetricGeometry

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

/-- At the first stage the selected radius is exact: `ρ(sel x) = ρ(p)` for every preimage `p` of
a point `x` of `S̃₁` (FC04's scale block). -/
theorem gafCloud_first_radius_eq_CFSA
    (sel : BlockSpace (fun _ : CGPTag L Z => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged L Z 0, cgpProjMap L Z (gafStageTags L Z 0) (sel x) = x)
    {x : BlockSpace (fun _ : CGPTag L Z => ℝ²)} (hx : x ∈ gafCloudEnlarged L Z 0) {p : X}
    (hp : (gafStageQ L Z 0).starProjection (cgpGlobalMap L Z p) = x) : ρ (sel x) = ρ p := by
  rw [gafStageQ_starProjection_globalMap] at hp
  have huniv := cgpProjMap_univ_GAF L Z
  have hp' : cgpGlobalMap L Z p = x := by
    rw [← huniv]
    exact hp
  have hs' : cgpGlobalMap L Z (sel x) = x := by
    rw [← huniv]
    exact hsel x hx
  have hr := (fc04_first_cloud_scale L Z (L' := 0) (sg := 1) zero_le_one (by norm_num)).1
  have h1 := hr p
  have h2 := hr (sel x)
  rw [hp'] at h1
  rw [hs'] at h2
  linarith

/-- **The radius inequality on the actual stage clouds** (`C = 2`): for `0 ≤ Σ ≤ 1/2` and every
selection of preimages over `S̃_st`, `|Σρ(sel y) − Σρ(sel x)| ≤ 2(|x − y| + Σρ(sel x))` on `S_st`. -/
theorem gafCloud_radius_ineq_CFSA (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (st : Fin 3)
    (sel : BlockSpace (fun _ : CGPTag L Z => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged L Z st, cgpProjMap L Z (gafStageTags L Z st) (sel x) = x)
    {sg : ℝ} (hsg : 0 ≤ sg) (hsg2 : sg ≤ 1 / 2) :
    ∀ x ∈ gafCloud L Z st, ∀ y ∈ gafCloud L Z st,
      |sg * ρ (sel y) - sg * ρ (sel x)| ≤ 2 * (dist x y + sg * ρ (sel x)) := by
  have hΔ0 : 0 ≤ Δ := by linarith
  intro x hx y hy
  have hxe := gafCloud_subset_enlarged L Z hΔ0 st hx
  have hye := gafCloud_subset_enlarged L Z hΔ0 st hy
  have hsx := hsel x hxe
  have hsy := hsel y hye
  have hρx := mul_nonneg hsg (hρ (sel x)).le
  have hd := dist_nonneg (x := x) (y := y)
  fin_cases st
  · have huniv := cgpProjMap_univ_GAF L Z
    have hx' : cgpGlobalMap L Z (sel x) = x := by
      rw [← huniv]
      exact hsx
    have hy' : cgpGlobalMap L Z (sel y) = y := by
      rw [← huniv]
      exact hsy
    obtain ⟨hr, hlip, -⟩ := fc04_first_cloud_scale L Z (L' := 0) (sg := sg) hsg (by norm_num)
    have h1 := hlip y x
    rw [← hx', ← hy', hr, hr, hx', hy'] at h1
    have h2 : sg * dist y x ≤ 2 * dist x y := by
      rw [dist_comm]
      nlinarith
    linarith
  · have hx8 : x ∈ cgpProjMap L Z (cgpQ2Tags L Z) '' fc27EdgeSet L 8 := hxe
    have hy8 : y ∈ cgpProjMap L Z (cgpQ2Tags L Z) '' fc27EdgeSet L 8 := hye
    have h := (fc27_edge_cloud_scale L Z hΔ hΛ hsmall).2.2.1 sg hsg hsg2 (sel x) (sel y)
      (by rw [show cgpProjMap L Z (cgpQ2Tags L Z) (sel x) = x from hsx]; exact hx8)
      (by rw [show cgpProjMap L Z (cgpQ2Tags L Z) (sel y) = y from hsy]; exact hy8)
    rwa [show cgpProjMap L Z (cgpQ2Tags L Z) (sel x) = x from hsx,
      show cgpProjMap L Z (cgpQ2Tags L Z) (sel y) = y from hsy] at h
  · have hx8 : x ∈ cgpProjMap L Z (cgpQ3Tags L Z) '' fc27SlimSet L 8 := hxe
    have hy8 : y ∈ cgpProjMap L Z (cgpQ3Tags L Z) '' fc27SlimSet L 8 := hye
    have h := (fc27_slim_cloud_scale L Z hΔ hΛ hsmall).2.2.1 sg hsg hsg2 (sel x) (sel y)
      (by rw [show cgpProjMap L Z (cgpQ3Tags L Z) (sel x) = x from hsx]; exact hx8)
      (by rw [show cgpProjMap L Z (cgpQ3Tags L Z) (sel y) = y from hsy]; exact hy8)
    rwa [show cgpProjMap L Z (cgpQ3Tags L Z) (sel x) = x from hsx,
      show cgpProjMap L Z (cgpQ3Tags L Z) (sel y) = y from hsy] at h

/-- **CFS16 on the actual stage clouds** (B:2911). Let `p` be an original point with
`x = π_st𝓔⁰(p) ∈ S_st` and `r(x) = Σρ(sel x)` the radius actually chosen at `x` (ANY selection of
preimages over `S̃_st`). Then `3/5 Σρ(p) ≤ r(x) ≤ 5/3 Σρ(p)`, with equality `r(x) = Σρ(p)` at the
first stage; and for every map `f` with `|f(p) − 𝓔⁰(p)| ≤ eρ(p)` and `e ≤ 3Σ/10`, the perturbed
input `y = π_st f(p)` has `|y − x| ≤ r(x)/2`, `B(y, r(x)/2) ⊆ B(x, r(x)) ⊆ N_r(S_st)`, and the
segment `[x, y]` lies in `B(x, r(x))`. -/
theorem cfs16_row_CFSA (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4)
    (st : Fin 3) (sel : BlockSpace (fun _ : CGPTag L Z => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged L Z st, cgpProjMap L Z (gafStageTags L Z st) (sel x) = x)
    {sg : ℝ} (hsg : 0 < sg) (p : X) (x : BlockSpace (fun _ : CGPTag L Z => ℝ²))
    (hx : x ∈ gafCloud L Z st) (hpx : (gafStageQ L Z st).starProjection (cgpGlobalMap L Z p) = x) :
    3 / 5 * (sg * ρ p) ≤ sg * ρ (sel x) ∧ sg * ρ (sel x) ≤ 5 / 3 * (sg * ρ p) ∧
      (st = 0 → sg * ρ (sel x) = sg * ρ p) ∧
      ∀ (f : X → BlockSpace (fun _ : CGPTag L Z => ℝ²)) (e : ℝ), e ≤ 3 * sg / 10 →
        ‖f p - cgpGlobalMap L Z p‖ ≤ e * ρ p →
        ‖(gafStageQ L Z st).starProjection (f p) - x‖ ≤ sg * ρ (sel x) / 2 ∧
        ball ((gafStageQ L Z st).starProjection (f p)) (sg * ρ (sel x) / 2) ⊆
          ball x (sg * ρ (sel x)) ∧
        ball x (sg * ρ (sel x)) ⊆ ⋃ x' ∈ gafCloud L Z st, ball x' (sg * ρ (sel x')) ∧
        segment ℝ x ((gafStageQ L Z st).starProjection (f p)) ⊆ ball x (sg * ρ (sel x)) := by
  have hΔ0 : 0 ≤ Δ := by linarith
  have hratio := gafCloud_preimage_ratio_two_GAF5 L Z hΔ hΛ hsmall st sel hsel x hx p hpx
  have hρp := hρ p
  have hρx : 0 < ρ (sel x) := by linarith [hratio.1]
  have hr : 0 < sg * ρ (sel x) := mul_pos hsg hρx
  refine ⟨by nlinarith [hratio.1], by nlinarith [hratio.2], fun h0 => ?_, ?_⟩
  · subst h0
    rw [gafCloud_first_radius_eq_CFSA L Z sel hsel (gafCloud_subset_enlarged L Z hΔ0 0 hx) hpx]
  intro f e he hf
  have hyx : ‖(gafStageQ L Z st).starProjection (f p) - x‖ ≤ sg * ρ (sel x) / 2 := by
    have heq : (gafStageQ L Z st).starProjection (f p) - x =
        (gafStageQ L Z st).starProjection (f p - cgpGlobalMap L Z p) := by
      rw [map_sub, hpx]
    rw [heq]
    have h1 := (gafStageQ L Z st).norm_starProjection_apply_le (f p - cgpGlobalMap L Z p)
    have h2 : e * ρ p ≤ 3 * sg / 10 * ρ p := mul_le_mul_of_nonneg_right he hρp.le
    have h3 : 3 * sg / 10 * ρ p ≤ sg * ρ (sel x) / 2 := by nlinarith [hratio.1]
    linarith
  refine ⟨hyx, fun z hz => ?_, ?_, ?_⟩
  · rw [mem_ball] at hz ⊢
    have ht := dist_triangle z ((gafStageQ L Z st).starProjection (f p)) x
    rw [dist_eq_norm ((gafStageQ L Z st).starProjection (f p)) x] at ht
    linarith
  · exact subset_biUnion_of_mem (u := fun x' => ball x' (sg * ρ (sel x'))) hx
  · refine (convex_ball x (sg * ρ (sel x))).segment_subset (mem_ball_self hr) ?_
    rw [mem_ball, dist_eq_norm]
    linarith

end Model

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14T_CFSA {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14T_CFSA {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14T_CFSA {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **CFS05's hypotheses on the actual stage clouds** (all but the (CS) tests, `C = 2`): on the
final family in FC07's range, for every selection of preimages over `S̃_st` and `0 < Σ ≤ 1/2`:
`S_st ⊆ S̃_st`, `S_st` totally bounded, `Σρ ∘ sel` bounded above and away from zero on `S_st`, the
radius inequality `|r(y) − r(x)| ≤ 2(|x − y| + r(x))` on `S_st`, and the stage dimension. -/
theorem cfs05_actual_inputs_CFSA {X : Type} [MetricSpace X] [ChartedSpace E3 X]
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
    {sg : ℝ} (hsg : 0 < sg) (hsg2 : sg ≤ 1 / 2) :
    gafCloud P.toLocalChartFamily P.zero st ⊆ gafCloudEnlarged P.toLocalChartFamily P.zero st ∧
      TotallyBounded (gafCloud P.toLocalChartFamily P.zero st) ∧
      (∃ rmin R : ℝ, 0 < rmin ∧ (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
          rmin ≤ sg * ρ (sel x)) ∧
        (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, sg * ρ (sel x) ≤ R)) ∧
      ∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, ∀ y ∈ gafCloud P.toLocalChartFamily P.zero st,
        |sg * ρ (sel y) - sg * ρ (sel x)| ≤ 2 * (dist x y + sg * ρ (sel x)) := by
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  have hmo : 128 * (640 : ℝ)⁻¹ * sg ≤ 1 / 5 := by
    have h1 : 128 * (640 : ℝ)⁻¹ * sg ≤ 128 * (640 : ℝ)⁻¹ * (1 / 2) :=
      mul_le_mul_of_nonneg_left hsg2 (by norm_num)
    linarith [show 128 * (640 : ℝ)⁻¹ * (1 / 2) = 1 / 10 by norm_num]
  have hin := cfs14_stage_inputs_GAF2 P.toLocalChartPackets hΛ hΔ hμ hτ he hLΛ st sel hsel
    (by norm_num : (0 : ℝ) < 640) hsg hmo
  exact ⟨hin.1, hin.2.1, hin.2.2.1, gafCloud_radius_ineq_CFSA P.toLocalChartFamily P.zero
    (hρ := hρ) hΔ hΛ hsmall st sel hsel hsg.le hsg2⟩

/-- **Consumer: CFS05 on an actual stage cloud** (`C = 2`, `λ = 1/300`): with the (CS) tests at
quality `0 < δ ≤ δ₀`, CFS05's selection exists on `S_st` (finite, disjoint `λr`-balls, the
`5λr`-cover of `N_{λr}(S_st)`) — `cfs05_row_CFSA` applied to `cfs05_actual_inputs_CFSA`. -/
theorem cfs05_actual_cover_CFSA (st : Fin 3) :
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
        ∀ sg : ℝ, 0 < sg → sg ≤ 1 / 2 →
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
          I.PairwiseDisjoint (fun i => ball i (1 / 300 * (sg * ρ (sel i)))) := by
  obtain ⟨δ₀, hδ₀, F, -, hker⟩ := cfs05_row_CFSA.{0} (gafStageDim st) 2 (by norm_num)
  refine ⟨δ₀, hδ₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hΛ hΔ hμ hτ he hLΛ sel hsel sg hsg hsg2 plane hdim δc hδc hδcd hcloud
  have hin := cfs05_actual_inputs_CFSA P hΛ hΔ hμ hτ he hLΛ st sel hsel hsg hsg2
  have h3 := hin.2.2.1
  obtain ⟨rmin, h3'⟩ := h3
  obtain ⟨R, h3''⟩ := h3'
  have hk := hker (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (gafCloud P.toLocalChartFamily P.zero st) (gafCloudEnlarged P.toLocalChartFamily P.zero st)
    hin.1 hin.2.1 (fun x => sg * ρ (sel x)) plane hdim rmin R δc h3''.1 h3''.2.1 h3''.2.2 hδc hδcd
    hin.2.2.2 hcloud
  have hl : (1 : ℝ) / (100 * (2 + 1)) = 1 / 300 := by norm_num
  exact hk.elim fun I hI => ⟨I, hI.1, hI.2.1, by simpa only [hl] using hI.2.2.1⟩

end DifferentialGeometry.Geometry.Collapse
