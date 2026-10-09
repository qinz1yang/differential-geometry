import DifferentialGeometry.Geometry.Fibration.ActualStageTargets
import DifferentialGeometry.Geometry.Fibration.ActualFirstCloud

/-!
# FC27's first-cloud test: TCP06's planes in the stage notation of GAF01/GAF02

Blueprint `master207B.tex`, FC27 (`found:fibration-projected-clouds`, B:1658, the first cloud from
TCP06) in the frozen form of `sheet-C14-GAF2.md` (stage `st = 0`, `k = 2`) with the amendment
`plane x ≤ Q₁` (`Q₁ = H`, so it is automatic).

* `gafCloud_zero_GAF4`, `gafCloudEnlarged_zero_GAF4`: `S₁ = 𝓔⁰(A₁)`, `S̃₁ = 𝓔⁰(Ã₁)` (`π₁ = id`).
* `gafStageQ_zero_GAF4`: `Q₁ = ⊤`.
* `fc27_first_of_tcp06_GAF4`: TCP06's dimension and (CS) clauses (radius `scaleRadius Σ`, FC04's
  exact first-image radius) give the stage form at radius `Σρ(sel x)` for EVERY selection of
  preimages over `S̃₁` (`scaleRadius Σ (𝓔⁰ q) = Σρ(q)`, `fc04_first_cloud_scale`).
* `fc27_first_test_GAF4`: on `LocalChartPacketsC14` under TCP06's thresholds and hypotheses
  (verbatim, `tcp06_row`), planes over `S₁ = gafCloud 0` with dimension `gafStageDim 0 = 2`, inside
  `gafStageQ 0`, the (CS) test at quality `Γ` and radius `Σρ(sel x)` for every selection, and
  TCP06's all-preimage rank clauses for the same planes.
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

/-- The first stage cloud is the `𝓔⁰`-image of FC04's core (`π₁ = id`). -/
theorem gafCloud_zero_GAF4 : gafCloud L Z 0 = cgpGlobalMap L Z '' fc04Set L Z 7 := by
  change cgpProjMap L Z Finset.univ '' fc04Set L Z 7 = _
  rw [cgpProjMap_univ_GAF]

/-- The enlarged first stage cloud is the `𝓔⁰`-image of FC04's enlargement. -/
theorem gafCloudEnlarged_zero_GAF4 :
    gafCloudEnlarged L Z 0 = cgpGlobalMap L Z '' fc04Set L Z 8 := by
  change cgpProjMap L Z Finset.univ '' fc04Set L Z 8 = _
  rw [cgpProjMap_univ_GAF]

/-- The first stage target is the whole block space. -/
theorem gafStageQ_zero_GAF4 : gafStageQ L Z 0 = ⊤ := by
  classical
  rw [eq_top_iff]
  intro v _
  rw [mem_gafStageQ_iff]
  change blockRestrict Finset.univ v = v
  rw [blockRestrict_univ]
  rfl

/-- **TCP06's clauses in the stage form.** Dimension `2` and the (CS) test at FC04's exact radius
`scaleRadius Σ` over `S₁ = 𝓔⁰(A₁)` give, at stage `0`: dimension `gafStageDim 0`, planes inside
`gafStageQ 0`, and the (CS) test at radius `Σρ(sel x)` for every selection of preimages over
`S̃₁`. -/
theorem fc27_first_of_tcp06_GAF4
    (plane : BlockSpace (fun _ : CGPTag L Z => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag L Z => ℝ²))) {sg Γ : ℝ} (hsg : 0 ≤ sg)
    (hdim : ∀ x ∈ cgpGlobalMap L Z '' fc04Set L Z 7, Module.finrank ℝ (plane x) = 2)
    (hcs : ∀ x ∈ cgpGlobalMap L Z '' fc04Set L Z 7,
      hausdorffEDist (cgpGlobalMap L Z '' fc04Set L Z 8 ∩
          ball x (scaleRadius (cgpScaleTag L Z) sg x / Γ))
        ((AffineSubspace.mk' x (plane x) : Set (BlockSpace (fun _ : CGPTag L Z => ℝ²))) ∩
          ball x (scaleRadius (cgpScaleTag L Z) sg x / Γ)) ≤
        ENNReal.ofReal (Γ * scaleRadius (cgpScaleTag L Z) sg x)) :
    (∀ x ∈ gafCloud L Z 0, Module.finrank ℝ (plane x) = gafStageDim 0 ∧
      plane x ≤ gafStageQ L Z 0) ∧
    ∀ sel : BlockSpace (fun _ : CGPTag L Z => ℝ²) → X,
      (∀ x ∈ gafCloudEnlarged L Z 0, cgpProjMap L Z (gafStageTags L Z 0) (sel x) = x) →
      ∀ x ∈ gafCloud L Z 0,
        hausdorffEDist (gafCloudEnlarged L Z 0 ∩ ball x (sg * ρ (sel x) / Γ))
          ((AffineSubspace.mk' x (plane x) : Set (BlockSpace (fun _ : CGPTag L Z => ℝ²))) ∩
            ball x (sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel x))) := by
  rw [gafCloud_zero_GAF4, gafStageQ_zero_GAF4]
  refine ⟨fun x hx => ⟨hdim x hx, le_top⟩, fun sel hsel x hx => ?_⟩
  rw [gafCloudEnlarged_zero_GAF4] at hsel ⊢
  have hx8 : x ∈ cgpGlobalMap L Z '' fc04Set L Z 8 :=
    image_mono (fc04Set_mono L Z (by norm_num)) hx
  have hF : cgpGlobalMap L Z (sel x) = x := by
    rw [← cgpProjMap_univ_GAF L Z]
    exact hsel x hx8
  have hr : scaleRadius (cgpScaleTag L Z) sg x = sg * ρ (sel x) := by
    have h0 := (fc04_first_cloud_scale L Z (L' := 0) hsg (by norm_num)).1 (sel x)
    rw [hF] at h0
    exact h0
  have h := hcs x hx
  rw [hr] at h
  exact h

end Model

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_GAF4f {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_GAF4f {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_GAF4f {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **FC27, the first-cloud test** (stage `0` of GAF01/GAF02; TCP06 in the stage notation). For
(TP) `0 < Γ < 1`, `0 < Σ < min(Γ/200, Γ³/(100C₁))`, `0 < e < min(1/100, ΓΣ/100)` and `0 < ν < 1`
there are TCP06's thresholds such that on every actual `LocalChartPacketsC14` with TCP06's
hypotheses (verbatim) there are planes `plane x` over `S₁ = gafCloud 0` with
(1) `dim plane x = gafStageDim 0` and `plane x ≤ gafStageQ 0 = H`; (2) for ANY selection of
preimages over `S̃₁ = gafCloudEnlarged 0`, the (CS) test at quality `Γ`, radius `r = Σρ(sel x)`;
(3) TCP06's rank clauses for `plane x` at every preimage of `x`. -/
theorem fc27_first_test_GAF4 {ν Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg)
    (hsgΓ : sg < Γ / 200) (hsgC : sg < Γ ^ 3 / (100 * tcpGraphConst)) (heg : 0 < eg)
    (heg1 : eg < 1 / 100) (hegΓ : eg < Γ * sg / 100) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ γ₀ ηc θ : ℝ, 0 < η₂ ∧ 0 < γ₀ ∧ 0 < ηc ∧ 0 < θ ∧
    θ < 1 ∧ ∀ Δ : ℝ, 1200 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
      (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
        e T V vs ζ Λz),
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      0 ≤ ε → ε ≤ 1 → 0 ≤ σc → σc ≤ θ ^ 2 / 1000 → μ * Δ ≤ θ / 100 →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → 0 < γc → γc ≤ γ₀ → βc ≤ ηc →
      b ≤ η₁ → β 1 ≤ η₁ → 0 < σs → σs ≤ θ ^ 2 / 1000 → vs ≤ θ / 100 → 0 < ζ →
      ζ ≤ θ ^ 2 / 1000 → εr ≤ θ / 100 → 20 * Λz ≤ T → σ⁻¹ ≤ Lmax →
      1000 * tcpGraphConst * Δ * Λ < eg →
      ∃ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
          Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
          Module.finrank ℝ (plane x) = gafStageDim 0 ∧
            plane x ≤ gafStageQ P.toLocalChartFamily P.zero 0) ∧
        (∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
          (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
            cgpProjMap P.toLocalChartFamily P.zero
              (gafStageTags P.toLocalChartFamily P.zero 0) (sel x) = x) →
          ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
            hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 0 ∩
                ball x (sg * ρ (sel x) / Γ))
              ((AffineSubspace.mk' x (plane x) :
                  Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
                ball x (sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel x)))) ∧
        ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
          ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
          ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x →
          let Pq := (plane x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
            (cgpGlobalMap P.toLocalChartFamily P.zero) q)
          Function.Surjective Pq ∧
          (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
              (Pq v : BlockSpace _)‖ ≤ eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
          (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
            1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
          ∀ v, ‖Pq v‖ ≤ 3 * tcpGraphConst * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) := by
  obtain ⟨σ, hσ, hσ1, η₂, γ₀, ηc, θ, hη₂, hγ₀, hηc, hθ, hθ1, hrow⟩ :=
    tcp06_row hΓ hΓ1 hsg hsgΓ hsgC heg heg1 hegΓ hν hν1
  refine ⟨σ, hσ, hσ1, η₂, γ₀, ηc, θ, hη₂, hγ₀, hηc, hθ, hθ1, fun Δ hΔ => ?_⟩
  obtain ⟨η₁, hη₁, h⟩ := hrow Δ hΔ
  refine ⟨η₁, hη₁, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
    h26 h27 h28 h29 h30 h31
  have hT := h P h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22
    h23 h24 h25 h26 h27 h28 h29 h30 h31
  refine hT.elim fun plane hp => ?_
  have hconv := fc27_first_of_tcp06_GAF4 P.toLocalChartFamily P.zero plane hsg.le hp.1 hp.2.1
  refine ⟨plane, hconv.1, hconv.2, fun x hx => ?_⟩
  rw [gafCloud_zero_GAF4] at hx
  exact hp.2.2 x hx

end DifferentialGeometry.Geometry.Collapse
