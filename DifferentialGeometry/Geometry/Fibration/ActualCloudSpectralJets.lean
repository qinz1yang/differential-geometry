import DifferentialGeometry.Geometry.Fibration.ActualCloudLargeCover
import DifferentialGeometry.Geometry.Metric.LargeCloudSpectralJets

/-!
# CFS12 on FC07's first cloud

Blueprint `master207B.tex`, CFS12 (`lem:fibration-cloud-large-spectral`, B:2513–2535) with the
standing hypotheses of CFS11 (B:2425–2449), bound to the actual first cloud `S₁ = 𝓔⁰(A₁)`,
`S̃₁ = 𝓔⁰(Ã₁)` of `ActualCloudPackets` with FC04's exact radius `r₁ = Σ x_ρ` (`k = 2`,
`B = 5/3`), in the same way as `cfs11_first_cloud`: boundedness, the radius bounds and (MCb) at
the buffer `128b` are discharged from the compact carrier, CGP01's continuity and FC04
(`fc04_first_cloud_scale`).

* `first_cloud_spectral_inputs_GAFS2`: the standing inputs (`S₁ ⊆ S̃₁`, total boundedness, radius
  bounds, (MCb) with `B = 5/3` at any buffer `L'` with `L'Σ ≤ 1/5`) on `LocalChartPackets`.
* `cfs12_first_cloud_GAFS2`: constants `C_m` depending only on `b` (and `k = 2`, `B = 5/3`) such
  that on every `LocalChartPackets` with two-dimensional planes and the (CS) tests on `S₁` at
  quality `δ` with `δ((80B + 31)b + 2) < 1`, CFS11's greedy selection carries CFS12's
  normalized cutoff weights `w_i = φ_i / Σ_j φ_j` (`φ_i = ballCutoff` at `40br_i`) with
  `Σ_i ‖D^j w_i‖ ≤ C_m / r^j` on every reference ball `B(x, 8br_x)` (`x ∈ S₁`) and
  `B(x_i, 30br_i)` (selected `x_i`) (kernel `exists_uniform_large_cloud_spectral_projection_jets`).
  The kernel's projector clauses (rank and (LS) for `Q`) are not restated here: on `BlockSpace`
  their instance unification exceeds the heartbeat budget; they are not needed downstream (EDP01
  uses the weights only).

This selection is CFS12's own; the weights of the stage-one smoothing of GAF02 (the selection of
CFS15 inside GAF01) are treated in `ActualStageMean.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricNSJ_GAFS2 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedNSJ_GAFS2 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricCSJ_GAFS2 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

section Inputs

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- CFS11/CFS12's standing inputs on FC07's first cloud (`LocalChartPackets`): `S₁ ⊆ S̃₁`, `S₁`
totally bounded, FC04's radius bounded above and away from zero on `S₁`, and (MCb) with `B = 5/3` at
the buffer `L'` (`L'Σ ≤ 1/5`) on `S₁`. -/
theorem first_cloud_spectral_inputs_GAFS2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (he : e ≤ 1 / 8) {L' sg : ℝ} (hsg : 0 < sg)
    (hLsg : L' * sg ≤ 1 / 5) :
    cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7 ⊆
        cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 8 ∧
      TotallyBounded
        (cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7) ∧
      (∃ rmin R : ℝ, 0 < rmin ∧
        (∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
          rmin ≤ scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x) ∧
        ∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
          scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x ≤ R) ∧
      ∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
        ∀ y ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
        dist y x ≤ L' * max (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg y)
          (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x) →
        scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x / (5 / 3) ≤
            scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg y ∧
          scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg y ≤
            (5 / 3) * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x := by
  obtain ⟨hc, -⟩ := continuous_cgpProjMap_packets P hΛ hΔ hμ hτ hΔΛ he ∅
  obtain ⟨m, M, hm, hmM⟩ := exists_pos_bounds_KA3 ρ P.contMDiff_scale.continuous hρ
  obtain ⟨hr, -, hmc⟩ := fc04_first_cloud_scale P.toLocalChartFamily P.zero hsg.le hLsg
  have hsub : cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7 ⊆
      range (cgpGlobalMap P.toLocalChartFamily P.zero) := image_subset_range _ _
  refine ⟨image_mono (fc04Set_mono _ _ (by norm_num)),
    (isCompact_range hc).totallyBounded.subset hsub, ⟨sg * m, sg * M, mul_pos hsg hm, ?_, ?_⟩,
    fun x hx y hy hd => hmc x (hsub hx) y (hsub hy) hd⟩
  · rintro _ ⟨p, -, rfl⟩
    rw [hr]
    exact mul_le_mul_of_nonneg_left (hmM p).1 hsg.le
  · rintro _ ⟨p, -, rfl⟩
    rw [hr]
    exact mul_le_mul_of_nonneg_left (hmM p).2 hsg.le

end Inputs

/-- **CFS12's weights on FC07's first cloud** (`LocalChartPackets`): constants `C_m` depending only
on `b` such that for `S₁ = 𝓔⁰(A₁) ⊆ S̃₁ = 𝓔⁰(Ã₁)`, FC04's radius `r₁ = Σ x_ρ` (`0 < Σ`,
`128bΣ ≤ 1/5`), two-dimensional planes and the (CS) tests on `S₁` at quality `δ` with
`δ((80·5/3 + 31)b + 2) < 1`: CFS11's selection and the weight bounds `Σ_i ‖D^j w_i‖ ≤ C_m / r^j`
on every reference ball. -/
theorem cfs12_first_cloud_GAFS2 (bb : ℝ) (hbb : 1 ≤ bb) :
    ∃ C : ℕ → ℝ≥0,
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ)
        (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
          T V),
        0 ≤ Λ → 0 < Δ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 100 * Δ * Λ ≤ 1 / 100 → e ≤ 1 / 8 →
        ∀ sg δc : ℝ, 0 < sg → 128 * bb * sg ≤ 1 / 5 →
        ∀ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
          Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
          Module.finrank ℝ (plane x) = 2) →
        0 < δc → δc * ((80 * (5 / 3) + 31) * bb + 2) < 1 →
        (∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
          hausdorffEDist (cgpGlobalMap P.toLocalChartFamily P.zero ''
              fc04Set P.toLocalChartFamily P.zero 8 ∩
              ball x (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x / δc))
            ((AffineSubspace.mk' x (plane x) :
                Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
              ball x (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x / δc)) ≤
            ENNReal.ofReal (δc * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x)) →
        let S₁ := cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7
        let r := scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg
        ∃ (I : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) (hI : I.Finite),
          I ⊆ S₁ ∧ I.PairwiseDisjoint (fun i => ball i (r i)) ∧
          (∀ x ∈ S₁, ∃ i ∈ I, r x ≤ 2 * r i ∧ dist x i < 3 * r i) ∧
          ((⋃ x ∈ S₁, ball x (8 * bb * r x)) ⊆ ⋃ i ∈ I, ball i (20 * bb * r i)) ∧
          let w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ :=
            fun i y => ballCutoff i (40 * bb * r i) (2 * (40 * bb * r i)) y /
              (∑ a ∈ hI.toFinset, ballCutoff a (40 * bb * r a) (2 * (40 * bb * r a)) y)
          (∀ m, ∀ x ∈ S₁, ∀ j ≤ m, ∀ z ∈ ball x (8 * bb * r x),
            (∑ i ∈ hI.toFinset, ‖iteratedFDeriv ℝ j (w i) z‖) ≤ (C m : ℝ) / (r x) ^ j) ∧
          ∀ m, ∀ i ∈ I, ∀ j ≤ m, ∀ z ∈ ball i (30 * bb * r i),
            (∑ a ∈ hI.toFinset, ‖iteratedFDeriv ℝ j (w a) z‖) ≤ (C m : ℝ) / (r i) ^ j := by
  obtain ⟨C, hC⟩ := exists_uniform_large_cloud_spectral_projection_jets.{0} 2 bb (5 / 3) hbb
    (by norm_num)
  refine ⟨C, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V P hΛ hΔ
    hμ hτ hΔΛ he sg δc hsg hbsg plane hdim hδ hδc hcloud
  have hin := first_cloud_spectral_inputs_GAFS2 P hΛ hΔ hμ hτ hΔΛ he hsg hbsg
  have hR := Classical.choose_spec (Classical.choose_spec hin.2.2.1)
  have h := hC _ _ _ hin.1 hin.2.1 _ plane hdim _ _ δc hR.1 hR.2.1 hR.2.2 hδ hδc hin.2.2.2 hcloud
  obtain ⟨I, hI, h1, h2, h3, h4, h5⟩ := h
  exact ⟨I, hI, h1, h2, h3, h4, h5.1, h5.2.1⟩

end DifferentialGeometry.Geometry.Collapse
