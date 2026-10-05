import DifferentialGeometry.Geometry.Fibration.ActualCloudPackets
import DifferentialGeometry.Geometry.Fibration.ActualActiveSupportPacket

/-!
# Consumers of the actual cloud data: (MCb) for every selection of preimages

* `fc27_edge_cloud_mcb`, `fc27_slim_cloud_mcb`: for ANY selection `select` of preimages over the
  enlarged projected image `S̃_j = π_j𝓔⁰(Ã_j)`, FC26's selected radius `r = Σρ ∘ select` satisfies
  the large-scale comparison (MCb) of CFS11/CFS14 (B:2437) at every scale `L'` with `L'Σ ≤ 1/5`.
* `actual_clouds_mcb_packets`: on the final family `LocalChartPackets` with FC07's parameter range
  `10⁶ΔΛ < 10⁻⁵`, the three actual clouds (FC04's exact radius on the first image, FC26's selected
  radius on the edge and slim projected images) satisfy (MCb) at CFS11's buffer `128b`, for
  `128bΣ ≤ 1/5` (TCP06's `Σ ≤ 1/(640b)`).
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

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a}

/-- From a scale ratio of the selected preimages to the (MCb) form of the selected radius. -/
theorem selected_radius_ratio_KA3 {sg ρx ρy : ℝ} (hsg : 0 ≤ sg)
    (h : (3 / 5 : ℝ) * ρx ≤ ρy ∧ ρy ≤ (5 / 3 : ℝ) * ρx) :
    sg * ρx / (5 / 3) ≤ sg * ρy ∧ sg * ρy ≤ (5 / 3) * (sg * ρx) := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · have := mul_le_mul_of_nonneg_left h1 hsg
    linarith
  · have := mul_le_mul_of_nonneg_left h2 hsg
    linarith

/-- (MCb) on the actual edge cloud `S̃₂` for ANY selection of preimages. -/
theorem fc27_edge_cloud_mcb
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (select : BlockSpace (fun _ : CGPTag L Z => ℝ²) → X)
    (hselect : ∀ x ∈ cgpProjMap L Z (cgpQ2Tags L Z) '' fc27EdgeSet L 8,
      cgpProjMap L Z (cgpQ2Tags L Z) (select x) = x)
    {sg L' : ℝ} (hsg : 0 ≤ sg) (hL' : 0 ≤ L') (hLsg : L' * sg ≤ 1 / 5) :
    ∀ x ∈ cgpProjMap L Z (cgpQ2Tags L Z) '' fc27EdgeSet L 8,
      ∀ y ∈ cgpProjMap L Z (cgpQ2Tags L Z) '' fc27EdgeSet L 8,
        dist y x ≤ L' * max (sg * ρ (select y)) (sg * ρ (select x)) →
        sg * ρ (select x) / (5 / 3) ≤ sg * ρ (select y) ∧
          sg * ρ (select y) ≤ (5 / 3) * (sg * ρ (select x)) := by
  intro x hx y hy hd
  have hx' := hselect x hx
  have hy' := hselect y hy
  refine selected_radius_ratio_KA3 hsg ((fc27_edge_cloud_scale L Z hΔ hΛ hsmall).2.2.2 sg L'
    hsg hL' hLsg (select x) (select y) (by rw [hx']; exact hx) (by rw [hy']; exact hy) ?_)
  rw [hx', hy']
  exact hd

/-- (MCb) on the actual slim cloud `S̃₃` for ANY selection of preimages. -/
theorem fc27_slim_cloud_mcb
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (select : BlockSpace (fun _ : CGPTag L Z => ℝ²) → X)
    (hselect : ∀ x ∈ cgpProjMap L Z (cgpQ3Tags L Z) '' fc27SlimSet L 8,
      cgpProjMap L Z (cgpQ3Tags L Z) (select x) = x)
    {sg L' : ℝ} (hsg : 0 ≤ sg) (hL' : 0 ≤ L') (hLsg : L' * sg ≤ 1 / 5) :
    ∀ x ∈ cgpProjMap L Z (cgpQ3Tags L Z) '' fc27SlimSet L 8,
      ∀ y ∈ cgpProjMap L Z (cgpQ3Tags L Z) '' fc27SlimSet L 8,
        dist y x ≤ L' * max (sg * ρ (select y)) (sg * ρ (select x)) →
        sg * ρ (select x) / (5 / 3) ≤ sg * ρ (select y) ∧
          sg * ρ (select y) ≤ (5 / 3) * (sg * ρ (select x)) := by
  intro x hx y hy hd
  have hx' := hselect x hx
  have hy' := hselect y hy
  refine selected_radius_ratio_KA3 hsg ((fc27_slim_cloud_scale L Z hΔ hΛ hsmall).2.2.2 sg L'
    hsg hL' hLsg (select x) (select y) (by rw [hx']; exact hx) (by rw [hy']; exact hy) ?_)
  rw [hx', hy']
  exact hd

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_KA3
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_KA3
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_KA3
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **The three actual clouds satisfy (MCb) at CFS11's buffer** on `LocalChartPackets` (FC07's
range `10⁶ΔΛ < 10⁻⁵`, `128bΣ ≤ 1/5`): FC04's exact radius on the image of `𝓔⁰`, and FC26's selected
radius `Σρ ∘ select` on `S̃₂` and `S̃₃` for any selections of preimages. -/
theorem actual_clouds_mcb_packets
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) {bb sg : ℝ} (hbb : 0 ≤ bb)
    (hsg : 0 ≤ sg) (hbsg : 128 * bb * sg ≤ 1 / 5)
    (sel₂ sel₃ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel₂ : ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) ''
        fc27EdgeSet P.toLocalChartFamily 8,
      cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) (sel₂ x) = x)
    (hsel₃ : ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) ''
        fc27SlimSet P.toLocalChartFamily 8,
      cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) (sel₃ x) = x) :
    (∀ x ∈ range (cgpGlobalMap P.toLocalChartFamily P.zero),
      ∀ y ∈ range (cgpGlobalMap P.toLocalChartFamily P.zero),
        dist y x ≤ 128 * bb * max (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg y)
          (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x) →
        scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x / (5 / 3) ≤
          scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg y ∧
        scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg y ≤
          (5 / 3) * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x) ∧
    (∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) ''
        fc27EdgeSet P.toLocalChartFamily 8,
      ∀ y ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) ''
        fc27EdgeSet P.toLocalChartFamily 8,
        dist y x ≤ 128 * bb * max (sg * ρ (sel₂ y)) (sg * ρ (sel₂ x)) →
        sg * ρ (sel₂ x) / (5 / 3) ≤ sg * ρ (sel₂ y) ∧
          sg * ρ (sel₂ y) ≤ (5 / 3) * (sg * ρ (sel₂ x))) ∧
    ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) ''
        fc27SlimSet P.toLocalChartFamily 8,
      ∀ y ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) ''
        fc27SlimSet P.toLocalChartFamily 8,
        dist y x ≤ 128 * bb * max (sg * ρ (sel₃ y)) (sg * ρ (sel₃ x)) →
        sg * ρ (sel₃ x) / (5 / 3) ≤ sg * ρ (sel₃ y) ∧
          sg * ρ (sel₃ y) ≤ (5 / 3) * (sg * ρ (sel₃ x)) := by
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  have hL : 0 ≤ 128 * bb := by positivity
  exact ⟨(fc04_first_cloud_scale P.toLocalChartFamily P.zero hsg hbsg).2.2,
    fc27_edge_cloud_mcb P.toLocalChartFamily P.zero hΔ hΛ hsmall sel₂ hsel₂ hsg hL hbsg,
    fc27_slim_cloud_mcb P.toLocalChartFamily P.zero hΔ hΛ hsmall sel₃ hsel₃ hsg hL hbsg⟩

end DifferentialGeometry.Geometry.Collapse
