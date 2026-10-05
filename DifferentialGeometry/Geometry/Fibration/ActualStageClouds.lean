import DifferentialGeometry.Geometry.Fibration.ActualCloudLargeCover
import DifferentialGeometry.Geometry.Fibration.ActualFullMarkerContributors
import DifferentialGeometry.Geometry.Fibration.ActualFirstGraphModel
import DifferentialGeometry.Geometry.Fibration.ActualEdgeGraphModel
import DifferentialGeometry.Geometry.Fibration.ActualSlimGraphModel

/-!
# The three actual stage clouds of GAF01/GAF02 and CFS14's hypotheses on them

Blueprint `master207B.tex`, FC27 (`found:fibration-projected-clouds`, B:1658), CFS14 / CFS15
(B:2628–2748) and GAF01–GAF02 (B:5704–5858). The three stages of GAF01 (index `st : Fin 3`:
`0` = first / circle cloud, `k = 2`; `1` = edge cloud, `k = 1`; `2` = slim cloud, `k = 1`) as
stage-indexed data on CGP01's actual `𝓔⁰ = cgpGlobalMap L Z`:

* `gafStageTags` (`Q₁ = H`, `Q₂`, `Q₃`), `gafStageCore` / `gafStageEnlargement` (FC04's `A₁ ⊆ Ã₁`,
  FC27's edge and slim cores and enlargements), `gafCloud` (`S_j = π_j𝓔⁰(A_j)`),
  `gafCloudEnlarged` (`S̃_j = π_j𝓔⁰(Ã_j)`), and `gafGraphConst` (the early graph constants
  `C = tcpGraphConst, egpGraphConst, sgpGraphBound` of TCP05 / EGP06 / SGP04 entering
  (TP) / (EP) / (CP)). The radius at stage `st` is FC26's selected radius `Σ ρ(sel x)` for a
  selection `sel` of preimages over `S̃_st` (at `st = 0` this is FC04's exact radius).
* `cfs14_stage_inputs_GAF2`: every hypothesis of CFS14 / CFS15 other than the (CS) tests on the
  actual stage cloud — `S ⊆ S̃`, `S` totally bounded, the radius bounded above and away from zero
  on `S`, and (MCb) on `S̃` at the buffer `128 ε⁻¹` for `0 < Σ`, `128 ε⁻¹ Σ ≤ 1/5` (CFS15's (MO)
  `Σ ≤ ε/640`), on `LocalChartPackets` with FC07's parameter range.
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

/-- The early graph constants `C` of the three actual graph producers (TCP05, EGP06, SGP04), the
constants of the cloud ranges (TP), (EP), (CP) and GAF01's `C_j`. -/
def gafGraphConst : Fin 3 → ℝ := ![tcpGraphConst, egpGraphConst, sgpGraphBound]

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

section Defs

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

/-- The tag sets of the three stage targets: `Q₁ = H` (all tags), `Q₂`, `Q₃`. -/
def gafStageTags : Fin 3 → Finset (CGPTag L Z) := ![Finset.univ, cgpQ2Tags L Z, cgpQ3Tags L Z]

/-- The original cores `A_j` of the three stages (threshold `7`). -/
def gafStageCore : Fin 3 → Set X := ![fc04Set L Z 7, fc27EdgeSet L 7, fc27SlimSet L 7]

/-- The original enlargements `Ã_j` of the three stages (threshold `8`). -/
def gafStageEnlargement : Fin 3 → Set X := ![fc04Set L Z 8, fc27EdgeSet L 8, fc27SlimSet L 8]

/-- The actual stage cloud `S_j = π_j𝓔⁰(A_j)`. -/
def gafCloud (st : Fin 3) : Set (BlockSpace (fun _ : CGPTag L Z => ℝ²)) :=
  cgpProjMap L Z (gafStageTags L Z st) '' gafStageCore L Z st

/-- The actual enlarged stage cloud `S̃_j = π_j𝓔⁰(Ã_j)`. -/
def gafCloudEnlarged (st : Fin 3) : Set (BlockSpace (fun _ : CGPTag L Z => ℝ²)) :=
  cgpProjMap L Z (gafStageTags L Z st) '' gafStageEnlargement L Z st

theorem gafCloud_subset_enlarged (hΔ : 0 ≤ Δ) (st : Fin 3) :
    gafCloud L Z st ⊆ gafCloudEnlarged L Z st := by
  refine image_mono ?_
  fin_cases st
  · exact fc04Set_mono L Z (by norm_num)
  · exact fc27EdgeSet_mono L hΔ (by norm_num)
  · exact fc27SlimSet_mono L hΔ (by norm_num)

end Defs

/-- (MCb) at stage `st` for the selected radius `Σρ ∘ sel`, any selection of preimages over the
enlarged stage cloud, any buffer `L' ≥ 0` with `L'Σ ≤ 1/5`. -/
theorem gafCloud_mcb_GAF2
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (st : Fin 3)
    (sel : BlockSpace (fun _ : CGPTag L Z => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged L Z st, cgpProjMap L Z (gafStageTags L Z st) (sel x) = x)
    {sg L' : ℝ} (hsg : 0 ≤ sg) (hL' : 0 ≤ L') (hLsg : L' * sg ≤ 1 / 5) :
    ∀ x ∈ gafCloudEnlarged L Z st, ∀ y ∈ gafCloudEnlarged L Z st,
      dist y x ≤ L' * max (sg * ρ (sel y)) (sg * ρ (sel x)) →
      sg * ρ (sel x) / (5 / 3) ≤ sg * ρ (sel y) ∧ sg * ρ (sel y) ≤ (5 / 3) * (sg * ρ (sel x)) := by
  fin_cases st
  · intro x hx y hy hd
    have huniv := cgpProjMap_univ_GAF L Z
    have hx' : cgpGlobalMap L Z (sel x) = x := by
      rw [← huniv]
      exact hsel x hx
    have hy' : cgpGlobalMap L Z (sel y) = y := by
      rw [← huniv]
      exact hsel y hy
    obtain ⟨hr, -, hmc⟩ := fc04_first_cloud_scale L Z hsg hLsg
    have hrx : scaleRadius (cgpScaleTag L Z) sg x = sg * ρ (sel x) := by
      rw [← hr, hx']
    have hry : scaleRadius (cgpScaleTag L Z) sg y = sg * ρ (sel y) := by
      rw [← hr, hy']
    have h := hmc x ⟨sel x, hx'⟩ y ⟨sel y, hy'⟩ (by rw [hrx, hry]; exact hd)
    rwa [hrx, hry] at h
  · exact fc27_edge_cloud_mcb L Z hΔ hΛ hsmall sel hsel hsg hL' hLsg
  · exact fc27_slim_cloud_mcb L Z hΔ hΛ hsmall sel hsel hsg hL' hLsg

variable {Lmax τ γ : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricNSC_GAF2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedNSC_GAF2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricCSC_GAF2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **CFS14's hypotheses on the actual stage clouds** (all but the (CS) tests): on
`LocalChartPackets` with FC07's parameter range, at every stage `st`, for every selection `sel` of
preimages over `S̃_st`, accuracy `ε > 0` and `0 < Σ` with CFS15's (MO) `128 ε⁻¹ Σ ≤ 1/5`:
`S ⊆ S̃`, `S` totally bounded, `Σρ ∘ sel` bounded above and away from zero on `S`, and (MCb) on `S̃`
at the buffer `128 ε⁻¹` with `B = 5/3`. -/
theorem cfs14_stage_inputs_GAF2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (he : e ≤ 1 / 8)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (st : Fin 3)
    (sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st)
        (sel x) = x)
    {εa sg : ℝ} (hεa : 0 < εa) (hsg : 0 < sg) (hmo : 128 * εa⁻¹ * sg ≤ 1 / 5) :
    gafCloud P.toLocalChartFamily P.zero st ⊆ gafCloudEnlarged P.toLocalChartFamily P.zero st ∧
      TotallyBounded (gafCloud P.toLocalChartFamily P.zero st) ∧
      (∃ rmin R : ℝ, 0 < rmin ∧ (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
          rmin ≤ sg * ρ (sel x)) ∧
        (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, sg * ρ (sel x) ≤ R)) ∧
      ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
        ∀ y ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
        dist y x ≤ 128 * εa⁻¹ * max (sg * ρ (sel y)) (sg * ρ (sel x)) →
        sg * ρ (sel x) / (5 / 3) ≤ sg * ρ (sel y) ∧
          sg * ρ (sel y) ≤ (5 / 3) * (sg * ρ (sel x)) := by
  have hΔ0 : 0 < Δ := by linarith
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  have hΔΛ : 100 * Δ * Λ ≤ 1 / 100 := by nlinarith
  obtain ⟨-, hc⟩ := continuous_cgpProjMap_packets P hΛ hΔ0 hμ hτ hΔΛ he
    (gafStageTags P.toLocalChartFamily P.zero st)
  obtain ⟨m, M, hm, hmM⟩ := exists_pos_bounds_KA3 ρ P.contMDiff_scale.continuous hρ
  have hL' : 0 ≤ 128 * εa⁻¹ := by positivity
  refine ⟨gafCloud_subset_enlarged P.toLocalChartFamily P.zero hΔ0.le st,
    (isCompact_range hc).totallyBounded.subset (image_subset_range _ _),
    ⟨sg * m, sg * M, mul_pos hsg hm, fun x _ => mul_le_mul_of_nonneg_left (hmM _).1 hsg.le,
      fun x _ => mul_le_mul_of_nonneg_left (hmM _).2 hsg.le⟩,
    gafCloud_mcb_GAF2 P.toLocalChartFamily P.zero hΔ hΛ hsmall st sel hsel hsg.le hL' hmo⟩

end DifferentialGeometry.Geometry.Collapse
