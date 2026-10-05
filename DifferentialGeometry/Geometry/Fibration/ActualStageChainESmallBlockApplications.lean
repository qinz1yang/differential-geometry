import DifferentialGeometry.Geometry.Fibration.ActualStageChainESmallBlock
import DifferentialGeometry.Geometry.Fibration.ActualStageChainPatches

/-!
# Consumers of the whole-small-block CGP04 on `Gaf02ChainE`

* `Gaf02ChainE.cgp04_vector_BASP`: the VECTOR part `u_a` of a small retained block vanishes on
  `Z ∩ B(y, 20Ξ⁻¹r_y)` (beyond the marker form `Gaf02Chain.cgp04_BAS`).
* `Gaf02ChainE.cgp04_marker_of_block_BASP`: the marker form recovered from the whole-block form.
* `Gaf02ChainE.slimPatch_selected_scale_BASP`, `circlePatch_selected_scale_BASP`,
  `edgePatch_selected_scale_BASP`: every point of a marked patch `V_j⁰` lies in a selected ball
  `B(y, 20Ξ⁻¹r_y)` with `ρ(sel y) ≤ 16R_j` (CGP04's consequence on the patches of the chain).
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

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

namespace Gaf02ChainE

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **The vector part of a small block vanishes** (whole-small-block CGP04). -/
theorem cgp04_vector_BASP (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) {st : Fin 3}
    (O : Cfs15StageOutput (gafStageDim st) Kj (Ξ st) (cw st) (gafCloud P.toLocalChartFamily P.zero st)
      (gafCloudEnlarged P.toLocalChartFamily P.zero st) (fun x => S st * ρ (C.toChain.sel st x))
      (C.toChain.plane st))
    {a : CGPMarkerIndex P.toLocalChartFamily}
    (ha : cgpMarkerTag P.toLocalChartFamily P.zero a ∈ gafStageTags P.toLocalChartFamily P.zero st)
    {y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)} (hy : y ∈ O.I)
    (hry : ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ (C.toChain.sel st y) / 16)
    {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)} (hw : w ∈ O.Z)
    (hwy : w ∈ ball y (20 * (Ξ st)⁻¹ * (S st * ρ (C.toChain.sel st y)))) :
    blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (cgpMarkerTag P.toLocalChartFamily P.zero a) w = 0 := by
  have h := C.cgp04_block_BASP O ha hy hry hw hwy
  rw [blockProjCLM_apply_PLN] at h
  rw [blockVectorCLM_apply, h]
  rfl

/-- **The marker form, recovered** (agrees with `Gaf02Chain.cgp04_BAS`). -/
theorem cgp04_marker_of_block_BASP (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) {st : Fin 3}
    (O : Cfs15StageOutput (gafStageDim st) Kj (Ξ st) (cw st) (gafCloud P.toLocalChartFamily P.zero st)
      (gafCloudEnlarged P.toLocalChartFamily P.zero st) (fun x => S st * ρ (C.toChain.sel st x))
      (C.toChain.plane st))
    {a : CGPMarkerIndex P.toLocalChartFamily}
    (ha : cgpMarkerTag P.toLocalChartFamily P.zero a ∈ gafStageTags P.toLocalChartFamily P.zero st)
    {y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)} (hy : y ∈ O.I)
    (hry : ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ (C.toChain.sel st y) / 16)
    {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)} (hw : w ∈ O.Z)
    (hwy : w ∈ ball y (20 * (Ξ st)⁻¹ * (S st * ρ (C.toChain.sel st y)))) :
    blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (cgpMarkerTag P.toLocalChartFamily P.zero a) w = 0 := by
  have h := C.cgp04_block_BASP O ha hy hry hw hwy
  rw [blockProjCLM_apply_PLN] at h
  rw [blockMarkerCLM_apply, h]
  rfl

/-- A positive marker gives a nonzero whole block. -/
theorem blockProj_ne_zero_of_marker_pos_BASP {t : CGPTag P.toLocalChartFamily P.zero}
    {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hv : 0 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) t w) :
    blockProjCLM_PLN (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) t w ≠ 0 := by
  intro h
  rw [blockProjCLM_apply_PLN] at h
  rw [blockMarkerCLM_apply, h] at hv
  exact lt_irrefl _ hv

/-- **Slim patch points sit at comparable selected centres** (CGP04 on `Z₃`): every
`w ∈ V_j⁰` (slim) lies in a selected ball `B(y, 20Ξ₃⁻¹r_y)`, `y ∈ S₃`, with `ρ(sel₃ y) ≤ 16R_j`. -/
theorem slimPatch_selected_scale_BASP (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (j : P.slim.finite_centres.toFinset)
    {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hw : w ∈ C.toChain.slimPatch_BAS j) :
    ∃ y ∈ gafCloud P.toLocalChartFamily P.zero 2,
      w ∈ ball y (20 * (Ξ 2)⁻¹ * (S 2 * ρ (C.toChain.sel 2 y))) ∧
      ρ (C.toChain.sel 2 y) ≤ 16 * ρ j.1 := by
  have hρj := hρ j.1
  obtain ⟨y, hy, hwy, himp⟩ := C.cgp04_slim_block_BASP j hw.1
  refine ⟨y, hy, hwy, himp (blockProj_ne_zero_of_marker_pos_BASP ?_)⟩
  have h := hw.2.1
  change 9 / 10 * ρ j.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
    (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl j))) w at h
  linarith

/-- **Circle patch points sit at comparable selected centres** (CGP04 on `Z₁`). -/
theorem circlePatch_selected_scale_BASP (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (j : P.toLocalChartFamily.circle.finite_centres.toFinset)
    {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hw : w ∈ C.toChain.circlePatch_BAS j) :
    ∃ y ∈ gafCloud P.toLocalChartFamily P.zero 0,
      w ∈ ball y (20 * (Ξ 0)⁻¹ * (S 0 * ρ (C.toChain.sel 0 y))) ∧
      ρ (C.toChain.sel 0 y) ≤ 16 * ρ j.1 := by
  have hρj := hρ j.1
  obtain ⟨y, hy, hwy, himp⟩ := C.cgp04_circle_block_BASP j hw.1
  refine ⟨y, hy, hwy, himp (blockProj_ne_zero_of_marker_pos_BASP ?_)⟩
  have h := hw.2.1
  change 9 / 10 * ρ j.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
    (cgpMarkerTag P.toLocalChartFamily P.zero (.inl j)) w at h
  linarith

/-- **Edge patch points sit at comparable selected centres** (CGP04 on `Z₂`). -/
theorem edgePatch_selected_scale_BASP (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (j : P.toLocalChartFamily.edge.finite_centres.toFinset)
    {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hw : w ∈ C.toChain.edgePatch_BAS j) :
    ∃ y ∈ gafCloud P.toLocalChartFamily P.zero 1,
      w ∈ ball y (20 * (Ξ 1)⁻¹ * (S 1 * ρ (C.toChain.sel 1 y))) ∧
      ρ (C.toChain.sel 1 y) ≤ 16 * ρ j.1 := by
  have hρj := hρ j.1
  obtain ⟨y, hy, hwy, himp⟩ := C.cgp04_edge_block_BASP j hw.1
  refine ⟨y, hy, hwy, himp (blockProj_ne_zero_of_marker_pos_BASP ?_)⟩
  have h := hw.2.1
  change 9 / 10 * ρ j.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
    (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr j))) w at h
  linarith

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
