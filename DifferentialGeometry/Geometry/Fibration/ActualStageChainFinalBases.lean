import DifferentialGeometry.Geometry.Fibration.ActualStageChainChartCircle
import DifferentialGeometry.Geometry.Fibration.ActualStageChainChartEdge
import DifferentialGeometry.Geometry.Fibration.ActualStageChainLater
import DifferentialGeometry.Geometry.Fibration.ActualStageChainChartSlim


/-!
# GAF02 BASES, sixth step: the final bases `W_st` as embedded submanifolds, no merging, (RF)

Blueprint `master207B.tex`, CGP08 (B:4259–4316) and GAF07's open bases (B:6049–6062); external
draft 59 §4 sixth–seventh steps (D59-5); review 66 §5.4 step 6 (D66-7); review 71 D71-13. Indexed
by ONE chain `C : Gaf02Chain P.toLocalChartPackets …` and its rough data `R` (slim charts:
lane C14-BASES-P's `cgp07_slim_BAS`).

Representation of "embedded submanifold" (chart form): for every chart `j` of the stage, a map
`ψ_j` smooth on the coordinate ball, onto the OPEN piece `W_st ∩ {v_j > .9R_j, |u_j| < 5.5ℓ_jR_j}`,
whose inverse on the piece is the restriction of the continuous LINEAR map `κ_j = R_j⁻¹u_j`
(`κ_j ∘ ψ_j = id`, `ψ_j ∘ κ_j = id` there); the pieces cover `W_st`.

* Generic: `embedded_piece_of_chart_BAS`, `open_piece_of_chart_BAS`.
* No merging: `Gaf02Chain.theta_injOn_circle_BAS`, `theta_injOn_edge_BAS`, `theta_injOn_slim_BAS`,
  `theta_injOn_BAS`.
* `W₁`: `Gaf02Chain.finalBase_circle_chart_BAS`, `finalBase_circle_cover_BAS`; `W₂`:
  `finalBase_edge_chart_BAS`, `finalBase_edge_cover_BAS`; `W₃`: `finalBase_inter_slim_BAS`,
  `finalBase_slim_chart_BAS`, `finalBase_slim_cover_BAS`.
* GAF07's open bases `B₁ = circleBase_BAS`, `B₃ = slimBase_BAS` and their charts
  `circleBase_chart_BAS`, `slimBase_chart_BAS` (open pieces of the `W` charts).
* (RF) on `D_st = carrier_BAS st = B⁶_st ∩ f_st⁻¹(V_st⁰)`: `Gaf02Chain.rf_BAS` (restricted only).
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

section Generic

variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- **A transported patch is a smoothly embedded piece of the final base** (generic CGP08 step):
for a patch `V = V_i⁰` with CGP07's chart inverse `φ` of `κ = R⁻¹u` on `B(0, 5.5ℓ)`, a later
transport `Θ` smooth at every point of `V` and retaining `u`, and a final base `W` with
`W ∩ {marked i} = Θ(V)`: the map `ψ = Θ ∘ φ` is smooth on the ball, lands in `W ∩ {marked i}`,
`κ ∘ ψ = id` on the ball, and every `y ∈ W ∩ {marked i}` has `κ y` in the ball and `ψ(κ y) = y`
(so `ψ` is a homeomorphism of the ball onto the open piece `W ∩ {marked i}`, with the CONTINUOUS
LINEAR left inverse `κ`: an embedded chart). -/
theorem embedded_piece_of_chart_BAS (Z : Set H) (u : H →L[ℝ] E) (v : H →L[ℝ] ℝ) (R ℓ : ℝ)
    (Θ : H → H) (φ : E → H) (W : Set H) (hφ : ContDiffOn ℝ ∞ φ (ball 0 (11 / 2 * ℓ)))
    (hbij : BijOn (R⁻¹ • u) (markedPatch_BPRE Z u v R ℓ) (ball 0 (11 / 2 * ℓ)))
    (hinv : InvOn φ (R⁻¹ • u) (markedPatch_BPRE Z u v R ℓ) (ball 0 (11 / 2 * ℓ)))
    (hmaps : MapsTo φ (ball 0 (11 / 2 * ℓ)) (markedPatch_BPRE Z u v R ℓ))
    (hΘ : ∀ w ∈ markedPatch_BPRE Z u v R ℓ, ContDiffAt ℝ ∞ Θ w)
    (hret : ∀ w ∈ markedPatch_BPRE Z u v R ℓ, u (Θ w) = u w)
    (hW : W ∩ markedCondition_BPRE u v R ℓ = Θ '' markedPatch_BPRE Z u v R ℓ) :
    ContDiffOn ℝ ∞ (Θ ∘ φ) (ball 0 (11 / 2 * ℓ)) ∧
      (∀ b ∈ ball (0 : E) (11 / 2 * ℓ),
        Θ (φ b) ∈ W ∩ markedCondition_BPRE u v R ℓ ∧ (R⁻¹ • u) (Θ (φ b)) = b) ∧
      ∀ y ∈ W ∩ markedCondition_BPRE u v R ℓ,
        (R⁻¹ • u) y ∈ ball (0 : E) (11 / 2 * ℓ) ∧ Θ (φ ((R⁻¹ • u) y)) = y := by
  obtain ⟨hsm, hpar⟩ := theta_patch_param_BPRE Z u v R ℓ Θ φ hφ hinv hmaps hΘ hret
  refine ⟨hsm, fun b hb => ⟨hW ▸ (hpar b hb).1, (hpar b hb).2⟩, fun y hy => ?_⟩
  rw [hW] at hy
  have h := theta_inverse_on_patch_BPRE Z u v R ℓ Θ φ hinv hret y hy
  refine ⟨?_, h.2⟩
  obtain ⟨w, hw, rfl⟩ := hy
  have hκ : (R⁻¹ • u) (Θ w) = (R⁻¹ • u) w := by
    rw [clm_smul_apply_BPRE, clm_smul_apply_BPRE, hret w hw]
  rw [hκ]
  exact hbij.mapsTo hw

/-- **Open pieces of an embedded piece** (the manifold structure of `B = W ∩ R` for an open `R`):
`W ∩ {marked i} ∩ R` is the `ψ`-image of the OPEN set `B(0, 5.5ℓ) ∩ ψ⁻¹(R)`. -/
theorem open_piece_of_chart_BAS (u : H →L[ℝ] E) (v : H →L[ℝ] ℝ) (R ℓ : ℝ) (ψ : E → H)
    (W Rset : Set H) (hRset : IsOpen Rset) (hψ : ContinuousOn ψ (ball 0 (11 / 2 * ℓ)))
    (hin : ∀ b ∈ ball (0 : E) (11 / 2 * ℓ), ψ b ∈ W ∩ markedCondition_BPRE u v R ℓ)
    (hout : ∀ y ∈ W ∩ markedCondition_BPRE u v R ℓ,
      (R⁻¹ • u) y ∈ ball (0 : E) (11 / 2 * ℓ) ∧ ψ ((R⁻¹ • u) y) = y) :
    IsOpen (ball (0 : E) (11 / 2 * ℓ) ∩ ψ ⁻¹' Rset) ∧
      W ∩ markedCondition_BPRE u v R ℓ ∩ Rset = ψ '' (ball (0 : E) (11 / 2 * ℓ) ∩ ψ ⁻¹' Rset) := by
  refine ⟨hψ.isOpen_inter_preimage isOpen_ball hRset, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hyR⟩
    obtain ⟨hb, hψy⟩ := hout y hy
    exact ⟨_, ⟨hb, by rw [mem_preimage, hψy]; exact hyR⟩, hψy⟩
  · rintro ⟨b, ⟨hb, hbR⟩, rfl⟩
    exact ⟨hin b hb, hbR⟩

end Generic

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

namespace Gaf02Chain

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- `Θ₁` is smooth at every point of the circle patch `V_j⁰` (threshold-6 exhaustion + the
image-neighbourhood smoothness at `f₁ p`). -/
theorem theta_contDiffAt_circlePatch_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    ∀ w ∈ C.circlePatch_BAS j, ContDiffAt ℝ ∞ (C.Θ_BAS 0) w := fun w hw =>
  Exists.elim ((C.cgp07_circle_BAS R j).2.1 w hw) fun p hp => hp.2 ▸ C.contDiffAt_theta_BAS 0 p

/-- **No merging, circle stage** (CGP08): `Θ₁` is injective on the whole marked base
`V₁⁰ = ⋃_j V_j⁰`. -/
theorem theta_injOn_circle_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) : InjOn (C.Θ_BAS 0) (C.markedBase_BAS 0) :=
  injOn_theta_BPRE (C.slot 0).zeroSet (gafCircleVector P.toLocalChartPackets)
    (gafCircleMarker P.toLocalChartPackets) (fun k => ρ k.1) (fun _ => 1) (C.Θ_BAS 0)
    (fun k w _ => C.theta_retains_circle_BAS k w) fun k w₁ h₁ w₂ h₂ h12 =>
      (C.cgp07_circle_BAS R k).1.injOn h₁ h₂ (by
        rw [clm_smul_apply_BPRE, clm_smul_apply_BPRE, h12])

/-- **`W₁` is a smoothly embedded surface, chart by chart** (CGP08): for every circle chart `j`,
`ψ_j = Θ₁ ∘ φ_j` is smooth on `B(0, 5.5)`, maps it onto the open piece
`W₁ ∩ {v_j > .9R_j, ‖u_j‖ < 5.5R_j}`, with the continuous LINEAR left inverse `κ_j = R_j⁻¹u_j`
(`κ_j ∘ ψ_j = id` on the ball, `ψ_j ∘ κ_j = id` on the piece). -/
theorem finalBase_circle_chart_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    ∃ ψ : ℝ² → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
      ContDiffOn ℝ ∞ ψ (ball 0 (11 / 2 * 1)) ∧
      (∀ b ∈ ball (0 : ℝ²) (11 / 2 * 1),
        ψ b ∈ C.finalBase_BAS 0 ∩ markedCondition_BPRE (gafCircleVector P.toLocalChartPackets j)
          (gafCircleMarker P.toLocalChartPackets j) (ρ j.1) 1 ∧
        ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) (ψ b) = b) ∧
      ∀ y ∈ C.finalBase_BAS 0 ∩ markedCondition_BPRE (gafCircleVector P.toLocalChartPackets j)
          (gafCircleMarker P.toLocalChartPackets j) (ρ j.1) 1,
        ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) y ∈ ball (0 : ℝ²) (11 / 2 * 1) ∧
        ψ (((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) y) = y := by
  have h07 := C.cgp07_circle_BAS R j
  obtain ⟨φ, hφ, hinv, hmaps, -⟩ := h07.2.2
  exact ⟨_, embedded_piece_of_chart_BAS (C.slot 0).zeroSet _ _ (ρ j.1) 1 (C.Θ_BAS 0) φ
    (C.finalBase_BAS 0) hφ h07.1 hinv hmaps (C.theta_contDiffAt_circlePatch_BAS R j)
    (fun w _ => (C.theta_retains_circle_BAS j w).1) (C.finalBase_inter_circle_BAS j)⟩

/-- **The marked pieces cover `W₁`**: every point of `W₁` satisfies the marked condition of some
circle chart. -/
theorem finalBase_circle_cover_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) :
    C.finalBase_BAS 0 ⊆ ⋃ j, markedCondition_BPRE (gafCircleVector P.toLocalChartPackets j)
      (gafCircleMarker P.toLocalChartPackets j) (ρ j.1) 1 := by
  rintro y ⟨w, hw, rfl⟩
  obtain ⟨j, hj⟩ := mem_iUnion.mp hw
  refine mem_iUnion.mpr ⟨j, ?_, ?_⟩
  · rw [(C.theta_retains_circle_BAS j w).2]
    exact hj.2.1
  · rw [(C.theta_retains_circle_BAS j w).1]
    exact hj.2.2

/-- GAF07's open circle base `B₁ = ⋃_j {w ∈ W₁ | v_j(w) > .9R_j, ‖u_j(w)‖ < 4 v_j(w)}`. -/
def circleBase_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) :
    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :=
  C.finalBase_BAS 0 ∩ ⋃ j : P.toLocalChartFamily.circle.finite_centres.toFinset,
    {w | 9 / 10 * ρ j.1 < gafCircleMarker P.toLocalChartPackets j w ∧
      ‖gafCircleVector P.toLocalChartPackets j w‖ < 4 * 1 * gafCircleMarker P.toLocalChartPackets j w}

/-- **`B₁` is an open piece of `W₁`, chart by chart** (GAF07's base as a manifold): in the chart
`ψ_j` of `finalBase_circle_chart_BAS`, `B₁ ∩ {marked j}` is the image of an OPEN subset of
`B(0, 5.5)`. -/
theorem circleBase_chart_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    ∃ ψ : ℝ² → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
      ContDiffOn ℝ ∞ ψ (ball 0 (11 / 2 * 1)) ∧
      (∀ b ∈ ball (0 : ℝ²) (11 / 2 * 1),
        ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) (ψ b) = b) ∧
      IsOpen (ball (0 : ℝ²) (11 / 2 * 1) ∩ ψ ⁻¹' (⋃ k : P.toLocalChartFamily.circle.finite_centres.toFinset,
        {w | 9 / 10 * ρ k.1 < gafCircleMarker P.toLocalChartPackets k w ∧
          ‖gafCircleVector P.toLocalChartPackets k w‖ <
            4 * 1 * gafCircleMarker P.toLocalChartPackets k w})) ∧
      C.circleBase_BAS ∩ markedCondition_BPRE (gafCircleVector P.toLocalChartPackets j)
          (gafCircleMarker P.toLocalChartPackets j) (ρ j.1) 1 =
        ψ '' (ball (0 : ℝ²) (11 / 2 * 1) ∩ ψ ⁻¹' (⋃ k : P.toLocalChartFamily.circle.finite_centres.toFinset,
          {w | 9 / 10 * ρ k.1 < gafCircleMarker P.toLocalChartPackets k w ∧
            ‖gafCircleVector P.toLocalChartPackets k w‖ <
              4 * 1 * gafCircleMarker P.toLocalChartPackets k w})) := by
  obtain ⟨ψ, hψ, hin, hout⟩ := C.finalBase_circle_chart_BAS R j
  have hopen : IsOpen (⋃ k : P.toLocalChartFamily.circle.finite_centres.toFinset,
      {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) |
        9 / 10 * ρ k.1 < gafCircleMarker P.toLocalChartPackets k w ∧
          ‖gafCircleVector P.toLocalChartPackets k w‖ <
            4 * 1 * gafCircleMarker P.toLocalChartPackets k w}) :=
    isOpen_iUnion fun k => (isOpen_lt continuous_const
      (gafCircleMarker P.toLocalChartPackets k).continuous).inter
        (isOpen_lt (gafCircleVector P.toLocalChartPackets k).continuous.norm
          (continuous_const.mul (gafCircleMarker P.toLocalChartPackets k).continuous))
  obtain ⟨h1, h2⟩ := open_piece_of_chart_BAS _ _ (ρ j.1) 1 ψ (C.finalBase_BAS 0) _ hopen
    hψ.continuousOn (fun b hb => (hin b hb).1) hout
  refine ⟨ψ, hψ, fun b hb => (hin b hb).2, h1, ?_⟩
  rw [← h2, circleBase_BAS]
  ext y
  simp only [mem_inter_iff]
  tauto

/-- `Θ₂` is smooth at every point of the edge patch `V_j⁰`. -/
theorem theta_contDiffAt_edgePatch_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.edge.finite_centres.toFinset) :
    ∀ w ∈ C.edgePatch_BAS j, ContDiffAt ℝ ∞ (C.Θ_BAS 1) w := fun w hw =>
  Exists.elim ((C.cgp07_edge_BAS R j).2.1 w hw) fun p hp => hp.2 ▸ C.contDiffAt_theta_BAS 1 p

/-- `Θ₂` retains the edge axis coordinate and marker of every chart. -/
theorem theta_retains_edgeAxis_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (j : P.edge.finite_centres.toFinset)
    (w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :
    (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) (C.Θ_BAS 1 w) = (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) w ∧
      gafEdgeMarker P.toLocalChartFamily P.zero j (C.Θ_BAS 1 w) =
        gafEdgeMarker P.toLocalChartFamily P.zero j w :=
  ⟨by rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    (C.theta_retains_edge_BAS j w).1], (C.theta_retains_edge_BAS j w).2⟩

/-- **No merging, edge stage** (CGP08): `Θ₂ = Ψ₃₂` is injective on `V₂⁰ = ⋃_j V_j⁰`. -/
theorem theta_injOn_edge_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) : InjOn (C.Θ_BAS 1) (C.markedBase_BAS 1) :=
  injOn_theta_BPRE (C.slot 1).zeroSet
    (fun k => axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero k))
    (gafEdgeMarker P.toLocalChartFamily P.zero) (fun k => ρ k.1) (fun _ => Δ) (C.Θ_BAS 1)
    (fun k w _ => C.theta_retains_edgeAxis_BAS k w) fun k w₁ h₁ w₂ h₂ h12 =>
      (C.cgp07_edge_BAS R k).1.injOn h₁ h₂ (by
        rw [clm_smul_apply_BPRE, clm_smul_apply_BPRE, h12])

/-- **`W₂` is a smoothly embedded curve, chart by chart** (CGP08): `ψ_j = Θ₂ ∘ φ_j` is smooth on
`(-5.5Δ, 5.5Δ)`, onto the open piece `W₂ ∩ {v_j > .9R_j, |u_j| < 5.5ΔR_j}`, with the linear left
inverse `κ_j = R_j⁻¹u_j`. -/
theorem finalBase_edge_chart_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.edge.finite_centres.toFinset) :
    ∃ ψ : ℝ → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
      ContDiffOn ℝ ∞ ψ (ball 0 (11 / 2 * Δ)) ∧
      (∀ b ∈ ball (0 : ℝ) (11 / 2 * Δ),
        ψ b ∈ C.finalBase_BAS 1 ∩ markedCondition_BPRE (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
          (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ ∧
        ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) (ψ b) = b) ∧
      ∀ y ∈ C.finalBase_BAS 1 ∩ markedCondition_BPRE (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
          (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ,
        ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) y ∈ ball (0 : ℝ) (11 / 2 * Δ) ∧
        ψ (((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) y) = y := by
  have h07 := C.cgp07_edge_BAS R j
  obtain ⟨φ, hφ, hinv, hmaps, -⟩ := h07.2.2
  exact ⟨_, embedded_piece_of_chart_BAS (C.slot 1).zeroSet _ _ (ρ j.1) Δ (C.Θ_BAS 1) φ
    (C.finalBase_BAS 1) hφ h07.1 hinv hmaps (C.theta_contDiffAt_edgePatch_BAS R j)
    (fun w _ => (C.theta_retains_edgeAxis_BAS j w).1) (C.finalBase_inter_edge_BAS j)⟩

/-- **The marked pieces cover `W₂`.** -/
theorem finalBase_edge_cover_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) :
    C.finalBase_BAS 1 ⊆ ⋃ j, markedCondition_BPRE
      (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
      (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ := by
  rintro y ⟨w, hw, rfl⟩
  obtain ⟨j, hj⟩ := mem_iUnion.mp hw
  refine mem_iUnion.mpr ⟨j, ?_, ?_⟩
  · rw [(C.theta_retains_edgeAxis_BAS j w).2]
    exact hj.2.1
  · rw [(C.theta_retains_edgeAxis_BAS j w).1]
    exact hj.2.2

/-- `Θ₃ = id`. -/
theorem theta_two_eq_id_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) :
    C.Θ_BAS 2 = id := rfl

/-- **No merging, slim stage** (`Θ₃ = id`). -/
theorem theta_injOn_slim_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) :
    InjOn (C.Θ_BAS 2) (C.markedBase_BAS 2) := by
  rw [C.theta_two_eq_id_BAS]
  exact injOn_id _

/-- **Patch identification, slim stage**: `W₃ ∩ {v_j > .9R_j, |u_j| < 5.5·10⁵ΔR_j} = V_j⁰`
(as `Θ₃(V_j⁰)`, `Θ₃ = id`). -/
theorem finalBase_inter_slim_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (j : P.slim.finite_centres.toFinset) :
    C.finalBase_BAS 2 ∩ markedCondition_BPRE (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ) =
      C.Θ_BAS 2 '' C.slimPatch_BAS j :=
  theta_image_inter_marked_BPRE (C.slot 2).zeroSet
    (fun k => axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero k))
    (gafSlimMarker P.toLocalChartFamily P.zero) (fun k => ρ k.1) (fun _ => 10 ^ 5 * Δ) (C.Θ_BAS 2)
    (fun _ _ _ => ⟨rfl, rfl⟩) j

/-- **`W₃` is a smoothly embedded curve, chart by chart** (`Θ₃ = id`): `ψ_j = φ_j` (CGP07's slim
chart inverse) onto the open piece `W₃ ∩ {marked j}`, linear left inverse `κ_j = R_j⁻¹u_j`. -/
theorem finalBase_slim_chart_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.slim.finite_centres.toFinset) :
    ∃ ψ : ℝ → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
      ContDiffOn ℝ ∞ ψ (ball 0 (11 / 2 * (10 ^ 5 * Δ))) ∧
      (∀ b ∈ ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)),
        ψ b ∈ C.finalBase_BAS 2 ∩ markedCondition_BPRE (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
          (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ) ∧
        ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)) (ψ b) = b) ∧
      ∀ y ∈ C.finalBase_BAS 2 ∩ markedCondition_BPRE (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
          (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ),
        ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)) y ∈ ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)) ∧
        ψ (((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)) y) = y := by
  have h07 := C.cgp07_slim_BAS R j
  obtain ⟨φ, hφ, hinv, hmaps, -⟩ := h07.2.2
  exact ⟨_, embedded_piece_of_chart_BAS (C.slot 2).zeroSet _ _ (ρ j.1) (10 ^ 5 * Δ) (C.Θ_BAS 2) φ
    (C.finalBase_BAS 2) hφ h07.1 hinv hmaps (fun _ _ => contDiffAt_id) (fun _ _ => rfl)
    (C.finalBase_inter_slim_BAS j)⟩

/-- **The marked pieces cover `W₃`.** -/
theorem finalBase_slim_cover_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) :
    C.finalBase_BAS 2 ⊆ ⋃ j, markedCondition_BPRE
      (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
      (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ) := by
  rintro y ⟨w, hw, rfl⟩
  obtain ⟨j, hj⟩ := mem_iUnion.mp hw
  exact mem_iUnion.mpr ⟨j, hj.2.1, hj.2.2⟩

/-- GAF07's open slim base `B₃ = ⋃_j {w ∈ W₃ | v_j(w) > .9R_j, |u_j(w)| < 4·10⁵Δ v_j(w)}`. -/
def slimBase_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) :
    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :=
  C.finalBase_BAS 2 ∩ ⋃ j : P.slim.finite_centres.toFinset,
    {w | 9 / 10 * ρ j.1 < gafSlimMarker P.toLocalChartFamily P.zero j w ∧
      ‖(axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)) w‖ <
        4 * (10 ^ 5 * Δ) * gafSlimMarker P.toLocalChartFamily P.zero j w}

/-- **`B₃` is an open piece of `W₃`, chart by chart** (GAF07's base as a manifold). -/
theorem slimBase_chart_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.slim.finite_centres.toFinset) :
    ∃ ψ : ℝ → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
      ContDiffOn ℝ ∞ ψ (ball 0 (11 / 2 * (10 ^ 5 * Δ))) ∧
      (∀ b ∈ ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)), ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)) (ψ b) = b) ∧
      IsOpen (ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)) ∩ ψ ⁻¹' (⋃ k : P.slim.finite_centres.toFinset,
        {w | 9 / 10 * ρ k.1 < gafSlimMarker P.toLocalChartFamily P.zero k w ∧
          ‖(axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero k)) w‖ <
            4 * (10 ^ 5 * Δ) * gafSlimMarker P.toLocalChartFamily P.zero k w})) ∧
      C.slimBase_BAS ∩ markedCondition_BPRE (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
          (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ) =
        ψ '' (ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)) ∩ ψ ⁻¹' (⋃ k : P.slim.finite_centres.toFinset,
          {w | 9 / 10 * ρ k.1 < gafSlimMarker P.toLocalChartFamily P.zero k w ∧
            ‖(axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero k)) w‖ <
              4 * (10 ^ 5 * Δ) * gafSlimMarker P.toLocalChartFamily P.zero k w})) := by
  obtain ⟨ψ, hψ, hin, hout⟩ := C.finalBase_slim_chart_BAS R j
  have hopen : IsOpen (⋃ k : P.slim.finite_centres.toFinset,
      {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) |
        9 / 10 * ρ k.1 < gafSlimMarker P.toLocalChartFamily P.zero k w ∧
          ‖(axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero k)) w‖ <
            4 * (10 ^ 5 * Δ) * gafSlimMarker P.toLocalChartFamily P.zero k w}) :=
    isOpen_iUnion fun k => (isOpen_lt continuous_const
      (gafSlimMarker P.toLocalChartFamily P.zero k).continuous).inter
        (isOpen_lt (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero k)).continuous.norm
          (continuous_const.mul (gafSlimMarker P.toLocalChartFamily P.zero k).continuous))
  obtain ⟨h1, h2⟩ := open_piece_of_chart_BAS _ _ (ρ j.1) (10 ^ 5 * Δ) ψ (C.finalBase_BAS 2) _ hopen
    hψ.continuousOn (fun b hb => (hin b hb).1) hout
  refine ⟨ψ, hψ, fun b hb => (hin b hb).2, h1, ?_⟩
  rw [← h2, slimBase_BAS]
  ext y
  simp only [mem_inter_iff]
  tauto

/-- **No merging at every stage** (CGP08): `Θ_st` is injective on the marked base `V_st⁰`. -/
theorem theta_injOn_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (st : Fin 3) : InjOn (C.Θ_BAS st) (C.markedBase_BAS st) := by
  fin_cases st
  · exact C.theta_injOn_circle_BAS R
  · exact C.theta_injOn_edge_BAS R
  · exact C.theta_injOn_slim_BAS

/-- The restricted carrier `D_st = B⁶_st ∩ f_st⁻¹(V_st⁰)` (draft 59 §4 seventh step; D71-11). -/
def carrier_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) (st : Fin 3) : Set X :=
  gafStagePlateau_BAS P.toLocalChartPackets st ∩ C.stageMap_BAS st ⁻¹' C.markedBase_BAS st

/-- **(RF) on the restricted carrier** (CGP08, draft 59 §4 seventh step): for `w₀ ∈ V_st⁰`, the
final fibre `{p ∈ D_st | π_st E(p) = Θ_st w₀}` equals the stage fibre `{p ∈ D_st | f_st p = w₀}`.
Restricted to `D_st` only (no whole-fibre claim). -/
theorem rf_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) (R : Gaf02RoughData C)
    (st : Fin 3) {w₀ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hw₀ : w₀ ∈ C.markedBase_BAS st) :
    {p | p ∈ C.carrier_BAS st ∧
        (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p) = C.Θ_BAS st w₀} =
      {p | p ∈ C.carrier_BAS st ∧ C.stageMap_BAS st p = w₀} :=
  rf_fiber_eq_BPRE (C.stageMap_BAS st)
    (fun p => (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p)) (C.Θ_BAS st)
    (C.markedBase_BAS st) (gafStagePlateau_BAS P.toLocalChartPackets st) (C.theta_injOn_BAS R st)
    (fun p _ _ => C.final_factor_BAS st p) hw₀

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
