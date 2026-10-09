import DifferentialGeometry.Geometry.Fibration.ActualStageChainEGaf05Circle
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEGaf0507Slim

/-!
# GAF05 on `Gaf02ChainE`: the edge patches, the slim charts, and the whole row

Blueprint `master207B.tex`, GAF05 (`prop:fibration-exact-interior-markers`, B:5971–6006): "Every
marked stage patch `V_i⁰` of CGP07 satisfies `v_i = R_i` identically. Its later image `V_i ⊂ W_j`
has the same property and `a = u_i/R_i = u_i/v_i : V_i → B(0, 5.5ℓ_i)` is a diffeomorphism.
Moreover, on the ORIGINAL threshold-6 source plateau for index `i` (including `t < 6Δ` for
edges), both its stage-`j` image and its final image have marker exactly `R_i`."

On ONE chain on the enhanced planes `C : Gaf02ChainE` with its OWN rough data `C.rough` and BASES'
patches / bases (lanes C14-BASESb, C14-BASES-P): `V_i⁰ = C.toChain.{circle,edge,slim}Patch_BAS i`
(CGP07), `W_j = C.toChain.finalBase_BAS j = Θ_j(V_j⁰)` (CGP08),
`V_i = W_j ∩ {marked i} = Θ_j(V_i⁰)`.
Edge and slim retained coordinates are BASES' one-dimensional axis coordinates
`u_i = axisCoordCLM_BAS ∘ gaf{Edge,Slim}Vector i` (`ℓ = Δ`, resp. `10⁵Δ`).

* Edge (open item 1 of C14-GAF-C): `Gaf02ChainE.gaf05_edgePatch_marker_GAFD` (every patch point is
  `f₂(p)` for an ORIGINAL threshold-6 plateau point, `|η_i(p)| < 6Δ`, `t(p) < 6Δ`
  (`Gaf02Chain.cgp07_edge_BAS`), whose stage-two output `g₂ p` has marker `R_i`
  (`Gaf02Chain.gaf05_edge_plateau_G47`); `π_{Q₂}` keeps the edge block),
  `gaf05_edgePatch_chart_GAFD`, `gaf05_edgeBase_marker_GAFD` (`Θ₂` keeps the edge block),
  `gaf05_edgeBase_chart_GAFD` (BASES' `finalBase_edge_chart_BAS`).
* Slim charts: `gaf05_slimPatch_chart_GAFD`, `gaf05_slimBase_chart_GAFD`.
* Generic: `bijOn_invOn_of_chart_GAFD` (a chart `ψ` with left inverse `κ` on the piece ⇒ BijOn,
  InvOn, MapsTo).
* The row: `Gaf02ChainE.gaf05_row_GAFD` — every clause of GAF05 for the three stages.

"Diffeomorphism" is in CHART FORM: `κ = R_i⁻¹u_i` is a continuous linear map (smooth), bijective
from `V_i` onto the coordinate ball, with an inverse `ψ` that is `C^∞` on the ball (`V_i` is a
subset of the Euclidean block space; its manifold structure is BASES' G8).
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

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

/-- **A chart with a left inverse is a bijection with inverse chart**: if `ψ` maps `B` into `A`
with `κ ∘ ψ = id` on `B`, and `κ` maps `A` into `B` with `ψ ∘ κ = id` on `A`, then `κ : A → B` is
bijective, `ψ` is its inverse on `(A, B)` and maps `B` into `A`. -/
theorem bijOn_invOn_of_chart_GAFD {H E : Type*} (κ : H → E) (ψ : E → H) (A : Set H) (B : Set E)
    (hin : ∀ b ∈ B, ψ b ∈ A ∧ κ (ψ b) = b) (hout : ∀ y ∈ A, κ y ∈ B ∧ ψ (κ y) = y) :
    BijOn κ A B ∧ InvOn ψ κ A B ∧ MapsTo ψ B A := by
  refine ⟨⟨fun y hy => (hout y hy).1, fun y₁ h₁ y₂ h₂ h => ?_, fun b hb =>
    ⟨ψ b, (hin b hb).1, (hin b hb).2⟩⟩, ⟨fun y hy => (hout y hy).2, fun b hb => (hin b hb).2⟩,
    fun b hb => (hin b hb).1⟩
  rw [← (hout y₁ h₁).2, ← (hout y₂ h₂).2, h]

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
    V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainE

/-- The stage-two map `f₂ = π_{Q₂} ∘ g₂` keeps the edge markers: `v_i(f₂ p) = v_i(g₂ p)`. -/
theorem edge_marker_stageMap_GAFD (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.edge.finite_centres.toFinset) (p : X) :
    gafEdgeMarker P.toLocalChartFamily P.zero i (C.toChain.stageMap_BAS 1 p) =
      gafEdgeMarker P.toLocalChartFamily P.zero i (C.toChain.g₂ p) :=
  marker_stageQ_G47 P.toLocalChartFamily P.zero (st := 1) (t := .inr (.inr (.inl i)))
    (edge_mem_cgpQ2Tags P.toLocalChartFamily P.zero i) (C.toChain.g₂ p)

/-- **GAF05's plateau clause, edge stage, stage image** (B:5998–6002): on the ORIGINAL threshold-6
edge plateau (`p ∈ B(c_i, 100Δρ_i)`, `|η_i(p)| < 6Δ`, `t(p) < 6Δ`) the stage image `f₂(p)` and the
final image `E p` have marker exactly `R_i`. -/
theorem gaf05_edge_stage_plateau_GAFD (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.edge.finite_centres.toFinset) {p : X}
    (hp : p ∈ ball i.1 (100 * Δ * ρ i.1)) (hη : |P.edge.coord i.1 p| < 6 * Δ)
    (ht : cgpHeight P.toLocalChartFamily p < 6 * Δ) :
    gafEdgeMarker P.toLocalChartFamily P.zero i (C.toChain.stageMap_BAS 1 p) = ρ i.1 ∧
      gafEdgeMarker P.toLocalChartFamily P.zero i (C.toChain.E p) = ρ i.1 := by
  obtain ⟨-, -, h2, h3⟩ := C.toChain.gaf05_edge_plateau_G47 C.planes₁ C.x₀ C.sel_eq.2.1
    C.plane_eq.2.1 (C.rough.sigma_le 1).le i hp hη ht
  rw [C.edge_marker_stageMap_GAFD]
  exact ⟨h2, h3⟩

/-- **GAF05, edge patches** (B:5971–5973): `v_i ≡ R_i` on CGP07's edge patch `V_i⁰`. -/
theorem gaf05_edgePatch_marker_GAFD (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.edge.finite_centres.toFinset) :
    ∀ w ∈ C.toChain.edgePatch_BAS i, gafEdgeMarker P.toLocalChartFamily P.zero i w = ρ i.1 := by
  intro w hw
  obtain ⟨p, ⟨hp, hη, ht⟩, hpw⟩ := (C.toChain.cgp07_edge_BAS C.rough i).2.1 w hw
  rw [← hpw]
  exact (C.gaf05_edge_stage_plateau_GAFD i hp hη ht).1

/-- **GAF05, edge patch chart** (B:5974–5977): on `V_i⁰`, `u_i/v_i = u_i/R_i`, and
`R_i⁻¹u_i : V_i⁰ → (-5.5Δ, 5.5Δ)` is a bijection with a smooth inverse chart (CGP07). -/
theorem gaf05_edgePatch_chart_GAFD (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.edge.finite_centres.toFinset) :
    (∀ w ∈ C.toChain.edgePatch_BAS i,
      (gafEdgeMarker P.toLocalChartFamily P.zero i w)⁻¹ •
          (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero i)) w =
        ((ρ i.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero i)) w) ∧
    BijOn ((ρ i.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero i))
      (C.toChain.edgePatch_BAS i) (ball 0 (11 / 2 * Δ)) ∧
    ∃ φ : ℝ → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
      ContDiffOn ℝ ∞ φ (ball 0 (11 / 2 * Δ)) ∧
      InvOn φ ((ρ i.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero i))
        (C.toChain.edgePatch_BAS i) (ball 0 (11 / 2 * Δ)) ∧
      MapsTo φ (ball 0 (11 / 2 * Δ)) (C.toChain.edgePatch_BAS i) := by
  obtain ⟨hbij, -, φ, hφ, hinv, hmaps, -⟩ := C.toChain.cgp07_edge_BAS C.rough i
  refine ⟨fun w hw => ?_, hbij, φ, hφ, hinv, hmaps⟩
  rw [C.gaf05_edgePatch_marker_GAFD i w hw, smul_apply]

/-- **GAF05, later edge image** (B:5974–5975): `v_i ≡ R_i` on
`V_i = W₂ ∩ {v_i > .9R_i, |u_i| < 5.5ΔR_i} = Θ₂(V_i⁰)` (CGP08 keeps the whole edge block). -/
theorem gaf05_edgeBase_marker_GAFD (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.edge.finite_centres.toFinset) :
    ∀ w ∈ C.toChain.finalBase_BAS 1 ∩ markedCondition_BPRE
        (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero i))
        (gafEdgeMarker P.toLocalChartFamily P.zero i) (ρ i.1) Δ,
      gafEdgeMarker P.toLocalChartFamily P.zero i w = ρ i.1 := by
  intro w hw
  rw [C.toChain.finalBase_inter_edge_BAS i] at hw
  obtain ⟨w₀, hw₀, rfl⟩ := hw
  rw [(C.toChain.theta_retains_edge_BAS i w₀).2]
  exact C.gaf05_edgePatch_marker_GAFD i w₀ hw₀

/-- **GAF05, later edge chart** (B:5975–5977): on `V_i = W₂ ∩ {marked i}`, `u_i/v_i = u_i/R_i`,
and `R_i⁻¹u_i : V_i → (-5.5Δ, 5.5Δ)` is a bijection with a smooth inverse chart landing in `V_i`
(BASES' `Θ₂ ∘ φ`). -/
theorem gaf05_edgeBase_chart_GAFD (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.edge.finite_centres.toFinset) :
    (∀ w ∈ C.toChain.finalBase_BAS 1 ∩ markedCondition_BPRE
        (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero i))
        (gafEdgeMarker P.toLocalChartFamily P.zero i) (ρ i.1) Δ,
      (gafEdgeMarker P.toLocalChartFamily P.zero i w)⁻¹ •
          (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero i)) w =
        ((ρ i.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero i)) w) ∧
    BijOn ((ρ i.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero i))
      (C.toChain.finalBase_BAS 1 ∩ markedCondition_BPRE
        (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero i))
        (gafEdgeMarker P.toLocalChartFamily P.zero i) (ρ i.1) Δ) (ball 0 (11 / 2 * Δ)) ∧
    ∃ ψ : ℝ → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
      ContDiffOn ℝ ∞ ψ (ball 0 (11 / 2 * Δ)) ∧
      InvOn ψ ((ρ i.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero i))
        (C.toChain.finalBase_BAS 1 ∩ markedCondition_BPRE
          (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero i))
          (gafEdgeMarker P.toLocalChartFamily P.zero i) (ρ i.1) Δ) (ball 0 (11 / 2 * Δ)) ∧
      MapsTo ψ (ball 0 (11 / 2 * Δ)) (C.toChain.finalBase_BAS 1 ∩ markedCondition_BPRE
        (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero i))
        (gafEdgeMarker P.toLocalChartFamily P.zero i) (ρ i.1) Δ) := by
  obtain ⟨ψ, hψ, hin, hout⟩ := C.toChain.finalBase_edge_chart_BAS C.rough i
  obtain ⟨hbij, hinv, hmaps⟩ := bijOn_invOn_of_chart_GAFD _ ψ _ _ hin hout
  refine ⟨fun w hw => ?_, hbij, ψ, hψ, hinv, hmaps⟩
  rw [C.gaf05_edgeBase_marker_GAFD i w hw, smul_apply]

/-- **GAF05, slim patch chart** (B:5974–5977): on `V_i⁰`, `u_i/v_i = u_i/R_i`, and
`R_i⁻¹u_i : V_i⁰ → (-5.5·10⁵Δ, 5.5·10⁵Δ)` is a bijection with a smooth inverse chart (CGP07). -/
theorem gaf05_slimPatch_chart_GAFD (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) :
    (∀ w ∈ C.toChain.slimPatch_BAS i,
      (gafSlimMarker P.toLocalChartFamily P.zero i w)⁻¹ •
          (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i)) w =
        ((ρ i.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i)) w) ∧
    BijOn ((ρ i.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i))
      (C.toChain.slimPatch_BAS i) (ball 0 (11 / 2 * (10 ^ 5 * Δ))) ∧
    ∃ φ : ℝ → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
      ContDiffOn ℝ ∞ φ (ball 0 (11 / 2 * (10 ^ 5 * Δ))) ∧
      InvOn φ ((ρ i.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i))
        (C.toChain.slimPatch_BAS i) (ball 0 (11 / 2 * (10 ^ 5 * Δ))) ∧
      MapsTo φ (ball 0 (11 / 2 * (10 ^ 5 * Δ))) (C.toChain.slimPatch_BAS i) := by
  obtain ⟨hbij, -, φ, hφ, hinv, hmaps, -⟩ := C.toChain.cgp07_slim_BAS C.rough i
  refine ⟨fun w hw => ?_, hbij, φ, hφ, hinv, hmaps⟩
  rw [C.gaf05_slimPatch_marker_GAFC i w hw, smul_apply]

/-- **GAF05, later slim chart** (B:5975–5977): on `V_i = W₃ ∩ {marked i} = V_i⁰` (`Θ₃ = id`),
`u_i/v_i = u_i/R_i`, and `R_i⁻¹u_i : V_i → (-5.5·10⁵Δ, 5.5·10⁵Δ)` is a bijection with a smooth
inverse chart landing in `V_i`. -/
theorem gaf05_slimBase_chart_GAFD (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) :
    (∀ w ∈ C.toChain.finalBase_BAS 2 ∩ markedCondition_BPRE
        (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i))
        (gafSlimMarker P.toLocalChartFamily P.zero i) (ρ i.1) (10 ^ 5 * Δ),
      (gafSlimMarker P.toLocalChartFamily P.zero i w)⁻¹ •
          (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i)) w =
        ((ρ i.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i)) w) ∧
    BijOn ((ρ i.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i))
      (C.toChain.finalBase_BAS 2 ∩ markedCondition_BPRE
        (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i))
        (gafSlimMarker P.toLocalChartFamily P.zero i) (ρ i.1) (10 ^ 5 * Δ))
      (ball 0 (11 / 2 * (10 ^ 5 * Δ))) ∧
    ∃ ψ : ℝ → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
      ContDiffOn ℝ ∞ ψ (ball 0 (11 / 2 * (10 ^ 5 * Δ))) ∧
      InvOn ψ ((ρ i.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i))
        (C.toChain.finalBase_BAS 2 ∩ markedCondition_BPRE
          (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i))
          (gafSlimMarker P.toLocalChartFamily P.zero i) (ρ i.1) (10 ^ 5 * Δ))
        (ball 0 (11 / 2 * (10 ^ 5 * Δ))) ∧
      MapsTo ψ (ball 0 (11 / 2 * (10 ^ 5 * Δ))) (C.toChain.finalBase_BAS 2 ∩ markedCondition_BPRE
        (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i))
        (gafSlimMarker P.toLocalChartFamily P.zero i) (ρ i.1) (10 ^ 5 * Δ)) := by
  obtain ⟨ψ, hψ, hin, hout⟩ := C.toChain.finalBase_slim_chart_BAS C.rough i
  obtain ⟨hbij, hinv, hmaps⟩ := bijOn_invOn_of_chart_GAFD _ ψ _ _ hin hout
  refine ⟨fun w hw => ?_, hbij, ψ, hψ, hinv, hmaps⟩
  rw [C.gaf05_slimBase_marker_GAFC i w hw, smul_apply]

/-- **GAF05's plateau clause, slim stage, stage image** (B:5998–6002): on the ORIGINAL threshold-6
slim plateau the stage image `f₃(p) = π₃E(p)` and the final image `E p` have marker exactly
`R_i`. -/
theorem gaf05_slim_stage_plateau_GAFD (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) {p : X}
    (hp : p ∈ ball i.1 (1000000 * Δ * ρ i.1))
    (hη : |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| < 6 * (10 ^ 5 * Δ)) :
    gafSlimMarker P.toLocalChartFamily P.zero i (C.toChain.stageMap_BAS 2 p) = ρ i.1 ∧
      gafSlimMarker P.toLocalChartFamily P.zero i (C.toChain.E p) = ρ i.1 := by
  have hE := C.gaf05_slim_plateau_G47 i hp hη
  refine ⟨?_, hE⟩
  rw [C.stageMap_two_eq_GAFC]
  rw [← hE]
  exact marker_stageQ_G47 P.toLocalChartFamily P.zero (st := 2) (t := .inr (.inl i))
    (slim_mem_cgpQ3Tags P.toLocalChartFamily P.zero i) (C.toChain.E p)

/-- **GAF05's plateau clause, circle stage, stage image** (B:5998–6002): on the ORIGINAL
threshold-6 circle plateau the stage image `f₁(p)` and the final image `E p` have marker exactly
`R_i`. -/
theorem gaf05_circle_stage_plateau_GAFD (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) {p : X}
    (hp : p ∈ ball i.1 (200 * ρ i.1))
    (hη : ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ < 6) :
    gafCircleMarker P.toLocalChartPackets i (C.toChain.stageMap_BAS 0 p) = ρ i.1 ∧
      gafCircleMarker P.toLocalChartPackets i (C.toChain.E p) = ρ i.1 := by
  rw [C.stageMap_zero_eq_GAFC]
  exact (C.gaf05_circle_GAFC i).2.2.2 p hp hη

/-- **GAF05, the whole row on the chain** (B:5971–6006), for `C : Gaf02ChainE` and BASES'
patches / bases, at every index of the three stages (`ℓ = 1`, `Δ`, `10⁵Δ`; edge / slim retained
coordinates are the axis coordinates): (1) `v_i ≡ R_i` on CGP07's patch `V_i⁰`; (2) the later image
is `V_i = Θ_j(V_i⁰) = W_j ∩ {marked i}` (so `V_i ⊂ W_j`); (3) `v_i ≡ R_i` on `V_i`; (4)
`u_i/v_i = u_i/R_i` on `V_i`; (5) `R_i⁻¹u_i : V_i → B(0, 5.5ℓ_i)` is bijective, (6) with an inverse
chart `C^∞` on the ball (chart form of "diffeomorphism"); (7) on the ORIGINAL threshold-6 plateau
(edges: `t < 6Δ`) the stage image `f_j(p)` and the final image `E p` have marker exactly `R_i`. -/
theorem gaf05_row_GAFD (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) :
    (∀ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
      (∀ w ∈ C.toChain.circlePatch_BAS i, gafCircleMarker P.toLocalChartPackets i w = ρ i.1) ∧
      C.toChain.finalBase_BAS 0 ∩ markedCondition_BPRE (gafCircleVector P.toLocalChartPackets i)
          (gafCircleMarker P.toLocalChartPackets i) (ρ i.1) 1 =
        C.toChain.Θ_BAS 0 '' C.toChain.circlePatch_BAS i ∧
      (∀ w ∈ C.toChain.finalBase_BAS 0 ∩ markedCondition_BPRE
          (gafCircleVector P.toLocalChartPackets i) (gafCircleMarker P.toLocalChartPackets i)
            (ρ i.1) 1,
        gafCircleMarker P.toLocalChartPackets i w = ρ i.1) ∧
      (∀ w ∈ C.toChain.finalBase_BAS 0 ∩ markedCondition_BPRE
          (gafCircleVector P.toLocalChartPackets i) (gafCircleMarker P.toLocalChartPackets i)
            (ρ i.1) 1,
        (gafCircleMarker P.toLocalChartPackets i w)⁻¹ • gafCircleVector P.toLocalChartPackets i w =
          ((ρ i.1)⁻¹ • gafCircleVector P.toLocalChartPackets i) w) ∧
      BijOn ((ρ i.1)⁻¹ • gafCircleVector P.toLocalChartPackets i)
        (C.toChain.finalBase_BAS 0 ∩ markedCondition_BPRE
          (gafCircleVector P.toLocalChartPackets i) (gafCircleMarker P.toLocalChartPackets i)
            (ρ i.1) 1) (ball 0 (11 / 2 * 1)) ∧
      (∃ ψ : ℝ² → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
        ContDiffOn ℝ ∞ ψ (ball 0 (11 / 2 * 1)) ∧
        InvOn ψ ((ρ i.1)⁻¹ • gafCircleVector P.toLocalChartPackets i)
          (C.toChain.finalBase_BAS 0 ∩ markedCondition_BPRE
            (gafCircleVector P.toLocalChartPackets i) (gafCircleMarker P.toLocalChartPackets i)
              (ρ i.1) 1) (ball 0 (11 / 2 * 1)) ∧
        MapsTo ψ (ball 0 (11 / 2 * 1)) (C.toChain.finalBase_BAS 0 ∩ markedCondition_BPRE
          (gafCircleVector P.toLocalChartPackets i) (gafCircleMarker P.toLocalChartPackets i)
            (ρ i.1) 1)) ∧
      ∀ p, p ∈ ball i.1 (200 * ρ i.1) → ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ < 6 →
        gafCircleMarker P.toLocalChartPackets i (C.toChain.stageMap_BAS 0 p) = ρ i.1 ∧
          gafCircleMarker P.toLocalChartPackets i (C.toChain.E p) = ρ i.1) ∧
    (∀ i : P.toLocalChartFamily.edge.finite_centres.toFinset,
      (∀ w ∈ C.toChain.edgePatch_BAS i, gafEdgeMarker P.toLocalChartFamily P.zero i w = ρ i.1) ∧
      C.toChain.finalBase_BAS 1 ∩ markedCondition_BPRE
          (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero i))
          (gafEdgeMarker P.toLocalChartFamily P.zero i) (ρ i.1) Δ =
        C.toChain.Θ_BAS 1 '' C.toChain.edgePatch_BAS i ∧
      (∀ w ∈ C.toChain.finalBase_BAS 1 ∩ markedCondition_BPRE
          (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero i))
          (gafEdgeMarker P.toLocalChartFamily P.zero i) (ρ i.1) Δ,
        gafEdgeMarker P.toLocalChartFamily P.zero i w = ρ i.1) ∧
      (∀ w ∈ C.toChain.finalBase_BAS 1 ∩ markedCondition_BPRE
          (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero i))
          (gafEdgeMarker P.toLocalChartFamily P.zero i) (ρ i.1) Δ,
        (gafEdgeMarker P.toLocalChartFamily P.zero i w)⁻¹ •
            (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero i)) w =
          ((ρ i.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero i)) w) ∧
      BijOn ((ρ i.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero i))
        (C.toChain.finalBase_BAS 1 ∩ markedCondition_BPRE
          (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero i))
          (gafEdgeMarker P.toLocalChartFamily P.zero i) (ρ i.1) Δ) (ball 0 (11 / 2 * Δ)) ∧
      (∃ ψ : ℝ → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
        ContDiffOn ℝ ∞ ψ (ball 0 (11 / 2 * Δ)) ∧
        InvOn ψ ((ρ i.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero i))
          (C.toChain.finalBase_BAS 1 ∩ markedCondition_BPRE
            (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero i))
            (gafEdgeMarker P.toLocalChartFamily P.zero i) (ρ i.1) Δ) (ball 0 (11 / 2 * Δ)) ∧
        MapsTo ψ (ball 0 (11 / 2 * Δ)) (C.toChain.finalBase_BAS 1 ∩ markedCondition_BPRE
          (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero i))
          (gafEdgeMarker P.toLocalChartFamily P.zero i) (ρ i.1) Δ)) ∧
      ∀ p, p ∈ ball i.1 (100 * Δ * ρ i.1) → |P.edge.coord i.1 p| < 6 * Δ →
        cgpHeight P.toLocalChartFamily p < 6 * Δ →
        gafEdgeMarker P.toLocalChartFamily P.zero i (C.toChain.stageMap_BAS 1 p) = ρ i.1 ∧
          gafEdgeMarker P.toLocalChartFamily P.zero i (C.toChain.E p) = ρ i.1) ∧
    ∀ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
      (∀ w ∈ C.toChain.slimPatch_BAS i, gafSlimMarker P.toLocalChartFamily P.zero i w = ρ i.1) ∧
      C.toChain.finalBase_BAS 2 ∩ markedCondition_BPRE
          (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i))
          (gafSlimMarker P.toLocalChartFamily P.zero i) (ρ i.1) (10 ^ 5 * Δ) =
        C.toChain.Θ_BAS 2 '' C.toChain.slimPatch_BAS i ∧
      (∀ w ∈ C.toChain.finalBase_BAS 2 ∩ markedCondition_BPRE
          (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i))
          (gafSlimMarker P.toLocalChartFamily P.zero i) (ρ i.1) (10 ^ 5 * Δ),
        gafSlimMarker P.toLocalChartFamily P.zero i w = ρ i.1) ∧
      (∀ w ∈ C.toChain.finalBase_BAS 2 ∩ markedCondition_BPRE
          (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i))
          (gafSlimMarker P.toLocalChartFamily P.zero i) (ρ i.1) (10 ^ 5 * Δ),
        (gafSlimMarker P.toLocalChartFamily P.zero i w)⁻¹ •
            (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i)) w =
          ((ρ i.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i)) w) ∧
      BijOn ((ρ i.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i))
        (C.toChain.finalBase_BAS 2 ∩ markedCondition_BPRE
          (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i))
          (gafSlimMarker P.toLocalChartFamily P.zero i) (ρ i.1) (10 ^ 5 * Δ))
        (ball 0 (11 / 2 * (10 ^ 5 * Δ))) ∧
      (∃ ψ : ℝ → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
        ContDiffOn ℝ ∞ ψ (ball 0 (11 / 2 * (10 ^ 5 * Δ))) ∧
        InvOn ψ ((ρ i.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i))
          (C.toChain.finalBase_BAS 2 ∩ markedCondition_BPRE
            (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i))
            (gafSlimMarker P.toLocalChartFamily P.zero i) (ρ i.1) (10 ^ 5 * Δ))
          (ball 0 (11 / 2 * (10 ^ 5 * Δ))) ∧
        MapsTo ψ (ball 0 (11 / 2 * (10 ^ 5 * Δ))) (C.toChain.finalBase_BAS 2 ∩
          markedCondition_BPRE (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i))
            (gafSlimMarker P.toLocalChartFamily P.zero i) (ρ i.1) (10 ^ 5 * Δ))) ∧
      ∀ p, p ∈ ball i.1 (1000000 * Δ * ρ i.1) →
        |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| < 6 * (10 ^ 5 * Δ) →
        gafSlimMarker P.toLocalChartFamily P.zero i (C.toChain.stageMap_BAS 2 p) = ρ i.1 ∧
          gafSlimMarker P.toLocalChartFamily P.zero i (C.toChain.E p) = ρ i.1 := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := C.gaf05_circleBase_chart_GAFC i
    exact ⟨C.gaf05_circlePatch_marker_GAFC i, C.toChain.finalBase_inter_circle_BAS i,
      C.gaf05_circleBase_marker_GAFC i, h1, h2, h3,
      fun p hp hη => C.gaf05_circle_stage_plateau_GAFD i hp hη⟩
  · obtain ⟨h1, h2, h3⟩ := C.gaf05_edgeBase_chart_GAFD i
    exact ⟨C.gaf05_edgePatch_marker_GAFD i, C.toChain.finalBase_inter_edge_BAS i,
      C.gaf05_edgeBase_marker_GAFD i, h1, h2, h3,
      fun p hp hη ht => C.gaf05_edge_stage_plateau_GAFD i hp hη ht⟩
  · obtain ⟨h1, h2, h3⟩ := C.gaf05_slimBase_chart_GAFD i
    exact ⟨C.gaf05_slimPatch_marker_GAFC i, C.toChain.finalBase_inter_slim_BAS i,
      C.gaf05_slimBase_marker_GAFC i, h1, h2, h3,
      fun p hp hη => C.gaf05_slim_stage_plateau_GAFD i hp hη⟩

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
