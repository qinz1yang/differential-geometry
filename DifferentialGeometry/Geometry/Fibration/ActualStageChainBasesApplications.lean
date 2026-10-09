import DifferentialGeometry.Geometry.Fibration.ActualStageChainBasesRow
import DifferentialGeometry.Geometry.Fibration.ActualStageChainERowInhabitant

/-!
# Consumers of `Gaf02Bases` (lane C14-BASESc)

* `Gaf02Chain.stage_submersion_slim_range_BAS`: consumer of lane C14-BASES-P's slim stage
  submersion (`ActualStageChainSubmersionSlim`).
* `Gaf02Bases.final_point_BAS`: `Θ_st(f_st p) ∈ W_st` on FC33's `U_st` (the factorization and the
  threshold-5 inclusion read off ONE bases object).
* `Gaf02Bases.circle_open_piece_BAS`, `edge_open_piece_BAS`, `slim_open_piece_BAS`: in the bases
  chart `Θ_st ∘ chart_j`, the piece `W_st ∩ {marked j} ∩ O` of an open `O` is the image of an OPEN
  subset of the coordinate ball (the manifold structure of open parts of `W_st`).
* `Gaf02Bases.fibre_eq_BAS`: (RF) on `D_st` from the object.
* `gaf02Bases_dihedralTiny_BAS`: on the dihedral `RP³ # RP³` fixture, the `Gaf02ChainE` of
  `exists_gaf02ChainE_row_dihedralTiny_CHI` carries `Gaf02Bases Ĉ.toChain Ĉ.rough` and `π_stE` maps
  `U_st` into `W_st` (joint satisfiability; the fixture's stage families are empty).
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

section Chain

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- At a slim-plateau point, `D(κ_j ∘ f₃)(p)` has full range (consumer of
`stage_submersion_slim_BAS`). -/
theorem Gaf02Chain.stage_submersion_slim_range_BAS
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.slim.finite_centres.toFinset) {p : X}
    (hp : p ∈ ball j.1 (1000000 * Δ * ρ j.1))
    (hη : |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| < 6 * (10 ^ 5 * Δ)) :
    LinearMap.range (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun q =>
      ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        (C.stageMap_BAS 2 q)) p).toLinearMap = ⊤ :=
  LinearMap.range_eq_top.mpr (C.stage_submersion_slim_BAS R j hp hη)

namespace Gaf02Bases

variable {C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw} {R : Gaf02RoughData C}

/-- `Θ_st(f_st p) ∈ W_st` for `p` in FC33's original threshold-5 domain `U_st`. -/
theorem final_point_BAS (B : Gaf02Bases C R) (st : Fin 3) {p : X}
    (hp : p ∈ gafStageDomain5_BAS P.toLocalChartPackets st) :
    C.Θ_BAS st (C.stageMap_BAS st p) ∈ C.finalBase_BAS st :=
  B.later.final_factor st p ▸ B.later.mapsTo_final st hp

/-- Open pieces of `W₁` in the bases chart `Θ₁ ∘ chart_j`. -/
theorem circle_open_piece_BAS (B : Gaf02Bases C R)
    (j : P.toLocalChartFamily.circle.finite_centres.toFinset)
    (O : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) (hO : IsOpen O) :
    IsOpen (ball (0 : ℝ²) (11 / 2 * 1) ∩ (C.Θ_BAS 0 ∘ B.circle.chart j) ⁻¹' O) ∧
      C.finalBase_BAS 0 ∩ markedCondition_BPRE (gafCircleVector P.toLocalChartPackets j)
          (gafCircleMarker P.toLocalChartPackets j) (ρ j.1) 1 ∩ O =
        (C.Θ_BAS 0 ∘ B.circle.chart j) '' (ball (0 : ℝ²) (11 / 2 * 1) ∩
          (C.Θ_BAS 0 ∘ B.circle.chart j) ⁻¹' O) :=
  open_piece_of_chart_BAS _ _ (ρ j.1) 1 _ _ O hO (B.circle.spec.base_chart j).1.continuousOn
    (fun b hb => ((B.circle.spec.base_chart j).2.1 b hb).1) (B.circle.spec.base_chart j).2.2

/-- Open pieces of `W₂` in the bases chart `Θ₂ ∘ chart_j`. -/
theorem edge_open_piece_BAS (B : Gaf02Bases C R) (j : P.edge.finite_centres.toFinset)
    (O : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) (hO : IsOpen O) :
    IsOpen (ball (0 : ℝ) (11 / 2 * Δ) ∩ (C.Θ_BAS 1 ∘ B.edge.chart j) ⁻¹' O) ∧
      C.finalBase_BAS 1 ∩ markedCondition_BPRE
          (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
          (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ ∩ O =
        (C.Θ_BAS 1 ∘ B.edge.chart j) '' (ball (0 : ℝ) (11 / 2 * Δ) ∩
          (C.Θ_BAS 1 ∘ B.edge.chart j) ⁻¹' O) :=
  open_piece_of_chart_BAS _ _ (ρ j.1) Δ _ _ O hO (B.edge.spec.base_chart j).1.continuousOn
    (fun b hb => ((B.edge.spec.base_chart j).2.1 b hb).1) (B.edge.spec.base_chart j).2.2

/-- Open pieces of `W₃` in the bases chart `Θ₃ ∘ chart_j` (`Θ₃ = id`). -/
theorem slim_open_piece_BAS (B : Gaf02Bases C R) (j : P.slim.finite_centres.toFinset)
    (O : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) (hO : IsOpen O) :
    IsOpen (ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)) ∩ (C.Θ_BAS 2 ∘ B.slim.chart j) ⁻¹' O) ∧
      C.finalBase_BAS 2 ∩ markedCondition_BPRE
          (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
          (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ) ∩ O =
        (C.Θ_BAS 2 ∘ B.slim.chart j) '' (ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)) ∩
          (C.Θ_BAS 2 ∘ B.slim.chart j) ⁻¹' O) :=
  open_piece_of_chart_BAS _ _ (ρ j.1) (10 ^ 5 * Δ) _ _ O hO
    (B.slim.spec.base_chart j).1.continuousOn
    (fun b hb => ((B.slim.spec.base_chart j).2.1 b hb).1) (B.slim.spec.base_chart j).2.2

/-- (RF) read off the bases object: for `w₀ ∈ V_st⁰`, the final fibre over `Θ_st w₀` in `D_st` is
the stage fibre over `w₀`. -/
theorem fibre_eq_BAS (B : Gaf02Bases C R) {st : Fin 3}
    {w₀ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hw₀ : w₀ ∈ C.markedBase_BAS st) {p : X} (hp : p ∈ C.carrier_BAS st) :
    (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p) = C.Θ_BAS st w₀ ↔
      C.stageMap_BAS st p = w₀ := by
  have h := B.later.rf st hw₀
  constructor
  · intro hE
    have hm : p ∈ {p | p ∈ C.carrier_BAS st ∧
        (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p) = C.Θ_BAS st w₀} :=
      ⟨hp, hE⟩
    rw [h] at hm
    exact hm.2
  · intro hf
    have hm : p ∈ {p | p ∈ C.carrier_BAS st ∧ C.stageMap_BAS st p = w₀} := ⟨hp, hf⟩
    rw [← h] at hm
    exact hm.2

end Gaf02Bases

end Chain

attribute [local instance] dihedralTinyMetricSpace_CHI

/-- **Inhabitant on `RP³ # RP³`** (dihedral fixture of lane C14-CHAIN-INST): the `Gaf02ChainE` of
`exists_gaf02ChainE_row_dihedralTiny_CHI` carries the bases object on its OWN rough data, and
`π_stE` maps FC33's `U_st` into `W_st` (read off the object). The fixture's stage families are
empty (joint satisfiability of the row's premises and of the object's fields). -/
theorem gaf02Bases_dihedralTiny_BAS (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainE (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h) Kj Ξ Γ S eg c cw),
      Nonempty (Gaf02Bases C.toChain C.rough) ∧
      ∀ st, MapsTo (fun p => (gafStageQ (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).toLocalChartFamily
          (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).zero st).starProjection (C.toChain.E p))
        (gafStageDomain5_BAS (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).toLocalChartPackets st)
        (C.toChain.finalBase_BAS st) := by
  obtain ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C, -, -, -, -, -⟩ :=
    exists_gaf02ChainE_row_dihedralTiny_CHI Kj
  exact ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C, ⟨C.bases_BAS⟩,
    C.bases_BAS.later.mapsTo_final⟩

end DifferentialGeometry.Geometry.Collapse
