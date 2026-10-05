import DifferentialGeometry.Geometry.Fibration.ActualStageChainEGaf0405
import DifferentialGeometry.Geometry.Fibration.ActualStageChainReplacement

/-!
# FDC01's EXACT replacement marker on the enhanced chain `Gaf02ChainE`

Blueprint `master207B.tex`, FDC01 (`lem:fibration-actual-replacement-edge-chart`, B:7157–7243):
"GAF02 and GAF05 therefore put its final image in `W₂` and give its exact full `j` marker. Finally
(AE) bounds the normalized vector by `|η_j(q)| + 5c₃/4 < 3Δ`." The EXACT marker is GAF05's
source-plateau clause on `Gaf02ChainE` (lane C14-GAF47 G5, `Gaf02ChainE.gaf05_edge_plateau_G47`):
a replacement index `j` has `ζ_j(q) = 1`, `|η_j(q)| < 2Δ` and `t(q) ≤ 4.01Δ`, so `q` lies on the
original threshold-`6` edge plateau of `j`. No BASES input is used for the marker.

* `stageQ_edge_repl_FDC`: (Repl)'s base clauses on `π₂ z` (`v_j(π₂z) = R_j`, `|u_j(π₂z)|/R_j < 3Δ`)
  from those on `z` (`π_{Q₂}` keeps every edge block).
* `Gaf02ChainE.edge_exact_marker_FDC`: `ζ_j(q) ≠ 0`, `|η_j(q)| < 6Δ`, `t(q) < 6Δ` ⇒
  `v_j(E q) = R_j` exactly.

NOT here: `π₂E(q) ∈ W₂` (hence `∈ B₂`): the base `W₂ = Θ₂(V₂⁰)` of BASES (CGP06–CGP08).
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

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- **(Repl)'s base clauses on `π₂ z`**: `v_j(z) = R_j` and `|u_j(z)| < 3ΔR_j` give
`v_j(π₂ z) = R_j` and `|u_j(π₂ z)|/R_j < 3Δ` (`π_{Q₂}` keeps every edge block). -/
theorem stageQ_edge_repl_FDC
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (j : P.edge.finite_centres.toFinset)
    (z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hv : blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) z = ρ j.1)
    (hu : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) z‖ < 3 * Δ * ρ j.1) :
    blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inr (.inl j)))
        ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection z) = ρ j.1 ∧
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl j))) ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection z)‖ /
          ρ j.1 < 3 * Δ := by
  refine ⟨(gafStageQ_edgeMarker_FDC P j z).trans hv, ?_⟩
  rw [gafStageQ_edgeVector_FDC P j z, div_lt_iff₀ (hρ j.1)]
  exact hu

namespace Gaf02ChainE

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **The exact final marker** (GAF05's plateau clause on `Gaf02ChainE`): `ζ_j(q) ≠ 0` (so
`q ∈ U_j`), `|η_j(q)| < 6Δ` and `t(q) < 6Δ` give `v_j(E q) = R_j`. -/
theorem edge_exact_marker_FDC (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (j : P.toLocalChartFamily.edge.finite_centres.toFinset) {q : X}
    (hζ : P.edge.cutoff j.1 q ≠ 0) (hη : |P.edge.coord j.1 q| < 6 * Δ)
    (ht : P.edge.smoothing q / ρ q < 6 * Δ) :
    blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.toChain.E q) = ρ j.1 := by
  obtain ⟨-, hΔ, -⟩ := C.toChain.std
  have hball : q ∈ ball j.1 (100 * Δ * ρ j.1) :=
    cgpMarkerCutoff_ne_zero P.toLocalChartFamily (by linarith) (.inr (.inr j)) q hζ
  exact C.gaf05_edge_plateau_G47 j hball hη ht

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
