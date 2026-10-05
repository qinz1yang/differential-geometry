import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf06Axis
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEJA

/-!
# GAF06 as ONE row on the chain with (JA)

Blueprint `master207B.tex`, GAF06 (`lem:fibration-whole-ratio-preimage-localization`,
B:6008–6047): `H_τ = (1 − τ)F + τE`, `0 ≤ τ ≤ 1`; for ANY original `i ∈ I_+` and ANY `p ∈ M`,
(RP) `v_i(H_τ p) > .9R_i`, `|u_i(H_τ p)|/v_i(H_τ p) ≤ 4ℓ_i` ⇒ the original coordinate is defined and
`|η_i(p)| < 4.01ℓ_i`; for circles and slim charts the original cutoff is one; for edge charts only
the tangential coordinate is controlled.

`Gaf02ChainEJA.gaf06_row_GAFD (C)` — no hypothesis beyond the object (`c₃ = c 2 < 1/1000` is GAF01's
(JA), the field `C.c_two_lt`; `F = 𝓔⁰ = cgpGlobalMap`, `E = C.toChain.E`; (AM0) on the segment and
`|E − F| < c₃ρ` are the chain's fields). Conjuncts:

1. every retained index `i` (circle, slim, edge), every `ℓ ≥ 1`, (RP) with the full block norm
   `‖u_i‖` ⇒ positive cutoff, `p` in the chart domain (coordinate defined), `‖η_i(p)‖ < 4.01ℓ`;
2. the same with (RP) for the AXIS coordinate `|axis u_i|` (the blueprint's real `u_i` of a
   one-dimensional chart; weaker hypothesis) ⇒ `|axis η_i(p)| < 4.01ℓ`;
3. circles (`ℓ = 1`, full `ℝ²` norm): `p ∈ B(c_j, 200ρ(c_j))`, `‖η_j(p)‖ < 4.01`, cutoff ONE;
4. slim charts (`ℓ = 10⁵Δ`, axis): `p ∈ B(c_j, 10⁶Δρ(c_j))`, `|η_j(p)| < 4.01·10⁵Δ`, cutoff ONE;
5. edge charts (`ℓ = Δ`, axis): positive cutoff, `p ∈ B(c_j, 100Δρ(c_j))`, tangential `|η_j(p)| <
   4.01Δ` — no height claim.
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

namespace Gaf02ChainEJA

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}

/-- **GAF06, the whole row, on the chain with (JA)** (B:6008–6047): for every retained index and
every point of the global segment `H_τ = (1 − τ)𝓔⁰ + τE`, (RP) localizes `p` in the original chart
with `|η_i(p)| < 4.01ℓ_i`; full `ℝ²` norm for circles, the real (axis) coordinate for slim and edge
charts; cutoff one for circles and slim charts, tangential bound only for edges. No hypothesis
beyond the object. -/
theorem gaf06_row_GAFD (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) :
    (∀ ℓ : ℝ, 1 ≤ ℓ → ∀ (i : CGPMarkerIndex P.toLocalChartFamily) (p : X), ∀ t ∈ Icc (0 : ℝ) 1,
      9 / 10 * ρ (cgpMarkerCentre P.toLocalChartFamily i) <
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero i)
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.toChain.E p) →
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero i)
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.toChain.E p)‖ ≤
        4 * ℓ * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero i)
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.toChain.E p) →
      0 < cgpMarkerCutoff P.toLocalChartFamily i p ∧
        p ∈ ball (cgpMarkerCentre P.toLocalChartFamily i)
          (cgpMarkerDomain P.toLocalChartFamily i * ρ (cgpMarkerCentre P.toLocalChartFamily i)) ∧
        ‖cgpCoord P.toLocalChartFamily P.zero (cgpMarkerTag P.toLocalChartFamily P.zero i) p‖ <
          401 / 100 * ℓ) ∧
    (∀ ℓ : ℝ, 1 ≤ ℓ → ∀ (i : CGPMarkerIndex P.toLocalChartFamily) (p : X), ∀ t ∈ Icc (0 : ℝ) 1,
      9 / 10 * ρ (cgpMarkerCentre P.toLocalChartFamily i) <
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero i)
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.toChain.E p) →
      ‖(axisCoordCLM_BAS.comp (blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero =>
          ℝ²) (cgpMarkerTag P.toLocalChartFamily P.zero i)))
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.toChain.E p)‖ ≤
        4 * ℓ * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero i)
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.toChain.E p) →
      0 < cgpMarkerCutoff P.toLocalChartFamily i p ∧
        p ∈ ball (cgpMarkerCentre P.toLocalChartFamily i)
          (cgpMarkerDomain P.toLocalChartFamily i * ρ (cgpMarkerCentre P.toLocalChartFamily i)) ∧
        ‖axisCoordCLM_BAS
          (cgpCoord P.toLocalChartFamily P.zero (cgpMarkerTag P.toLocalChartFamily P.zero i) p)‖ <
          401 / 100 * ℓ) ∧
    (∀ (j : P.toLocalChartFamily.circle.finite_centres.toFinset) (p : X), ∀ t ∈ Icc (0 : ℝ) 1,
      9 / 10 * ρ j.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inl j) ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.toChain.E p) →
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl j)
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.toChain.E p)‖ ≤
        4 * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl j)
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.toChain.E p) →
      p ∈ ball j.1 (200 * ρ j.1) ∧
        ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 401 / 100 ∧
        P.toLocalChartFamily.circle.cutoff j.1 p = 1) ∧
    (∀ (j : P.toLocalChartFamily.slim.finite_centres.toFinset) (p : X), ∀ t ∈ Icc (0 : ℝ) 1,
      9 / 10 * ρ j.1 < gafSlimMarker P.toLocalChartFamily P.zero j
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.toChain.E p) →
      ‖(axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.toChain.E p)‖ ≤
        4 * (10 ^ 5 * Δ) * gafSlimMarker P.toLocalChartFamily P.zero j
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.toChain.E p) →
      p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
        |(P.toLocalChartFamily.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| <
          401 / 100 * (10 ^ 5 * Δ) ∧
        P.toLocalChartFamily.slim.cutoff j.1 p = 1) ∧
    ∀ (j : P.toLocalChartFamily.edge.finite_centres.toFinset) (p : X), ∀ t ∈ Icc (0 : ℝ) 1,
      9 / 10 * ρ j.1 < gafEdgeMarker P.toLocalChartFamily P.zero j
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.toChain.E p) →
      ‖(axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.toChain.E p)‖ ≤
        4 * Δ * gafEdgeMarker P.toLocalChartFamily P.zero j
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.toChain.E p) →
      0 < P.toLocalChartFamily.edge.cutoff j.1 p ∧ p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
        |P.toLocalChartFamily.edge.coord j.1 p| < 401 / 100 * Δ :=
  ⟨fun _ hℓ i => C.toChain.gaf06_G47 C.c_two_lt hℓ i,
    fun _ hℓ i => C.toChain.gaf06_axis_GAFD C.c_two_lt hℓ i,
    fun j => C.toChain.gaf06_circle_G47 C.c_two_lt j,
    fun j => C.toChain.gaf06_slim_axis_GAFD C.c_two_lt j,
    fun j => C.toChain.gaf06_edge_axis_GAFD C.c_two_lt j⟩

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
