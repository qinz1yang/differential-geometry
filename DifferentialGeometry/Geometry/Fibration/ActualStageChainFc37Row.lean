import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeBaseExactApplicationsEDP23
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeLimit
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeFibreDiskEFE

/-!
# FC37 (proper edge disk bundles with faces): the delivered part of the row on the chain

Lane S-FC-WRAP, group G3 (suffix `_FCW`). Blueprint `master207B.tex`, FC37
(`found:fibration-edge-bundles`, B:6260–6285): KL 14.8–14.11 truncate the edge base by marker
`≥ .9R_i` and ratio `< 4Δ`; the vertical restriction is the union `{η_{E'} ≤ .35Δ} ∪
E⁻¹{x_ρ > 0, x'_{E'}/x_ρ ≤ 4Δ}`; the full preimage of the base intersected with it is `U'₂`
(= EDP02's `X₂`); after removing the zero and slim interiors, `M₂ ∩ U'₂` is compact and a union of
disk fibres of the proper restriction `π₂E` — it is `M^edge` [EDP02, EDP04, EDP05, FDC02].

`Gaf02ChainEJA.fc37_row_FCW` (a chain with (JA) on `LocalChartPacketsC14Z`; the numeric premises
are EDP-E's, readable at every register by `ClosedRegisterV4.edpE_numerics_RGC`) is the conjunction
of the clauses delivered in the tree:

1. `type_of% (C.toGaf02ChainE.edgeBase_exact_row_EDP23 hΔ2)` — EDP02's base level: the exact marker
   `v_i = R_i` on `B₂`, `B₂` written out, patch membership;
2. EDP04's whole fibres over EVERY point of `B₂`: `{x | π₂E x = w, T x ≤ 4Δ}` is the range of a
   smooth embedding of `ClosedCell 2` whose boundary circle is exactly the rim `{T = 4Δ}`
   (`edgeBase_fibre_disk_EDP23`; boundary (EV) of the fibres);
3. EDP04's ontoness `B₂ ⊆ π₂E(X₂)` (`edgeBase_subset_image_EDP23`);
4. EDP04's properness over the height sublevel: for compact `K'`, `(π₂E)⁻¹(K') ∩ {T ≤ 4Δ}` is
   compact (`edgeSublevel_preimage_isCompact_EFE`);
5. FDC02 in its reduced form (`fdc02_isCompact_FDC`): for closed `M₂` and `S ⊆ M₂ ∩ V` whose points
   have a witnessing index, if `S` contains every point of `M₂ ∩ V` that FDC01's replacement
   produces (`hrepl`, FDC01's exit), then `S` (= `M₂ ∩ X₂`, `Gaf02Chain.edgePiece_eq_witnessed_FDC`)
   is compact.

NOT in the tree (so not in the row; owners in the delivery block): EDP04's smooth BUNDLE structure
(local trivializations of `π₂E : X₂ → B₂` and the circle-fibred boundary restriction), EDP05
(`M₂ ∩ X₂ = f₂⁻¹(C₂)` saturated, `C₂` a smooth one-dimensional domain, the proper disk bundle over
`C₂` as a manifold with corners of depth `≤ 2`, the horizontal face equations), and FDC02's base
`C₂` as a compact smooth one-manifold. FDC02's compactness for the ACTUAL `M₂` with FDC01's
replacement discharged is `eventually_fdc02_actual_C14Z_FDC` (standing-tail shell).

Consumer: `fc37_disk_over_image_FCW`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology
open GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainEJA

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **FC37, the delivered part of the row on the final family**: EDP02's base-level exactness, the
whole disk fibre over every point of `B₂` with its rim, ontoness, properness over the height
sublevel, and FDC02's compactness reduced to FDC01's replacement. -/
theorem fc37_row_FCW
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hΔ2 : 2 ≤ Δ) (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000) :
    type_of% (C.toGaf02ChainE.edgeBase_exact_row_EDP23 hΔ2) ∧
    (∀ w ∈ C.toGaf02ChainE.edgeBase_EDP23,
      ∃ φ : ClosedCell 2 → X, IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, E3) ∞ φ ∧
        range φ = {x | (gafStageQ P.toLocalChartFamily P.zero 1).starProjection
            (C.toChain.E x) = w ∧ EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
              P.toLocalChartFamily P.zero (C.toChain.E x)) / C.toChain.scale x ≤ 4 * Δ} ∧
        range (φ ∘ cellBoundaryInclusion 2) = {x |
          (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.toChain.E x) = w ∧
            EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero
              (C.toChain.E x)) / C.toChain.scale x = 4 * Δ}) ∧
    type_of% (C.toGaf02ChainE.edgeBase_subset_image_EDP23 hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1
      hβc1) ∧
    (∀ K' : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsCompact K' →
      IsCompact ({x | (gafStageQ P.toLocalChartFamily P.zero 1).starProjection
          (C.toChain.E x) ∈ K'} ∩
        {x | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero
          (C.toChain.E x)) / C.toChain.scale x ≤ 4 * Δ})) ∧
    (∀ {M₂ Sx : Set X}, IsClosed M₂ →
      Sx ⊆ M₂ ∩ ({p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < C.toChain.scale p ∧
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero
          (C.toChain.E p)) / C.toChain.scale p ≤ 4 * Δ}) →
      (∀ x ∈ Sx, ∃ j : P.edge.finite_centres.toFinset,
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl j))) (C.toChain.E x) = ρ j.1 ∧
        ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl j))) (C.toChain.E x)‖ < 4 * Δ * ρ j.1) →
      (∀ x ∈ M₂ ∩ ({p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪
        {p | 0 < C.toChain.scale p ∧ EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
          P.toLocalChartFamily P.zero (C.toChain.E p)) / C.toChain.scale p ≤ 4 * Δ}),
        ∀ j ∈ P.edge.centres, x ∈ ball j (100 * Δ * ρ j) →
          |P.edge.coord j x| ≤ 401 / 100 * Δ → P.edge.smoothing x / ρ x ≤ 401 / 100 * Δ →
          x ∈ Sx) →
      IsCompact Sx) := by
  refine ⟨C.toGaf02ChainE.edgeBase_exact_row_EDP23 hΔ2, fun w hw => ?_,
    C.toGaf02ChainE.edgeBase_subset_image_EDP23 hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1,
    fun K' hK' => C.toChain.edgeSublevel_preimage_isCompact_EFE hK',
    fun {M₂ Sx} hM₂ hSK hwit hrepl => C.toChain.fdc02_isCompact_FDC hM₂ hSK hwit hrepl⟩
  exact C.toGaf02ChainE.edgeBase_fibre_disk_EDP23 hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 hw

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
