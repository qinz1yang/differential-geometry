import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeBaseExactEDP23
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeFibreDiskEFE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainRowsInhabitant
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRowsEZ

/-!
# EDP02 (B), base level: the whole fibre over EVERY point of `B₂`, ontoness, and consumers

Companion of `ActualStageChainEdgeBaseExactEDP23.lean` (group G1 of lane S-EDP02-03). With the
exact marker on all of `B₂` (`Gaf02ChainE.edgeBase_marker_exact_EDP23`), lane S-EDP-FDC's
whole-disk result `edp04_fibre_disk_EFE` (stated over a patch point `w ∈ W₂ ∩ {marked k}` with
`‖u_k w‖ < 4ΔR_k`) applies over EVERY `w ∈ B₂`, not only over `π₂E(X₂)`:

* `Gaf02ChainE.edgeBase_fibre_disk_EDP23`: for `w ∈ B₂` the WHOLE fibre
  `{x : π₂E x = w, T x ≤ 4Δ}` is the range of a smooth embedding of `ClosedCell 2`, boundary circle
  onto the rim `{T = 4Δ}` (this is `EdgeBundle.fibre_disk` with `Base := B₂`);
* `Gaf02ChainE.edgeBase_subset_image_EDP23`: `B₂ ⊆ π₂E(X₂)` (ontoness of `f₂ : X₂ → B₂`, the
  nonempty disk).

Consumers: on the final closed family (`..._C14Z_EDP23`), at the closed rows' source of every
register on a tail (`eventually_edgeBase_exact_rowsSourceZ_EDP23`, the same shape as GAF05's
`eventually_gaf05_rowsSourceZ_GAFD`; `Δ ≥ 2` read off `Δ > 10⁶` of the register), and the
dihedral final-family fixture (`exists_edgeBase_exact_row_dihedralTiny_EDP23`; KNOWN ACCEPTANCE GAP
D71-7 / D70-8: its edge family is EMPTY, so `W₂ = ∅` and the clauses are vacuously true there).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

section Kernel

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
  {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz}

namespace Gaf02ChainE

/-- **The whole fibre over EVERY point of `B₂` is a smooth disk** (EDP04's fibre identification at
the base level; `EdgeBundle.fibre_disk` for `Base := B₂`): for `w ∈ B₂` the set
`{x : π₂E x = w, T x ≤ 4Δ}` is the range of a smooth embedding of `ClosedCell 2` whose boundary
circle covers exactly the rim `{T = 4Δ}`. -/
theorem edgeBase_fibre_disk_EDP23 (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000)
    {w : BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)}
    (hw : w ∈ Ĉ.edgeBase_EDP23) :
    ∃ φ : ClosedCell 2 → X, IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, E3) ∞ φ ∧
      range φ = {x | (gafStageQ L.toLocalChartFamily L.zero 1).starProjection
          (Ĉ.toChain.E x) = w ∧ EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
            L.toLocalChartFamily L.zero (Ĉ.toChain.E x)) / Ĉ.toChain.scale x ≤ 4 * Δ} ∧
      range (φ ∘ cellBoundaryInclusion 2) = {x |
        (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x) = w ∧
          EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
            (Ĉ.toChain.E x)) / Ĉ.toChain.scale x = 4 * Δ} := by
  obtain ⟨hW, k, hv, hu⟩ := hw
  obtain ⟨hmem, -, hu'⟩ := Ĉ.edgeBase_mem_patch_EDP23 hΔ2 k hW hv hu
  exact Ĉ.edp04_fibre_disk_EFE hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 k hmem hu'

/-- **Ontoness of `f₂ : X₂ → B₂`** (EDP04, "gives their smooth type and onto-ness"): every
point of `B₂` is `π₂E x` for a point `x` of `X₂` (the whole fibre is a nonempty disk). -/
theorem edgeBase_subset_image_EDP23 (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000) :
    Ĉ.edgeBase_EDP23 ⊆ (fun x => (gafStageQ L.toLocalChartFamily L.zero 1).starProjection
      (Ĉ.toChain.E x)) '' Ĉ.edgeTotal_EDP23 := by
  intro w hw
  obtain ⟨φ, -, hr, -⟩ := Ĉ.edgeBase_fibre_disk_EDP23 hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1
    hβc1 hw
  have hx : φ (closedCellCenter 2) ∈ range φ := mem_range_self _
  rw [hr] at hx
  obtain ⟨hπ, hT⟩ := hx
  have hmem : (gafStageQ L.toLocalChartFamily L.zero 1).starProjection
      (Ĉ.toChain.E (φ (closedCellCenter 2))) ∈ Ĉ.edgeBase_EDP23 := by
    rw [hπ]
    exact hw
  exact ⟨φ (closedCellCenter 2), ⟨hmem, Or.inr ⟨(Ĉ.toChain.scale_pos _).2, hT⟩⟩, hπ⟩

end Gaf02ChainE

end Kernel

section FinalFamily

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

/-- **The base-level exactness on the final closed family** (D71-3: the chain lives on the
`LocalChartPacketsC14` projection of the final-family packet): the exact marker on `W₂`, the
equality of the marker conventions and the patch membership of `B₂`. -/
theorem edgeBase_exact_row_C14Z_EDP23
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw)
    (hΔ : 2 ≤ Δ) : type_of% (Ĉ.edgeBase_exact_row_EDP23 hΔ) :=
  Ĉ.edgeBase_exact_row_EDP23 hΔ

/-- **The whole fibre over every point of `B₂` on the final closed family.** -/
theorem edgeBase_fibre_disk_C14Z_EDP23
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw)
    (hΔ2 : 2 ≤ Δ) (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000)
    {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hw : w ∈ Ĉ.edgeBase_EDP23) :
    ∃ φ : ClosedCell 2 → X, IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, E3) ∞ φ ∧
      range φ = {x | (gafStageQ P.toLocalChartFamily P.zero 1).starProjection
          (Ĉ.toChain.E x) = w ∧ EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
            P.toLocalChartFamily P.zero (Ĉ.toChain.E x)) / Ĉ.toChain.scale x ≤ 4 * Δ} ∧
      range (φ ∘ cellBoundaryInclusion 2) = {x |
        (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (Ĉ.toChain.E x) = w ∧
          EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero
            (Ĉ.toChain.E x)) / Ĉ.toChain.scale x = 4 * Δ} :=
  Ĉ.edgeBase_fibre_disk_EDP23 hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 hw

end FinalFamily

namespace ClosedRegisterV4

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}

/-- `2 ≤ Δ` at every register (`Δ > 10⁶`, PR13). -/
theorem two_le_Δ_EDP23 (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) : 2 ≤ R.later.excl.Δ :=
  (by norm_num : (2 : ℝ) ≤ 10 ^ 6).trans ((le_max_left _ _).trans R.later.Δ_gt.le)

end ClosedRegisterV4

/-- **The base-level exactness at the closed rows' source of every register, on a tail** (final
family C14Z): on every closed standing sequence, at the strategy of
`exists_closedChainEZRowsSource_RGC`, every register has `ε_r, δ, Λ_z` such that for all large
members `m` there is a nonempty model on which, for every base point, the rows' source `S` with
`S.chain.x₀ = x₀` satisfies the base-level exactness row (exact marker on `W₂`, equality of the
marker conventions, patch membership of `B₂`). -/
theorem eventually_edgeBase_exact_rowsSourceZ_EDP23 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ClosedStrategyRefinesV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) ∧
      PartialClosedThresholdValidityV4Rows K A Wseq gseq (earlyDataSharedV4 K) T ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ, ∀ᶠ m in atTop,
        ∃ M : ClosedModel (Wseq m) (gseq m), Nonempty M.X ∧ ∀ x₀ : M.X,
          ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀ ∧
            type_of% (S.chain.toGaf02ChainE.edgeBase_exact_row_EDP23 R.two_le_Δ_EDP23) := by
  have key := exists_closedChainEZRowsSource_RGC K hK A hA Wseq gseq hf hg
  obtain ⟨T, hTU, hv, h1, h2, hR⟩ := key
  refine ⟨T, hTU, hv, fun R => ?_⟩
  exact (hR R).imp fun εr h => h.imp fun δ h => h.imp fun Λz ht =>
    eventually_atTop.mpr ⟨R.later.tail, fun m hm => (ht m hm).imp fun M hM =>
      ⟨hM.1, fun x₀ => (hM.2 x₀).imp fun S hS =>
        ⟨hS, by exact S.chain.toGaf02ChainE.edgeBase_exact_row_EDP23 R.two_le_Δ_EDP23⟩⟩⟩

section Dihedral

attribute [local instance] dihedralTinyMetricSpace_CHI

/-- **All premises of the base-level exactness hold at once** on the dihedral final-family fixture
(`Δ = 1200`): a chain with (JA) exists there and the row holds for it. The fixture's circle, edge
and slim families are EMPTY (stated), so `W₂ = ∅` and the clauses are vacuous on it — the known
acceptance gap (D71-7, D70-8). -/
theorem exists_edgeBase_exact_row_dihedralTiny_EDP23 (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainEJA
        (dihedralRowZ_CHI β₂ γc Lmax σs ζ h).toLocalChartPacketsC14D.toLocalChartPacketsC14
        Kj Ξ Γ S eg c cw (1 / 100000)),
      (dihedralRowZ_CHI β₂ γc Lmax σs ζ h).circle.centres = ∅ ∧
        (dihedralRowZ_CHI β₂ γc Lmax σs ζ h).edge.centres = ∅ ∧
        (dihedralRowZ_CHI β₂ γc Lmax σs ζ h).slim.centres = ∅ ∧
        type_of% (C.toGaf02ChainE.edgeBase_exact_row_EDP23 (by norm_num : (2 : ℝ) ≤ 1200)) := by
  exact (exists_gaf02ChainEJA_rowsZ_dihedralTiny_CHI Kj).imp fun _ h => h.imp fun _ h =>
    h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h =>
    h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h =>
    h.imp fun C _ => ⟨rfl, rfl, rfl,
      C.toGaf02ChainE.edgeBase_exact_row_EDP23 (by norm_num : (2 : ℝ) ≤ 1200)⟩

end Dihedral

end DifferentialGeometry.Geometry.Collapse
