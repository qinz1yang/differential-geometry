import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRatio
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRemainder
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdpHeight
import DifferentialGeometry.Topology.Manifold.LocalExtrema
import DifferentialGeometry.Topology.Maps.RelativeInteriorRemoval

/-!
# EDP02 / FDC03: the ambient interior of the actual `X₂` is `{T < 4Δ}` on the witnessed set

Blueprint `master207B.tex`, EDP02 (B:6748–6775: "(ED) `X₂ = (π₂E)⁻¹(B₂) ∩ V`", "all original closed
smaller sets `{|η_i| ≤ 3.5Δ, t ≤ 3.5Δ}` lie in the ambient interior of `X₂`") and FDC03
(B:7341–7344: "For a point of `M^edge` the relative interior in (Last) is characterized by
`T < 4Δ`"), for an enhanced chain `Ĉ : Gaf02ChainE L` (conventions of lanes C14-EDP-E / C14-FDCb:
`A = proj₀(gafHeightVector E)`, `s = C.scale`, `T = A/s`, `W₂ = C.finalBase_BAS 1`, `B₂` the
FULL-norm ratio set, `V` the union of (ED)).

* `Gaf02ChainE.height_lt_of_mem_interior_EFC`: on ANY set `Y` whose points satisfy `T ≤ 4Δ` and a
  ratio condition `v_k(E y) > .9R_k`, `|u_k(E y)| < 4Δ v_k(E y)`, an interior point has
  `T < 4Δ`. At `T = 4Δ`, (ELoc) (`ratio_localization_FDC`) and GAF05's plateau put the point in
  `Y_k` with `|g_k| < 4Δ`, so EDP-E's rim rank (`edge_vertical_rank_EDPE`) gives `dT ≠ 0`,
  contradicting the local maximum of `T` on the interior.
* `Gaf02ChainE.interior_edgeBase_eq_EFC`: `int X₂ = {T < 4Δ} ∩ {∃k, v_k(E) = R_k, |u_k(E)| < 4ΔR_k}`
  (= lane C14-FDCb's open edge candidate `X₂°`), for the ACTUAL `X₂` (with `W₂`).
* `Gaf02ChainE.smaller_set_interior_X2_EFC`: EDP02's interior clause for the actual `X₂`.
* `mem_relInterior_iff_of_mem_interior_EFC` (with `interior_edgeBase_eq_EFC`): at a point of the
  ambient interior of `M₂`, membership in `int_{M₂}(M₂ ∩ X₂)` is `x ∈ X₂, T(x) < 4Δ` (FDC03's
  characterization away from `∂M₂`; at the horizontal faces it needs EDP05's face charts).

Numeric hypotheses (parameters only, as `edge_vertical_rank_EDPE`): `Δ ≥ 2`, `c₃ < 10⁻⁵`,
`κΔ < 10⁻⁶`, `0 ≤ ε < 1`, `0 < γc ≤ 1/100`, `βc ≤ 10⁻⁵`; `0 ≤ c_w(1)`, `Σ₁ ≤ Ξ₁/10⁴` come from the
rough data `Ĉ.rough`.
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

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- `|v₀| ≤ ‖v‖` in the plane. -/
theorem abs_proj_zero_le_norm_EFC (v : ℝ²) : |EuclideanSpace.proj (0 : Fin 2) v| ≤ ‖v‖ := by
  have h := PiLp.norm_apply_le v (0 : Fin 2)
  rw [Real.norm_eq_abs] at h
  exact h

/-- **Relative interior at an ambient interior point**: if `x ∈ int M₂`, then
`x ∈ int_{M₂}(M₂ ∩ X')` iff `x ∈ int X'`. -/
theorem mem_relInterior_iff_of_mem_interior_EFC {M : Type*} [TopologicalSpace M] {M₂ X' : Set M}
    {x : M} (hx : x ∈ interior M₂) :
    x ∈ Subtype.val '' interior (Subtype.val ⁻¹' (M₂ ∩ X') : Set M₂) ↔ x ∈ interior X' := by
  rw [DifferentialGeometry.Topology.mem_image_interior_preimage_val_iff]
  constructor
  · rintro ⟨-, O, hO, hxO, hOA⟩
    refine mem_interior.mpr ⟨O ∩ interior M₂, fun y hy => (hOA ⟨hy.1,
      interior_subset hy.2⟩).2, hO.inter isOpen_interior, hxO, hx⟩
  · intro hxX
    exact ⟨interior_subset hx, interior X', isOpen_interior, hxX,
      fun y hy => ⟨hy.2, interior_subset hy.1⟩⟩

namespace Gaf02ChainE

/-- **An interior point of a ratio set below the rim has `T < 4Δ`** (EDP04's rank at `T = 4Δ`
excludes a local maximum of `T`). -/
theorem height_lt_of_mem_interior_EFC
    {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz} (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ : 2 ≤ Δ) (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000) {Y : Set X}
    (hY : ∀ y ∈ Y, EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
        (Ĉ.toChain.E y)) / Ĉ.toChain.scale y ≤ 4 * Δ ∧
      ∃ k : L.edge.finite_centres.toFinset,
        9 / 10 * ρ k.1 < blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl k))) (Ĉ.toChain.E y) ∧
        ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl k))) (Ĉ.toChain.E y)‖ <
          4 * Δ * blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k))) (Ĉ.toChain.E y))
    {x : X} (hx : x ∈ interior Y) :
    EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
      (Ĉ.toChain.E x)) / Ĉ.toChain.scale x < 4 * Δ := by
  have hT := (hY x (interior_subset hx)).1
  obtain ⟨k, hv, hu⟩ := (hY x (interior_subset hx)).2
  rcases lt_or_eq_of_le hT with hlt | hT4
  · exact hlt
  exfalso
  have hV : x ∈ {p | L.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < Ĉ.toChain.scale p ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
        (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ} :=
    Or.inr ⟨(Ĉ.toChain.scale_pos x).2, hT⟩
  obtain ⟨hball, hη, ht, -⟩ := Ĉ.toChain.ratio_localization_FDC hΔ k hv hu hV
  have hmk : blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
      (.inr (.inr (.inl k))) (Ĉ.toChain.E x) = ρ k.1 :=
    Ĉ.gaf05_edge_plateau_G47 k hball (by linarith)
      (by change L.edge.smoothing x / ρ x < 6 * Δ; linarith)
  have hrk := hρ k.1
  have hk := (Set.Finite.mem_toFinset _).mp k.2
  have hg : |EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector L.toLocalChartFamily L.zero
      ⟨k.1, (Set.Finite.mem_toFinset _).mpr hk⟩ (Ĉ.toChain.E x)) / ρ k.1| < 4 * Δ := by
    rw [abs_div, abs_of_pos hrk, div_lt_iff₀ hrk]
    have h1 := abs_proj_zero_le_norm_EFC (blockVectorCLM (V := fun _ : CGPTag
      L.toLocalChartFamily L.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x))
    rw [hmk] at hu
    exact lt_of_le_of_lt h1 hu
  have hR := Ĉ.toChain.edge_vertical_rank_EDPE (L := L) (Ĉ.rough.cw_nonneg 0)
    (Ĉ.rough.sigma_le 0).le hc hϑ hε0 hε hγc hγc1 hβc1 hk x hball (by linarith) (by linarith)
    hg hT4
  obtain ⟨W, hW⟩ := hR.2.2.2.2 id 1 (hasDerivAt_id _) one_ne_zero ((0 : ℝ), (1 : ℝ))
  have hW2 : mvfderiv 𝓘(ℝ, E3) (fun z => EuclideanSpace.proj (0 : Fin 2)
      (gafHeightVector L.toLocalChartFamily L.zero (Ĉ.toChain.E z)) / Ĉ.toChain.scale z) x W =
      1 := congrArg Prod.snd hW
  have hmax : IsLocalMax (fun z => EuclideanSpace.proj (0 : Fin 2)
      (gafHeightVector L.toLocalChartFamily L.zero (Ĉ.toChain.E z)) / Ĉ.toChain.scale z) x := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    rw [hT4]
    exact (hY y (interior_subset hy)).1
  rw [hmax.mvfderiv_eq_zero (I := 𝓘(ℝ, E3)) BoundarylessManifold.isInteriorPoint] at hW2
  exact zero_ne_one hW2

/-- The points of the actual `X₂` satisfy the hypotheses of `height_lt_of_mem_interior_EFC`. -/
theorem edgeBase_ratio_EFC
    {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz} (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) {y : X}
    (hy : y ∈ {x | (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x) ∈
        Ĉ.toChain.finalBase_BAS 1 ∧
        ∃ k : L.edge.finite_centres.toFinset,
          9 / 10 * ρ k.1 < blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x)) ∧
          ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x))‖ <
          4 * Δ * blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x))} ∩
      ({p | L.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < Ĉ.toChain.scale p ∧
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
          (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ})) :
    EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
        (Ĉ.toChain.E y)) / Ĉ.toChain.scale y ≤ 4 * Δ ∧
      ∃ k : L.edge.finite_centres.toFinset,
        9 / 10 * ρ k.1 < blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl k))) (Ĉ.toChain.E y) ∧
        ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl k))) (Ĉ.toChain.E y)‖ <
          4 * Δ * blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k))) (Ĉ.toChain.E y) := by
  have hV := hy.2
  rw [Ĉ.toChain.vertical_eq_FDC] at hV
  obtain ⟨k, hv, hu⟩ := hy.1.2
  rw [gafStageQ_edgeMarker_FDC] at hv hu
  rw [gafStageQ_edgeVector_FDC] at hu
  exact ⟨hV, k, hv, hu⟩

/-- **The ambient interior of the actual `X₂`** (EDP02 / FDC03, ambient form): with
`X₂ = (π₂E)⁻¹(B₂) ∩ V` (`W₂ = C.finalBase_BAS 1`),
`int X₂ = {T < 4Δ} ∩ {x | ∃ k, v_k(E x) = R_k, |u_k(E x)| < 4ΔR_k}`. -/
theorem interior_edgeBase_eq_EFC
    {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz} (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ : 2 ≤ Δ) (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000) :
    interior ({x | (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x) ∈
        Ĉ.toChain.finalBase_BAS 1 ∧
        ∃ k : L.edge.finite_centres.toFinset,
          9 / 10 * ρ k.1 < blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x)) ∧
          ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x))‖ <
          4 * Δ * blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x))} ∩
      ({p | L.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < Ĉ.toChain.scale p ∧
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
          (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ})) =
    {x | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
        (Ĉ.toChain.E x)) / Ĉ.toChain.scale x < 4 * Δ} ∩
      {x | ∃ k : L.toLocalChartFamily.edge.finite_centres.toFinset,
        blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl k))) (Ĉ.toChain.E x) = ρ k.1 ∧
        ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl k))) (Ĉ.toChain.E x)‖ < 4 * Δ * ρ k.1} := by
  apply Subset.antisymm
  · intro x hx
    have hxT := Ĉ.height_lt_of_mem_interior_EFC hΔ hc hϑ hε0 hε hγc hγc1 hβc1
      (fun y hy => Ĉ.edgeBase_ratio_EFC hy) hx
    obtain ⟨hT, k, hv, hu⟩ := Ĉ.edgeBase_ratio_EFC (interior_subset hx)
    have hV : x ∈ {p | L.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < Ĉ.toChain.scale p ∧
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
          (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ} :=
      Or.inr ⟨(Ĉ.toChain.scale_pos x).2, hT⟩
    obtain ⟨hball, hη, ht, -⟩ := Ĉ.toChain.ratio_localization_FDC hΔ k hv hu hV
    have hmk : blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
        (.inr (.inr (.inl k))) (Ĉ.toChain.E x) = ρ k.1 :=
      Ĉ.gaf05_edge_plateau_G47 k hball (by linarith)
        (by change L.edge.smoothing x / ρ x < 6 * Δ; linarith)
    rw [hmk] at hu
    exact ⟨hxT, k, hmk, hu⟩
  · refine interior_maximal (fun x hx => ?_) Ĉ.isOpen_edgeCandidate_FDC
    obtain ⟨hxT, k, hv, hu⟩ := hx
    have hxT' : EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
        (Ĉ.toChain.E x)) / Ĉ.toChain.scale x < 4 * Δ := hxT
    have hV : x ∈ {p | L.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < Ĉ.toChain.scale p ∧
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
          (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ} :=
      Or.inr ⟨(Ĉ.toChain.scale_pos x).2, hxT'.le⟩
    obtain ⟨hW, h9, h4⟩ := Ĉ.toChain.stageTwo_mem_base_FDC k hv hu hV
    exact ⟨⟨hW, k, h9, h4⟩, hV⟩

/-- **The open edge candidate lies in the interior of the actual `X₂`** (no numeric hypothesis):
`X₂° = {T < 4Δ} ∩ {∃ k, v_k(E) = R_k, |u_k(E)| < 4ΔR_k}` is open and contained in `X₂`. -/
theorem edgeCandidate_subset_interior_EFC
    {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz} (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) :
    {x | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
        (Ĉ.toChain.E x)) / Ĉ.toChain.scale x < 4 * Δ} ∩
      {x | ∃ k : L.toLocalChartFamily.edge.finite_centres.toFinset,
        blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl k))) (Ĉ.toChain.E x) = ρ k.1 ∧
        ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl k))) (Ĉ.toChain.E x)‖ < 4 * Δ * ρ k.1} ⊆
    interior ({x | (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x) ∈
        Ĉ.toChain.finalBase_BAS 1 ∧
        ∃ k : L.edge.finite_centres.toFinset,
          9 / 10 * ρ k.1 < blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x)) ∧
          ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x))‖ <
          4 * Δ * blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x))} ∩
      ({p | L.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < Ĉ.toChain.scale p ∧
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
          (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ})) := by
  refine interior_maximal (fun x hx => ?_) Ĉ.isOpen_edgeCandidate_FDC
  obtain ⟨hxT, k, hv, hu⟩ := hx
  have hxT' : EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
      (Ĉ.toChain.E x)) / Ĉ.toChain.scale x < 4 * Δ := hxT
  have hV : x ∈ {p | L.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < Ĉ.toChain.scale p ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
        (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ} :=
    Or.inr ⟨(Ĉ.toChain.scale_pos x).2, hxT'.le⟩
  obtain ⟨hW, h9, h4⟩ := Ĉ.toChain.stageTwo_mem_base_FDC k hv hu hV
  exact ⟨⟨hW, k, h9, h4⟩, hV⟩

/-- **EDP02's interior clause for the actual `X₂`** (B:6768–6770, with `W₂`):
`{|η_k| ≤ 3.5Δ, t ≤ 3.5Δ} ∩ U_k ⊆ int X₂`. -/
theorem smaller_set_interior_X2_EFC
    {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz} (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw)
    (k : L.toLocalChartFamily.edge.finite_centres.toFinset) {x : X}
    (hball : x ∈ ball k.1 (100 * Δ * ρ k.1)) (hη : |L.edge.coord k.1 x| ≤ 35 / 10 * Δ)
    (ht : L.edge.smoothing x / ρ x ≤ 35 / 10 * Δ) :
    x ∈ interior ({x | (gafStageQ L.toLocalChartFamily L.zero 1).starProjection
          (Ĉ.toChain.E x) ∈ Ĉ.toChain.finalBase_BAS 1 ∧
        ∃ k : L.edge.finite_centres.toFinset,
          9 / 10 * ρ k.1 < blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x)) ∧
          ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x))‖ <
          4 * Δ * blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x))} ∩
      ({p | L.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < Ĉ.toChain.scale p ∧
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
          (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ})) := by
  have h := Ĉ.smaller_set_interior_FDC k hball hη ht
  rw [Ĉ.isOpen_edgeCandidate_FDC.interior_eq] at h
  exact Ĉ.edgeCandidate_subset_interior_EFC h

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
