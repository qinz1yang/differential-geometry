import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeWholeDiskEFE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRimCircle
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEGaf05Edge
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeMarkerConvention
import DifferentialGeometry.Geometry.Fibration.ActualStageChainFinalSubmersion
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeSublevel

/-!
# EDP04: the whole fibre of the final edge map is a smooth disk (binding to the base) and properness

Lane S-EDP-FDC, group G3 (EDP04 whole-disk binding, step D; draft 74 D74-11). On a chain
`Ĉ : Gaf02ChainE L …` of a family `L : LocalChartPacketsC14`
(`π₂E = (gafStageQ … 1).starProjection ∘ E`,
`T = A/s`, `W₂ = Ĉ.toChain.finalBase_BAS 1`):

* `Gaf02ChainE.edp04_fibre_disk_EFE`: over a point `w ∈ W₂ ∩ {marked k}` of an edge patch with
  `‖u_k(w)‖ < 4ΔR_k` the WHOLE fibre `{x : π₂E x = w, T x ≤ 4Δ}` is the range of a smooth embedding
  of `ClosedCell 2` (boundary circle onto the rim `{T = 4Δ}`). This is
  `Gaf02Chain.edp04_whole_disk_EFE`
  (E0 on the actual `Y_k`, level `a = κ_k(w)`) plus EDP04's last paragraph: `π₂E` on `Y_k` lands in
  `W₂ ∩ {marked k}` (`final_submersion_edge_BAS`), where `κ_k = R_k⁻¹u_k` is injective
  (`gaf05_edgeBase_chart_GAFD`), so `{g_k = a} ∩ Y_k = (π₂E)⁻¹(w) ∩ Y_k`; conversely every point of
  the fibre below `4Δ` lies in `Y_k` by EDP02's (ELoc) (`stageTwo_ratio_localization_FDC`).
* `Gaf02ChainE.edp04_fibre_disk_of_mem_EFE`: the same over `π₂E q₀` for any point `q₀` of the actual
  `X₂` (`v_k(π₂E q₀) > .9R_k`, `‖u_k(π₂E q₀)‖ < 4Δ v_k(π₂E q₀)`, `T q₀ ≤ 4Δ`): the marker is exactly
  `R_k` (`marker_eq_of_ratio_ge_EFC`), so no further hypothesis. Consumer on the final family:
  `Gaf02ChainE.edp04_fibre_disk_C14Z_EFE`.
* `Gaf02Chain.edgeSublevel_preimage_isCompact_EFE`: D74-11's `proper` from the actual sublevel
  preimage: `(π₂E)⁻¹(K) ∩ {T ≤ 4Δ}` is compact for compact `K` (closed in the compact `X`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

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
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

namespace Gaf02ChainE

/-- **EDP04: the whole fibre of the final edge map over a point of an edge patch is a smooth
disk.** -/
theorem edp04_fibre_disk_EFE
    {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz} (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000) (k : L.edge.finite_centres.toFinset)
    {w : BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)}
    (hw : w ∈ Ĉ.toChain.finalBase_BAS 1 ∩ markedCondition_BPRE
      (axisCoordCLM_BAS.comp (gafEdgeVector L.toLocalChartFamily L.zero k))
      (gafEdgeMarker L.toLocalChartFamily L.zero k) (ρ k.1) Δ)
    (hu : ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
      (.inr (.inr (.inl k))) w‖ < 4 * Δ * ρ k.1) :
    ∃ φ : ClosedCell 2 → X, IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, E3) ∞ φ ∧
      range φ = {x | (gafStageQ L.toLocalChartFamily L.zero 1).starProjection
          (Ĉ.toChain.E x) = w ∧ EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
            L.toLocalChartFamily L.zero (Ĉ.toChain.E x)) / Ĉ.toChain.scale x ≤ 4 * Δ} ∧
      range (φ ∘ cellBoundaryInclusion 2) = {x |
        (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x) = w ∧
          EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
            (Ĉ.toChain.E x)) / Ĉ.toChain.scale x = 4 * Δ} := by
  have hΔ0 : 0 < Δ := by linarith
  have hk : k.1 ∈ L.edge.centres := (Set.Finite.mem_toFinset _).mp k.2
  have hrk := hρ k.1
  have hmark : gafEdgeMarker L.toLocalChartFamily L.zero k w = ρ k.1 :=
    Ĉ.gaf05_edgeBase_marker_GAFD k w hw
  set a : ℝ := ((ρ k.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector L.toLocalChartFamily
    L.zero k)) w with ha_def
  have ha_eq : a = (ρ k.1)⁻¹ * EuclideanSpace.proj (0 : Fin 2)
      (blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
        (.inr (.inr (.inl k))) w) := rfl
  have ha : |a| < 4 * Δ := by
    rw [ha_eq, abs_mul, abs_inv, abs_of_pos hrk, inv_mul_lt_iff₀ hrk]
    exact (abs_proj_zero_le_norm_EFC _).trans_lt (by linarith)
  obtain ⟨φ, hφ, hr, hb'⟩ := Ĉ.toChain.edp04_whole_disk_EFE (Ĉ.rough.cw_nonneg 0)
    (Ĉ.rough.sigma_le 0).le hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 hk ha
  -- one point `x` with `T x ≤ 4Δ`: being in `Y_k` with `g_k = a` is the same as `π₂E x = w`
  have hiff : ∀ x : X, EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily
      L.zero (Ĉ.toChain.E x)) / Ĉ.toChain.scale x ≤ 4 * Δ →
      ((x ∈ ball k.1 (100 * Δ * ρ k.1) ∧ |L.edge.coord k.1 x| < 5 * Δ ∧
        L.edge.smoothing x / ρ x < 5 * Δ ∧
        EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector L.toLocalChartFamily L.zero k
          (Ĉ.toChain.E x)) / ρ k.1 = a) ↔
        (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x) = w) := by
    intro x hTx
    constructor
    · rintro ⟨hp, hη, ht, hga⟩
      have hmem := Ĉ.toChain.final_submersion_edge_BAS Ĉ.rough k hp hη ht
      refine ((Ĉ.gaf05_edgeBase_chart_GAFD k).2.1).injOn hmem.1 hw ?_
      have hvec : blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl k))) ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection
            (Ĉ.toChain.E x)) = blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero
              => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x) :=
        gafStageQ_edgeVector_FDC L.toLocalChartPackets k (Ĉ.toChain.E x)
      change (ρ k.1)⁻¹ * EuclideanSpace.proj (0 : Fin 2) (blockVectorCLM (V := fun _ :
        CGPTag L.toLocalChartFamily L.zero => ℝ²) (.inr (.inr (.inl k)))
          ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x))) = a
      rw [hvec, ← hga, div_eq_inv_mul]
      rfl
    · intro hxw
      have hv : 9 / 10 * ρ k.1 < blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily
          L.zero => ℝ²) (.inr (.inr (.inl k))) ((gafStageQ L.toLocalChartFamily L.zero 1
          ).starProjection
            (Ĉ.toChain.E x)) := by
        rw [hxw]
        exact hw.2.1
      have hu' : ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl k))) ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection
            (Ĉ.toChain.E x))‖ < 4 * Δ * blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily
              L.zero => ℝ²) (.inr (.inr (.inl k))) ((gafStageQ L.toLocalChartFamily L.zero 1
          ).starProjection
                (Ĉ.toChain.E x)) := by
        rw [hxw]
        change ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl k))) w‖ < 4 * Δ * gafEdgeMarker L.toLocalChartFamily L.zero k w
        rw [hmark]
        exact hu
      obtain ⟨hball, hη, ht, -⟩ := Ĉ.toChain.stageTwo_ratio_localization_FDC hΔ2 k hv hu'
        (Or.inr ⟨(Ĉ.toChain.scale_pos x).2, hTx⟩)
      refine ⟨hball, by linarith, by linarith, ?_⟩
      have hvec : blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl k))) ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection
            (Ĉ.toChain.E x)) = blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero
              => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x) :=
        gafStageQ_edgeVector_FDC L.toLocalChartPackets k (Ĉ.toChain.E x)
      rw [hxw] at hvec
      change EuclideanSpace.proj (0 : Fin 2) (blockVectorCLM (V := fun _ :
        CGPTag L.toLocalChartFamily L.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x)) /
          ρ k.1 = a
      rw [← hvec, ha_eq, div_eq_inv_mul]
  refine ⟨φ, hφ, ?_, ?_⟩
  · rw [hr]
    ext x
    constructor
    · rintro ⟨⟨hp, hη, ht⟩, hga, hT⟩
      exact ⟨(hiff x hT).mp ⟨hp, hη, ht, hga⟩, hT⟩
    · rintro ⟨hxw, hT⟩
      obtain ⟨hp, hη, ht, hga⟩ := (hiff x hT).mpr hxw
      exact ⟨⟨hp, hη, ht⟩, hga, hT⟩
  · rw [hb']
    ext x
    constructor
    · rintro ⟨⟨hp, hη, ht⟩, hga, hT⟩
      exact ⟨(hiff x hT.le).mp ⟨hp, hη, ht, hga⟩, hT⟩
    · rintro ⟨hxw, hT⟩
      obtain ⟨hp, hη, ht, hga⟩ := (hiff x hT.le).mpr hxw
      exact ⟨⟨hp, hη, ht⟩, hga, hT⟩

/-- **EDP04 over a point of the actual `X₂`**: for `q₀` with `π₂E q₀ ∈ W₂`, a witnessing edge index
(`v_k(π₂E q₀) > .9R_k`, `‖u_k(π₂E q₀)‖ < 4Δ v_k(π₂E q₀)`) and `T q₀ ≤ 4Δ` (i.e. `q₀ ∈ X₂`), the
WHOLE fibre `{x : π₂E x = π₂E q₀, T x ≤ 4Δ}` is a smooth disk, boundary circle onto the rim. -/
theorem edp04_fibre_disk_of_mem_EFE
    {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz} (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000) {q₀ : X}
    (hwit : ∃ k : L.edge.finite_centres.toFinset,
      9 / 10 * ρ k.1 < blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
        (.inr (.inr (.inl k))) ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection
          (Ĉ.toChain.E q₀)) ∧
      ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
        (.inr (.inr (.inl k))) ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection
          (Ĉ.toChain.E q₀))‖ <
        4 * Δ * blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl k))) ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection
            (Ĉ.toChain.E q₀)))
    (hT : EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
      (Ĉ.toChain.E q₀)) / Ĉ.toChain.scale q₀ ≤ 4 * Δ) :
    ∃ φ : ClosedCell 2 → X, IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, E3) ∞ φ ∧
      range φ = {x | (gafStageQ L.toLocalChartFamily L.zero 1).starProjection
          (Ĉ.toChain.E x) = (gafStageQ L.toLocalChartFamily L.zero 1).starProjection
            (Ĉ.toChain.E q₀) ∧ EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
              L.toLocalChartFamily L.zero (Ĉ.toChain.E x)) / Ĉ.toChain.scale x ≤ 4 * Δ} ∧
      range (φ ∘ cellBoundaryInclusion 2) = {x |
        (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x) =
          (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E q₀) ∧
          EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
            (Ĉ.toChain.E x)) / Ĉ.toChain.scale x = 4 * Δ} := by
  obtain ⟨k, hv, hu⟩ := hwit
  have hV : q₀ ∈ {p | L.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < Ĉ.toChain.scale p ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
        (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ} :=
    Or.inr ⟨(Ĉ.toChain.scale_pos q₀).2, hT⟩
  obtain ⟨hball, hη, ht, -⟩ := Ĉ.toChain.stageTwo_ratio_localization_FDC hΔ2 k hv hu hV
  have hv' := hv
  have hu' := hu
  rw [gafStageQ_edgeMarker_FDC] at hv'
  rw [gafStageQ_edgeVector_FDC, gafStageQ_edgeMarker_FDC] at hu'
  have hmk : blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
      (.inr (.inr (.inl k))) (Ĉ.toChain.E q₀) = ρ k.1 :=
    Ĉ.marker_eq_of_ratio_ge_EFC hΔ2 k hv'.le hu' hV
  have hmem := Ĉ.toChain.final_submersion_edge_BAS Ĉ.rough k hball (by linarith)
    (by change L.edge.smoothing q₀ / ρ q₀ < 5 * Δ; linarith)
  refine Ĉ.edp04_fibre_disk_EFE hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 k hmem.1 ?_
  rw [gafStageQ_edgeVector_FDC]
  rw [hmk] at hu'
  exact hu'


end Gaf02ChainE

namespace Gaf02Chain

/-- **Properness over the height sublevel (D74-11's `proper`, chain form)**: for a compact `K` of
the block space, `(π₂E)⁻¹(K) ∩ {T ≤ 4Δ}` is compact (closed in the compact `X`; no hypothesis
that `W₂` or `X₂` be compact). -/
theorem edgeSublevel_preimage_isCompact_EFE
    {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz} (C : Gaf02Chain L.toLocalChartPackets Kj Ξ Γ S eg c cw)
    {K' : Set (BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²))}
    (hK : IsCompact K') :
    IsCompact ({x | (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (C.E x) ∈ K'} ∩
      {x | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
        (C.E x)) / C.scale x ≤ 4 * Δ}) := by
  have hE := C.stage_smooth.2.2
  have hπ : Continuous (fun x => (gafStageQ L.toLocalChartFamily L.zero 1).starProjection
      (C.E x)) := (gafStageQ L.toLocalChartFamily L.zero 1).starProjection.continuous.comp
    hE.continuous
  have hT : Continuous (fun x => EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
      L.toLocalChartFamily L.zero (C.E x)) / C.scale x) := (C.final_smooth_EDPE).2.2.2.1.continuous
  exact ((hK.isClosed.preimage hπ).inter (isClosed_le hT continuous_const)).isCompact

end Gaf02Chain


/-- **Consumer on the final closed family** (`LocalChartPacketsC14Z`): over every point of the
actual `X₂`, the whole fibre of `π₂E` below `4Δ` is a smooth disk. -/
theorem Gaf02ChainE.edp04_fibre_disk_C14Z_EFE
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw)
    (hΔ2 : 2 ≤ Δ) (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000) {q₀ : X}
    (hwit : ∃ k : P.edge.finite_centres.toFinset,
      9 / 10 * ρ k.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl k))) ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
          (Ĉ.toChain.E q₀)) ∧
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl k))) ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
          (Ĉ.toChain.E q₀))‖ <
        4 * Δ * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
            (Ĉ.toChain.E q₀)))
    (hT : EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero
      (Ĉ.toChain.E q₀)) / Ĉ.toChain.scale q₀ ≤ 4 * Δ) :
    ∃ φ : ClosedCell 2 → X, IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, E3) ∞ φ ∧
      range φ = {x | (gafStageQ P.toLocalChartFamily P.zero 1).starProjection
          (Ĉ.toChain.E x) = (gafStageQ P.toLocalChartFamily P.zero 1).starProjection
            (Ĉ.toChain.E q₀) ∧ EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
              P.toLocalChartFamily P.zero (Ĉ.toChain.E x)) / Ĉ.toChain.scale x ≤ 4 * Δ} ∧
      range (φ ∘ cellBoundaryInclusion 2) = {x |
        (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (Ĉ.toChain.E x) =
          (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (Ĉ.toChain.E q₀) ∧
          EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero
            (Ĉ.toChain.E x)) / Ĉ.toChain.scale x = 4 * Δ} :=
  Ĉ.edp04_fibre_disk_of_mem_EFE hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 hwit hT

end DifferentialGeometry.Geometry.Collapse
