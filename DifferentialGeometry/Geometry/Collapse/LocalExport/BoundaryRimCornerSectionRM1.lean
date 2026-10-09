import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInteriorSectionRM1
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRimInteriorRM1
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornersVerticalConfigG6C

/-!
# BCF02 rim clauses, G2b: the corner section on the horizontal face (lane S-RIM81)

External review 81 (b). At a point `p` of the horizontal edge face `H_e = ∂M₂ ∩ X₂` on the rim
`T = 4Δ`, `face_complete` gives an active label `ℓ`, `local_single` makes the other labels positive
near `p`, `face_smooth` and `transverse` make `(h_ℓ ∘ f₂, T)` a submersion at the INTERIOR point `p`
onto `ℝ²`. The local section `s` of `(h_ℓ ∘ f₂, T)` (`exists_section_of_surjective_pair_RM1`) then
parametrizes a coordinate square `(u, T)` around `p` in which, below the rim (`T ≤ 4Δ`), `M₂` is
`{u ≥ 0}` with interior `{u > 0}` (`face_complete` through
`mem_interior_M₂_of_faces_pos_RM1`) and `{u < 0}` misses `M₂`.

* `BoundaryGaf02ChainE.exists_corner_section_RM1`: the section with the three clauses.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **The corner section** at a point of `H_e` on the rim: a continuous local section `s` of
`(h_ℓ ∘ f₂, T)` over an open `V ∋ (0, 4Δ)`, inside any neighbourhood `N` of `p` and the edge parent,
with `T (s y) = y.2`; below the rim a positive first coordinate gives an interior point of `M₂`
and a negative one leaves `M₂`. -/
theorem exists_corner_section_RM1 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) {Kc : BoundaryCompactSlimChoiceV2 Bs}
    (er : BoundaryRelativeEdgeRestrictionV2 Kc) {p : W.Carrier} (hpH : p ∈ Kc.horizontalFace)
    (hT : C.toChain.heightRatio p = 4 * Δ) {N : Set W.Carrier} (hN : N ∈ 𝓝 p) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧ ((0 : ℝ), 4 * Δ) ∈ V ∧ ∃ s : ℝ × ℝ → W.Carrier,
      ContinuousOn s V ∧
      (∀ y ∈ V, s y ∈ N ∧ s y ∈ Bs.edgeParent ∧ C.toChain.heightRatio (s y) = y.2) ∧
      (∀ y ∈ V, y.2 ≤ 4 * Δ → 0 < y.1 → s y ∈ interior Kc.M₂) ∧
      (∀ y ∈ V, y.2 ≤ 4 * Δ → y.1 < 0 → s y ∉ Kc.M₂) := by
  have hpX : p ∈ Bs.source 1 := hpH.2
  have hpU : p ∈ Bs.edgeParent := Bs.source_one_subset_edgeParent_BIFc hpX
  have hpM : p ∈ Kc.M₂ := Kc.isClosed_M₂_BCF.frontier_subset hpH.1
  obtain ⟨ℓ, hℓ⟩ := er.face_complete p hpH
  obtain ⟨Ol, hOlo, hpOl, hOl⟩ :=
    er.local_single (C.toChain.stageMap 1 p) ⟨p, ⟨hpM, hpX⟩, rfl⟩ ℓ hℓ
  have hint : W.model.IsInteriorPoint p :=
    (W.model.isInteriorPoint_iff_not_isBoundaryPoint p).mpr
      (not_isBoundaryPoint_of_mem_source_G6C WF hpX)
  have hf₂ : Continuous (C.toChain.stageMap 1) := (C.stageMap_contMDiff_BAUGD 1).continuous
  have hN' : N ∩ Bs.edgeParent ∩ C.toChain.stageMap 1 ⁻¹' Ol ∈ 𝓝 p :=
    inter_mem (inter_mem hN (Bs.parent.isOpen_edgeParent.mem_nhds hpU))
      ((hOlo.preimage hf₂).mem_nhds hpOl)
  have hu : ContMDiffAt W.model 𝓘(ℝ, ℝ) 1
      (fun q => er.faceFun ℓ (C.toChain.stageMap 1 q)) p :=
    (er.face_smooth ℓ p hpX hℓ).of_le (by simp)
  have hTs : ContMDiffAt W.model 𝓘(ℝ, ℝ) 1 C.toChain.heightRatio p :=
    (C.heightRatio_contMDiff_BAUGD p).of_le (by simp)
  obtain ⟨V, hV, hVp, s, hsc, hspec⟩ := exists_section_of_surjective_pair_RM1 hint hu hTs
    (er.transverse ℓ p hpX hℓ hT) hN'
  -- the points of the section below the rim lie in `X₂`, with the other labels positive
  have hq : ∀ y ∈ V, y.2 ≤ 4 * Δ → s y ∈ Bs.source 1 ∧
      ∀ ℓ', ℓ' ≠ ℓ → 0 < er.faceFun ℓ' (C.toChain.stageMap 1 (s y)) := by
    intro y hy hy2
    obtain ⟨⟨⟨-, hqU⟩, hqO⟩, hqu, hqT⟩ := hspec y hy
    have hqX : s y ∈ Bs.source 1 := by
      rw [Bs.parent.edgeParent_cut]
      exact ⟨hqU, show C.toChain.heightRatio (s y) ≤ 4 * Δ from hqT ▸ hy2⟩
    have hb : C.toChain.stageMap 1 (s y) ∈ Bs.base 1 :=
      Bs.image_eq 1 ▸ mem_image_of_mem _ hqX
    exact ⟨hqX, fun ℓ' hne => hOl ℓ' hne _ ⟨hqO, hb⟩⟩
  refine ⟨V, hV, ?_, s, hsc, fun y hy => ?_, fun y hy hy2 hy1 => ?_, fun y hy hy2 hy1 => ?_⟩
  · have h0 : (er.faceFun ℓ (C.toChain.stageMap 1 p), C.toChain.heightRatio p) =
        ((0 : ℝ), 4 * Δ) := by rw [hℓ, hT]
    exact h0 ▸ hVp
  · obtain ⟨⟨⟨hqN, hqU⟩, -⟩, -, hqT⟩ := hspec y hy
    exact ⟨hqN, hqU, hqT⟩
  · obtain ⟨hqX, hpos⟩ := hq y hy hy2
    refine er.mem_interior_M₂_of_faces_pos_RM1 hqX fun ℓ' => ?_
    by_cases hne : ℓ' = ℓ
    · subst hne
      rw [(hspec y hy).2.1]
      exact hy1
    · exact hpos ℓ' hne
  · intro hqM
    obtain ⟨hqX, -⟩ := hq y hy hy2
    have h1 := (er.mem_M₂_iff_faces_nonneg_RM1 hqX).mp hqM ℓ
    rw [(hspec y hy).2.1] at h1
    exact absurd h1 (not_le.mpr hy1)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
