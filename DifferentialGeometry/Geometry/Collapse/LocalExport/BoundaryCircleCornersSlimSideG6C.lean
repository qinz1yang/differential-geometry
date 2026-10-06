import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornersCornerCuspG6CApplications
import DifferentialGeometry.Topology.Ehresmann.SlimEndChartG6C

/-!
# G6c, slim ends: the side function of a NEW slim end (lane O-G6C, G2l)

`BoundaryGaf02ChainE.exists_slimEnd_side_G6C`: at the end `a = arc_j(e)` of an arc of `K₃` there is
a smooth (affine) `χ : H → ℝ` with `χ a = 0` and an open `N ∋ a` such that on `B₃ ∩ N`,
`K₃ = {χ ≥ 0}` and `χ = 0` only at `a`; every point of the slim fibre over `a` is a limit of points
of `X₃` with `χ ∘ f₃ < 0`, and `d(χ ∘ f₃) ≠ 0` along the slim fibre over `a` (slim chart
`WF.slim_chart`, `slimEnd_side_of_chart_G6C`).
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

/-- **The side function of a new slim end.** -/
theorem exists_slimEnd_side_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (j : Fin Kc.arcCount) (e : Bool) :
    ∃ χ : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ, ContDiff ℝ ∞ χ ∧
      χ (Kc.arc j (BoundaryCompactSlimChoiceV2.arcEnd_BIFc e)) = 0 ∧
      ∃ N : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)), IsOpen N ∧
        Kc.arc j (BoundaryCompactSlimChoiceV2.arcEnd_BIFc e) ∈ N ∧
        (∀ b ∈ Bs.base 2 ∩ N, (b ∈ Kc.K₃ ↔ 0 ≤ χ b)) ∧
        (∀ b ∈ Bs.base 2 ∩ N, χ b = 0 → b = Kc.arc j (BoundaryCompactSlimChoiceV2.arcEnd_BIFc e)) ∧
        (∀ p ∈ Bs.source 2,
          C.toChain.stageMap 2 p = Kc.arc j (BoundaryCompactSlimChoiceV2.arcEnd_BIFc e) →
          ∀ V ∈ 𝓝 p, ∃ q ∈ V, q ∈ Bs.source 2 ∧ C.toChain.stageMap 2 q ∈ N ∧
            χ (C.toChain.stageMap 2 q) < 0) ∧
        ∀ p ∈ Bs.source 2,
          C.toChain.stageMap 2 p = Kc.arc j (BoundaryCompactSlimChoiceV2.arcEnd_BIFc e) →
          mfderiv W.model 𝓘(ℝ, ℝ) (fun q => χ (C.toChain.stageMap 2 q)) p ≠ 0 := by
  set a := Kc.arc j (BoundaryCompactSlimChoiceV2.arcEnd_BIFc e) with hadef
  -- the arc reparametrized to start at `a`
  set τ : ℝ → ℝ := fun t => if e then 1 - t else t with hτdef
  have hτc : Continuous τ := by
    cases e
    · exact continuous_id
    · exact continuous_const.sub continuous_id
  have hτI : MapsTo τ (Icc 0 1) (Icc 0 1) := fun t ht => by
    cases e
    · exact ht
    · exact ⟨by simp only [hτdef, ↓reduceIte]; linarith [ht.2], by
        simp only [hτdef, ↓reduceIte]; linarith [ht.1]⟩
  have hτi : InjOn τ (Icc 0 1) := fun t _ t' _ h => by
    cases e
    · exact h
    · simp only [hτdef, ↓reduceIte] at h
      linarith
  have hτimg : τ '' Icc 0 1 = Icc 0 1 := by
    apply Subset.antisymm (image_subset_iff.mpr hτI)
    intro t ht
    cases e
    · exact ⟨t, ht, rfl⟩
    · refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
      simp only [hτdef, ↓reduceIte]
      ring
  set γ : ℝ → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) :=
    fun t => Kc.arc j (τ t) with hγdef
  have hγc : ContinuousOn γ (Icc 0 1) := (Kc.arc_smooth j).continuousOn.comp hτc.continuousOn hτI
  have hγi : InjOn γ (Icc 0 1) := fun t ht t' ht' h =>
    hτi ht ht' (Kc.arc_injOn j (hτI ht) (hτI ht') h)
  have hγimg : γ '' Icc 0 1 = Kc.arc j '' Icc 0 1 := by
    rw [show γ = Kc.arc j ∘ τ from rfl, image_comp, hτimg]
  have hγB : γ '' Icc 0 1 ⊆ Bs.base 2 := hγimg ▸ Kc.arc_subset_base j
  have hγ0 : γ 0 = a := by
    simp only [hγdef, hτdef, hadef, BoundaryCompactSlimChoiceV2.arcEnd_BIFc]
    cases e <;> simp
  -- the other arcs are far from `a`
  have hcl : ∀ k : {k : Fin Kc.arcCount // k ≠ j}, IsClosed (Kc.arc k.1 '' Icc 0 1) := fun k =>
    (isCompact_Icc.image_of_continuousOn (Kc.arc_smooth k.1).continuousOn).isClosed
  set N₀ := (⋃ k : {k : Fin Kc.arcCount // k ≠ j}, Kc.arc k.1 '' Icc 0 1)ᶜ with hN₀def
  have hN₀ : IsOpen N₀ := (isClosed_iUnion_of_finite hcl).isOpen_compl
  have hend : BoundaryCompactSlimChoiceV2.arcEnd_BIFc e ∈ Icc (0 : ℝ) 1 := by
    cases e <;> simp [BoundaryCompactSlimChoiceV2.arcEnd_BIFc]
  have haN₀ : a ∈ N₀ := by
    rw [hN₀def, mem_compl_iff, mem_iUnion]
    rintro ⟨k, hk⟩
    exact Set.disjoint_left.mp (Kc.arc_disjoint (Ne.symm k.2)) ⟨_, hend, rfl⟩ hk
  have hK : Kc.K₃ ∩ N₀ = γ '' Icc 0 1 ∩ N₀ := by
    rw [hγimg]
    ext b
    constructor
    · rintro ⟨hbK, hbN⟩
      obtain ⟨k, hk⟩ := mem_iUnion.mp hbK
      by_cases hkj : k = j
      · exact ⟨hkj ▸ hk, hbN⟩
      · exact absurd (mem_iUnion.mpr ⟨⟨k, hkj⟩, hk⟩) hbN
    · rintro ⟨hb, hbN⟩
      exact ⟨mem_iUnion.mpr ⟨j, hb⟩, hbN⟩
  have haB : a ∈ Bs.base 2 := Kc.arc_subset_base j ⟨_, hend, rfl⟩
  have hfd : ∀ p, MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) (C.toChain.stageMap 2) p :=
    fun p => (C.stageMap_contMDiff_BAUGD 2 p).mdifferentiableAt (by simp)
  rcases WF.slim_chart a haB with h | h
  · obtain ⟨σ, φ, O, h0, hσs, hσe, hσd, hO, hrσ, hφ, hr, hf⟩ := h
    obtain ⟨χ, hχs, hχa, N, hN, haN, hKN, hz, hout, hreg⟩ := slimEnd_side_of_chart_G6C h0 hσs hσe
      hσd hO hrσ hφ hr hf hγc hγi hγB hγ0 hN₀ haN₀ hK
    exact ⟨χ, hχs, hχa, N, hN, haN, hKN, hz, hout, fun p hp hpa => hreg p hp hpa (hfd p)⟩
  · obtain ⟨σ, φ, O, h0, hσs, hσe, hσd, hO, hrσ, hφ, hr, hf⟩ := h
    obtain ⟨χ, hχs, hχa, N, hN, haN, hKN, hz, hout, hreg⟩ := slimEnd_side_of_chart_G6C h0 hσs hσe
      hσd hO hrσ hφ hr hf hγc hγi hγB hγ0 hN₀ haN₀ hK
    exact ⟨χ, hχs, hχa, N, hN, haN, hKN, hz, hout, fun p hp hpa => hreg p hp hpa (hfd p)⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
