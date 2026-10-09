import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeSlimFunBG4
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornersInteriorConfigG6C

/-!
# BCF02 G4, group G5a: the slim cut, seen from the edge base (lane S-BCF02-G4)

The removed slim part `int_{M₁} S` (with `S = X₃ ∩ f₃⁻¹(K₃ ∩ D₃)`, `K₃ = ⋃ arcs`) is, over the edge
region `X₂`, exactly the preimage `f₃⁻¹(⋃ γ_j((0, 1)))` of the open arcs:

* `exists_open_avoid_other_arcs_BG4`: a point of an arc has an open neighbourhood missing the other
  arcs (finitely many disjoint compact arcs);
* `mem_relInterior_of_arc_interior_BG4` (S1): a point `p ∈ M₁ ∩ X₃` with `f₃ p = γ_j t`,
  `t ∈ (0, 1)`, lies in `int_{M₁} S` (the base points of `B₃` near `γ_j t` are arc points);
* `not_arcEnd_of_mem_relInterior_BG4` (S2): a point of `int_{M₁} S` does not lie over an end of an
  arc (the end of an arc is not interior in `B₃`; `Kc.faces_subset` on `∂M₁`, openness of `f₃` on
  `int M₁`);
* `exists_arc_interior_of_mem_relInterior_BG4` (S3): a point of `int_{M₁} S` lies over `γ_j t`,
  `t ∈ (0, 1)`.
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

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

namespace BoundaryGaf02ChainE

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **A point of an arc has an open neighbourhood missing the other arcs.** -/
theorem exists_open_avoid_other_arcs_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Kc : BoundaryCompactSlimChoiceV2 Bs) (j : Fin Kc.arcCount) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ N : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)), IsOpen N ∧
      Kc.arc j t ∈ N ∧ ∀ k, k ≠ j → Disjoint N (Kc.arc k '' Icc 0 1) := by
  have hcomp : IsCompact (⋃ k : {k : Fin Kc.arcCount // k ≠ j}, Kc.arc k.1 '' Icc 0 1) :=
    isCompact_iUnion fun k => isCompact_Icc.image_of_continuousOn (Kc.arc_smooth k.1).continuousOn
  refine ⟨(⋃ k : {k : Fin Kc.arcCount // k ≠ j}, Kc.arc k.1 '' Icc 0 1)ᶜ,
    hcomp.isClosed.isOpen_compl, ?_, ?_⟩
  · intro hmem
    obtain ⟨k, hk⟩ := mem_iUnion.mp hmem
    obtain ⟨t', ht', htt⟩ := hk
    exact Set.disjoint_left.mp (Kc.arc_disjoint (Ne.symm k.2)) ⟨t, ht, rfl⟩ ⟨t', ht', htt⟩
  · intro k hk
    refine Set.disjoint_left.mpr fun z hz hzk => hz (mem_iUnion.mpr ⟨⟨k, hk⟩, hzk⟩)

/-- **(S1)** A point of `M₁ ∩ X₃` over an interior point of an arc lies in `int_{M₁} S`. -/
theorem mem_relInterior_of_arc_interior_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (j : Fin Kc.arcCount) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {p : W.Carrier}
    (hpX : p ∈ Bs.source 2) (hpM : p ∈ C.toChain.M₁_BIFc)
    (hpt : C.toChain.stageMap 2 p = Kc.arc j t) :
    p ∈ relInterior_BIF C.toChain.M₁_BIFc Kc.piece := by
  obtain ⟨ℓ, V, δ, hV, hy, hδ, -, -, hcls, -, -⟩ := C.slim_point_datum_BG4 WF Kc j
    (t₀ := t) ⟨ht.1.le, ht.2.le⟩ (δ₀ := 1) one_pos
  have hf₃ : Continuous (C.toChain.stageMap 2) := (C.stageMap_contMDiff_BAUGD 2).continuous
  have hU : IsOpen (Bs.source 2 ∩ C.toChain.stageMap 2 ⁻¹' V) :=
    (Bs.isOpen_source 2 (by decide)).inter (hV.preimage hf₃)
  have harc : ∀ z ∈ Bs.base 2 ∩ V, z ∈ Kc.arc j '' Icc 0 1 := by
    intro z hz
    rcases hcls z hz with h | ⟨t', ht', -, -, hzt, -⟩ | ⟨-, ⟨h1, -⟩ | ⟨h1, -⟩⟩
    · exact ⟨t, ⟨ht.1.le, ht.2.le⟩, h.symm⟩
    · exact ⟨t', ht', hzt.symm⟩
    · exfalso
      linarith [ht.1]
    · exfalso
      linarith [ht.2]
  refine mem_relInterior_iff_BCF.mpr ⟨hpM, _, hU, ⟨hpX, by rw [mem_preimage, hpt]; exact hy⟩, ?_⟩
  rintro r ⟨⟨hrX, hrV⟩, hrM⟩
  have hrB : C.toChain.stageMap 2 r ∈ Bs.base 2 := Bs.image_eq 2 ▸ mem_image_of_mem _ hrX
  have hK : C.toChain.stageMap 2 r ∈ Kc.K₃ := mem_iUnion.mpr ⟨j, harc _ ⟨hrB, hrV⟩⟩
  exact ⟨hrX, hK, ⟨r, ⟨hrM, hrX⟩, rfl⟩⟩

/-- **(S2)** A point of `int_{M₁} S` does not lie over an end of an arc. -/
theorem not_arcEnd_of_mem_relInterior_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    {p : W.Carrier} (hpX : p ∈ Bs.source 2) (hpM : p ∈ C.toChain.M₁_BIFc)
    (hrel : p ∈ relInterior_BIF C.toChain.M₁_BIFc Kc.piece) (j : Fin Kc.arcCount) {e : ℝ}
    (he : e = 0 ∨ e = 1) : C.toChain.stageMap 2 p ≠ Kc.arc j e := by
  intro heq
  have he1 : e ∈ Icc (0 : ℝ) 1 := by
    rcases he with rfl | rfl
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
  -- a neighbourhood of `f₃ p` in `B₃` inside `K₃`
  obtain ⟨N', hN', hyN', hN'K⟩ : ∃ N' : Set (BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count)), IsOpen N' ∧ C.toChain.stageMap 2 p ∈ N' ∧
      ∀ z ∈ N' ∩ Bs.base 2, z ∈ Kc.K₃ := by
    by_cases hfr : p ∈ frontier C.toChain.M₁_BIFc
    · have hmem := Kc.faces_subset ⟨p, ⟨hfr, hpX⟩, rfl⟩
      obtain ⟨-, N', hN', hyN', hsub⟩ := mem_relInterior_iff_BCF.mp hmem
      exact ⟨N', hN', hyN', fun z hz => hsub hz⟩
    · obtain ⟨-, U, hU, hpU, hUS⟩ := mem_relInterior_iff_BCF.mp hrel
      have hint : p ∈ interior C.toChain.M₁_BIFc := by
        rw [← self_sdiff_frontier]
        exact ⟨hpM, hfr⟩
      obtain ⟨V, hV, hpV, hVimg⟩ := C.exists_open_nbhd_image_slim_BG4 WF
        (hU.inter isOpen_interior) hpX ⟨hpU, hint⟩
      refine ⟨V, hV, hpV, fun z hz => ?_⟩
      obtain ⟨r, ⟨hrX, hrU⟩, rfl⟩ := hVimg ⟨hz.1, hz.2⟩
      exact (hUS ⟨hrU.1, interior_subset hrU.2⟩).2.1
  obtain ⟨ℓ, V₀, δ, -, -, -, -, -, -, hend, -⟩ := C.slim_point_datum_BG4 WF Kc j
    (t₀ := e) he1 (δ₀ := 1) one_pos
  obtain ⟨N'', hN'', hyN'', hdisj''⟩ := C.exists_open_avoid_other_arcs_BG4 Kc j he1
  obtain ⟨z, ⟨hzB, hzN⟩, hzoff⟩ := hend he (N' ∩ N'') (hN'.inter hN'')
    ⟨by rw [← heq]; exact hyN', hyN''⟩
  obtain ⟨k, hk⟩ := mem_iUnion.mp (hN'K z ⟨hzN.1, hzB⟩)
  by_cases hkj : k = j
  · subst hkj
    exact hzoff hk
  · exact Set.disjoint_left.mp (hdisj'' k hkj) hzN.2 hk

/-- **(S3)** A point of `int_{M₁} S` lies over an interior point of an arc. -/
theorem exists_arc_interior_of_mem_relInterior_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    {p : W.Carrier} (hpX : p ∈ Bs.source 2) (hpM : p ∈ C.toChain.M₁_BIFc)
    (hrel : p ∈ relInterior_BIF C.toChain.M₁_BIFc Kc.piece) :
    ∃ j : Fin Kc.arcCount, ∃ t ∈ Ioo (0 : ℝ) 1, C.toChain.stageMap 2 p = Kc.arc j t := by
  obtain ⟨-, U, hU, hpU, hUS⟩ := mem_relInterior_iff_BCF.mp hrel
  have hS : p ∈ Kc.piece := hUS ⟨hpU, hpM⟩
  have hK : C.toChain.stageMap 2 p ∈ ⋃ k, Kc.arc k '' Icc 0 1 := hS.2.1
  obtain ⟨j, hj⟩ := mem_iUnion.mp hK
  obtain ⟨t, ht, hpt⟩ := hj
  have hpt' : C.toChain.stageMap 2 p = Kc.arc j t := hpt.symm
  have hne : ∀ e : ℝ, (e = 0 ∨ e = 1) → e = t → False := by
    intro e he het
    subst het
    exact C.not_arcEnd_of_mem_relInterior_BG4 WF Kc hpX hpM hrel j he hpt'
  exact ⟨j, t, ⟨lt_of_le_of_ne ht.1 fun h0 => hne 0 (Or.inl rfl) h0,
    lt_of_le_of_ne ht.2 fun h1 => hne 1 (Or.inr rfl) h1.symm⟩, hpt'⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
