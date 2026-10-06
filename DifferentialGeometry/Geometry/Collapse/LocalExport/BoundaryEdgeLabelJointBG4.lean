import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeLabelFunBG4
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleBaseFacesBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryHorizontalFaceBCF

/-!
# BCF02 G4, group G5c: the labels together (lane S-BCF02-G4b)

The set-theoretic bookkeeping between the removed open sets `labelRemoved_BG4` and the actual
`M₂`, labelled faces `edgeFaceSet_BIFc` (all points `p` of the chain; the edge source is only
used by the caller):

* `not_mem_labelRemoved_of_mem_M₂_BG4` (M2R): a point of `M₂` lies in no removed set;
* `exists_labelRemoved_of_not_mem_M₂_BG4` (COV): a point outside `M₂` lies in some removed set
  (zero domains and cusp cores are pairwise disjoint closed sets, so `int (⋃ P_t) = ⋃ int P_t`;
  a point of `int_{M₁} S` lies over an interior point of an arc, which is covered by one of the
  two sub-arcs of the arc);
* `mem_edgeFaceSet_of_mem_labelZero_BG4` (PM2): a point of `M₂` in the zero set of a label lies in
  the actual face of the label (the extra zero `γ(2/3)`, `γ(1/3)` is over `int_{M₁} S`);
* `mem_labelZero_of_mem_edgeFaceSet_BG4` (FP): the actual face of a label lies in its zero set.
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

/-- **The interior of a finite union of pairwise disjoint closed sets** is the union of the
interiors. -/
theorem interior_iUnion_eq_of_disjoint_BG4 {X : Type*} [TopologicalSpace X] {ι : Type*}
    [Finite ι] (P : ι → Set X) (hcl : ∀ i, IsClosed (P i)) (hd : Pairwise (Disjoint on P)) :
    interior (⋃ i, P i) = ⋃ i, interior (P i) := by
  refine Set.Subset.antisymm (fun x hx => ?_)
    (iUnion_subset fun i => interior_mono (subset_iUnion P i))
  obtain ⟨j, hj⟩ := mem_iUnion.mp (interior_subset hx)
  refine mem_iUnion.mpr ⟨j, ?_⟩
  by_contra hnot
  exact Set.disjoint_left.mp (disjoint_iUnion_frontier_interior_BGR P hcl hd)
    (mem_iUnion.mpr ⟨j, subset_closure hj, hnot⟩) hx

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

/-- A point over a point of an arc lies in `X₃` (`X₃ = f₃⁻¹ B₃`, arcs lie in `B₃`). -/
theorem mem_source_two_of_arc_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Kc : BoundaryCompactSlimChoiceV2 Bs) {p : W.Carrier} {j : Fin Kc.arcCount} {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (h : C.toChain.stageMap 2 p = Kc.arc j t) : p ∈ Bs.source 2 := by
  rw [Bs.slim_source_eq]
  change C.toChain.stageMap 2 p ∈ Bs.base 2
  rw [h]
  exact Kc.arc_subset_base j ⟨t, ht, rfl⟩

/-- A point of `int_{M₁} S` lies in `X₃`. -/
theorem mem_source_two_of_mem_relInterior_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Kc : BoundaryCompactSlimChoiceV2 Bs) {p : W.Carrier}
    (hrel : p ∈ relInterior_BIF C.toChain.M₁_BIFc Kc.piece) : p ∈ Bs.source 2 := by
  obtain ⟨hpM, U, -, hpU, hUS⟩ := mem_relInterior_iff_BCF.mp hrel
  exact (hUS ⟨hpU, hpM⟩).1

/-- A point of `M₂` is not over an interior point of an arc. -/
theorem not_mem_M₂_of_arc_interior_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    {p : W.Carrier} {j : Fin Kc.arcCount} {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hp : p ∈ Kc.M₂)
    (h : C.toChain.stageMap 2 p = Kc.arc j t) : False :=
  hp.2 (C.mem_relInterior_of_arc_interior_BG4 WF Kc j ht
    (C.mem_source_two_of_arc_BG4 Kc ⟨ht.1.le, ht.2.le⟩ h) hp.1 h)

/-- **(M2R)** A point of `M₂` lies in no removed set. -/
theorem not_mem_labelRemoved_of_mem_M₂_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    {p : W.Carrier} (hp : p ∈ Kc.M₂) (ℓ : Kc.EdgeFaceLabel_BIFc) :
    p ∉ C.labelRemoved_BG4 Kc ℓ := by
  rcases ℓ with k | i | je
  · intro hmem
    exact hp.1 (interior_mono
      ((subset_iUnion (fun k => C.toChain.actualZeroDomain_BIFc k) k).trans subset_union_left)
      hmem)
  · intro hmem
    exact hp.1 (interior_mono
      ((show C.toChain.cuspCore_BIF i ⊆ C.toChain.cuspCores_BIF from subset_iUnion _ i).trans
        subset_union_right) hmem)
  · rintro ⟨t, ht, hpt⟩
    exact C.not_mem_M₂_of_arc_interior_BG4 WF Kc (Ioo_label_subset_BG4 je.2 ht) hp hpt.symm

/-- The interior of `⋃ Z_k ∪ ⋃ cores` is the union of the interiors (pairwise disjoint closed
pieces; premises of `frontier_M₁_BGR`). -/
theorem interior_zeroCusp_eq_BG4 {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    interior ((⋃ k, C.toChain.actualZeroDomain_BIFc k) ∪ C.toChain.cuspCores_BIF) =
      (⋃ k, interior (C.toChain.actualZeroDomain_BIFc k)) ∪
        ⋃ i, interior (C.toChain.cuspCore_BIF i) := by
  have hcomp := (C.bcg06_on_boundary_chain_BGR hrd hrd4 hrdc hprem hθ).1
  have hspec := C.bcg06_coreSpec_on_chain_BGR hrd hrd4 hrdc hprem hθ
  have hA : (⋃ k, C.toChain.actualZeroDomain_BIFc k) ∪ C.toChain.cuspCores_BIF =
      ⋃ t, Sum.elim C.toChain.actualZeroDomain_BIFc C.toChain.cuspCore_BIF t := by
    rw [iUnion_sum]
    rfl
  have hB : (⋃ k, interior (C.toChain.actualZeroDomain_BIFc k)) ∪
      ⋃ i, interior (C.toChain.cuspCore_BIF i) =
      ⋃ t, interior (Sum.elim C.toChain.actualZeroDomain_BIFc C.toChain.cuspCore_BIF t) := by
    rw [iUnion_sum]
    rfl
  rw [hA, hB]
  refine interior_iUnion_eq_of_disjoint_BG4 _ ?_ ?_
  · rintro (k | i)
    · exact (C.isCompact_actualZeroDomain_BGR k).isClosed
    · exact (hcomp i).compact_core.isClosed
  · rintro (k | i) (k' | i') hne
    · exact C.actualZeroDomain_pairwise_disjoint_BGR fun h => hne (congrArg Sum.inl h)
    · exact (C.cuspCore_disjoint_actualZeroDomain_BGR hrd hrd4 hrdc hprem hθ i' k).symm
    · exact C.cuspCore_disjoint_actualZeroDomain_BGR hrd hrd4 hrdc hprem hθ i k'
    · exact hspec.pairwise_disjoint i i' fun h => hne (congrArg Sum.inr h)

/-- **(COV)** A point outside `M₂` lies in some removed set. -/
theorem exists_labelRemoved_of_not_mem_M₂_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs) {p : W.Carrier} (hp : p ∉ Kc.M₂) :
    ∃ ℓ : Kc.EdgeFaceLabel_BIFc, p ∈ C.labelRemoved_BG4 Kc ℓ := by
  by_cases hM : p ∈ C.toChain.M₁_BIFc
  · have hrel : p ∈ relInterior_BIF C.toChain.M₁_BIFc Kc.piece := by
      by_contra h
      exact hp ⟨hM, h⟩
    obtain ⟨j, t, ht, hpt⟩ := C.exists_arc_interior_of_mem_relInterior_BG4 WF Kc
      (C.mem_source_two_of_mem_relInterior_BG4 Kc hrel) hM hrel
    obtain ⟨e, he⟩ := Ioo_zero_one_subset_labels_BG4 ht
    exact ⟨Sum.inr (Sum.inr (j, e)), t, he, hpt.symm⟩
  · have hint : p ∈ interior ((⋃ k, C.toChain.actualZeroDomain_BIFc k) ∪
        C.toChain.cuspCores_BIF) := by
      by_contra h
      exact hM h
    rw [C.interior_zeroCusp_eq_BG4 hrd hrd4 hrdc hprem hθ] at hint
    rcases hint with hz | hc
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hz
      exact ⟨Sum.inl k, hk⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hc
      exact ⟨Sum.inr (Sum.inl i), hi⟩

/-- **(PM2)** A point of `M₂` in the zero set of a label lies in the actual face of the label. -/
theorem mem_edgeFaceSet_of_mem_labelZero_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    {p : W.Carrier} (hpM : p ∈ Kc.M₂) (ℓ : Kc.EdgeFaceLabel_BIFc)
    (hp : p ∈ C.labelZero_BG4 Kc ℓ) : p ∈ Kc.edgeFaceSet_BIFc ℓ := by
  rcases ℓ with k | i | ⟨j, e⟩
  · exact hp
  · exact hp
  · have h13 : (1 / 3 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have h23 : (2 / 3 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    cases e
    · rcases hp with h | h
      · exact ⟨C.mem_source_two_of_arc_BG4 Kc (t := 0) ⟨le_rfl, zero_le_one⟩ h, by
          simpa [BoundaryCompactSlimChoiceV2.arcEnd_BIFc, slimLabelLo_BG4] using h⟩
      · exact (C.not_mem_M₂_of_arc_interior_BG4 WF Kc h23 hpM (by
          simpa [slimLabelHi_BG4] using h)).elim
    · rcases hp with h | h
      · exact (C.not_mem_M₂_of_arc_interior_BG4 WF Kc h13 hpM (by
          simpa [slimLabelLo_BG4] using h)).elim
      · exact ⟨C.mem_source_two_of_arc_BG4 Kc (t := 1) ⟨zero_le_one, le_rfl⟩ h, by
          simpa [BoundaryCompactSlimChoiceV2.arcEnd_BIFc, slimLabelHi_BG4] using h⟩

/-- **(FP)** The actual face of a label lies in its zero set. -/
theorem mem_labelZero_of_mem_edgeFaceSet_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Kc : BoundaryCompactSlimChoiceV2 Bs) {p : W.Carrier} (ℓ : Kc.EdgeFaceLabel_BIFc)
    (hp : p ∈ Kc.edgeFaceSet_BIFc ℓ) : p ∈ C.labelZero_BG4 Kc ℓ := by
  rcases ℓ with k | i | ⟨j, e⟩
  · exact hp
  · exact hp
  · have h : C.toChain.stageMap 2 p = Kc.arc j (BoundaryCompactSlimChoiceV2.arcEnd_BIFc e) :=
      hp.2
    cases e
    · exact Or.inl (by simpa [BoundaryCompactSlimChoiceV2.arcEnd_BIFc, slimLabelLo_BG4] using h)
    · exact Or.inr (by simpa [BoundaryCompactSlimChoiceV2.arcEnd_BIFc, slimLabelHi_BG4] using h)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
