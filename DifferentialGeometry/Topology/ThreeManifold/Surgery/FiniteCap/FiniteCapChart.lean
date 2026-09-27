import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapNeighborhood

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.Geometry.Neck
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev Cap (L : ℝ) := {x : E3 // ‖x‖ ≤ L}
private abbrev Collar (δ : ℝ) := S2 × Ico (0 : ℝ) (cuttingCollarWidth δ)
variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M]
variable {precision : ι → ℝ} {L : ℝ}
variable (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) (b : ι × Bool)
local notation "Q" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "N" => finiteCapNeighborhood hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj b
local notation "core" => finiteCoreInclusion hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "cap" => finiteCapInclusion hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "collar" => cuttingCollarMap hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj b

private def localCap (x : Cap L) : N := ⟨cap ⟨b, x⟩, Or.inl ⟨x, rfl⟩⟩
private def localLower (q : Collar (precision b.1)) : N := ⟨core (collar q), Or.inr ⟨q, rfl⟩⟩
private def lowerRegion : Set N := Subtype.val ⁻¹' range core
private def localLowerIntoRegion (q : Collar (precision b.1)) : lowerRegion hL hδ f hf hdisj b :=
  ⟨localLower hL hδ f hf hdisj b q, ⟨collar q, rfl⟩⟩

private theorem lowerRegion_closed : IsClosed (lowerRegion hL hδ f hf hdisj b) :=
  (isClosedEmbedding_finiteCoreInclusion hL hδ f hf hdisj).isClosed_range.preimage continuous_subtype_val

private theorem localLowerIntoRegion_embedding :
    _root_.Topology.IsEmbedding (localLowerIntoRegion hL hδ f hf hdisj b) := by
  have he : _root_.Topology.IsEmbedding (fun q : Collar (precision b.1) => core (collar q)) :=
    (isClosedEmbedding_finiteCoreInclusion hL hδ f hf hdisj).isEmbedding.comp
      (isOpenEmbedding_cuttingCollarMap hδ f hf hdisj b).isEmbedding
  have hn : _root_.Topology.IsEmbedding (localLower hL hδ f hf hdisj b) :=
    he.codRestrict N (fun q => Or.inr ⟨q, rfl⟩)
  exact hn.codRestrict (lowerRegion hL hδ f hf hdisj b) (fun q => ⟨collar q, rfl⟩)

omit [Finite ι] [T2Space M] in
private theorem localLowerIntoRegion_surjective :
    Surjective (localLowerIntoRegion hL hδ f hf hdisj b) := by
  intro p
  obtain ⟨x, hx⟩ := p.property
  have hn : x ∈ core ⁻¹' N := by
    change core x ∈ N
    rw [hx]
    exact p.val.property
  rw [finiteCapNeighborhood_core_preimage] at hn
  obtain ⟨q, hq⟩ := hn
  refine ⟨q, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change core (collar q) = p.val.val
  rw [hq, hx]

private def localLowerHomeomorph : Collar (precision b.1) ≃ₜ lowerRegion hL hδ f hf hdisj b :=
  (localLowerIntoRegion_embedding hL hδ f hf hdisj b).toHomeomorphOfSurjective
    (localLowerIntoRegion_surjective hL hδ f hf hdisj b)

private theorem localCap_continuous : Continuous (localCap hL hδ f hf hdisj b) :=
  ((isClosedEmbedding_finiteCapInclusion hL hδ f hf hdisj).continuous.comp continuous_sigmaMk).subtype_mk _

omit [Finite ι] [T2Space M] in
private theorem localCap_injective : Injective (localCap hL hδ f hf hdisj b) := by
  intro x y he
  exact eq_of_heq (Sigma.mk.inj (injective_finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj
    (congrArg Subtype.val he))).2

omit [Finite ι] [T2Space M] in
private theorem localCap_boundary (x : Cap L)
    (hx : localCap hL hδ f hf hdisj b x ∈ lowerRegion hL hδ f hf hdisj b) :
    x ∈ range (radialCapBoundary hL) := by
  obtain ⟨p, hp⟩ := hx
  obtain ⟨a, ha, _⟩ := (adjunctionCell_eq_lower_iff _ _
    (injective_indexedCapBoundary hL) ⟨b, x⟩ p).mp hp.symm
  have hb : a.1 = b := congrArg Sigma.fst ha
  refine ⟨a.2, ?_⟩
  have he : (⟨b, radialCapBoundary hL a.2⟩ : IndexedCaps ι L) = ⟨b, x⟩ := by
    simpa only [indexedCapBoundary, hb] using ha
  exact eq_of_heq (Sigma.mk.inj he).2

private theorem localBoundary_coherence (y : S2) :
    ((localLowerHomeomorph hL hδ f hf hdisj b
      (retainedBoundary (cuttingCollarWidth_pos (hδ b.1)) y)).val : N) =
      localCap hL hδ f hf hdisj b (radialCapBoundary hL y) := by
  apply Subtype.ext
  change core (collar (y, ⟨0, ⟨le_rfl, cuttingCollarWidth_pos (hδ b.1)⟩⟩)) = cap (indexedCapBoundary hL ⟨b, y⟩)
  rw [cuttingCollarMap_zero, finiteCapQuotient_coherence]

omit [Finite ι] [T2Space M] in
private theorem lowerRegion_union_cap :
    lowerRegion hL hδ f hf hdisj b ∪ range (localCap hL hδ f hf hdisj b) = univ := by
  apply eq_univ_of_forall
  intro p
  rcases p.property with ⟨x, hx⟩ | ⟨q, hq⟩
  · exact Or.inr ⟨x, Subtype.ext hx⟩
  · exact Or.inl ⟨collar q, hq⟩

private def localRadialQuotientHomeomorph :
    AdjunctionSpace (radialCapBoundary hL)
      (retainedBoundary (cuttingCollarWidth_pos (hδ b.1))) ≃ₜ N := by
  let : T2Space Q := finiteCapQuotient_t2Space hL hδ f hf hdisj
  let : CompactSpace (Cap L) := isCompact_iff_compactSpace.mp
    (show IsCompact {x : E3 | ‖x‖ ≤ L} by
      simpa only [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : E3) L)
  let H := localLowerHomeomorph hL hδ f hf hdisj b
  let i := radialCapBoundary hL
  let φ := retainedBoundary (cuttingCollarWidth_pos (hδ b.1))
  let U := adjunctionHomeomorphUnionImage i (H ∘ φ) (localCap hL hδ f hf hdisj b)
    (localBoundary_coherence hL hδ f hf hdisj b)
    (localCap_injective hL hδ f hf hdisj b) (localCap_continuous hL hδ f hf hdisj b)
    (localCap_boundary hL hδ f hf hdisj b) (lowerRegion_closed hL hδ f hf hdisj b)
  exact ((adjunctionHomeoOfLowerEquiv i φ H).symm.trans U).trans
    ((Homeomorph.setCongr (lowerRegion_union_cap hL hδ f hf hdisj b)).trans (Homeomorph.Set.univ N))

private theorem localRadialQuotientHomeomorph_cap (x : Cap L) :
    localRadialQuotientHomeomorph hL hδ f hf hdisj b
      (adjunctionCell (radialCapBoundary hL) (retainedBoundary (cuttingCollarWidth_pos (hδ b.1))) x) =
        localCap hL hδ f hf hdisj b x := rfl

private theorem localRadialQuotientHomeomorph_collar (q : Collar (precision b.1)) :
    localRadialQuotientHomeomorph hL hδ f hf hdisj b
      (adjunctionLower (i := radialCapBoundary hL) (retainedBoundary (cuttingCollarWidth_pos (hδ b.1))) q) =
        localLower hL hδ f hf hdisj b q := rfl

def finiteCapNeighborhoodHomeomorph : N ≃ₜ {x : E3 // ‖x‖ < L + cuttingCollarWidth (precision b.1)} :=
  (localRadialQuotientHomeomorph hL hδ f hf hdisj b).symm.trans
    (radialCapAttachmentHomeomorph hL (cuttingCollarWidth_pos (hδ b.1)))

theorem finiteCapNeighborhoodHomeomorph_cap (x : Cap L) :
    (finiteCapNeighborhoodHomeomorph hL hδ f hf hdisj b
      ⟨cap ⟨b, x⟩, Or.inl ⟨x, rfl⟩⟩).val = x.val := by
  change (finiteCapNeighborhoodHomeomorph hL hδ f hf hdisj b
    (localCap hL hδ f hf hdisj b x)).val = x.val
  rw [← localRadialQuotientHomeomorph_cap hL hδ f hf hdisj b x]
  change (radialCapAttachmentHomeomorph hL (cuttingCollarWidth_pos (hδ b.1))
    ((localRadialQuotientHomeomorph hL hδ f hf hdisj b).symm
      (localRadialQuotientHomeomorph hL hδ f hf hdisj b
        (adjunctionCell (radialCapBoundary hL) (retainedBoundary (cuttingCollarWidth_pos (hδ b.1))) x)))).val = x.val
  rw [Homeomorph.symm_apply_apply, radialCapAttachmentHomeomorph_cap]

theorem finiteCapNeighborhoodHomeomorph_collar (q : Collar (precision b.1)) :
    (finiteCapNeighborhoodHomeomorph hL hδ f hf hdisj b
      ⟨core (collar q), Or.inr ⟨q, rfl⟩⟩).val = (L + q.2.val) • q.1.val := by
  change (finiteCapNeighborhoodHomeomorph hL hδ f hf hdisj b
    (localLower hL hδ f hf hdisj b q)).val = _
  rw [← localRadialQuotientHomeomorph_collar hL hδ f hf hdisj b q]
  change (radialCapAttachmentHomeomorph hL (cuttingCollarWidth_pos (hδ b.1))
    ((localRadialQuotientHomeomorph hL hδ f hf hdisj b).symm
      (localRadialQuotientHomeomorph hL hδ f hf hdisj b
        (adjunctionLower (i := radialCapBoundary hL) (retainedBoundary (cuttingCollarWidth_pos (hδ b.1))) q)))).val = _
  rw [Homeomorph.symm_apply_apply, radialCapAttachmentHomeomorph_retained]
end DifferentialGeometry.Topology.ThreeManifold.Surgery
