import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapSeparation
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreCollar

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.Geometry.Neck
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev Cap (L : ℝ) := {x : E3 // ‖x‖ ≤ L}
private abbrev Collar (δ : ℝ) := S2 × Ico (0 : ℝ) (cuttingCollarWidth δ)
variable {ι M : Type*} {precision : ι → ℝ} {L : ℝ}

theorem cuttingSphereAttachment_mem_collar_iff (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
    (a : CuttingSpheres ι) (b : ι × Bool) :
    cuttingSphereAttachment hδ f hf hdisj a ∈ range (cuttingCollarMap hδ f hf hdisj b) ↔ a.1 = b := by
  have hz : cuttingSphereAttachment hδ f hf hdisj a ∈
      range (cuttingCollarMap hδ f hf hdisj a.1) :=
    ⟨(a.2, ⟨0, ⟨le_rfl, cuttingCollarWidth_pos (hδ a.1.1)⟩⟩),
      cuttingCollarMap_zero hδ f hf hdisj a.1 a.2⟩
  constructor
  · intro hb
    by_contra hab
    exact disjoint_left.mp (pairwise_disjoint_cuttingCollars hδ f hf hdisj hab) hz hb
  · intro hab
    exact hab ▸ hz

def finiteCapNeighborhood (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) (b : ι × Bool) :
    Set (FiniteCapQuotient hL hδ f hf hdisj) :=
  range (fun x : Cap L => finiteCapInclusion hL hδ f hf hdisj ⟨b, x⟩) ∪
    range (fun q : Collar (precision b.1) =>
      finiteCoreInclusion hL hδ f hf hdisj (cuttingCollarMap hδ f hf hdisj b q))

theorem finiteCapNeighborhood_cap_preimage (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) (b : ι × Bool) :
    finiteCapInclusion hL hδ f hf hdisj ⁻¹' finiteCapNeighborhood hL hδ f hf hdisj b =
      range (fun x : Cap L => (⟨b, x⟩ : IndexedCaps ι L)) := by
  ext p
  constructor
  · rintro (⟨x, hx⟩ | ⟨q, hq⟩)
    · exact ⟨x, injective_finiteCapInclusion hL hδ f hf hdisj hx⟩
    · obtain ⟨a, ha, hp⟩ := (adjunctionCell_eq_lower_iff _ _
        (injective_indexedCapBoundary hL) p (cuttingCollarMap hδ f hf hdisj b q)).mp hq.symm
      have hb := (cuttingSphereAttachment_mem_collar_iff hδ f hf hdisj a b).mp ⟨q, hp.symm⟩
      refine ⟨radialCapBoundary hL a.2, ?_⟩
      rw [← ha]
      change (⟨b, radialCapBoundary hL a.2⟩ : IndexedCaps ι L) = ⟨a.1, radialCapBoundary hL a.2⟩
      rw [hb]
  · rintro ⟨x, rfl⟩
    exact Or.inl ⟨x, rfl⟩

theorem finiteCapNeighborhood_core_preimage (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) (b : ι × Bool) :
    finiteCoreInclusion hL hδ f hf hdisj ⁻¹' finiteCapNeighborhood hL hδ f hf hdisj b =
      range (cuttingCollarMap hδ f hf hdisj b) := by
  ext p
  constructor
  · rintro (⟨x, hx⟩ | ⟨q, hq⟩)
    · obtain ⟨a, ha, hp⟩ := (adjunctionCell_eq_lower_iff _ _
        (injective_indexedCapBoundary hL) ⟨b, x⟩ p).mp hx
      have hb : a.1 = b := congrArg Sigma.fst ha
      have hh := (cuttingSphereAttachment_mem_collar_iff hδ f hf hdisj a b).mpr hb
      exact hp ▸ hh
    · exact ⟨q, injective_finiteCoreInclusion hL hδ f hf hdisj hq⟩
  · rintro ⟨q, rfl⟩
    exact Or.inr ⟨q, rfl⟩

theorem pairwise_disjoint_finiteCapNeighborhoods (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :
    Pairwise (fun b c : ι × Bool => Disjoint
      (finiteCapNeighborhood hL hδ f hf hdisj b) (finiteCapNeighborhood hL hδ f hf hdisj c)) := by
  intro b c hbc
  apply disjoint_left.mpr
  intro p hb hc
  have hp := eq_univ_iff_forall.mp (finiteCapQuotient_cover hL hδ f hf hdisj) p
  rcases hp with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · have hb' : q ∈ finiteCapInclusion hL hδ f hf hdisj ⁻¹' finiteCapNeighborhood hL hδ f hf hdisj b := hb
    have hc' : q ∈ finiteCapInclusion hL hδ f hf hdisj ⁻¹' finiteCapNeighborhood hL hδ f hf hdisj c := hc
    rw [finiteCapNeighborhood_cap_preimage] at hb' hc'
    obtain ⟨x, hx⟩ := hb'
    obtain ⟨y, hy⟩ := hc'
    exact hbc (congrArg Sigma.fst (hx.trans hy.symm))
  · have hb' : q ∈ finiteCoreInclusion hL hδ f hf hdisj ⁻¹' finiteCapNeighborhood hL hδ f hf hdisj b := hb
    have hc' : q ∈ finiteCoreInclusion hL hδ f hf hdisj ⁻¹' finiteCapNeighborhood hL hδ f hf hdisj c := hc
    rw [finiteCapNeighborhood_core_preimage] at hb' hc'
    exact disjoint_left.mp (pairwise_disjoint_cuttingCollars hδ f hf hdisj hbc) hb' hc'

variable [TopologicalSpace M]

theorem isOpen_finiteCapNeighborhood (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) (b : ι × Bool) :
    IsOpen (finiteCapNeighborhood hL hδ f (fun i => (hf i).injective) hdisj b) := by
  apply (isQuotientMap_adjunctionMk (indexedCapBoundary hL)
    (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj)).isCoinducing.isOpen_preimage.mp
  apply isOpen_sum_iff.mpr
  change IsOpen (finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⁻¹'
    finiteCapNeighborhood hL hδ f (fun i => (hf i).injective) hdisj b) ∧
    IsOpen (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj ⁻¹'
      finiteCapNeighborhood hL hδ f (fun i => (hf i).injective) hdisj b)
  rw [finiteCapNeighborhood_cap_preimage, finiteCapNeighborhood_core_preimage]
  exact ⟨isOpen_range_sigmaMk, (isOpenEmbedding_cuttingCollarMap hδ f hf hdisj b).isOpen_range⟩

def finiteCoreInterior (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :
    Set (FiniteCapQuotient hL hδ f hf hdisj) :=
  finiteCoreInclusion hL hδ f hf hdisj '' (Subtype.val ⁻¹' interior (cutCore f))

theorem finiteCoreInterior_core_preimage (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :
    finiteCoreInclusion hL hδ f hf hdisj ⁻¹' finiteCoreInterior hL hδ f hf hdisj =
      Subtype.val ⁻¹' interior (cutCore f) :=
  preimage_image_eq _ (injective_finiteCoreInclusion hL hδ f hf hdisj)

variable [Finite ι] [T2Space M]

theorem finiteCoreInterior_cap_preimage (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :
    finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⁻¹'
      finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro q hq
  obtain ⟨p, hp, he⟩ := hq
  obtain ⟨a, _, ha⟩ := (adjunctionCell_eq_lower_iff _ _
    (injective_indexedCapBoundary hL) q p).mp he.symm
  have hfront : (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj a).val ∈
      frontier (cutCore f) := by
    have hh : cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj a ∈
        range (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj) := ⟨a, rfl⟩
    rw [range_cuttingSphereAttachment hδ f hf hdisj] at hh
    exact hh
  rw [congrArg Subtype.val ha] at hfront
  exact hfront.2 hp

theorem isOpen_finiteCoreInterior (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :
    IsOpen (finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj) := by
  apply (isQuotientMap_adjunctionMk (indexedCapBoundary hL)
    (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj)).isCoinducing.isOpen_preimage.mp
  apply isOpen_sum_iff.mpr
  change IsOpen (finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⁻¹'
    finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj) ∧
    IsOpen (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj ⁻¹'
      finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj)
  rw [finiteCoreInterior_cap_preimage hL hδ f hf hdisj, finiteCoreInterior_core_preimage]
  exact ⟨isOpen_empty, isOpen_interior.preimage continuous_subtype_val⟩

theorem finiteCapNeighborhood_cover (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :
    finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj ∪
      (⋃ b : ι × Bool, finiteCapNeighborhood hL hδ f (fun i => (hf i).injective) hdisj b) = univ := by
  apply eq_univ_of_forall
  intro p
  have hp := eq_univ_iff_forall.mp (finiteCapQuotient_cover hL hδ f (fun i => (hf i).injective) hdisj) p
  rcases hp with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · exact Or.inr (mem_iUnion.mpr ⟨q.1, Or.inl ⟨q.2, rfl⟩⟩)
  · by_cases hq : q.val ∈ interior (cutCore f)
    · exact Or.inl ⟨q, hq, rfl⟩
    · have hfront : q.val ∈ frontier (cutCore f) := ⟨subset_closure q.property, hq⟩
      have hr : q ∈ range (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj) := by
        rw [range_cuttingSphereAttachment hδ f hf hdisj]
        exact hfront
      obtain ⟨a, ha⟩ := hr
      apply Or.inr
      apply mem_iUnion.mpr
      refine ⟨a.1, Or.inl ⟨radialCapBoundary hL a.2, ?_⟩⟩
      change finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj (indexedCapBoundary hL a) = _
      rw [finiteCapQuotient_coherence, ha]
end DifferentialGeometry.Topology.ThreeManifold.Surgery
