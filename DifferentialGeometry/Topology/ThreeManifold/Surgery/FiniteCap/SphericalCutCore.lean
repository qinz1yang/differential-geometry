import DifferentialGeometry.Geometry.Neck.RecenteringChart
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1

def centralDomain (δ : ℝ) : Set (bufferedCylinder δ) := {q | q.val.2 ∈ Ioo (-1 : ℝ) 1}

def closedCentralDomain (δ : ℝ) : Set (bufferedCylinder δ) := {q | q.val.2 ∈ Icc (-1 : ℝ) 1}

theorem isOpen_centralDomain (δ : ℝ) : IsOpen (centralDomain δ) :=
  isOpen_Ioo.preimage continuous_subtype_val.snd

theorem isCompact_closedCentralDomain (δ : ℝ) (hδ : 0 < δ) : IsCompact (closedCentralDomain δ) := by
  rw [Subtype.isCompact_iff]
  have he : Subtype.val '' closedCentralDomain δ = (univ : Set S2) ×ˢ Icc (-1 : ℝ) 1 := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨mem_univ _, hq⟩
    · intro hp
      have hmem : p ∈ bufferedCylinder δ := by
        change -δ⁻¹ - 1 < p.2 ∧ p.2 < δ⁻¹ + 1
        constructor <;> linarith [inv_pos.mpr hδ, hp.2.1, hp.2.2]
      exact ⟨⟨p, hmem⟩, hp.2, rfl⟩
  rw [he]
  exact isCompact_univ.prod isCompact_Icc

theorem closure_centralDomain (δ : ℝ) : closure (centralDomain δ) = closedCentralDomain δ := by
  have hf : IsOpenMap (fun q : bufferedCylinder δ => q.val.2) :=
    isOpenMap_snd.comp (bufferedCylinder δ).isOpen.isOpenMap_subtype_val
  have he := hf.preimage_closure_eq_closure_preimage continuous_subtype_val.snd (Ioo (-1 : ℝ) 1)
  simpa only [centralDomain, closedCentralDomain, Set.preimage, closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)] using he.symm

variable {M : Type*} [TopologicalSpace M] {δ : ℝ}

def removedSlab (f : bufferedCylinder δ → M) : Set M := f '' centralDomain δ

def closedSlab (f : bufferedCylinder δ → M) : Set M := f '' closedCentralDomain δ

def cutFaces (hδ : 0 < δ) (f : bufferedCylinder δ → M) : Set M :=
  range (fun y : S2 => f ⟨(y, -1), offset_mem_bufferedCylinder hδ (by norm_num) y⟩) ∪
    range (fun y : S2 => f ⟨(y, 1), offset_mem_bufferedCylinder hδ (by norm_num) y⟩)

theorem isOpen_removedSlab (f : bufferedCylinder δ → M) (hf : _root_.Topology.IsOpenEmbedding f) :
    IsOpen (removedSlab f) := hf.isOpenMap _ (isOpen_centralDomain δ)

theorem closure_removedSlab [T2Space M] (hδ : 0 < δ)
    (f : bufferedCylinder δ → M) (hf : Continuous f) : closure (removedSlab f) = closedSlab f := by
  have hc : IsCompact (closure (centralDomain δ)) := by
    rw [closure_centralDomain]
    exact isCompact_closedCentralDomain δ hδ
  have he := image_closure_of_isCompact hc hf.continuousOn
  simpa only [closure_centralDomain, removedSlab, closedSlab] using he.symm

theorem frontier_removedSlab [T2Space M] (hδ : 0 < δ)
    (f : bufferedCylinder δ → M) (hf : _root_.Topology.IsOpenEmbedding f) :
    frontier (removedSlab f) = cutFaces hδ f := by
  rw [frontier, closure_removedSlab hδ f hf.continuous, (isOpen_removedSlab f hf).interior_eq]
  ext p
  constructor
  · rintro ⟨⟨q, hq, rfl⟩, hn⟩
    have hnot : ¬(-1 < q.val.2 ∧ q.val.2 < 1) := fun hh => hn ⟨q, hh, rfl⟩
    have hends : q.val.2 = -1 ∨ q.val.2 = 1 := by
      change -1 ≤ q.val.2 ∧ q.val.2 ≤ 1 at hq
      rcases not_and_or.mp hnot with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases hends with h | h
    · apply Or.inl
      refine ⟨q.val.1, congrArg f ?_⟩
      apply Subtype.ext
      exact Prod.ext rfl h.symm
    · apply Or.inr
      refine ⟨q.val.1, congrArg f ?_⟩
      apply Subtype.ext
      exact Prod.ext rfl h.symm
  · rintro (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · refine ⟨⟨_, ⟨le_rfl, by norm_num⟩, rfl⟩, ?_⟩
      rintro ⟨q, hq, he⟩
      have hp := congrArg (fun z : bufferedCylinder δ => z.val.2) (hf.injective he)
      change q.val.2 = -1 at hp
      have hh : -1 < q.val.2 := hq.1
      linarith
    · refine ⟨⟨_, ⟨by norm_num, le_rfl⟩, rfl⟩, ?_⟩
      rintro ⟨q, hq, he⟩
      have hp := congrArg (fun z : bufferedCylinder δ => z.val.2) (hf.injective he)
      change q.val.2 = 1 at hp
      have hh : q.val.2 < 1 := hq.2
      linarith

variable {ι : Type*} {precision : ι → ℝ}

def cutCore (f : ∀ i : ι, bufferedCylinder (precision i) → M) : Set M :=
  (⋃ i, removedSlab (f i))ᶜ

theorem isClosed_cutCore (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i)) : IsClosed (cutCore f) :=
  (isOpen_iUnion (fun i => isOpen_removedSlab (f i) (hf i))).isClosed_compl

theorem isCompact_cutCore [CompactSpace M] (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i)) : IsCompact (cutCore f) :=
  (isClosed_cutCore f hf).isCompact

theorem frontier_cutCore [Finite ι] [T2Space M]
    (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :
    frontier (cutCore f) = ⋃ i, cutFaces (hδ i) (f i) := by
  have hopen := isOpen_iUnion (fun i => isOpen_removedSlab (f i) (hf i))
  rw [cutCore, frontier_compl, frontier, hopen.interior_eq, closure_iUnion_of_finite]
  simp_rw [closure_removedSlab (hδ _) _ (hf _).continuous]
  have hface (i : ι) : closedSlab (f i) \ removedSlab (f i) = cutFaces (hδ i) (f i) := by
    simpa only [frontier, closure_removedSlab (hδ i) _ (hf i).continuous,
      (isOpen_removedSlab (f i) (hf i)).interior_eq] using frontier_removedSlab (hδ i) (f i) (hf i)
  ext p
  constructor
  · rintro ⟨hp, hn⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨i, hface i ▸ ⟨hi, fun hh => hn (mem_iUnion.mpr ⟨i, hh⟩)⟩⟩
  · intro hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    have hi' : p ∈ closedSlab (f i) \ removedSlab (f i) := hface i ▸ hi
    refine ⟨mem_iUnion.mpr ⟨i, hi'.1⟩, ?_⟩
    intro hn
    obtain ⟨j, hj⟩ := mem_iUnion.mp hn
    by_cases hij : i = j
    · subst j
      exact hi'.2 hj
    · exact disjoint_left.mp (hdisj hij) (image_subset_range _ _ hi'.1) (image_subset_range _ _ hj)

section ActualNeckFamily
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

def neckAmbientMap (U : Opens M) {g : SmoothRiemannianMetric I U} {x₀ : U} {k : ℕ}
    (d : normalizedDatum g x₀ δ k) : bufferedCylinder δ → M := fun q => (d.map q : M)

theorem isOpenEmbedding_neckAmbientMap (U : Opens M) {g : SmoothRiemannianMetric I U} {x₀ : U} {k : ℕ}
    (d : normalizedDatum g x₀ δ k) : _root_.Topology.IsOpenEmbedding (neckAmbientMap U d) :=
  U.isOpen.isOpenEmbedding_subtypeVal.comp d.isOpenEmbedding_map

theorem range_neckAmbientMap_subset (U : Opens M) {g : SmoothRiemannianMetric I U} {x₀ : U} {k : ℕ}
    (d : normalizedDatum g x₀ δ k) : range (neckAmbientMap U d) ⊆ U := by
  rintro p ⟨q, rfl⟩
  exact (d.map q).property

theorem normalizedNeckFamily_cutCore [CompactSpace M] [Finite ι]
    (U : Opens M) (g : SmoothRiemannianMetric I U) (x₀ : ι → U) (order : ι → ℕ)
    (d : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i))
    (hdisj : Pairwise (fun i j => Disjoint (range (neckAmbientMap U (d i))) (range (neckAmbientMap U (d j))))) :
    IsCompact (cutCore (fun i => neckAmbientMap U (d i))) ∧
      frontier (cutCore (fun i => neckAmbientMap U (d i))) =
        ⋃ i, cutFaces (d i).precision_pos (neckAmbientMap U (d i)) :=
  ⟨isCompact_cutCore _ (fun i => isOpenEmbedding_neckAmbientMap U (d i)),
    frontier_cutCore (fun i => (d i).precision_pos) _
      (fun i => isOpenEmbedding_neckAmbientMap U (d i)) hdisj⟩
end ActualNeckFamily

omit [TopologicalSpace M] in
theorem cutCore_empty [IsEmpty ι] (f : ∀ i : ι, bufferedCylinder (precision i) → M) :
    cutCore f = univ := by simp [cutCore]
end DifferentialGeometry.Topology.ThreeManifold.Surgery
