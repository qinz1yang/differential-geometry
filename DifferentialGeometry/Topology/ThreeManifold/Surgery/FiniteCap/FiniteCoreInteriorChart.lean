import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapNeighborhood
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Neck
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
variable {ι M : Type*} [TopologicalSpace M] {precision : ι → ℝ} {L : ℝ}

def coreInteriorDomain (f : ∀ i : ι, bufferedCylinder (precision i) → M) : Opens M :=
  ⟨interior (cutCore f), isOpen_interior⟩

def finiteCoreInteriorMap (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :
    coreInteriorDomain f → FiniteCapQuotient hL hδ f hf hdisj :=
  fun p => finiteCoreInclusion hL hδ f hf hdisj ⟨p.val, interior_subset p.property⟩

theorem finiteCoreInteriorMap_apply (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) (p : coreInteriorDomain f) :
    finiteCoreInteriorMap hL hδ f hf hdisj p =
      finiteCoreInclusion hL hδ f hf hdisj ⟨p.val, interior_subset p.property⟩ := rfl

theorem range_finiteCoreInteriorMap (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :
    range (finiteCoreInteriorMap hL hδ f hf hdisj) = finiteCoreInterior hL hδ f hf hdisj := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨⟨p.val, interior_subset p.property⟩, p.property, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p.val, hp⟩, rfl⟩

variable [Finite ι] [T2Space M]

theorem isOpenEmbedding_finiteCoreInteriorMap (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :
    _root_.Topology.IsOpenEmbedding (finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj) := by
  have hi : _root_.Topology.IsEmbedding (fun p : coreInteriorDomain f =>
      (⟨p.val, interior_subset p.property⟩ : cutCore f)) :=
    _root_.Topology.IsEmbedding.subtypeVal.codRestrict (cutCore f) (fun p => interior_subset p.property)
  refine ⟨(isClosedEmbedding_finiteCoreInclusion hL hδ f hf hdisj).isEmbedding.comp hi, ?_⟩
  rw [range_finiteCoreInteriorMap]
  exact isOpen_finiteCoreInterior hL hδ f hf hdisj

variable {H : Type*} [TopologicalSpace H] [ChartedSpace H M]
variable (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
local notation "Q" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "old" => finiteCoreInteriorMap hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

def finiteCoreOpenChart (x : coreInteriorDomain f) : OpenPartialHomeomorph Q H := by
  let : Nonempty H := ⟨chartAt H x x⟩
  exact (chartAt H x).lift_openEmbedding (isOpenEmbedding_finiteCoreInteriorMap hL hδ f hf hdisj)

theorem finiteCoreOpenChart_source (x : coreInteriorDomain f) :
    (finiteCoreOpenChart (H := H) hL hδ f hf hdisj x).source = old '' (chartAt H x).source := rfl

theorem finiteCoreOpenChart_target (x : coreInteriorDomain f) :
    (finiteCoreOpenChart (H := H) hL hδ f hf hdisj x).target = (chartAt H x).target := rfl

theorem finiteCoreOpenChart_apply (x p : coreInteriorDomain f) :
    finiteCoreOpenChart (H := H) hL hδ f hf hdisj x (old p) = chartAt H x.val p.val := by
  let : Nonempty H := ⟨chartAt H x x⟩
  rw [finiteCoreOpenChart, OpenPartialHomeomorph.lift_openEmbedding_apply]
  rfl

theorem finiteCoreOpenChart_source_cover :
    (⋃ x : coreInteriorDomain f, (finiteCoreOpenChart (H := H) hL hδ f hf hdisj x).source) =
      finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj := by
  rw [← range_finiteCoreInteriorMap]
  ext q
  constructor
  · intro hq
    obtain ⟨x, p, _, hp⟩ := mem_iUnion.mp hq
    exact ⟨p, hp⟩
  · rintro ⟨p, rfl⟩
    exact mem_iUnion.mpr ⟨p, p, mem_chart_source H p, rfl⟩
end DifferentialGeometry.Topology.ThreeManifold.Surgery
