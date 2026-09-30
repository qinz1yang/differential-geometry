import DifferentialGeometry.Topology.ClosedBall.UnitDisk
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace DifferentialGeometry.Topology

open Set Metric _root_.Topology

structure EmbeddedClosedCell (n : ℕ) (X : Type*) [TopologicalSpace X] where
  map : Disk n → X
  isClosedEmbedding : IsClosedEmbedding map
  isOpen_interior : IsOpen (map '' diskInterior n)

namespace EmbeddedClosedCell

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

def carrier (c : EmbeddedClosedCell n X) : Set X := range c.map

def interiorSet (c : EmbeddedClosedCell n X) : Set X := c.map '' diskInterior n

theorem isClosed_carrier (c : EmbeddedClosedCell n X) : IsClosed c.carrier :=
  c.isClosedEmbedding.isClosed_range

theorem isCompact_carrier (c : EmbeddedClosedCell n X) : IsCompact c.carrier := by
  have : CompactSpace (Disk n) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  exact isCompact_range c.isClosedEmbedding.continuous

theorem interiorSet_subset_carrier (c : EmbeddedClosedCell n X) : c.interiorSet ⊆ c.carrier :=
  image_subset_range _ _

theorem interiorSet_subset_interior (c : EmbeddedClosedCell n X) : c.interiorSet ⊆ interior c.carrier :=
  interior_maximal c.interiorSet_subset_carrier c.isOpen_interior

theorem carrier_sdiff_interiorSet (c : EmbeddedClosedCell n X) :
    c.carrier \ c.interiorSet = c.map '' diskSphere n := by
  ext x
  constructor
  · rintro ⟨⟨v, rfl⟩, hv⟩
    refine ⟨v, ?_, rfl⟩
    have hnot : v ∉ diskInterior n := fun h => hv ⟨v, h, rfl⟩
    have hall : v ∈ diskSphere n ∪ diskInterior n := by
      rw [diskSphere_union_diskInterior]
      trivial
    exact hall.resolve_right hnot
  · rintro ⟨v, hv, rfl⟩
    refine ⟨mem_range_self v, ?_⟩
    intro hi
    rw [interiorSet, c.isClosedEmbedding.injective.mem_set_image] at hi
    exact Set.disjoint_left.1 (disjoint_diskSphere_diskInterior n) hv hi

theorem frontier_carrier_subset (c : EmbeddedClosedCell n X) :
    frontier c.carrier ⊆ c.map '' diskSphere n := by
  rw [frontier, c.isClosed_carrier.closure_eq, ← c.carrier_sdiff_interiorSet]
  exact sdiff_subset_sdiff_right c.interiorSet_subset_interior

theorem interiorSet_nonempty (c : EmbeddedClosedCell n X) : c.interiorSet.Nonempty := by
  let z : Disk n := ⟨0, mem_closedBall_self zero_le_one⟩
  exact ⟨c.map z, z, mem_diskInterior.mpr (by simp [z]), rfl⟩

theorem carrier_nonempty (c : EmbeddedClosedCell n X) : c.carrier.Nonempty :=
  c.interiorSet_nonempty.mono c.interiorSet_subset_carrier

theorem exists_radius_of_isCompact [T2Space X] (c : EmbeddedClosedCell n X) {K : Set X}
    (hK : IsCompact K) (hKC : K ⊆ c.interiorSet) :
    ∃ R : ℝ, 0 < R ∧ R < 1 ∧
      ∀ x : Disk n, c.map x ∈ K → ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ R := by
  have : CompactSpace (Disk n) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hc : IsCompact (c.map ⁻¹' K) :=
    (hK.isClosed.preimage c.isClosedEmbedding.continuous).isCompact
  rcases (c.map ⁻¹' K).eq_empty_or_nonempty with he | hne
  · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    intro x hx
    have : x ∈ c.map ⁻¹' K := hx
    simp only [he, mem_empty_iff_false] at this
  · obtain ⟨x, hx, hmax⟩ := hc.exists_isMaxOn hne continuous_subtype_val.norm.continuousOn
    have hx1 : ‖(x : EuclideanSpace ℝ (Fin n))‖ < 1 := by
      have hi := hKC hx
      rw [interiorSet, c.isClosedEmbedding.injective.mem_set_image] at hi
      exact mem_diskInterior.mp hi
    refine ⟨(‖(x : EuclideanSpace ℝ (Fin n))‖ + 1) / 2, by positivity, by linarith, ?_⟩
    intro y hy
    have hle : ‖(y : EuclideanSpace ℝ (Fin n))‖ ≤ ‖(x : EuclideanSpace ℝ (Fin n))‖ := hmax hy
    linarith

end EmbeddedClosedCell

def isCellular {X : Type*} [TopologicalSpace X] (n : ℕ) (K : Set X) : Prop :=
  ∃ c : ℕ → EmbeddedClosedCell n X,
    (∀ i, (c (i + 1)).carrier ⊆ (c i).interiorSet) ∧ K = ⋂ i, (c i).carrier

theorem isCellular_of_cell_neighborhoods {X : Type*} [MetricSpace X] {n : ℕ} {K : Set X}
    (hclosed : IsClosed K) (hne : K.Nonempty)
    (hcell : ∀ U : Set X, IsOpen U → K ⊆ U →
      ∃ c : EmbeddedClosedCell n X, K ⊆ c.interiorSet ∧ c.carrier ⊆ U) : isCellular n K := by
  classical
  obtain ⟨c₀, hc₀, -⟩ := hcell univ isOpen_univ (subset_univ _)
  let C := {c : EmbeddedClosedCell n X // K ⊆ c.interiorSet}
  have hnext (i : ℕ) (c : C) : ∃ d : C,
      d.1.carrier ⊆ c.1.interiorSet ∩ {x | infDist x K < 1 / ((i : ℝ) + 1)} := by
    obtain ⟨d, hdK, hd⟩ := hcell
      (c.1.interiorSet ∩ {x | infDist x K < 1 / ((i : ℝ) + 1)})
      (c.1.isOpen_interior.inter (isOpen_lt (continuous_infDist_pt K) continuous_const))
      (by
        intro x hx
        refine ⟨c.2 hx, ?_⟩
        change infDist x K < 1 / ((i : ℝ) + 1)
        rw [infDist_zero_of_mem hx]
        positivity)
    exact ⟨⟨d, hdK⟩, hd⟩
  let step (i : ℕ) (c : C) : C := Classical.choose (hnext i c)
  let seq : ℕ → C := fun i => Nat.rec ⟨c₀, hc₀⟩ step i
  have hstep (i : ℕ) : (seq (i + 1)).1.carrier ⊆
      (seq i).1.interiorSet ∩ {x | infDist x K < 1 / ((i : ℝ) + 1)} :=
    Classical.choose_spec (hnext i (seq i))
  refine ⟨fun i => (seq i).1, fun i => (hstep i).trans inter_subset_left, ?_⟩
  ext x
  constructor
  · intro hx
    exact mem_iInter.mpr fun i => (seq i).1.interiorSet_subset_carrier ((seq i).2 hx)
  · intro hx
    apply (hclosed.mem_iff_infDist_zero hne).mpr
    apply le_antisymm _ infDist_nonneg
    apply ge_of_tendsto (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact Filter.Eventually.of_forall fun i =>
      ((hstep i (mem_iInter.mp hx (i + 1))).2).le

end DifferentialGeometry.Topology
