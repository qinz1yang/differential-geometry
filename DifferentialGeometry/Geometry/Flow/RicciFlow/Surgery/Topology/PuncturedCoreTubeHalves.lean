import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCoreDeformationRetract

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace TubeSystem

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)

theorem range_tube_eq_positiveTube_union_middleSphere_union_negativeTube (a : T.Index) :
    range (T.tube a) = T.positiveTube a ∪ (T.middleSphere a ∪ T.negativeTube a) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    rcases lt_trichotomy z.2.1 0 with h | h | h
    · exact Or.inr (Or.inr ⟨z, h, rfl⟩)
    · exact Or.inr (Or.inl ⟨z, h, rfl⟩)
    · exact Or.inl ⟨z, h, rfl⟩
  · rintro (h | h | h)
    · exact image_subset_range _ _ h
    · exact image_subset_range _ _ h
    · exact image_subset_range _ _ h

theorem mem_puncturedCore_of_mem_range_of_tubeCoord_ne_zero {a : T.Index} {x : M}
    (ha : x ∈ range (T.tube a)) (hz : (T.tubeCoord a x ha).2.1 ≠ 0) :
    x ∈ T.puncturedCore := by
  rw [T.mem_puncturedCore_iff]
  intro b hb
  obtain ⟨w, hw, hwz⟩ := hb
  by_cases hba : b = a
  · subst hba
    have hcoord : T.tubeCoord b x ha = w := T.tubeCoord_eq_of_eq_tube ha hwz
    rw [hcoord] at hz
    exact hz hw
  · exact Set.disjoint_left.mp (T.disjoint (Ne.symm hba)) ha ⟨w, hwz⟩

theorem positiveTube_subset_puncturedCore (a : T.Index) :
    T.positiveTube a ⊆ T.puncturedCore := by
  rintro x ⟨z, hz, rfl⟩
  refine T.mem_puncturedCore_of_mem_range_of_tubeCoord_ne_zero (mem_range_self z) ?_
  rw [T.tubeCoord_tube]
  exact ne_of_gt hz

theorem negativeTube_subset_puncturedCore (a : T.Index) :
    T.negativeTube a ⊆ T.puncturedCore := by
  rintro x ⟨z, hz, rfl⟩
  refine T.mem_puncturedCore_of_mem_range_of_tubeCoord_ne_zero (mem_range_self z) ?_
  rw [T.tubeCoord_tube]
  exact ne_of_lt hz

theorem union_puncturedCore_tubeHalves_eq_puncturedCore (a : T.Index) :
    T.puncturedCore ∪ (T.positiveTube a ∪ T.negativeTube a) = T.puncturedCore :=
  Set.union_eq_left.mpr
    (Set.union_subset (T.positiveTube_subset_puncturedCore a)
      (T.negativeTube_subset_puncturedCore a))

theorem disjoint_middleSphere_tubeHalves (a : T.Index) :
    Disjoint (T.middleSphere a) (T.positiveTube a ∪ T.negativeTube a) := by
  rw [Set.disjoint_left]
  rintro x ⟨z, hz, rfl⟩ (h | h)
  · obtain ⟨w, hw, hwz⟩ := h
    simp only [Set.mem_ofPred_eq] at hz hw
    have hwz' : w = z := (T.embedding a).injective hwz
    subst hwz'
    exact absurd hw (not_lt_of_ge (le_of_eq hz))
  · obtain ⟨w, hw, hwz⟩ := h
    simp only [Set.mem_ofPred_eq] at hz hw
    have hwz' : w = z := (T.embedding a).injective hwz
    subst hwz'
    exact absurd hw (not_lt_of_ge (by rw [hz]))

theorem puncturedCore_ne_univ (a : T.Index) (y : Sphere 2) :
    T.puncturedCore ≠ univ := by
  intro h
  have hmem : T.tube a (y, (⟨0, by norm_num, by norm_num⟩ : Icc (-2 : ℝ) 2)) ∈
      T.middleSphere a :=
    ⟨_, rfl, rfl⟩
  have hcore : T.tube a (y, (⟨0, by norm_num, by norm_num⟩ : Icc (-2 : ℝ) 2)) ∈
      T.puncturedCore := by
    rw [h]
    trivial
  exact ((T.mem_puncturedCore_iff _).mp hcore a) hmem

end TubeSystem

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
