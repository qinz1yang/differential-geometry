import DifferentialGeometry.Topology.ClosedCover
import Mathlib.Topology.UnitInterval

open Set

namespace DifferentialGeometry.Topology

variable {ι X Y : Type*} [Finite ι] [TopologicalSpace X] [TopologicalSpace Y]

theorem exists_continuous_homotopy_gluing (A : Set X) (B : ι → Set X)
    (hA : IsClosed A) (hB : ∀ i, IsClosed (B i))
    (hBA : ∀ i j, i ≠ j → B i ∩ B j ⊆ A)
    (f : C(X, Y)) (H : C(unitInterval × A, Y))
    (hH : ∀ x : A, H (0, x) = f x.val)
    (G : ∀ i, C(unitInterval × B i, Y))
    (hG₀ : ∀ i (x : B i), G i (0, x) = f x.val)
    (hG : ∀ i t x (hxA : x ∈ A) (hxB : x ∈ B i),
      G i (t, ⟨x, hxB⟩) = H (t, ⟨x, hxA⟩)) :
    ∃ F : C(unitInterval × ↥(A ∪ ⋃ i, B i), Y),
      (∀ x, F (0, x) = f x.val) ∧
      (∀ t (x : A), F (t, ⟨x.val, Or.inl x.property⟩) = H (t, x)) ∧
      ∀ i t (x : B i),
        F (t, ⟨x.val, Or.inr (mem_iUnion.mpr ⟨i, x.property⟩)⟩) = G i (t, x) := by
  let U := A ∪ ⋃ i, B i
  let P := unitInterval × U
  let S : Option ι → Set P := fun o => match o with
    | none => {z | z.2.val ∈ A}
    | some i => {z | z.2.val ∈ B i}
  let φ : ∀ o, C(S o, Y) := fun o => by
    cases o with
    | none =>
      exact ⟨fun z => H (z.val.1, ⟨z.val.2.val, z.property⟩),
        H.continuous.comp ((continuous_fst.comp continuous_subtype_val).prodMk
          ((continuous_subtype_val.comp
            (continuous_snd.comp continuous_subtype_val)).subtype_mk _))⟩
    | some i =>
      exact ⟨fun z => G i (z.val.1, ⟨z.val.2.val, z.property⟩),
        (G i).continuous.comp ((continuous_fst.comp continuous_subtype_val).prodMk
          ((continuous_subtype_val.comp
            (continuous_snd.comp continuous_subtype_val)).subtype_mk _))⟩
  have hφ : ∀ (i j : Option ι) (z : P) (hi : z ∈ S i) (hj : z ∈ S j),
      φ i ⟨z, hi⟩ = φ j ⟨z, hj⟩ := by
    intro i j z hi hj
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j => exact (hG j z.1 z.2.val hi hj).symm
    | some i =>
      cases j with
      | none => exact hG i z.1 z.2.val hj hi
      | some j =>
        by_cases hij : i = j
        · subst j
          rfl
        · have hzA := hBA i j hij ⟨hi, hj⟩
          exact (hG i z.1 z.2.val hzA hi).trans (hG j z.1 z.2.val hzA hj).symm
  have hcov : ⋃ o, S o = univ := by
    apply eq_univ_of_forall
    intro z
    rcases z.2.property with hzA | hzB
    · exact mem_iUnion.mpr ⟨none, hzA⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hzB
      exact mem_iUnion.mpr ⟨some i, hi⟩
  have hclosed : ∀ o, IsClosed (S o) := by
    intro o
    cases o with
    | none => exact hA.preimage (continuous_subtype_val.comp continuous_snd)
    | some i => exact (hB i).preimage (continuous_subtype_val.comp continuous_snd)
  let F := ContinuousMap.liftClosedCover S φ hφ hcov hclosed (locallyFinite_of_finite _)
  have hFA : ∀ t (x : A), F (t, ⟨x.val, Or.inl x.property⟩) = H (t, x) := by
    intro t x
    exact ContinuousMap.liftClosedCover_coe (S := S) (φ := φ) (hφ := hφ)
      (hcov := hcov) (hclosed := hclosed) (hfinite := locallyFinite_of_finite _)
      (i := none) ⟨(t, ⟨x.val, Or.inl x.property⟩), x.property⟩
  have hFB : ∀ i t (x : B i),
      F (t, ⟨x.val, Or.inr (mem_iUnion.mpr ⟨i, x.property⟩)⟩) = G i (t, x) := by
    intro i t x
    exact ContinuousMap.liftClosedCover_coe (S := S) (φ := φ) (hφ := hφ)
      (hcov := hcov) (hclosed := hclosed) (hfinite := locallyFinite_of_finite _)
      (i := some i) ⟨(t, ⟨x.val, Or.inr (mem_iUnion.mpr ⟨i, x.property⟩)⟩), x.property⟩
  refine ⟨F, ?_, hFA, hFB⟩
  intro x
  rcases x.property with hxA | hxB
  · exact (hFA 0 ⟨x.val, hxA⟩).trans (hH ⟨x.val, hxA⟩)
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hxB
    exact (hFB i 0 ⟨x.val, hi⟩).trans (hG₀ i ⟨x.val, hi⟩)

end DifferentialGeometry.Topology
