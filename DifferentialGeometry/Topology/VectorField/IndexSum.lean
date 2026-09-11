import DifferentialGeometry.Topology.VectorField.InteriorIndexTransport
import Mathlib.Algebra.BigOperators.Finprod

set_option autoImplicit false
noncomputable section
open Set Filter Bundle
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.VectorField
variable {d : ℕ} {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H)
  [IsManifold I 1 M]
  (V : ∀ x : M, TangentSpace I x) (hfinite : {x | V x = 0}.Finite)
  (hisolated : ∀ x, V x = 0 → HasContinuousIsolatedZero I V x)
  (hinterior : ∀ x, V x = 0 → I.IsInteriorPoint x)

def interiorIndexSum : ℤ :=
  ∑ p : hfinite.toFinset, interiorIndex I V p
    (hisolated p (hfinite.mem_toFinset.mp p.property))
    (hinterior p (hfinite.mem_toFinset.mp p.property))


theorem interiorIndexSum_eq_finsum :
    interiorIndexSum I V hfinite hisolated hinterior =
      ∑ᶠ p : {x | V x = 0}, interiorIndex I V p
        (hisolated p p.property) (hinterior p p.property) := by
  classical
  rw [interiorIndexSum,← finsum_eq_sum_of_fintype]
  exact finsum_comp_equiv (Equiv.setCongr hfinite.coe_toFinset)
    (f := fun p : {x | V x = 0} => interiorIndex I V p
      (hisolated p p.property) (hinterior p p.property))


theorem interiorIndexSum_eq_zero_of_nonzero (hzero : ∀ x, V x ≠ 0) :
    interiorIndexSum I V hfinite hisolated hinterior = 0 := by
  let : IsEmpty {x | V x = 0} := ⟨fun x => hzero x x.property⟩
  rw [interiorIndexSum_eq_finsum]
  exact finsum_of_isEmpty _


theorem interiorIndexSum_eq_zero_of_zeroSet_eq_empty (hzero : {x | V x = 0} = ∅) :
    interiorIndexSum I V hfinite hisolated hinterior = 0 := by
  apply interiorIndexSum_eq_zero_of_nonzero
  intro x hx
  have : x ∈ (∅ : Set M) := hzero ▸ hx
  exact this

theorem interiorIndexSum_eq_index_of_unique_zero (x : M) (hx : V x = 0)
    (hunique : ∀ y, V y = 0 → y = x) :
    interiorIndexSum I V hfinite hisolated hinterior =
      interiorIndex I V x (hisolated x hx) (hinterior x hx) := by
  let : Unique {x | V x = 0} :=
    ⟨⟨x,hx⟩,fun y => Subtype.ext (hunique y y.property)⟩
  rw [interiorIndexSum_eq_finsum,finsum_eq_sum_of_fintype,Fintype.sum_unique]
  rfl

theorem interiorIndexSum_neg :
    interiorIndexSum I (-V)
      (by simpa only [Pi.neg_apply,neg_eq_zero] using hfinite)
      (fun x hx => (hisolated x (neg_eq_zero.mp hx)).neg I)
      (fun x hx => hinterior x (neg_eq_zero.mp hx)) =
      (-1 : ℤ) ^ (d + 1) * interiorIndexSum I V hfinite hisolated hinterior := by
  have hz : {x | (-V) x = 0} = {x | V x = 0} := by
    ext x
    exact neg_eq_zero
  let e := Equiv.setCongr hz
  rw [interiorIndexSum_eq_finsum,interiorIndexSum_eq_finsum]
  calc
    _ = ∑ᶠ p : {x | (-V) x = 0}, (-1 : ℤ) ^ (d + 1) *
        interiorIndex I V (e p) (hisolated (e p) (e p).property)
          (hinterior (e p) (e p).property) := by
      apply finsum_congr
      intro p
      exact interiorIndex_neg I (hisolated p (neg_eq_zero.mp p.property))
        (hinterior p (neg_eq_zero.mp p.property))
    _ = (-1 : ℤ) ^ (d + 1) * ∑ᶠ p : {x | (-V) x = 0},
        interiorIndex I V (e p) (hisolated (e p) (e p).property)
          (hinterior (e p) (e p).property) := (mul_finsum _ _).symm
    _ = _ := congrArg (fun n : ℤ => (-1 : ℤ) ^ (d + 1) * n)
      (finsum_comp_equiv e (f := fun p : {x | V x = 0} =>
        interiorIndex I V p (hisolated p p.property) (hinterior p p.property)))

def interiorIndexSumOn (S : Set M) : ℤ := by
  classical
  exact ∑ p : hfinite.toFinset with p.val ∈ S, interiorIndex I V p
    (hisolated p (hfinite.mem_toFinset.mp p.property))
    (hinterior p (hfinite.mem_toFinset.mp p.property))

theorem interiorIndexSumOn_eq_finsum (S : Set M) :
    interiorIndexSumOn I V hfinite hisolated hinterior S =
      ∑ᶠ p : {x | V x = 0 ∧ x ∈ S}, interiorIndex I V p
        (hisolated p p.property.1) (hinterior p p.property.1) := by
  classical
  let t : Finset hfinite.toFinset := Finset.univ.filter (fun p => p.val ∈ S)
  let e : t ≃ {x | V x = 0 ∧ x ∈ S} := {
    toFun p := ⟨p.val.val,hfinite.mem_toFinset.mp p.val.property,
      (Finset.mem_filter.mp p.property).2⟩
    invFun p := ⟨⟨p.val,hfinite.mem_toFinset.mpr p.property.1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,p.property.2⟩⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  let q : hfinite.toFinset → ℤ := fun p => interiorIndex I V p
    (hisolated p (hfinite.mem_toFinset.mp p.property))
    (hinterior p (hfinite.mem_toFinset.mp p.property))
  change ∑ p ∈ t, q p = _
  rw [← Finset.sum_coe_sort t q,← finsum_eq_sum_of_fintype]
  exact finsum_comp_equiv e (f := fun p : {x | V x = 0 ∧ x ∈ S} =>
    interiorIndex I V p (hisolated p p.property.1) (hinterior p p.property.1))

theorem interiorIndexSumOn_eq_of_germ (W : ∀ x : M, TangentSpace I x)
    (hWfinite : {x | W x = 0}.Finite)
    (hWisolated : ∀ x, W x = 0 → HasContinuousIsolatedZero I W x)
    (hWinterior : ∀ x, W x = 0 → I.IsInteriorPoint x)
    (S : Set M) (hVW : ∀ x ∈ S, V =ᶠ[𝓝 x] W) :
    interiorIndexSumOn I V hfinite hisolated hinterior S =
      interiorIndexSumOn I W hWfinite hWisolated hWinterior S := by
  have hz : {x | V x = 0 ∧ x ∈ S} = {x | W x = 0 ∧ x ∈ S} := by
    ext x
    constructor
    · rintro ⟨hx,hxS⟩
      exact ⟨(hVW x hxS).eq_of_nhds.symm.trans hx,hxS⟩
    · rintro ⟨hx,hxS⟩
      exact ⟨(hVW x hxS).eq_of_nhds.trans hx,hxS⟩
  let e := Equiv.setCongr hz
  rw [interiorIndexSumOn_eq_finsum,interiorIndexSumOn_eq_finsum]
  calc
    _ = ∑ᶠ p : {x | V x = 0 ∧ x ∈ S}, interiorIndex I W (e p)
        (hWisolated (e p) (e p).property.1) (hWinterior (e p) (e p).property.1) := by
      apply finsum_congr
      intro p
      exact interiorIndex_congr I (hisolated p p.property.1)
        (hWisolated (e p) (e p).property.1) (hVW p p.property.2)
        (hinterior p p.property.1)
    _ = _ := finsum_comp_equiv e (f := fun p : {x | W x = 0 ∧ x ∈ S} =>
      interiorIndex I W p (hWisolated p p.property.1) (hWinterior p p.property.1))


@[simp]
theorem interiorIndexSumOn_empty :
    interiorIndexSumOn I V hfinite hisolated hinterior ∅ = 0 := by
  classical
  simp [interiorIndexSumOn]


@[simp]
theorem interiorIndexSumOn_univ :
    interiorIndexSumOn I V hfinite hisolated hinterior univ =
      interiorIndexSum I V hfinite hisolated hinterior := by
  classical
  simp [interiorIndexSumOn,interiorIndexSum]


theorem interiorIndexSumOn_add_compl (S : Set M) :
    interiorIndexSumOn I V hfinite hisolated hinterior S +
      interiorIndexSumOn I V hfinite hisolated hinterior Sᶜ =
        interiorIndexSum I V hfinite hisolated hinterior := by
  classical
  simpa only [interiorIndexSumOn,interiorIndexSum,Set.mem_compl_iff] using
    Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun p : hfinite.toFinset => p.val ∈ S)
    (fun p => interiorIndex I V p (hisolated p (hfinite.mem_toFinset.mp p.property))
      (hinterior p (hfinite.mem_toFinset.mp p.property)))


theorem interiorIndexSumOn_union {S T : Set M} (hST : Disjoint S T) :
    interiorIndexSumOn I V hfinite hisolated hinterior (S ∪ T) =
      interiorIndexSumOn I V hfinite hisolated hinterior S +
      interiorIndexSumOn I V hfinite hisolated hinterior T := by
  classical
  unfold interiorIndexSumOn
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hs : p.val ∈ S
  · have ht : p.val ∉ T := fun ht => Set.disjoint_left.mp hST hs ht
    simp [hs,ht]
  · by_cases ht : p.val ∈ T <;> simp [hs,ht]

theorem interiorIndexSumOn_biUnion {ι : Type*} (s : Finset ι) (S : ι → Set M)
    (hdis : (s : Set ι).PairwiseDisjoint S) :
    interiorIndexSumOn I V hfinite hisolated hinterior (⋃ i ∈ s, S i) =
      ∑ i ∈ s, interiorIndexSumOn I V hfinite hisolated hinterior (S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hsdis : (s : Set ι).PairwiseDisjoint S :=
      fun j hj k hk hne => hdis (Finset.mem_insert_of_mem hj)
        (Finset.mem_insert_of_mem hk) hne
    have hsplit : Disjoint (S i) (⋃ j ∈ s, S j) := by
      apply Set.disjoint_iUnion_right.mpr
      intro j
      apply Set.disjoint_iUnion_right.mpr
      intro hj
      exact hdis (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hj)
        (fun he => hi (he ▸ hj))
    have hUnion : (⋃ j ∈ insert i s, S j) = S i ∪ ⋃ j ∈ s, S j := by
      ext x
      simp
    rw [hUnion,interiorIndexSumOn_union I V hfinite hisolated hinterior hsplit,
      ih hsdis,Finset.sum_insert hi]

end DifferentialGeometry.VectorField
