import DifferentialGeometry.Topology.SimplicialComplex.BoundaryCounting
import Mathlib.Data.Nat.Choose.Sum

open Finset

namespace DifferentialGeometry.Topology.SimplicialComplex

variable {ι : Type*}


def simplex (vertices : Finset ι) : PreAbstractSimplicialComplex ι where
  faces := {s | s.Nonempty ∧ s ⊆ vertices}
  isRelLowerSet_faces := fun {_s} hs => ⟨hs.1, fun _ hts ht => ⟨ht, hts.trans hs.2⟩⟩


def boundarySimplex (vertices : Finset ι) : PreAbstractSimplicialComplex ι where
  faces := {s | s.Nonempty ∧ s ⊂ vertices}
  isRelLowerSet_faces := fun {_s} hs => ⟨hs.1, fun _ hts ht => ⟨ht, lt_of_le_of_lt hts hs.2⟩⟩

@[simp]
theorem mem_simplex {vertices s : Finset ι} :
    s ∈ simplex vertices ↔ s.Nonempty ∧ s ⊆ vertices := Iff.rfl

@[simp]
theorem mem_boundarySimplex {vertices s : Finset ι} :
    s ∈ boundarySimplex vertices ↔ s.Nonempty ∧ s ⊂ vertices := Iff.rfl

theorem boundarySimplex_le_simplex (vertices : Finset ι) :
    boundarySimplex vertices ≤ simplex vertices :=
  fun _ hs => ⟨hs.1, hs.2.le⟩

instance (vertices : Finset ι) : Finite (simplex vertices).faces := by
  classical
  apply Set.Finite.to_subtype
  exact vertices.powerset.finite_toSet.subset fun s hs => mem_powerset.mpr hs.2

instance (vertices : Finset ι) : Finite (boundarySimplex vertices).faces :=
  Set.Finite.to_subtype ((Set.toFinite (simplex vertices).faces).subset
    (boundarySimplex_le_simplex vertices))

@[simp]
theorem simplex_empty : simplex (∅ : Finset ι) = ⊥ := by
  ext s
  change (s.Nonempty ∧ s ⊆ (∅ : Finset ι)) ↔ False
  simp only [subset_empty]
  constructor
  · rintro ⟨h, rfl⟩
    exact h.ne_empty rfl
  · exact False.elim

@[simp]
theorem boundarySimplex_empty : boundarySimplex (∅ : Finset ι) = ⊥ := by
  apply le_antisymm
  · simpa only [simplex_empty] using boundarySimplex_le_simplex (∅ : Finset ι)
  · exact bot_le


theorem link_simplex [DecidableEq ι] {vertices s : Finset ι} (hs : s ⊆ vertices) :
    link (simplex vertices) s = simplex (vertices \ s) := by
  ext t
  change (t.Nonempty ∧ Disjoint s t ∧ (s ∪ t).Nonempty ∧ s ∪ t ⊆ vertices) ↔
    (t.Nonempty ∧ t ⊆ vertices \ s)
  simp only [subset_sdiff, union_subset_iff]
  constructor
  · rintro ⟨ht, hdisj, _, _, htv⟩
    exact ⟨ht, htv, hdisj.symm⟩
  · rintro ⟨ht, htv, hdisj⟩
    exact ⟨ht, hdisj.symm, ht.mono subset_union_right, hs, htv⟩


theorem link_boundarySimplex [DecidableEq ι] {vertices s : Finset ι} (hs : s ⊆ vertices) :
    link (boundarySimplex vertices) s = boundarySimplex (vertices \ s) := by
  ext t
  change (t.Nonempty ∧ Disjoint s t ∧ (s ∪ t).Nonempty ∧ s ∪ t ⊂ vertices) ↔
    (t.Nonempty ∧ t ⊂ vertices \ s)
  constructor
  · rintro ⟨ht, hdisj, _, hproper⟩
    refine ⟨ht, lt_of_le_of_ne ?_ ?_⟩
    · exact subset_sdiff.mpr ⟨subset_union_right.trans hproper.le, hdisj.symm⟩
    · intro heq
      exact hproper.ne (by rw [heq, union_sdiff_of_subset hs])
  · rintro ⟨ht, hproper⟩
    obtain ⟨htv, hdisj⟩ := subset_sdiff.mp hproper.le
    refine ⟨ht, hdisj.symm, ht.mono subset_union_right,
      lt_of_le_of_ne (union_subset hs htv) ?_⟩
    intro heq
    have heq' := congrArg (fun u : Finset ι => u \ s) heq
    rw [union_sdiff_cancel_left hdisj.symm] at heq'
    exact hproper.ne heq'

noncomputable section


theorem facesOfCard_simplex (vertices : Finset ι) (n : ℕ) (hn : 0 < n) :
    facesOfCard (simplex vertices) n = vertices.powersetCard n := by
  classical
  ext s
  simp only [mem_facesOfCard, mem_simplex, mem_powersetCard]
  constructor
  · rintro ⟨⟨_, hsv⟩, hc⟩
    exact ⟨hsv, hc⟩
  · rintro ⟨hsv, hc⟩
    exact ⟨⟨card_pos.mp (hc ▸ hn), hsv⟩, hc⟩

theorem card_facesOfCard_simplex (vertices : Finset ι) (n : ℕ) (hn : 0 < n) :
    (facesOfCard (simplex vertices) n).card = vertices.card.choose n := by
  rw [facesOfCard_simplex vertices n hn, card_powersetCard]


theorem facesOfCard_boundarySimplex [DecidableEq ι] (vertices : Finset ι) (n : ℕ) :
    facesOfCard (boundarySimplex vertices) n =
      (facesOfCard (simplex vertices) n).erase vertices := by
  ext s
  simp only [mem_facesOfCard, mem_boundarySimplex, mem_erase, mem_simplex,
    lt_iff_le_and_ne]
  tauto


theorem facesOfCard_boundarySimplex_of_lt (vertices : Finset ι) (n : ℕ)
    (hn : 0 < n) (hlt : n < vertices.card) :
    facesOfCard (boundarySimplex vertices) n = vertices.powersetCard n := by
  classical
  rw [facesOfCard_boundarySimplex, facesOfCard_simplex vertices n hn,
    erase_eq_of_notMem]
  simp only [mem_powersetCard, subset_refl, true_and]
  omega

theorem card_facesOfCard_boundarySimplex_of_lt (vertices : Finset ι) (n : ℕ)
    (hn : 0 < n) (hlt : n < vertices.card) :
    (facesOfCard (boundarySimplex vertices) n).card = vertices.card.choose n := by
  rw [facesOfCard_boundarySimplex_of_lt vertices n hn hlt, card_powersetCard]


theorem facesOfCard_boundarySimplex_eq_empty (vertices : Finset ι) (n : ℕ)
    (hn : vertices.card ≤ n) : facesOfCard (boundarySimplex vertices) n = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro s hs
  obtain ⟨⟨_, hproper⟩, hc⟩ := (mem_facesOfCard (boundarySimplex vertices)).mp hs
  have hlt := card_lt_card hproper
  omega

private theorem simplex_faces_toFinset [DecidableEq ι] (vertices : Finset ι) :
    (Set.toFinite (simplex vertices).faces).toFinset = vertices.powerset.erase ∅ := by
  ext s
  simp only [Set.Finite.mem_toFinset, mem_erase, mem_powerset]
  change (s.Nonempty ∧ s ⊆ vertices) ↔ (s ≠ ∅ ∧ s ⊆ vertices)
  rw [nonempty_iff_ne_empty]

private theorem boundarySimplex_faces_toFinset [DecidableEq ι] (vertices : Finset ι) :
    (Set.toFinite (boundarySimplex vertices).faces).toFinset =
      (Set.toFinite (simplex vertices).faces).toFinset.erase vertices := by
  ext s
  simp only [Set.Finite.mem_toFinset, mem_erase]
  change (s.Nonempty ∧ s ⊂ vertices) ↔ (s ≠ vertices ∧ s.Nonempty ∧ s ⊆ vertices)
  rw [lt_iff_le_and_ne]
  tauto


theorem faceEulerChar_simplex {vertices : Finset ι} (hvertices : vertices.Nonempty) :
    faceEulerChar (simplex vertices) = 1 := by
  classical
  rw [faceEulerChar, simplex_faces_toFinset, sum_neg_distrib]
  have hsum := sum_erase_add (s := vertices.powerset)
    (f := fun s : Finset ι => (-1 : ℤ) ^ s.card) (mem_powerset.mpr (empty_subset vertices))
  rw [sum_powerset_neg_one_pow_card_of_nonempty hvertices] at hsum
  simp only [card_empty, pow_zero] at hsum
  omega


theorem faceEulerChar_boundarySimplex {vertices : Finset ι} (hvertices : vertices.Nonempty) :
    faceEulerChar (boundarySimplex vertices) = 1 + (-1 : ℤ) ^ vertices.card := by
  classical
  have hmem : vertices ∈ (Set.toFinite (simplex vertices).faces).toFinset := by
    exact (Set.toFinite (simplex vertices).faces).mem_toFinset.mpr ⟨hvertices, subset_refl _⟩
  have hsum := sum_erase_add (s := (Set.toFinite (simplex vertices).faces).toFinset)
    (f := fun s : Finset ι => -(-1 : ℤ) ^ s.card) hmem
  have hsimplex := faceEulerChar_simplex hvertices
  rw [faceEulerChar, boundarySimplex_faces_toFinset]
  change (∑ s ∈ (Set.toFinite (simplex vertices).faces).toFinset.erase vertices,
    -(-1 : ℤ) ^ s.card) + -(-1 : ℤ) ^ vertices.card =
    faceEulerChar (simplex vertices) at hsum
  rw [hsimplex] at hsum
  omega


theorem faceEulerChar_link_simplex [DecidableEq ι] {vertices s : Finset ι}
    (hs : s ⊂ vertices) : faceEulerChar (link (simplex vertices) s) = 1 := by
  simpa only [link_simplex hs.le] using
    faceEulerChar_simplex (sdiff_nonempty.mpr hs.not_ge)


theorem faceEulerChar_link_boundarySimplex [DecidableEq ι] {vertices s : Finset ι}
    (hs : s ⊂ vertices) :
    faceEulerChar (link (boundarySimplex vertices) s) =
      1 + (-1 : ℤ) ^ (vertices.card - s.card) := by
  simpa only [link_boundarySimplex hs.le, card_sdiff_of_subset hs.le] using
    faceEulerChar_boundarySimplex (sdiff_nonempty.mpr hs.not_ge)


theorem tetrahedron_face_counts :
    (facesOfCard (simplex (univ : Finset (Fin 4))) 1).card = 4 ∧
    (facesOfCard (simplex (univ : Finset (Fin 4))) 2).card = 6 ∧
    (facesOfCard (simplex (univ : Finset (Fin 4))) 3).card = 4 ∧
    (facesOfCard (simplex (univ : Finset (Fin 4))) 4).card = 1 := by
  norm_num [card_facesOfCard_simplex, Nat.choose]


theorem tetrahedron_boundary_face_counts :
    (facesOfCard (boundarySimplex (univ : Finset (Fin 4))) 1).card = 4 ∧
    (facesOfCard (boundarySimplex (univ : Finset (Fin 4))) 2).card = 6 ∧
    (facesOfCard (boundarySimplex (univ : Finset (Fin 4))) 3).card = 4 ∧
    (facesOfCard (boundarySimplex (univ : Finset (Fin 4))) 4).card = 0 := by
  rw [card_facesOfCard_boundarySimplex_of_lt _ 1 (by omega) (by simp),
    card_facesOfCard_boundarySimplex_of_lt _ 2 (by omega) (by simp),
    card_facesOfCard_boundarySimplex_of_lt _ 3 (by omega) (by simp),
    facesOfCard_boundarySimplex_eq_empty _ 4 (by simp)]
  norm_num [Nat.choose]

theorem faceEulerChar_boundarySimplex_eq_two_mul_of_card_eq_four
    (vertices : Finset ι) (hcard : vertices.card = 4) :
    faceEulerChar (boundarySimplex vertices) = 2 * faceEulerChar (simplex vertices) := by
  classical
  have hproper {s : Finset ι} {k : ℕ}
      (hs : s ∈ facesOfCard (simplex vertices) k) (hk : k < 4) : s ⊂ vertices := by
    obtain ⟨⟨_, hsub⟩, hsc⟩ := (mem_facesOfCard (simplex vertices)).mp hs
    apply lt_of_le_of_ne hsub
    intro heq
    have := congrArg Finset.card heq
    omega
  apply faceEulerChar_eq_two_mul_of_link_counts (simplex vertices) (boundarySimplex vertices)
    (boundarySimplex_le_simplex vertices)
  · intro u hu
    exact hcard ▸ card_le_card hu.2
  · intro u hu
    have := card_lt_card hu.2
    omega
  · intro s hs
    have hsp := hproper hs (by decide)
    obtain ⟨⟨hsne, hsub⟩, hsc⟩ := (mem_facesOfCard (simplex vertices)).mp hs
    have hboundary : s ∈ boundarySimplex vertices := ⟨hsne, hsp⟩
    rw [if_pos hboundary]
    have hlink : (facesOfCard (link (simplex vertices) s) 1).card = 1 := by
      simpa [link_simplex hsub, card_sdiff_of_subset hsub, hcard, hsc] using
        card_facesOfCard_simplex (vertices \ s) 1 (by decide)
    have hco := (card_facesOfCard_link (simplex vertices) s 1 (by decide)).symm.trans hlink
    simpa only [hsc] using hco
  · intro s hs
    have hsp := hproper hs (by decide)
    have hboundary : s ∈ boundarySimplex vertices :=
      ⟨((mem_facesOfCard (simplex vertices)).mp hs).1.1, hsp⟩
    rw [if_pos hboundary]
    exact faceEulerChar_link_simplex hsp
  · intro s hs
    have hsp := hproper hs (by decide)
    have hboundary : s ∈ boundarySimplex vertices :=
      ⟨((mem_facesOfCard (simplex vertices)).mp hs).1.1, hsp⟩
    rw [if_pos hboundary]
    exact faceEulerChar_link_simplex hsp


theorem tetrahedron_boundary_faceEulerChar :
    faceEulerChar (boundarySimplex (univ : Finset (Fin 4))) =
      2 * faceEulerChar (simplex (univ : Finset (Fin 4))) :=
  faceEulerChar_boundarySimplex_eq_two_mul_of_card_eq_four univ (by simp)

end

end DifferentialGeometry.Topology.SimplicialComplex
