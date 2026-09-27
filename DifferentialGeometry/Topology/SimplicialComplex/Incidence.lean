import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Powerset

open Finset

namespace DifferentialGeometry.Topology.SimplicialComplex

variable {ι : Type*}


def link [DecidableEq ι] (K : PreAbstractSimplicialComplex ι) (s : Finset ι) :
    PreAbstractSimplicialComplex ι where
  faces := {t | t.Nonempty ∧ Disjoint s t ∧ s ∪ t ∈ K}
  isRelLowerSet_faces := by
    intro t ht
    refine ⟨ht.1, ?_⟩
    intro u hut hu
    refine ⟨hu, ht.2.1.mono_right hut, ?_⟩
    exact (K.isRelLowerSet_faces ht.2.2).2 (union_subset_union_right hut)
      (hu.mono subset_union_right)

@[simp]
theorem mem_link [DecidableEq ι] {K : PreAbstractSimplicialComplex ι} {s t : Finset ι} :
    t ∈ link K s ↔ t.Nonempty ∧ Disjoint s t ∧ s ∪ t ∈ K := Iff.rfl

theorem link_le [DecidableEq ι] (K : PreAbstractSimplicialComplex ι) (s : Finset ι) :
    link K s ≤ K := by
  intro t ht
  exact (K.isRelLowerSet_faces ht.2.2).2 subset_union_right ht.1

instance [DecidableEq ι] (K : PreAbstractSimplicialComplex ι) [Finite K.faces]
    (s : Finset ι) : Finite (link K s).faces :=
  Set.Finite.to_subtype ((Set.toFinite K.faces).subset (link_le K s))

instance : Finite (⊥ : PreAbstractSimplicialComplex ι).faces :=
  Set.finite_empty.to_subtype

instance (K L : PreAbstractSimplicialComplex ι) [Finite K.faces] [Finite L.faces] :
    Finite (K ⊔ L).faces :=
  ((Set.toFinite K.faces).union (Set.toFinite L.faces)).to_subtype

instance (K : PreAbstractSimplicialComplex ι) [Finite K.faces]
    (L : PreAbstractSimplicialComplex ι) : Finite (K ⊓ L).faces :=
  ((Set.toFinite K.faces).subset Set.inter_subset_left).to_subtype

instance {κ : Type*} [DecidableEq κ] (K : PreAbstractSimplicialComplex ι) [Finite K.faces]
    (f : ι → κ) : Finite (K.map f).faces :=
  ((Set.toFinite K.faces).image (fun s => s.image f)).to_subtype

noncomputable section

variable (K : PreAbstractSimplicialComplex ι) [Finite K.faces]


def facesOfCard (n : ℕ) : Finset (Finset ι) :=
  (Set.toFinite K.faces).toFinset.filter (fun s => s.card = n)

@[simp]
theorem mem_facesOfCard {n : ℕ} {s : Finset ι} :
    s ∈ facesOfCard K n ↔ s ∈ K ∧ s.card = n := by
  classical
  change s ∈ (Set.toFinite K.faces).toFinset.filter (fun s => s.card = n) ↔
    s ∈ K.faces ∧ s.card = n
  simp

@[simp]
theorem facesOfCard_zero : facesOfCard K 0 = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  obtain ⟨hs, hcard⟩ := (mem_facesOfCard K).mp hs
  exact (K.isRelLowerSet_faces hs).1.ne_empty (card_eq_zero.mp hcard)


def cofaces [DecidableEq ι] (s : Finset ι) (n : ℕ) : Finset (Finset ι) :=
  (facesOfCard K n).filter (s ⊆ ·)

@[simp]
theorem mem_cofaces [DecidableEq ι] {s t : Finset ι} {n : ℕ} :
    t ∈ cofaces K s n ↔ t ∈ K ∧ t.card = n ∧ s ⊆ t := by
  simp [cofaces, and_assoc]

def linkFaceEquiv [DecidableEq ι] (s : Finset ι) (n : ℕ) (hn : 0 < n) :
    {t // t ∈ facesOfCard (link K s) n} ≃
      {u // u ∈ cofaces K s (s.card + n)} where
  toFun t := ⟨s ∪ t.1, by
    obtain ⟨⟨_, hd, hface⟩, hc⟩ := (mem_facesOfCard (link K s)).mp t.2
    exact (mem_cofaces K).mpr ⟨hface, by rw [card_union_of_disjoint hd, hc],
      subset_union_left⟩⟩
  invFun u := ⟨u.1 \ s, by
    obtain ⟨hface, hc, hsu⟩ := (mem_cofaces K).mp u.2
    have hcard : (u.1 \ s).card = n := by
      rw [card_sdiff_of_subset hsu, hc, Nat.add_sub_cancel_left]
    apply (mem_facesOfCard (link K s)).mpr
    exact ⟨⟨card_pos.mp (by omega), disjoint_sdiff_self_right,
      by simpa only [union_sdiff_of_subset hsu] using hface⟩, hcard⟩⟩
  left_inv t := by
    apply Subtype.ext
    exact union_sdiff_cancel_left ((mem_facesOfCard (link K s)).mp t.2).1.2.1
  right_inv u := by
    apply Subtype.ext
    exact union_sdiff_of_subset ((mem_cofaces K).mp u.2).2.2

@[simp]
theorem linkFaceEquiv_apply [DecidableEq ι] (s : Finset ι) (n : ℕ) (hn : 0 < n)
    (t : {t // t ∈ facesOfCard (link K s) n}) :
    (linkFaceEquiv K s n hn t).1 = s ∪ t.1 := rfl

@[simp]
theorem linkFaceEquiv_symm_apply [DecidableEq ι] (s : Finset ι) (n : ℕ) (hn : 0 < n)
    (u : {u // u ∈ cofaces K s (s.card + n)}) :
    ((linkFaceEquiv K s n hn).symm u).1 = u.1 \ s := rfl


theorem card_facesOfCard_link [DecidableEq ι] (s : Finset ι) (n : ℕ) (hn : 0 < n) :
    (facesOfCard (link K s) n).card = (cofaces K s (s.card + n)).card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (linkFaceEquiv K s n hn)

theorem sum_card_cofaces [DecidableEq ι] (k n : ℕ) (hk : 0 < k) :
    ∑ s ∈ facesOfCard K k, (cofaces K s n).card =
      n.choose k * (facesOfCard K n).card := by
  classical
  have hcount (t : Finset ι) (ht : t ∈ facesOfCard K n) :
      ((facesOfCard K k).filter (· ⊆ t)) = t.powersetCard k := by
    ext s
    simp only [mem_filter, mem_facesOfCard, mem_powersetCard]
    constructor
    · rintro ⟨⟨_, hs⟩, hst⟩
      exact ⟨hst, hs⟩
    · rintro ⟨hst, hs⟩
      exact ⟨⟨(K.isRelLowerSet_faces ((mem_facesOfCard K).mp ht).1).2 hst
        (card_pos.mp (hs ▸ hk)), hs⟩, hst⟩
  calc
    _ = ∑ t ∈ facesOfCard K n, ((facesOfCard K k).filter (· ⊆ t)).card := by
      exact Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (fun s t : Finset ι => s ⊆ t)
    _ = ∑ t ∈ facesOfCard K n, n.choose k := by
      apply sum_congr rfl
      intro t ht
      rw [hcount t ht, card_powersetCard, ((mem_facesOfCard K).mp ht).2]
    _ = _ := by simp [Nat.mul_comm]


theorem sum_card_facesOfCard_link [DecidableEq ι] (k n : ℕ) (hk : 0 < k) (hn : 0 < n) :
    ∑ s ∈ facesOfCard K k, (facesOfCard (link K s) n).card =
      (k + n).choose k * (facesOfCard K (k + n)).card := by
  calc
    _ = ∑ s ∈ facesOfCard K k, (cofaces K s (k + n)).card := by
      apply sum_congr rfl
      intro s hs
      rw [card_facesOfCard_link K s n hn, ((mem_facesOfCard K).mp hs).2]
    _ = _ := sum_card_cofaces K k (k + n) hk

end

end DifferentialGeometry.Topology.SimplicialComplex
