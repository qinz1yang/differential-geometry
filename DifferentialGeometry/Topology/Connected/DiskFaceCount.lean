import Mathlib.Topology.Clopen
import Mathlib.Topology.Connected.Clopen
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

/-!
# Disk faces of a connected surface split into disks and circle-bundle pieces (FC40, incidence part)

A connected space `Y` is covered by finitely many pairwise disjoint closed "disks" `D i` and finitely many
pairwise disjoint nonempty closed "circle-bundle components" `B j`.  Each disk has one boundary circle, lying in
the bundle component `side i`, and a disk meets a bundle component only along that circle.  Every bundle component
has `0` (closed, base a circle) or `2` (annulus, base an interval) boundary circles.  Then there is exactly one
bundle component, and the number of disks is `0` or `2`.

This is the Euler-characteristic-free part of FC40.  Deciding `0` for `T²` and `2` for `S²` needs a recognition
statement for closed surfaces (FC40b), which is not in this file.
-/

set_option autoImplicit false

open Set Finset Function

namespace DifferentialGeometry.Topology

/-- **FC40a.** The disk-face dichotomy on actual embedded pieces of a connected space. -/
theorem disk_face_count_dichotomy {Y ι κ : Type*} [TopologicalSpace Y] [ConnectedSpace Y]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (D : ι → Set Y) (B : κ → Set Y) (hD : ∀ i, IsClosed (D i)) (hB : ∀ j, IsClosed (B j))
    (hBne : ∀ j, (B j).Nonempty) (hcover : (⋃ i, D i) ∪ (⋃ j, B j) = univ)
    (hDD : Pairwise (Disjoint on D)) (hBB : Pairwise (Disjoint on B))
    (side : ι → κ) (hDB : ∀ i j, (D i ∩ B j).Nonempty → side i = j)
    (hdeg : ∀ j, (univ.filter (fun i => side i = j)).card = 0 ∨
      (univ.filter (fun i => side i = j)).card = 2) :
    Fintype.card κ = 1 ∧ (Fintype.card ι = 0 ∨ Fintype.card ι = 2) := by
  classical
  -- the star of a bundle component: itself and the disks attached to it
  let S : κ → Set Y := fun j => B j ∪ ⋃ i ∈ univ.filter (fun i => side i = j), D i
  have hSclosed : ∀ j, IsClosed (S j) := fun j =>
    (hB j).union (isClosed_biUnion_finset fun i _ => hD i)
  have hSmem : ∀ y, ∃ j, y ∈ S j := by
    intro y
    have hy : y ∈ (⋃ i, D i) ∪ (⋃ j, B j) := hcover ▸ mem_univ y
    rcases hy with hy | hy
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      exact ⟨side i, Or.inr (mem_biUnion (by simp) hi)⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hy
      exact ⟨j, Or.inl hj⟩
  have hSdisj : ∀ j j', j ≠ j' → Disjoint (S j) (S j') := by
    intro j j' hjj'
    rw [Set.disjoint_left]
    intro y hy hy'
    rcases hy with hy | hy <;> rcases hy' with hy' | hy'
    · exact Set.disjoint_left.mp (hBB hjj') hy hy'
    · obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hy'
      have hside : side i = j := hDB i j ⟨y, hyi, hy⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact hjj' (hside.symm.trans hi)
    · obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hy
      have hside : side i = j' := hDB i j' ⟨y, hyi, hy'⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact hjj' (hi.symm.trans hside)
    · obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hy
      obtain ⟨i', hi', hyi'⟩ := mem_iUnion₂.mp hy'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
      have hii' : i ≠ i' := fun h => hjj' (hi.symm.trans (h ▸ hi'))
      exact Set.disjoint_left.mp (hDD hii') hyi hyi'
  have hSclopen : ∀ j, IsClopen (S j) := by
    intro j
    refine ⟨hSclosed j, ?_⟩
    have hcompl : (S j)ᶜ = ⋃ j' ∈ univ.filter (fun j' => j' ≠ j), S j' := by
      ext y
      simp only [mem_compl_iff, mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
        exists_prop]
      constructor
      · intro hy
        obtain ⟨j', hj'⟩ := hSmem y
        exact ⟨j', fun h => hy (h ▸ hj'), hj'⟩
      · rintro ⟨j', hj', hy'⟩ hy
        exact Set.disjoint_left.mp (hSdisj j' j hj') hy' hy
    rw [← isClosed_compl_iff, hcompl]
    exact isClosed_biUnion_finset fun j' _ => hSclosed j'
  -- exactly one bundle component
  have hcard : Fintype.card κ = 1 := by
    obtain ⟨y⟩ := (inferInstance : Nonempty Y)
    obtain ⟨j₀, hj₀⟩ := hSmem y
    rw [Fintype.card_eq_one_iff]
    refine ⟨j₀, fun j => ?_⟩
    by_contra hne
    rcases isClopen_iff.mp (hSclopen j) with h | h
    · obtain ⟨z, hz⟩ := hBne j
      have : z ∈ S j := Or.inl hz
      rw [h] at this
      exact this
    · have hy' : y ∈ S j := h ▸ mem_univ y
      exact Set.disjoint_left.mp (hSdisj j j₀ hne) hy' hj₀
  refine ⟨hcard, ?_⟩
  obtain ⟨j₀, hj₀⟩ := Fintype.card_eq_one_iff.mp hcard
  have hall : Finset.univ.filter (fun i => side i = j₀) = Finset.univ := by
    ext i
    simp [hj₀ (side i)]
  rcases hdeg j₀ with h | h
  · left
    rw [hall, Finset.card_univ] at h
    exact h
  · right
    rw [hall, Finset.card_univ] at h
    exact h

/-- Consumer (the vertex-degree input of FC42): if some disk face exists, there are exactly two. -/
theorem card_disk_faces_eq_two_of_nonempty {Y ι κ : Type*} [TopologicalSpace Y] [ConnectedSpace Y]
    [Fintype ι] [Finite κ] [DecidableEq κ] [Nonempty ι]
    (D : ι → Set Y) (B : κ → Set Y) (hD : ∀ i, IsClosed (D i)) (hB : ∀ j, IsClosed (B j))
    (hBne : ∀ j, (B j).Nonempty) (hcover : (⋃ i, D i) ∪ (⋃ j, B j) = univ)
    (hDD : Pairwise (Disjoint on D)) (hBB : Pairwise (Disjoint on B))
    (side : ι → κ) (hDB : ∀ i j, (D i ∩ B j).Nonempty → side i = j)
    (hdeg : ∀ j, (univ.filter (fun i => side i = j)).card = 0 ∨
      (univ.filter (fun i => side i = j)).card = 2) :
    Fintype.card ι = 2 := by
  have _ : Fintype κ := Fintype.ofFinite κ
  rcases (disk_face_count_dichotomy D B hD hB hBne hcover hDD hBB side hDB hdeg).2 with h | h
  · exact absurd h Fintype.card_ne_zero
  · exact h

end DifferentialGeometry.Topology
