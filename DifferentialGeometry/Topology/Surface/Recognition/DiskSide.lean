import DifferentialGeometry.Topology.Attachment.Defs
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Connected.Basic

/-!
# Which of two complementary disks is a given side (SF6, step 5)

Two closed cells `b₀`, `b₁` cover a space `X` and meet exactly in their common boundary `C`.  If `P` is a
nonempty connected open set disjoint from `C` with `P ∪ C` closed, then `P ∪ C` is one of the two
cells: each `range bᵢ \ C` is the connected open complement of the other cell.
-/

set_option autoImplicit false

open Set Function

namespace DifferentialGeometry.Topology.Surface

open DifferentialGeometry.Topology

instance compactSpace_closedCell (n : ℕ) : CompactSpace (ClosedCell n) := by
  have hset : {x : EuclideanSpace ℝ (Fin n) | ‖x‖ ≤ 1} = Metric.closedBall 0 1 := by
    ext x
    simp
  have h : IsCompact {x : EuclideanSpace ℝ (Fin n) | ‖x‖ ≤ 1} := by
    rw [hset]
    exact isCompact_closedBall _ _
  exact isCompact_iff_compactSpace.mp h

/-- The open cell `{‖x‖ < 1}` of `ClosedCell n` is connected. -/
theorem isConnected_cellInteriorSet (n : ℕ) :
    IsConnected {x : ClosedCell n | ‖(x : EuclideanSpace ℝ (Fin n))‖ < 1} := by
  have himage : (Subtype.val : ClosedCell n → EuclideanSpace ℝ (Fin n)) ''
      {x : ClosedCell n | ‖(x : EuclideanSpace ℝ (Fin n))‖ < 1} =
        Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    ext y
    simp only [mem_image, mem_ofPred_eq, mem_ball_zero_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, hy.le⟩, hy, rfl⟩
  have hne : {x : ClosedCell n | ‖(x : EuclideanSpace ℝ (Fin n))‖ < 1}.Nonempty :=
    ⟨⟨0, by simp⟩, by simp⟩
  refine ⟨hne, ?_⟩
  have hind : Topology.IsInducing (Subtype.val : ClosedCell n → EuclideanSpace ℝ (Fin n)) :=
    Topology.IsInducing.subtypeVal
  apply hind.isPreconnected_image.mp
  rw [himage]
  exact (convex_ball (0 : EuclideanSpace ℝ (Fin n)) 1).isPreconnected

/-- The part of a cell off its boundary is the image of the open cell. -/
theorem range_diff_eq_image_cellInterior {n : ℕ} {X : Type*} {b : ClosedCell n → X}
    (hb : Injective b) {C : Set X} (hC : range (b ∘ cellBoundaryInclusion n) = C) :
    range b \ C = b '' {x | ‖(x : EuclideanSpace ℝ (Fin n))‖ < 1} := by
  ext y
  constructor
  · rintro ⟨⟨x, rfl⟩, hy⟩
    refine ⟨x, ?_, rfl⟩
    rcases lt_or_eq_of_le x.2 with h | h
    · exact h
    · exact absurd ⟨⟨x, h⟩, rfl⟩ (hC ▸ hy)
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, fun hy => ?_⟩
    rw [← hC] at hy
    obtain ⟨z, hz⟩ := hy
    have := hb hz
    have hz1 : ‖(z : EuclideanSpace ℝ (Fin n))‖ = 1 := z.2
    rw [← this] at hx
    change ‖(z : EuclideanSpace ℝ (Fin n))‖ < 1 at hx
    linarith

/-- **Side identification.** Two cells covering `X` and meeting in their common boundary `C`; a
nonempty connected open `P` disjoint from `C` with `P ∪ C` closed is one cell minus `C`. -/
theorem union_eq_range_or_range {n : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X]
    {b₀ b₁ : ClosedCell n → X} (hb₀ : Continuous b₀) (hb₀' : Injective b₀)
    (hb₁ : Continuous b₁) (hb₁' : Injective b₁) {C : Set X}
    (hC₀ : range (b₀ ∘ cellBoundaryInclusion n) = C)
    (hC₁ : range (b₁ ∘ cellBoundaryInclusion n) = C)
    (hcover : range b₀ ∪ range b₁ = univ) (hinter : range b₀ ∩ range b₁ = C)
    {P : Set X} (hP : IsOpen P) (hPc : IsConnected P) (hPC : Disjoint P C)
    (hK : IsClosed (P ∪ C)) :
    P ∪ C = range b₀ ∨ P ∪ C = range b₁ := by
  have hCsub₀ : C ⊆ range b₀ := hC₀ ▸ range_comp_subset_range _ _
  have hCsub₁ : C ⊆ range b₁ := hC₁ ▸ range_comp_subset_range _ _
  -- `range bᵢ \ C` is the complement of the other cell
  have hA₀ : range b₀ \ C = (range b₁)ᶜ := by
    ext y
    constructor
    · rintro ⟨hy0, hyC⟩ hy1
      exact hyC (hinter ▸ ⟨hy0, hy1⟩)
    · intro hy1
      have hy : y ∈ range b₀ ∪ range b₁ := hcover ▸ mem_univ y
      exact ⟨hy.resolve_right hy1, fun hyC => hy1 (hCsub₁ hyC)⟩
  have hA₁ : range b₁ \ C = (range b₀)ᶜ := by
    ext y
    constructor
    · rintro ⟨hy1, hyC⟩ hy0
      exact hyC (hinter ▸ ⟨hy0, hy1⟩)
    · intro hy0
      have hy : y ∈ range b₀ ∪ range b₁ := hcover ▸ mem_univ y
      exact ⟨hy.resolve_left hy0, fun hyC => hy0 (hCsub₀ hyC)⟩
  have hopen₀ : IsOpen (range b₁)ᶜ := (isCompact_range hb₁).isClosed.isOpen_compl
  have hopen₁ : IsOpen (range b₀)ᶜ := (isCompact_range hb₀).isClosed.isOpen_compl
  have key : ∀ (R : Set X) (b : ClosedCell n → X), Continuous b → Injective b →
      range (b ∘ cellBoundaryInclusion n) = C → C ⊆ R → R = range b → P ⊆ R \ C → P ∪ C = R := by
    intro R b hb hb' hbC hCR hR hPR
    have hconn : IsConnected (R \ C) := by
      rw [hR, range_diff_eq_image_cellInterior hb' hbC]
      exact (isConnected_cellInteriorSet n).image b hb.continuousOn
    have hsplit : R \ C ⊆ P ∪ (P ∪ C)ᶜ := by
      rintro y ⟨-, hyC⟩
      by_cases hyP : y ∈ P
      · exact Or.inl hyP
      · exact Or.inr fun h => h.elim hyP hyC
    rcases IsPreconnected.subset_or_subset hP hK.isOpen_compl
        (Set.disjoint_left.mpr fun y hy h => h (Or.inl hy)) hsplit hconn.isPreconnected with h | h
    · apply Subset.antisymm
      · exact union_subset (fun y hy => (hPR hy).1) hCR
      · intro y hy
        by_cases hyC : y ∈ C
        · exact Or.inr hyC
        · exact Or.inl (h ⟨hy, hyC⟩)
    · obtain ⟨y, hy⟩ := hPc.nonempty
      exact absurd (Or.inl hy) (h (hPR hy))
  have hsplit : P ⊆ (range b₁)ᶜ ∪ (range b₀)ᶜ := by
    intro y hy
    by_contra hcon
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
    exact Set.disjoint_left.mp hPC hy (hinter ▸ ⟨hcon.2, hcon.1⟩)
  have hdisj : Disjoint (range b₁)ᶜ (range b₀)ᶜ := by
    rw [Set.disjoint_left]
    intro y hy1 hy0
    have hy : y ∈ range b₀ ∪ range b₁ := hcover ▸ mem_univ y
    exact hy.elim hy0 hy1
  rcases IsPreconnected.subset_or_subset hopen₀ hopen₁ hdisj hsplit hPc.isPreconnected with h | h
  · exact Or.inl (key _ b₀ hb₀ hb₀' hC₀ hCsub₀ rfl (hA₀ ▸ h))
  · exact Or.inr (key _ b₁ hb₁ hb₁' hC₁ hCsub₁ rfl (hA₁ ▸ h))

end DifferentialGeometry.Topology.Surface
