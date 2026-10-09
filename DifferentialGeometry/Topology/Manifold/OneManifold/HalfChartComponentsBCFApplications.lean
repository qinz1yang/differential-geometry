import DifferentialGeometry.Topology.Manifold.OneManifold.HalfChartComponentsBCF

/-!
# Consumer of `exists_components_of_halfCharts_BCF`: the segment `[0, 1] ⊆ ℝ` (lane S-BCF03)

Two half charts of `T = [0, 1]` (the coordinates `t` and `1 - t`, base `ℝ`) cover `T`; the
hypotheses of the component theorem hold, so `[0, 1]` is a finite disjoint union of arcs and loops.
-/

set_option autoImplicit false

open Set Function Topology

noncomputable section

namespace DifferentialGeometry.Topology

/-- The left half chart `t`. -/
def segmentLeftChart_BCF : HalfChart_BCF (univ : Set ℝ) (Icc (0 : ℝ) 1) where
  L := ContinuousLinearMap.id ℝ ℝ
  κ := 0
  π := id
  W := univ
  V := Iio (3 / 4)
  O := Iio (3 / 4)
  isOpen_W := isOpen_univ
  isOpen_V := isOpen_Iio
  V_subset := subset_univ _
  smooth := contDiff_id.contDiffOn
  coord := fun t _ => by simp
  mem := fun _ _ => mem_univ _
  relOpen := ⟨univ, isOpen_univ, by simp⟩
  isOpen_O := isOpen_Iio
  inter_eq := by
    ext z
    constructor
    · rintro ⟨⟨h0, -⟩, h⟩
      exact ⟨z, ⟨h, h0⟩, rfl⟩
    · rintro ⟨t, ⟨ht, ht0⟩, rfl⟩
      exact ⟨⟨ht0, by have : t < 3 / 4 := ht; change t ≤ 1; linarith⟩, ht⟩

/-- The right half chart `1 - t`. -/
def segmentRightChart_BCF : HalfChart_BCF (univ : Set ℝ) (Icc (0 : ℝ) 1) where
  L := -ContinuousLinearMap.id ℝ ℝ
  κ := 1
  π := fun t => 1 - t
  W := univ
  V := Iio (3 / 4)
  O := Ioi (1 / 4)
  isOpen_W := isOpen_univ
  isOpen_V := isOpen_Iio
  V_subset := subset_univ _
  smooth := (contDiff_const.sub contDiff_id).contDiffOn
  coord := fun t _ => by simp
  mem := fun _ _ => mem_univ _
  relOpen := ⟨univ, isOpen_univ, by
    ext z
    constructor
    · intro _
      exact ⟨1 - z, mem_univ _, by ring⟩
    · intro _
      exact ⟨mem_univ _, mem_univ _⟩⟩
  isOpen_O := isOpen_Ioi
  inter_eq := by
    ext z
    simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_image, mem_Iio, mem_Ici]
    constructor
    · rintro ⟨⟨h0, h1⟩, h⟩
      exact ⟨1 - z, ⟨by linarith, by linarith⟩, by ring⟩
    · rintro ⟨t, ⟨ht, ht0⟩, rfl⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith⟩

theorem exists_components_segment_BCF :
    ∃ (n m : ℕ) (a : Fin n → ℝ → ℝ) (l : Fin m → Circle → ℝ),
      (∀ k, ContinuousOn (a k) (Icc 0 1) ∧ InjOn (a k) (Icc 0 1)) ∧
      (∀ j, Continuous (l j) ∧ Injective (l j)) ∧
      (∀ k k', k ≠ k' → Disjoint (a k '' Icc 0 1) (a k' '' Icc 0 1)) ∧
      (∀ j j', j ≠ j' → Disjoint (range (l j)) (range (l j'))) ∧
      (∀ k j, Disjoint (a k '' Icc 0 1) (range (l j))) ∧
      Icc (0 : ℝ) 1 = (⋃ k, a k '' Icc 0 1) ∪ ⋃ j, range (l j) ∧
      (∀ k, ∃ G : Set ℝ, IsOpen G ∧ G ∩ Icc 0 1 = a k '' Icc 0 1) ∧
      (∀ j, ∃ G : Set ℝ, IsOpen G ∧ G ∩ Icc 0 1 = range (l j)) ∧ True ∧ True := by
  classical
  let d : ∀ y : Icc (0 : ℝ) 1, HalfChart_BCF ((fun _ => (univ : Set ℝ)) y) (Icc (0 : ℝ) 1) :=
    fun y => if (y : ℝ) ≤ 1 / 2 then segmentLeftChart_BCF else segmentRightChart_BCF
  have hd : ∀ y : Icc (0 : ℝ) 1, (y : ℝ) ∈ (d y).O := by
    intro y
    by_cases h : (y : ℝ) ≤ 1 / 2
    · simp only [d, h, ↓reduceIte]
      change (y : ℝ) ∈ Iio (3 / 4)
      exact mem_Iio.mpr (by linarith)
    · simp only [d, h, ↓reduceIte]
      change (y : ℝ) ∈ Ioi (1 / 4)
      exact mem_Ioi.mpr (by have := not_le.mp h; linarith)
  obtain ⟨n, m, a, l, h1, h2, h3, h4, h5, h6, h7, h8, -, -⟩ :=
    exists_components_of_halfCharts_BCF (T := Icc (0 : ℝ) 1) isCompact_Icc
      (fun _ => (univ : Set ℝ)) d hd
  exact ⟨n, m, a, l, h1, h2, h3, h4, h5, h6, h7, h8, trivial, trivial⟩

end DifferentialGeometry.Topology
