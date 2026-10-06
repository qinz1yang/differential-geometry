import DifferentialGeometry.Topology.Surface.Recognition.DiskFaceCountRow

/-!
# Consumers of the FC40 row (`fc40_row_RWS`)

Lane S-ROWS-FIN (suffix `_SRF`). Blueprint `master207B.tex`, FC40 (B:7457–7463).

* `fc40_sphere_two_disks_SRF`: on a sphere face the FC40 data have exactly two disks `h i`, `h j`
  (`i ≠ j`, every disk is `h i` or `h j`), and `Y = h i (D²) ∪ h j (D²) ∪ B` — the form in which
  BCF03's sphere branch (the two end disks of one handle, the circle-bundle piece between them)
  consumes the row.
* `fc40_card_dichotomy_SRF`: on a face that is `S²` or `T²` the number of disks is `0` or `2`.
-/

set_option autoImplicit false

open Set Function Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Surface

open DifferentialGeometry.Topology

variable {Y ι C : Type*} [TopologicalSpace Y] [Fintype ι] [TopologicalSpace C] [T2Space C]
  [ChartedSpace (EuclideanHalfSpace 1) C] [IsManifold (𝓡∂ 1) ∞ C]

/-- **Consumer (sphere branch)**: under the data of `fc40_row_RWS` on `Y ≃ₜ S²` there are exactly
two disks `h i`, `h j`, and `Y` is the union of these two disks and the circle-bundle surface
`B`. -/
theorem fc40_sphere_two_disks_SRF (φ : Y ≃ₜ SphereTwo) (h : ι → Disk 2 → Y)
    (hh : ∀ i, Continuous (h i)) (hinj : ∀ i, Injective (h i))
    (hdisj : Pairwise (Disjoint on fun i => range (h i)))
    (B : Set Y) (hBc : IsCompact B) (π : B → C) (hπ : Continuous π)
    (hloc : ∀ c : C, ∃ U ∈ 𝓝 c, ∃ e : π ⁻¹' U ≃ₜ U × Circle,
      ∀ x : π ⁻¹' U, ((e x).1 : C) = π x)
    (hcover : (⋃ i, range (h i)) ∪ B = univ)
    (hAB : (⋃ i, range (h i)) ∩ B = ⋃ i, h i '' diskSphere 2)
    (hbd : ⋃ i, h i '' diskSphere 2 = Subtype.val '' (π ⁻¹' (𝓡∂ 1).boundary C)) :
    ∃ i j : ι, i ≠ j ∧ (∀ k, k = i ∨ k = j) ∧ range (h i) ∪ range (h j) ∪ B = univ := by
  have h2 := (fc40_row_RWS h hh hinj hdisj B hBc π hπ hloc hcover hAB hbd).1 ⟨φ⟩
  classical
  have hN : Nat.card ι = 2 := by rw [Nat.card_eq_fintype_card, h2]
  obtain ⟨i, j, hij, hset⟩ := Nat.card_eq_two_iff.mp hN
  have hk : ∀ k, k = i ∨ k = j := fun k => by
    have : k ∈ ({i, j} : Set ι) := by rw [hset]; exact mem_univ k
    simpa using this
  refine ⟨i, j, hij, hk, ?_⟩
  have hU : (⋃ k, range (h k)) = range (h i) ∪ range (h j) := by
    ext p
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨k, hp⟩
      rcases hk k with rfl | rfl
      · exact Or.inl hp
      · exact Or.inr hp
    · rintro (hp | hp)
      · exact ⟨i, hp⟩
      · exact ⟨j, hp⟩
  rw [← hU]
  exact hcover

/-- **Consumer (both branches)**: on a face homeomorphic to `S²` or to `T²`, FC40 leaves exactly
the counts `d = 2` and `d = 0`. -/
theorem fc40_card_dichotomy_SRF (h : ι → Disk 2 → Y)
    (hh : ∀ i, Continuous (h i)) (hinj : ∀ i, Injective (h i))
    (hdisj : Pairwise (Disjoint on fun i => range (h i)))
    (B : Set Y) (hBc : IsCompact B) (π : B → C) (hπ : Continuous π)
    (hloc : ∀ c : C, ∃ U ∈ 𝓝 c, ∃ e : π ⁻¹' U ≃ₜ U × Circle,
      ∀ x : π ⁻¹' U, ((e x).1 : C) = π x)
    (hcover : (⋃ i, range (h i)) ∪ B = univ)
    (hAB : (⋃ i, range (h i)) ∩ B = ⋃ i, h i '' diskSphere 2)
    (hbd : ⋃ i, h i '' diskSphere 2 = Subtype.val '' (π ⁻¹' (𝓡∂ 1).boundary C))
    (hY : Nonempty (Y ≃ₜ SphereTwo) ∨ Nonempty (Y ≃ₜ Circle × Circle)) :
    (Nonempty (Y ≃ₜ SphereTwo) ∧ Fintype.card ι = 2) ∨
      (Nonempty (Y ≃ₜ Circle × Circle) ∧ Fintype.card ι = 0) := by
  have hrow := fc40_row_RWS h hh hinj hdisj B hBc π hπ hloc hcover hAB hbd
  rcases hY with hS | hT
  · exact Or.inl ⟨hS, hrow.1 hS⟩
  · exact Or.inr ⟨hT, hrow.2 hT⟩

end DifferentialGeometry.Topology.Surface
