import DifferentialGeometry.Topology.Schoenflies.BrownTwoFiber
import DifferentialGeometry.Topology.Cellular.CellularLocalization

namespace DifferentialGeometry.Topology

open Set Metric _root_.Topology

theorem isCellular_two_fibers_of_homeomorph {n : ℕ} {X : Type*} [TopologicalSpace X]
    (e : X ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    {f : X → sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1} {A B : Set X}
    (hf : Continuous f) (hfs : Function.Surjective f)
    (hfAB : ∀ x y, f x = f y ↔ x = y ∨ (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B))
    (hA : IsCompact A) (hB : IsCompact B) (hneA : A.Nonempty) (hneB : B.Nonempty)
    (hAB : Disjoint A B) (hproper : A ∪ B ≠ univ) :
    isCellular n A ∧ isCellular n B := by
  let A' := e '' A
  let B' := e '' B
  have ha (x) : x ∈ A' ↔ e.symm x ∈ A := by
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  have hb (x) : x ∈ B' ↔ e.symm x ∈ B := by
    constructor
    · rintro ⟨b, hb, rfl⟩
      simpa using hb
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  have hF : ∀ x y, (f ∘ e.symm) x = (f ∘ e.symm) y ↔
      x = y ∨ (x ∈ A' ∧ y ∈ A') ∨ (x ∈ B' ∧ y ∈ B') := by
    intro x y
    simpa only [Function.comp_apply, e.symm.injective.eq_iff, ha, hb] using
      hfAB (e.symm x) (e.symm y)
  have hdisj : Disjoint A' B' := by
    apply disjoint_left.mpr
    intro x hx hy
    exact disjoint_left.mp hAB ((ha x).mp hx) ((hb x).mp hy)
  have hproper' : A' ∪ B' ≠ univ := by
    intro h
    apply hproper
    apply eq_univ_of_univ_subset
    intro x _
    have hx : e x ∈ A' ∪ B' := h ▸ mem_univ _
    simpa only [mem_union, ha, hb, e.symm_apply_apply] using hx
  obtain ⟨hAc, hBc⟩ := isCellular_two_fibers (hf.comp e.symm.continuous)
    (hfs.comp e.symm.surjective) hF (hA.image e.continuous) (hB.image e.continuous)
    (hneA.image e) (hneB.image e) hdisj hproper'
  constructor
  · simpa [A', image_image] using hAc.mapHomeomorph e.symm
  · simpa [B', image_image] using hBc.mapHomeomorph e.symm

end DifferentialGeometry.Topology
