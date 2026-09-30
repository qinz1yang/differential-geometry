import DifferentialGeometry.Topology.Quotient.SameFibers
import Mathlib.Topology.Compactification.OnePoint.Basic

namespace DifferentialGeometry.Topology

open Set _root_.Topology
open scoped OnePoint

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]

theorem exists_collapse_of_openEmbedding {φ : Y → X} (hφ : IsOpenEmbedding φ)
    (hproper : range φ ≠ univ) :
    ∃ f : C(X, OnePoint Y), Function.Surjective f ∧
      collapsesExactly f (range φ)ᶜ ∧
      (∀ y, f (φ y) = (y : OnePoint Y)) ∧
      (∀ x ∉ range φ, f x = ∞) := by
  classical
  let e : Y ≃ₜ range φ := hφ.isEmbedding.toHomeomorph
  let f : X → OnePoint Y := fun x => if hx : x ∈ range φ then e.symm ⟨x, hx⟩ else ∞
  have hfin (y : Y) : f (φ y) = (y : OnePoint Y) := by
    rw [show f (φ y) = (e.symm ⟨φ y, mem_range_self y⟩ : OnePoint Y) from
      dite_eq_left (mem_range_self y)]
    exact congrArg (fun z : Y => (z : OnePoint Y)) (e.symm_apply_apply y)
  have hout (x : X) (hx : x ∉ range φ) : f x = ∞ := dite_eq_right hx
  have hcont : Continuous f := by
    apply continuous_def.mpr
    intro U hU
    by_cases hinfty : (∞ : OnePoint Y) ∈ U
    · have heq : f ⁻¹' U = (φ '' (((↑) : Y → OnePoint Y) ⁻¹' U)ᶜ)ᶜ := by
        ext x
        by_cases hx : x ∈ range φ
        · obtain ⟨y, rfl⟩ := hx
          simp only [mem_preimage, hfin, mem_compl_iff,
            hφ.injective.mem_set_image]
          exact not_not.symm
        · simp only [mem_preimage, hout x hx, hinfty, true_iff, mem_compl_iff]
          exact fun hi => hx ((image_subset_range _ _) hi)
      rw [heq]
      exact (((OnePoint.isOpen_def.mp hU).1 hinfty).image hφ.continuous).isClosed.isOpen_compl
    · have heq : f ⁻¹' U = φ '' (((↑) : Y → OnePoint Y) ⁻¹' U) := by
        ext x
        by_cases hx : x ∈ range φ
        · obtain ⟨y, rfl⟩ := hx
          simp only [mem_preimage, hfin, hφ.injective.mem_set_image]
        · simp only [mem_preimage, hout x hx, hinfty, false_iff]
          exact fun hi => hx ((image_subset_range _ _) hi)
      rw [heq]
      exact hφ.isOpenMap _ (OnePoint.isOpen_def.mp hU).2
  have hfiber : collapsesExactly f (range φ)ᶜ := by
    intro x y
    by_cases hx : x ∈ range φ
    · obtain ⟨u, rfl⟩ := hx
      by_cases hy : y ∈ range φ
      · obtain ⟨v, rfl⟩ := hy
        simp only [hfin, OnePoint.coe_eq_coe, mem_compl_iff, mem_range_self, not_true_eq_false,
          and_self, or_false]
        exact hφ.injective.eq_iff.symm
      · simp only [hfin, hout y hy, OnePoint.coe_ne_infty, mem_compl_iff, mem_range_self,
          not_true_eq_false, false_and, or_false, false_iff]
        exact fun h => hy (h ▸ mem_range_self u)
    · by_cases hy : y ∈ range φ
      · obtain ⟨v, rfl⟩ := hy
        simp only [hout x hx, hfin, OnePoint.infty_ne_coe, mem_compl_iff, mem_range_self,
          not_true_eq_false, and_false, or_false, false_iff]
        exact fun h => hx (h.symm ▸ mem_range_self v)
      · simp [hout x hx, hout y hy, hx, hy]
  refine ⟨⟨f, hcont⟩, ?_, hfiber, hfin, hout⟩
  intro z
  induction z using OnePoint.rec with
  | infty =>
      obtain ⟨x, hx⟩ := nonempty_compl.mpr hproper
      exact ⟨x, hout x hx⟩
  | coe y => exact ⟨φ y, hfin y⟩

end DifferentialGeometry.Topology
