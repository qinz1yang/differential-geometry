import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

set_option autoImplicit false
noncomputable section
open Set Filter Bundle
open scoped Manifold ContDiff Topology
namespace Poincare.VectorBundle
variable {B ι : Type*} {V : B → Type*} [∀ x, AddCommGroup (V x)] [Fintype ι]
  (s : ∀ x, V x) (t : ι → ∀ x, V x)


def finitePatch (x : B) : V x := s x + ∑ i, (t i x - s x)

theorem finitePatch_eq_patch (i : ι) (x : B)
    (h : ∀ j, j ≠ i → t j x = s x) : finitePatch s t x = t i x := by
  classical
  rw [finitePatch, Finset.sum_eq_single i]
  · exact add_sub_cancel _ _
  · intro j _ hji
    rw [h j hji, sub_self]
  · simp


theorem finitePatch_eq_self (x : B) (h : ∀ i, t i x = s x) :
    finitePatch s t x = s x := by
  simp only [finitePatch, h, sub_self, Finset.sum_const_zero, add_zero]

variable [TopologicalSpace B]

theorem finitePatch_eventuallyEq_patch (i : ι) {x : B}
    (h : ∀ j, j ≠ i → ∀ᶠ y in 𝓝 x, t j y = s y) : ∀ᶠ y in 𝓝 x, finitePatch s t y = t i y := by
  have he : ∀ᶠ y in 𝓝 x, ∀ j, j ≠ i → t j y = s y := by
    apply eventually_all.mpr
    intro j
    by_cases hj : j = i
    · exact Filter.Eventually.of_forall (fun _ hji => (hji hj).elim)
    · exact (h j hj).mono (fun _ hy _ => hy)
  filter_upwards [he] with y hy
  exact finitePatch_eq_patch s t i y hy


theorem finitePatch_eventuallyEq_self {x : B} (h : ∀ i, ∀ᶠ y in 𝓝 x, t i y = s y) :
    ∀ᶠ y in 𝓝 x, finitePatch s t y = s y := by
  filter_upwards [eventually_all.mpr h] with y hy
  exact finitePatch_eq_self s t y hy

theorem closure_change_finitePatch_subset {K : Set B} (hK : IsClosed K)
    (h : ∀ i x, x ∉ K → t i x = s x) :
    closure {x | finitePatch s t x ≠ s x} ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hxK
  exact hx (finitePatch_eq_self s t x (fun i => h i x hxK))

section Smooth
variable {𝕜 EB HB F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] [ChartedSpace HB B] (I : ModelWithCorners 𝕜 EB HB)
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [∀ x, TopologicalSpace (V x)] [∀ x, Module 𝕜 (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  {n : ℕ∞ω}


theorem contMDiff_finitePatch
    (hs : ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (s x)))
    (ht : ∀ i, ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (t i x))) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (finitePatch s t x)) :=
  hs.add_section (ContMDiff.sum_section (fun i _ => (ht i).sub_section hs))
end Smooth
end Poincare.VectorBundle
