import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.DenselyOrdered

set_option autoImplicit false
open Set
open scoped Topology

namespace DifferentialGeometry.Topology

variable {X L : Type*} [TopologicalSpace X]
  [CompleteLattice L] [TopologicalSpace L] [OrderClosedTopology L]

theorem iSup_eq_of_subset_of_subset_closure {s t : Set X} (hst : s ⊆ t)
    (hts : t ⊆ closure s) (f : X → L)
    (hf : ∀ x ∈ t \ s, ContinuousWithinAt f s x) :
    (⨆ x ∈ t, f x) = ⨆ x ∈ s, f x := by
  apply le_antisymm
  · refine iSup_le fun x => iSup_le fun hx => ?_
    by_cases hxs : x ∈ s
    · exact le_iSup_of_le x (le_iSup_of_le hxs le_rfl)
    · exact (hf x ⟨hx, hxs⟩).closure_le (hts hx) continuousWithinAt_const
        (fun y hy => le_iSup_of_le y (le_iSup_of_le hy le_rfl))
  · exact iSup_le fun x => iSup_le fun hx =>
      le_iSup_of_le x (le_iSup_of_le (hst hx) le_rfl)

theorem iSup_preimage_Iic_eq_iSup_preimage_Iio
    (height : X → ℝ) (hheight : IsOpenMap height) (c : ℝ) (f : X → L)
    (hf : ∀ x, height x = c → ContinuousWithinAt f (height ⁻¹' Iic c) x) :
    (⨆ x ∈ height ⁻¹' Iic c, f x) = ⨆ x ∈ height ⁻¹' Iio c, f x := by
  apply iSup_eq_of_subset_of_subset_closure (preimage_mono Iio_subset_Iic_self)
  · simpa only [closure_Iio] using
      (hheight.preimage_closure_subset_closure_preimage (s := Iio c))
  · intro x hx
    have hxc : height x = c := le_antisymm hx.1 (not_lt.mp hx.2)
    exact (hf x hxc).mono (preimage_mono Iio_subset_Iic_self)

theorem iSup_prod_Ioc_eq_iSup_prod_Ioo {a b : ℝ} (hab : a < b)
    (f : X × ℝ → L)
    (hf : ∀ x : X, ContinuousWithinAt f (univ ×ˢ Ioc a b) (x, b)) :
    (⨆ q ∈ univ ×ˢ Ioc a b, f q) = ⨆ q ∈ univ ×ˢ Ioo a b, f q := by
  have hsub : (univ : Set X) ×ˢ Ioo a b ⊆ univ ×ˢ Ioc a b :=
    prod_mono Subset.rfl Ioo_subset_Ioc_self
  apply iSup_eq_of_subset_of_subset_closure hsub
  · rw [closure_prod_eq, closure_univ, closure_Ioo hab.ne]
    exact prod_mono Subset.rfl Ioc_subset_Icc_self
  · rintro ⟨x, z⟩ hx
    have hz : z = b := le_antisymm hx.1.2.2 (by
      by_contra! hz
      exact hx.2 ⟨mem_univ x, hx.1.2.1, hz⟩)
    subst z
    exact (hf x).mono hsub

end DifferentialGeometry.Topology
