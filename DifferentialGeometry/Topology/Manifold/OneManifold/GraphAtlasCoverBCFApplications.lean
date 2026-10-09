import DifferentialGeometry.Topology.Manifold.OneManifold.GraphAtlasCoverBCF

/-!
# Consumer of the `K₃` kernel's part (K-a) (lane B-BCF134)

`lineGraphAtlas_cover_BCF`: on the one-chart atlas of the real line, the compact set `[0, 1]` gets a
NONEMPTY finite family of closed chart intervals whose union contains `[0, 1]` in its interior.
-/

set_option autoImplicit false

open Set Function Filter Topology

namespace DifferentialGeometry.Topology

/-- **Consumer**: the kernel (K-a) on the line with `Kset = [0, 1]`, `Fset = ∅`, `Dset = ℝ`: at
least one chart interval, and `[0, 1]` inside the relative interior of their union. -/
theorem lineGraphAtlas_cover_BCF :
    ∃ (n : ℕ) (c : Fin n → Unit) (a b : Fin n → ℝ), 0 < n ∧ (∀ r, a r < b r) ∧
      Icc (0 : ℝ) 1 ⊆ Subtype.val '' interior (Subtype.val ⁻¹'
        (⋃ r, lineGraphAtlas_BCF.param (c r) '' Icc (a r) (b r)) : Set (univ : Set ℝ)) := by
  obtain ⟨n, c, a, b, hab, -, -, hK, -⟩ := lineGraphAtlas_BCF.exists_cover_union_BCF
    (Kset := Icc 0 1) (Fset := ∅) (Dset := univ) isCompact_Icc (subset_univ _) finite_empty
    (fun x _ => subset_closure (mem_image_interior_preimage_val_iff.mpr
      ⟨mem_univ x, univ, isOpen_univ, mem_univ x, fun _ _ => mem_univ _⟩))
    (fun x hx => (hx.2 (mem_image_interior_preimage_val_iff.mpr
      ⟨mem_univ x, univ, isOpen_univ, mem_univ x, fun _ _ => mem_univ _⟩)).elim)
  refine ⟨n, c, a, b, Nat.pos_of_ne_zero fun h0 => ?_, fun r => (hab r).1, hK⟩
  subst h0
  obtain ⟨y, hy, -⟩ := hK (left_mem_Icc.mpr zero_le_one)
  simpa using interior_subset hy

end DifferentialGeometry.Topology
