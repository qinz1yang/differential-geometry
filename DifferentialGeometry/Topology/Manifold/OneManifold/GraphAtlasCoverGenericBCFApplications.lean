import DifferentialGeometry.Topology.Manifold.OneManifold.GraphAtlasCoverGenericBCF

/-!
# Consumer of the `K₃` kernel's generic cover (lane B-BCF134)

`lineGraphAtlas_cover_generic_BCF`: on the one-chart atlas of the real line, `[0, 1]` gets a
nonempty finite family of closed chart intervals with generic endpoints (pairwise distinct, avoiding
`{0, 1}`) whose union contains `[0, 1]` in its interior.
-/

set_option autoImplicit false

open Set Function Filter Topology

namespace DifferentialGeometry.Topology

/-- **Consumer**: generic kernel cover of `[0, 1]` on the line atlas, endpoints off `{0, 1}`. -/
theorem lineGraphAtlas_cover_generic_BCF :
    ∃ (n : ℕ) (c : Fin n → Unit) (a b : Fin n → ℝ), 0 < n ∧
      lineGraphAtlas_BCF.GenericEndpoints_BCF c a b ∧
      (∀ r, a r ∉ ({0, 1} : Set ℝ) ∧ b r ∉ ({0, 1} : Set ℝ)) ∧
      Icc (0 : ℝ) 1 ⊆ Subtype.val '' interior (Subtype.val ⁻¹'
        (⋃ r, lineGraphAtlas_BCF.param (c r) '' Icc (a r) (b r)) : Set (univ : Set ℝ)) := by
  obtain ⟨n, c, a, b, hab, hgen, -, -, hK, -⟩ := lineGraphAtlas_BCF.exists_cover_union_generic_BCF
    (Kset := Icc 0 1) (Fset := {0, 1}) (Dset := univ) isCompact_Icc (subset_univ _)
    ((finite_singleton 1).insert 0)
    (fun x _ => subset_closure (mem_image_interior_preimage_val_iff.mpr
      ⟨mem_univ x, univ, isOpen_univ, mem_univ x, fun _ _ => mem_univ _⟩))
    (fun x hx => (hx.2 (mem_image_interior_preimage_val_iff.mpr
      ⟨mem_univ x, univ, isOpen_univ, mem_univ x, fun _ _ => mem_univ _⟩)).elim)
  refine ⟨n, c, a, b, Nat.pos_of_ne_zero fun h0 => ?_, hgen,
    fun r => ⟨(hab r).2.2.1, (hab r).2.2.2⟩, hK⟩
  subst h0
  obtain ⟨y, hy, -⟩ := hK (left_mem_Icc.mpr zero_le_one)
  simpa using interior_subset hy

end DifferentialGeometry.Topology
