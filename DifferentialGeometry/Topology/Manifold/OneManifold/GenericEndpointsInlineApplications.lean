import DifferentialGeometry.Topology.Manifold.OneManifold.GenericEndpointsInline
import DifferentialGeometry.Topology.Manifold.OneManifold.GraphAtlasCoverGenericBCFApplications

/-!
# Consumers of the inline `GenericEndpoints_BCF` variants (lane S-CLEAN, suffix `_SCL`)

* `exists_halfChart_of_cover_old_of_inline_SCL`: the OLD theorem `exists_halfChart_of_cover_BCF`
  (premise `GenericEndpoints_BCF`) re-derived from the inline form alone, so the two forms are
  interderivable (the other direction is `exists_halfChart_of_cover_inline_SCL`);
* `lineGraphAtlas_cover_generic_inline_SCL` / `lineGraphAtlas_cover_generic_of_inline_SCL`: the
  generic cover of `[0,1]` on the line atlas (consumer of `exists_cover_union_generic_BCF`) in
  inline form, and the old statement `lineGraphAtlas_cover_generic_BCF` recovered from it;
* `lineGraphAtlas_halfChart_inline_SCL`: end to end WITHOUT the named `Prop`: inline cover →
  inline half-chart theorem gives a half chart of the cover at each of its points.
-/

set_option autoImplicit false

open Set Function Filter Topology
open scoped ContDiff

noncomputable section

namespace DifferentialGeometry.Topology

/-- The old half-chart theorem (premise `GenericEndpoints_BCF`) from the inline form only. -/
theorem exists_halfChart_of_cover_old_of_inline_SCL {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] {ι : Type*} {Bs : Set H} (At : GraphAtlas1_BCF ι Bs) {n : ℕ}
    {c : Fin n → ι} {a b : Fin n → ℝ}
    (hab : ∀ r, a r < b r ∧ Icc (a r) (b r) ⊆ At.dom (c r))
    (hgen : At.GenericEndpoints_BCF c a b) {y : H}
    (hy : y ∈ ⋃ r, At.param (c r) '' Icc (a r) (b r)) :
    ∃ d : HalfChart_BCF Bs (⋃ r, At.param (c r) '' Icc (a r) (b r)), y ∈ d.O :=
  At.exists_halfChart_of_cover_inline_SCL hab hgen.1 hgen.2 hy

/-- **Consumer**: the generic cover of `[0, 1]` on the line atlas, inline form (with the interval
orders `a r < b r`, needed by the half-chart theorem). -/
theorem lineGraphAtlas_cover_generic_inline_SCL :
    ∃ (n : ℕ) (c : Fin n → Unit) (a b : Fin n → ℝ), 0 < n ∧ (∀ r, a r < b r) ∧
      (∀ r, lineGraphAtlas_BCF.param (c r) (a r) ≠ lineGraphAtlas_BCF.param (c r) (b r)) ∧
      (∀ r s, r ≠ s → ∀ p ∈ ({lineGraphAtlas_BCF.param (c r) (a r),
          lineGraphAtlas_BCF.param (c r) (b r)} : Set ℝ),
        p ∉ ({lineGraphAtlas_BCF.param (c s) (a s),
          lineGraphAtlas_BCF.param (c s) (b s)} : Set ℝ)) ∧
      (∀ r, a r ∉ ({0, 1} : Set ℝ) ∧ b r ∉ ({0, 1} : Set ℝ)) ∧
      Icc (0 : ℝ) 1 ⊆ Subtype.val '' interior (Subtype.val ⁻¹'
        (⋃ r, lineGraphAtlas_BCF.param (c r) '' Icc (a r) (b r)) : Set (univ : Set ℝ)) := by
  obtain ⟨n, c, a, b, hab, hdist, hdisj, -, -, hK, -⟩ :=
    lineGraphAtlas_BCF.exists_cover_union_generic_inline_SCL
    (Kset := Icc 0 1) (Fset := {0, 1}) (Dset := univ) isCompact_Icc (subset_univ _)
    ((finite_singleton 1).insert 0)
    (fun x _ => subset_closure (mem_image_interior_preimage_val_iff.mpr
      ⟨mem_univ x, univ, isOpen_univ, mem_univ x, fun _ _ => mem_univ _⟩))
    (fun x hx => (hx.2 (mem_image_interior_preimage_val_iff.mpr
      ⟨mem_univ x, univ, isOpen_univ, mem_univ x, fun _ _ => mem_univ _⟩)).elim)
  refine ⟨n, c, a, b, Nat.pos_of_ne_zero fun h0 => ?_, fun r => (hab r).1, hdist, hdisj,
    fun r => ⟨(hab r).2.2.1, (hab r).2.2.2⟩, hK⟩
  subst h0
  obtain ⟨y, hy, -⟩ := hK (left_mem_Icc.mpr zero_le_one)
  simpa using interior_subset hy

/-- **The old consumer from the inline one**: the statement of `lineGraphAtlas_cover_generic_BCF`
(with `GenericEndpoints_BCF`) follows from `lineGraphAtlas_cover_generic_inline_SCL`. -/
theorem lineGraphAtlas_cover_generic_of_inline_SCL :
    ∃ (n : ℕ) (c : Fin n → Unit) (a b : Fin n → ℝ), 0 < n ∧
      lineGraphAtlas_BCF.GenericEndpoints_BCF c a b ∧
      (∀ r, a r ∉ ({0, 1} : Set ℝ) ∧ b r ∉ ({0, 1} : Set ℝ)) ∧
      Icc (0 : ℝ) 1 ⊆ Subtype.val '' interior (Subtype.val ⁻¹'
        (⋃ r, lineGraphAtlas_BCF.param (c r) '' Icc (a r) (b r)) : Set (univ : Set ℝ)) := by
  obtain ⟨n, c, a, b, hn, -, hdist, hdisj, h1, h2⟩ := lineGraphAtlas_cover_generic_inline_SCL
  exact ⟨n, c, a, b, hn, ⟨hdist, hdisj⟩, h1, h2⟩

/-- **Consumer, end to end without the named `Prop`**: on the line atlas, `[0, 1]` has a finite
generic interval cover, and the union of the closed chart intervals has a half chart at each of
its points. -/
theorem lineGraphAtlas_halfChart_inline_SCL :
    ∃ (n : ℕ) (c : Fin n → Unit) (a b : Fin n → ℝ), 0 < n ∧
      ∀ y ∈ ⋃ r, lineGraphAtlas_BCF.param (c r) '' Icc (a r) (b r),
        ∃ d : HalfChart_BCF (univ : Set ℝ)
          (⋃ r, lineGraphAtlas_BCF.param (c r) '' Icc (a r) (b r)), y ∈ d.O := by
  obtain ⟨n, c, a, b, hn, hlt, hdist, hdisj, -⟩ := lineGraphAtlas_cover_generic_inline_SCL
  exact ⟨n, c, a, b, hn, fun y hy => lineGraphAtlas_BCF.exists_halfChart_of_cover_inline_SCL
    (fun r => ⟨hlt r, fun _ _ => mem_univ _⟩) hdist hdisj hy⟩

end DifferentialGeometry.Topology
