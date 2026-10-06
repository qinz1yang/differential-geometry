import DifferentialGeometry.Topology.Connected.CompactFiniteComponentsFCP
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Consumers of the finite-component kernel (FDC04 lists), group G1

Lane S-FINCOMP (suffix `_FCP`). Concrete inhabitants of
`exists_finite_components_of_convex_charts_FCP`, `finite_connectedComponents_of_image_FCP` and the
local-connectedness criterion: the model corner (closed quadrant square) of a compact manifold base
with corners, and a circle-bundle-shaped projection `s × S¹ → s`.
-/

set_option autoImplicit false

open Set Function Filter Topology

namespace DifferentialGeometry.Topology

/-- The model corner: the closed unit quadrant square in `ℝ × ℝ` (the local model of `C₁` at a
corner, `{Tb ≥ 0, hb ≥ 0}`) is locally connected and has a finite list of components. -/
theorem quadrantSquare_finite_components_FCP :
    ∃ (m : ℕ) (B : Fin m → Set (ℝ × ℝ)), (∀ i, IsCompact (B i)) ∧ (∀ i, IsConnected (B i)) ∧
      (∀ i, B i ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∧ Pairwise (Disjoint on B) ∧
      Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 = ⋃ i, B i := by
  obtain ⟨m, B, hc, hcon, hsub, -, -, hd, hU⟩ :=
    exists_finite_components_of_convex_charts_FCP (E := ℝ × ℝ)
      ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod (isCompact_Icc (a := (0 : ℝ)) (b := 1)))
      (s := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) fun p _ =>
        ⟨OpenPartialHomeomorph.refl (ℝ × ℝ), trivial,
          Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, (convex_Icc 0 1).prod (convex_Icc 0 1), by simp⟩
  exact ⟨m, B, hc, hcon, hsub, hd, hU⟩

/-- The projection `s × S¹ → s` of a trivial circle bundle over a compact locally connected
base: the connected fibres give as many components upstairs as downstairs, and both are finite. -/
theorem trivialCircleBundle_finite_components_FCP {Y : Type*} [TopologicalSpace Y]
    [T2Space Y] {s : Set Y} (hs : IsCompact s) [LocallyConnectedSpace s] :
    Finite (ConnectedComponents (s ×ˢ (univ : Set Circle) : Set (Y × Circle))) := by
  have hsc : IsCompact (s ×ˢ (univ : Set Circle) : Set (Y × Circle)) := hs.prod isCompact_univ
  refine finite_connectedComponents_of_image_FCP hsc (f := Prod.fst) continuous_fst.continuousOn
    ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    have : s ×ˢ (univ : Set Circle) ∩ Prod.fst ⁻¹' {x.1} = {x.1} ×ˢ (univ : Set Circle) := by
      ext z
      simp only [mem_inter_iff, mem_prod, mem_univ, and_true, mem_preimage, mem_singleton_iff]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ hx.1, h⟩⟩
    rw [this]
    exact isConnected_singleton.prod isConnected_univ
  · have himg : Prod.fst '' (s ×ˢ (univ : Set Circle) : Set (Y × Circle)) = s :=
      fst_image_prod s univ_nonempty
    rw [himg]
    exact finite_connectedComponents_of_isCompact_locallyConnected_FCP hs

end DifferentialGeometry.Topology
