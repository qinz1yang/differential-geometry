import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutCapped
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugCapping

/-!
# Consumers of `SphereCutCapped`

Two concrete consumers of `AssemblySphereCutCapped.lean`.

* `exists_fibrePlug_sphereCutCapped`: the actual bounded fibre plug (`FibrePlugCapping.lean:23`)
  with its canonical sphere seam carries a `SphereCutCapped` record over its two retained ports.
* `SphereCutCapped.components_count_eq_one_iff`: the case split of `components_count` is decided
  by the two cut spheres: one capped component exactly when both capped cut spheres lie in the
  same component (the non-separating case of L2-relative).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- The bounded fibre plug, cut along its canonical sphere seam and capped, is a
`SphereCutCapped` record over two ports. -/
theorem exists_fibrePlug_sphereCutCapped :
    ∃ (W : CompactCarrier.{u}) (S : SphereSeam W) (n : ℕ) (E : BoundaryTori W n),
      W.kind = .withBoundary ∧ n = 2 ∧ Nonempty (SphereCutCapped W S E) := by
  obtain ⟨W, P, -, -, -, d, hW, -, -, hE, hs, hI, -, δ, hδ, hδ1, C, B, hn, h2, fold, hk, hsm,
    hsurj, ho, ht, hf, hrel, -, ⟨K⟩⟩ := exists_fibrePlugCapping.{u}
  exact ⟨W, ⟨d, hs, hI⟩, P.toTorus.externalCount, P.toTorus.external.shrink hδ hδ1, hW, hE,
    ⟨⟨C, B, hn, h2, fold, hk, hsm, hsurj, ho, ht, hf, fun {x y} h => (hrel x y).mp h, _, K⟩⟩⟩

/-- One capped component exactly when the two capped cut spheres lie in the same component. -/
theorem SphereCutCapped.components_count_eq_one_iff {W : CompactCarrier.{u}}
    [ConnectedSpace W.Carrier] {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
    {X : SphereCutCapped W S E} {DQ : X.Q.Components} :
    DQ.count = 1 ↔
      X.spherePiece DQ (Fin.cast X.h2.symm 0) = X.spherePiece DQ (Fin.cast X.h2.symm 1) := by
  constructor
  · intro h1
    apply Fin.ext
    have h0 := (X.spherePiece DQ (Fin.cast X.h2.symm 0)).isLt
    have h1' := (X.spherePiece DQ (Fin.cast X.h2.symm 1)).isLt
    omega
  · intro heq
    have hall : ∀ i : Fin DQ.count, i = X.spherePiece DQ (Fin.cast X.h2.symm 0) := by
      intro i
      obtain ⟨j, rfl⟩ := X.spherePiece_surjective DQ i
      have hj : j = Fin.cast X.h2.symm 0 ∨ j = Fin.cast X.h2.symm 1 := by
        have hlt : j.val < 2 := X.h2 ▸ j.isLt
        by_cases h0 : j.val = 0
        · exact Or.inl (Fin.ext h0)
        · exact Or.inr (Fin.ext (by change j.val = 1; omega))
      rcases hj with rfl | rfl
      · rfl
      · exact heq.symm
    have hsub : Subsingleton (Fin DQ.count) :=
      ⟨fun a b => (hall a).trans (hall b).symm⟩
    have hle : Fintype.card (Fin DQ.count) ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr hsub
    simp only [Fintype.card_fin] at hle
    have hpos := DQ.count_pos
    omega

end GC.GraphManifold.Assembly
