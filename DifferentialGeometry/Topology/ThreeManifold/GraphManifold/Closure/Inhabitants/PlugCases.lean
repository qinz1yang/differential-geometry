import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelPlugFibre

/-!
The actual bounded fibre plug has two nonempty solid pieces, two retained torus ports and genuine
cap-centres in the capped interior. The connected carrier and raw presentation come from the
existing geometric construction, without assuming the desired plug or its port count.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Manifold DifferentialGeometry GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff

namespace GC.GraphManifold.Assembly

universe u

theorem exists_twoPiece_solidCapPlug :
    ∃ (P : CompactCarrier.{u}) (Y : SolidCapPlug P),
      Nonempty (RawGraphPresentation P) ∧ P.kind = .withBoundary ∧ ConnectedSpace P.Carrier ∧
        Y.cut.B.torusCount = 2 ∧
        (∀ t : Fin 2, (Y.piece t : Set Y.cut.Q.Carrier).Nonempty) ∧
        ∀ t : Fin 2, Y.capChart t 0 ∈ (Y.piece t : Set Y.cut.Q.Carrier) ∩ Y.cut.Q.interior := by
  obtain ⟨P, Y, hraw, hkind, hconn⟩ := exists_fibreSolidCapPlug.{u}
  have hcard := Fintype.card_congr (Equiv.ofBijective Y.port Y.port_bijective)
  have htwo : Y.cut.B.torusCount = 2 := by simpa only [Fintype.card_fin] using hcard.symm
  refine ⟨P, Y, hraw, hkind, hconn, htwo, ?_, ?_⟩
  · intro t
    obtain ⟨x⟩ := Y.piece_nonempty t
    exact ⟨x.val, x.property⟩
  · intro t
    have hz : (0 : EuclideanSpace ℝ (Fin 3)) ∈ (Y.capChart t).source :=
      Y.capChart_source t (by simp)
    have ht := (Y.capChart t).map_source hz
    exact ⟨Y.capChart_piece t ht, Y.capChart_interior t ht⟩

end GC.GraphManifold.Assembly
