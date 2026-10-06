import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageFaceModelJN74

/-!
# Draft 74, the shared faces are removed (field g7 `shared_removed` of `JunctionFaceFacts74`)

Lane S-JUNCTIONS (by S-JUNCTIONS4), G28 (suffix `_JN74`). On any rows without cusp pieces, from the
removal property `hKR` of the zero faces over `D₃` (`∂Z_i ∩ slimSet ⊆ relInt_{M₁} slimSet`, produced
at `D_R` by `zeroFace_slim_relInt_at_JN74`): a shared end is a model boundary face of a zero domain
(`shared_eq`) lying in the slim set, hence its set is in the relative interior of the slim set.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} {A : SmoothStageGeometry74 W E}
  {D : StageCutChoice74 A}

/-- **g7: the shared ends lie in the relative interior of the slim set.** -/
theorem shared_removed_JN74 [IsEmpty (Fin n)] (R : StageCutRows74 A D)
    (hKR : ∀ i, pieceBoundary (A.zero.piece i) ∩ D.slimSet ⊆
      relInt (regionM1 A.zero A.cusp) D.slimSet) :
    ∀ σ : ActualSharedFace R.slimPieces,
      R.slimPieces.endSet σ.1 ⊆ relInt (regionM1 A.zero A.cusp) D.slimSet := by
  intro σ x hx0
  obtain ⟨F', hF'⟩ := Option.isSome_iff_exists.1 σ.2
  have hset := R.slim.shared_eq σ.1 F' hF'
  have hsl : x ∈ D.slimSet := by
    rw [← R.slim.union_eq]
    exact mem_iUnion.2 ⟨σ.1.1.1, R.slimPieces.endSet_subset_GSAFE σ.1 hx0⟩
  rw [hset] at hx0
  rcases F' with ⟨i, Fm⟩ | ⟨b, -⟩
  · obtain ⟨p, hp, rfl⟩ := hx0
    refine hKR i ⟨⟨p, ?_, rfl⟩, hsl⟩
    obtain ⟨y, -, hm⟩ := Fm.2
    rw [hm] at hp
    exact connectedComponentIn_subset _ _ hp
  · exact (IsEmpty.false b).elim

end GC.GraphManifold.Assembly.FC39P0
