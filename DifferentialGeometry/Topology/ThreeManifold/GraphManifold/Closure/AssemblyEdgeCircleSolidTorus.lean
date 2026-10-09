import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCircleLiftFlow
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyDiskOrientedIsotopy
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyDiskBundleTorus
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyMonodromyOrientation
import DifferentialGeometry.Topology.Manifold.ClosedSolidTorusOrientation

/-!
# Chapter-14 assembly, D2S1: a circle-fibred edge piece is a solid torus

Frozen statement: V2 `exists_solidTorus_of_edgeCirclePiece` (`build-logs/scratch/ASM-FIX/AssemblyInterfacesV2.lean:856`,
recorded with its decomposition in `build-logs/scratch/ASM-D2S1/D2S1Inputs.lean`).

Assembly of the inputs, all built:
* (a) the boundary-preserving lift flow `Φ` of the rotation (`exists_circleLiftFlow_of_boundary_submersion`,
  lane D2S1-FLOW, `AssemblyCircleLiftFlow.lean`);
* (c) the monodromy `μ` of `Φ` on the fibre disk preserves orientation
  (`exists_monodromy_preservesOrientation`, `AssemblyMonodromyOrientation.lean`); the piece is oriented
  by `PieceEmbedding.pullbackOrientation`;
* (b) `μ⁻¹` is smoothly isotopic to the identity (`exists_diskIsotopy_from_refl_of_preservesOrientation`,
  `AssemblyDiskOrientedIsotopy.lean`, from (b1) rim isotopy + (b2)/SM-D of lane D2S1-RIM);
* G2 the mapping-torus lemma `nonempty_solidTorus_diffeomorph_of_liftFlow` (`AssemblyDiskBundleTorus.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskChartsEdgeTorus_D2S1C : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothEdgeTorus_D2S1C : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-- **D2S1** (frozen V2 text): the piece of a circle-fibred edge piece is diffeomorphic to the
standard solid torus. -/
theorem exists_solidTorus_of_edgeCirclePiece {W : CompactCarrier.{u}} (P : EdgeCirclePiece W) :
    Nonempty (solidTorusCarrier.{u}.Carrier ≃ₘ⟮solidTorusCarrier.{u}.model, 𝓡∂ 3⟯
      P.piece.Piece) := by
  obtain ⟨Φ, hΦ, hΦ0, hΦadd, hΦp⟩ := exists_circleLiftFlow_of_boundary_submersion P.proj
    P.proj_smooth P.proj_submersion P.boundary_submersion
  let o : ManifoldOrientation (𝓡∂ 2) (ClosedCell 2) 2 :=
    DifferentialGeometry.Topology.Manifold.closedDiskPositiveOrientation
  obtain ⟨μ, hμ, hμo⟩ := exists_monodromy_preservesOrientation P.piece.pullbackOrientation P.proj
    P.proj_smooth Φ hΦ hΦ0 hΦadd hΦp P.fibre P.fibre_embedding P.fibre_range o
  obtain ⟨K, hK, hKi, ε, hε, hlo, hhi⟩ :=
    exists_diskIsotopy_from_refl_of_preservesOrientation o μ.symm
      (Diffeomorph.preservesOrientation_symm hμo)
  refine nonempty_solidTorus_diffeomorph_of_liftFlow P.proj P.proj_smooth Φ hΦ hΦadd hΦp P.fibre
    P.fibre_embedding P.fibre_range K hK hKi hε hlo (fun t x ht => ?_)
  rw [hhi t x ht, ← hμ, Diffeomorph.apply_symm_apply]

end GC.GraphManifold.Assembly
