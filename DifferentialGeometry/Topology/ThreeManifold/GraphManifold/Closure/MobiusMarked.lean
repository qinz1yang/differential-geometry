import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.MobiusOnePiece

/-!
The actual one-piece Möbius bundle exports its regular base and the native cover projection.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

theorem exists_mobiusWholeCircleFibration_marked :
    ∃ F : CircleFibration mobiusBundleCarrier.{u} ⊤,
      ∃ hbase : F.base = mobiusSurface.{u},
        ∀ p : (Circle × unitInterval) × Circle,
          hbase ▸ F.projection ⟨mobiusRegularTotalCover.{u} p,
            Set.mem_univ (mobiusRegularTotalCover.{u} p)⟩ = mobiusRegularBaseParam.{u} p.1 :=
  exists_circleFibration_of_mobiusCover mobiusBundleCarrier.{u} mobiusRegularTotalCover
    isLocalDiffeomorph_mobiusRegularTotalCover mobiusRegularTotalCover_surjective
    mobiusRegularTotalCover_eq_iff

theorem exists_mobiusSinglePieceRaw_marked :
    let : ConnectedSpace mobiusBundleCarrier.{u}.Carrier :=
      mobiusRegularTotalCover_surjective.connectedSpace
        contMDiff_mobiusRegularTotalCover.continuous
    ∃ F : CircleFibration mobiusBundleCarrier.{u} ⊤,
      ∃ hbase : F.base = mobiusSurface.{u},
        (∀ p : (Circle × unitInterval) × Circle,
          hbase ▸ F.projection ⟨mobiusRegularTotalCover.{u} p,
            Set.mem_univ (mobiusRegularTotalCover.{u} p)⟩ = mobiusRegularBaseParam.{u} p.1) ∧
        ∃ G : RawGraphPresentation mobiusBundleCarrier.{u},
          G = singlePieceRawPresentation mobiusBundleCarrier.{u} F
            mobiusPresentation.external mobiusPresentation.external_exhausted ∧
          G.components.count = 1 ∧ G.pairing.count = 0 ∧ G.externalCount = 1 := by
  let : ConnectedSpace mobiusBundleCarrier.{u}.Carrier :=
    mobiusRegularTotalCover_surjective.connectedSpace
      contMDiff_mobiusRegularTotalCover.continuous
  dsimp only
  obtain ⟨F, hbase, hprojection⟩ := exists_mobiusWholeCircleFibration_marked.{u}
  let G := singlePieceRawPresentation mobiusBundleCarrier.{u} F
    mobiusPresentation.external mobiusPresentation.external_exhausted
  exact ⟨F, hbase, hprojection, G, rfl, rfl, rfl, rfl⟩

theorem mobiusWholeCircleFibration_of_marked :
    Nonempty (CircleFibration mobiusBundleCarrier.{u} ⊤) := by
  obtain ⟨F, hbase, hprojection⟩ := exists_mobiusWholeCircleFibration_marked.{u}
  exact ⟨F⟩

theorem mobiusSinglePieceRaw_of_marked :
    ∃ G : RawGraphPresentation mobiusBundleCarrier.{u},
      G.components.count = 1 ∧ G.pairing.count = 0 ∧ G.externalCount = 1 := by
  obtain ⟨F, hbase, hprojection, G, heq, hc, hp, he⟩ :=
    exists_mobiusSinglePieceRaw_marked.{u}
  exact ⟨G, hc, hp, he⟩

end GC.GraphManifold
