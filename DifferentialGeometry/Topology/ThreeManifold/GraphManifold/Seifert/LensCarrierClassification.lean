import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LensCarrierNonzero
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LensCarrierProductComparison

/-!
# Classification of actual two-solid-torus carriers

Every actual solid torus has a boundary side. Closedness supplies a glued seam, whose lower-left
matching coefficient separates the positive lens parameter from the sphere-product case.
Both branches identify the complete carrier and retain its actual orientation.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

theorem TorusPresentation.exists_seam_of_allSolidTori
    {Q : ConnectedClosedOrientedManifold.{u} 3}
    (T : TorusPresentation (NoCuts.carrier Q)) (P : ∀ i, SolidTorusPiece T i) :
    Nonempty (Fin T.pairing.count) := by
  let i : Fin T.components.count := ⟨0, T.components.count_pos⟩
  obtain ⟨s, _hs⟩ := (P i).port 0
  rcases s with j | j | j
  · exact ⟨j⟩
  · exact ⟨j⟩
  · have hz : j.val < 0 := by simpa only [T.externalCount_eq_zero] using j.isLt
    exact (Nat.not_lt_zero _ hz).elim

theorem isStandardFactor_of_twoSolidTori
    {Q : ConnectedClosedOrientedManifold.{u} 3}
    (T : TorusPresentation (NoCuts.carrier Q)) (hc : T.components.count = 2)
    (P : ∀ i, SolidTorusPiece T i) : isStandardFactor Q := by
  obtain ⟨j⟩ := T.exists_seam_of_allSolidTori P
  by_cases hp : PrimitiveSlope.delta (torusUnit (T.pairing.matching j) • meridianSlope)
      meridianSlope = 0
  · obtain ⟨e⟩ := exists_orientedDiffeomorph_product_of_twoSolidTori T hc P j hp
    exact Or.inr ⟨e.1.trans sphereTwoTimesCircleModelCopy.equiv.symm,
      Diffeomorph.preservesOrientation_trans e.2
        sphereTwoTimesCircleLift_preservesOrientation⟩
  · have h10 : (torusUnit (T.pairing.matching j)).val 1 0 ≠ 0 := by
      intro hz
      apply hp
      rw [delta_smul_meridian_meridian, hz, Int.natAbs_zero]
    exact isStandardFactor_of_nonzero_twoSolidTori T hc P j h10

end GC.Seifert
