import DifferentialGeometry.Topology.ThreeManifold.Geometrization.Prime
import DifferentialGeometry.Topology.VanKampen.FiniteConnectedSumFreeProduct
import DifferentialGeometry.Topology.VanKampen.SimplyConnectedUnion
import DifferentialGeometry.Topology.ThreeManifold.Poincare
import DifferentialGeometry.Topology.ThreeManifold.StandardSphere
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OppositeSumOrientation
import DifferentialGeometry.Topology.Manifold.DiffeomorphOrientationDichotomy
import DifferentialGeometry.Compat.Ch567.Topology.ThreeManifold.ConnectedSum.OppositeSumOrientation

/-!
# Nontrivial splittings of non-prime closed oriented 3-manifolds

A diffeomorphism between connected closed oriented 3-manifolds is oriented either for the given
orientation of the target or for its opposite.  A non-prime connected closed oriented 3-manifold is
an oriented connected sum of two factors, each with nontrivial fundamental group; nontriviality
comes from the smooth Poincaré conjecture, and orientations are fixed by passing to opposite
factors when necessary.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff
universe u

namespace DifferentialGeometry.Topology

theorem orientedDiffeomorph_or_opposite_of_diffeomorph
    (M N : ConnectedClosedOrientedManifold.{u} 3)
    (f : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ N.Carrier) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      M.toClosedOrientedManifold N.toClosedOrientedManifold) ∨
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      M.toClosedOrientedManifold N.opposite.toClosedOrientedManifold) := by
  rcases f.preservesOrientation_or_preservesOrientation_opposite M.orientation N.orientation
    with h | h
  · exact Or.inl ⟨⟨f, h⟩⟩
  · exact Or.inr ⟨⟨f, h⟩⟩

private theorem nontrivial_fundamentalGroup_of_not_diffeomorph_sphere
    (A : ConnectedClosedOrientedManifold.{u} 3)
    (h : ¬ Nonempty (A.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.Carrier)) :
    Nontrivial (FundamentalGroup A.Carrier (chosenPoint A)) := by
  rw [← not_subsingleton_iff_nontrivial]
  intro hA
  let : SimplyConnectedSpace A.Carrier :=
    (VanKampen.simplyConnectedSpace_iff_fundamentalGroup_subsingleton
      A.Carrier (chosenPoint A)).mpr hA
  obtain ⟨f⟩ := smooth_poincare_conjecture A.Carrier
  exact h ⟨f.trans standardThreeSphereLiftDiffeomorph⟩

theorem exists_nontrivial_splitting_of_not_isPrime
    (M : ConnectedClosedOrientedManifold.{u} 3) (h : ¬ GC.Endpoint.IsPrime M) :
    ∃ A B : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (connectedSum A B).toClosedOrientedManifold M.toClosedOrientedManifold) ∧
      Nontrivial (FundamentalGroup A.Carrier (chosenPoint A)) ∧
      Nontrivial (FundamentalGroup B.Carrier (chosenPoint B)) := by
  unfold GC.Endpoint.IsPrime at h
  push Not at h
  obtain ⟨A, B, ⟨d⟩, hA, hB⟩ := h
  have hA' := nontrivial_fundamentalGroup_of_not_diffeomorph_sphere A (not_nonempty_iff.mpr hA)
  have hB' := nontrivial_fundamentalGroup_of_not_diffeomorph_sphere B (not_nonempty_iff.mpr hB)
  rcases orientedDiffeomorph_or_opposite_of_diffeomorph M (connectedSum A B) d with he | he
  · obtain ⟨e⟩ := he
    exact ⟨A, B, ⟨e.symm⟩, hA', hB'⟩
  · obtain ⟨e⟩ := he
    obtain ⟨c⟩ := connectedSum_opposite A B
    exact ⟨A.opposite, B.opposite, ⟨(e.trans c).symm⟩, hA', hB'⟩

end DifferentialGeometry.Topology
