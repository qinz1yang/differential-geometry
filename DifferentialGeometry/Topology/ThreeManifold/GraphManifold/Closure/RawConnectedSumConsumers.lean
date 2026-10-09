import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawConnectedSumConnector
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Sphere
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.Prime

/-!
# Consumers of the raw connected-sum endpoint

`rawGraphPresentation_connectedSum` gives a raw graph presentation of the fixed oriented
`connectedSum M N` from raw graph presentations of `M` and `N`. Combined with
`rawGraphPresentation_of_diffeomorph`, which allows a diffeomorphism of either orientation
behaviour, this gives:

* a raw graph presentation of every closed manifold diffeomorphic to `connectedSum M N`;
* by induction on the list, a raw graph presentation of the fixed iterated sum
  `finiteConnectedSum L` whenever every factor of `L` has one (the empty list is the standard
  three-sphere, presented by `standardThreeSphereLiftRawGraphPresentation`);
* the same for a `Fin n`-indexed family, and for every manifold diffeomorphic to the iterated sum;
* reassembly: a prime decomposition of `M` whose factors all have raw graph presentations gives
  one of `M`.
-/

set_option autoImplicit false

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff

namespace GC.GraphManifold

universe u

theorem nonempty_rawGraphPresentation_of_connectedSum_diffeomorph
    {M N Q : ConnectedClosedOrientedManifold.{u} 3}
    (G : RawGraphPresentation (NoCuts.carrier M))
    (H : RawGraphPresentation (NoCuts.carrier N))
    (f : (connectedSum M N).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ Q.Carrier) :
    Nonempty (RawGraphPresentation (NoCuts.carrier Q)) := by
  obtain ⟨R⟩ := rawGraphPresentation_connectedSum M N G H
  exact rawGraphPresentation_of_diffeomorph R f

theorem nonempty_rawGraphPresentation_finiteConnectedSum
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (h : ∀ M ∈ L, Nonempty (RawGraphPresentation (NoCuts.carrier M))) :
    Nonempty (RawGraphPresentation (NoCuts.carrier (finiteConnectedSum L))) := by
  induction L with
  | nil => exact ⟨standardThreeSphereLiftRawGraphPresentation⟩
  | cons M L ih =>
    cases L with
    | nil => exact h M (by simp)
    | cons N L =>
      obtain ⟨G⟩ := h M (by simp)
      obtain ⟨H⟩ := ih fun A hA => h A (List.mem_cons_of_mem M hA)
      exact rawGraphPresentation_connectedSum M (finiteConnectedSum (N :: L)) G H

theorem nonempty_rawGraphPresentation_finiteConnectedSum_ofFn {n : ℕ}
    (F : Fin n → ConnectedClosedOrientedManifold.{u} 3)
    (h : ∀ i, Nonempty (RawGraphPresentation (NoCuts.carrier (F i)))) :
    Nonempty (RawGraphPresentation (NoCuts.carrier (finiteConnectedSum (List.ofFn F)))) := by
  refine nonempty_rawGraphPresentation_finiteConnectedSum _ fun M hM => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hM
  exact h i

theorem nonempty_rawGraphPresentation_of_finiteConnectedSum_diffeomorph
    {L : List (ConnectedClosedOrientedManifold.{u} 3)} {Q : ConnectedClosedOrientedManifold.{u} 3}
    (h : ∀ M ∈ L, Nonempty (RawGraphPresentation (NoCuts.carrier M)))
    (f : (finiteConnectedSum L).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ Q.Carrier) :
    Nonempty (RawGraphPresentation (NoCuts.carrier Q)) := by
  obtain ⟨R⟩ := nonempty_rawGraphPresentation_finiteConnectedSum L h
  exact rawGraphPresentation_of_diffeomorph R f

theorem nonempty_rawGraphPresentation_of_primeDecomposition
    {M : ConnectedClosedOrientedManifold.{u} 3} (D : PrimeDecomposition M)
    (h : ∀ P ∈ D.factors, Nonempty (RawGraphPresentation (NoCuts.carrier P))) :
    Nonempty (RawGraphPresentation (NoCuts.carrier M)) :=
  nonempty_rawGraphPresentation_of_finiteConnectedSum_diffeomorph h D.reconstruction.1

theorem nonempty_rawGraphPresentation_of_primeDecomposition_get
    {M : ConnectedClosedOrientedManifold.{u} 3} (D : PrimeDecomposition M)
    (h : ∀ i : Fin D.factors.length,
      Nonempty (RawGraphPresentation (NoCuts.carrier (D.factors.get i)))) :
    Nonempty (RawGraphPresentation (NoCuts.carrier M)) := by
  refine nonempty_rawGraphPresentation_of_primeDecomposition D fun P hP => ?_
  obtain ⟨i, rfl⟩ := List.get_of_mem hP
  exact h i

end GC.GraphManifold
