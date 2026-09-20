/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteCollar
import DifferentialGeometry.Topology.PiecewiseLinear.StageTransport

/-!
# Piecewise linearity read off from a local model

`IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isOpen_inter_eq` says that a locally
finite polyhedral manifold with boundary `K` agrees near each of its points with a *compact*
polyhedral manifold with boundary `P`, on an open set `O`: `O ∩ K = O ∩ P`.  Everything local
about `K` can therefore be read off from `P`, and this file records the two consequences a
stagewise inward push needs.

The first is that piecewise linearity within a set is insensitive to replacing the set by
another one agreeing with it near the point.  This is not monotonicity — `IsPLWithinAt` is
monotone in neither direction — but the congruence
`StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_set`, whose hypothesis is equality
of the two sets *in a full neighbourhood*, which `O ∩ K = O ∩ P` supplies.

The second is that the identity is piecewise linear on `K`.  `SkeletonReduction.lean` has this
for an open set only, and openness is not available at a manifold with boundary; the proof here
transports the identity of the presenting complex along the presenting piece, exactly as
`ControlledInwardPush.lean` transports the compact push, and then reads the locally finite case
off the compact one.

## Main results

* `isPLWithinAt_congr_of_isOpen_inter_eq`: two sets agreeing on an open neighbourhood of a point
  have the same piecewise linear maps at that point.
* `isPLOn_of_forall_exists_isOpen_inter_eq`: piecewise linearity on `K` from piecewise linearity
  on a local model at each point.  This is what pastes a map defined by one formula near part of
  the relative boundary and by another formula elsewhere.
* `PLPiece.isPLOn_id`, `IsPolyhedralManifoldWithBoundary.isPLOn_id` and
  `IsLocallyFinitePolyhedralManifoldWithBoundary.isPLOn_id`: the identity is piecewise linear on
  a set presented by a piecewise linear piece, on a compact polyhedral manifold with boundary,
  and on a locally finite one.

The last of these is what lets a push supported in a compact part of `K` be extended by the
identity over the rest of `K`: off the support the extended map agrees with the identity on a
relatively open set, and there piecewise linearity is the statement proved here.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section LocalModel

variable {n m : ℕ} {M N : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]

/-- **Piecewise linearity within a set only depends on the set near the point.**

The hypothesis `O ∩ K = O ∩ P` for an open `O` containing `x` makes `K` and `P` equal on a
neighbourhood of `x`, which is what
`StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_set` consumes.  Neither inclusion
between `K` and `P` is needed, and neither set has to be open. -/
theorem isPLWithinAt_congr_of_isOpen_inter_eq {f : M → N} {K P O : Set M} {x : M}
    (hO : IsOpen O) (hx : x ∈ O) (hKP : O ∩ K = O ∩ P) :
    IsPLWithinAt n m f K x ↔ IsPLWithinAt n m f P x := by
  refine piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_set ?_
  filter_upwards [hO.mem_nhds hx] with z hz
  apply propext
  exact ⟨fun hzK => (hKP.subset ⟨hz, hzK⟩).2, fun hzP => (hKP.symm.subset ⟨hz, hzP⟩).2⟩

/-- **Piecewise linearity on a set from piecewise linearity on a local model at each point.**

The local models are unrelated to one another, and no compatibility between them is asked for:
piecewise linearity within a set is a property at a single point, and
`isPLWithinAt_congr_of_isOpen_inter_eq` transfers it from whichever model is available there. -/
theorem isPLOn_of_forall_exists_isOpen_inter_eq {f : M → N} {K : Set M}
    (hloc : ∀ x ∈ K, ∃ O : Set M, IsOpen O ∧ x ∈ O ∧ ∃ P : Set M, O ∩ K = O ∩ P ∧
      IsPLWithinAt n m f P x) : IsPLOn n m f K := by
  intro x hx
  obtain ⟨O, hO, hxO, P, hOP, hf⟩ := hloc x hx
  exact (isPLWithinAt_congr_of_isOpen_inter_eq hO hxO hOP).mpr hf

end LocalModel

section Identity

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

/-- **The identity is piecewise linear on a set presented by a piecewise linear piece.**

The identity of the presenting complex is piecewise affine on the polyhedron it carries, so its
transport `T.map ∘ id` along the piece is piecewise linear there, and composing that transport
with the inverse of the presenting bijection returns the identity of the presented set.  No
manifold hypothesis on the complex is used. -/
theorem PLPiece.isPLOn_id {Y : Set X} (T : PLPiece n X Y) : IsPLOn n n (id : X → X) Y := by
  classical
  have _ : Finite T.piece.complex.faces := T.piece.finite_faces.to_subtype
  have hid : IsPiecewiseAffineOn (id : EuclideanSpace ℝ (Fin T.ambientDim) →
      EuclideanSpace ℝ (Fin T.ambientDim)) T.piece.complex.space :=
    (isPolyhedron_space T.piece.complex).isPLHomeomorphOn_id.isPiecewiseAffineOn
  have hw : IsPLOn T.ambientDim n (T.piece.map ∘ id) T.piece.complex.space :=
    T.piece.isPLOn_comp hid (mapsTo_id _)
  refine T.piece.isPLOn_of_eqOn_comp_invFunOn hw fun y hy => ?_
  exact (T.piece.bijOn.invOn_invFunOn.2 hy).symm

/-- **The identity is piecewise linear on a compact polyhedral manifold with boundary.** -/
theorem IsPolyhedralManifoldWithBoundary.isPLOn_id {m : ℕ} {P : Set X}
    (hP : IsPolyhedralManifoldWithBoundary (n := n) m P) : IsPLOn n n (id : X → X) P := by
  obtain ⟨T, -⟩ := hP
  exact T.isPLOn_id

end Identity

section LocallyFinite

variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) X]

/-- **The identity is piecewise linear on a locally finite polyhedral manifold with boundary.**

Near each of its points the manifold agrees with a compact stage of its presenting tower, and
the identity is piecewise linear there; `isPLWithinAt_congr_of_isOpen_inter_eq` carries that
back.  This is the statement that lets a push supported in a compact part of the manifold be
extended by the identity over the rest, and it is not available from
`SkeletonReduction.isPLOn_id_of_isOpen`, whose hypothesis fails at a boundary point. -/
theorem IsLocallyFinitePolyhedralManifoldWithBoundary.isPLOn_id {K : Set X}
    (hK : IsLocallyFinitePolyhedralManifoldWithBoundary (n := m + 1) (m + 1) K) :
    IsPLOn (m + 1) (m + 1) (id : X → X) K := by
  refine isPLOn_of_forall_exists_isOpen_inter_eq fun x hx => ?_
  obtain ⟨O, hO, hxO, P, hP, -, hOP⟩ := hK.exists_isOpen_inter_eq hx
  exact ⟨O, hO, hxO, P, hOP, hP.isPLOn_id x (hOP.subset ⟨hxO, hx⟩).2⟩

end LocallyFinite

end DifferentialGeometry.Topology.PiecewiseLinear
