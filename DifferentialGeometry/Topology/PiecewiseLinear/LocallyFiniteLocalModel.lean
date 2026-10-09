/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteCollar
import DifferentialGeometry.Topology.PiecewiseLinear.StageTransport

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section LocalModel

variable {n m : ℕ} {M N : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]

theorem isPLWithinAt_congr_of_isOpen_inter_eq {f : M → N} {K P O : Set M} {x : M}
    (hO : IsOpen O) (hx : x ∈ O) (hKP : O ∩ K = O ∩ P) :
    IsPLWithinAt n m f K x ↔ IsPLWithinAt n m f P x := by
  refine piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_set ?_
  filter_upwards [hO.mem_nhds hx] with z hz
  apply propext
  exact ⟨fun hzK => (hKP.subset ⟨hz, hzK⟩).2, fun hzP => (hKP.symm.subset ⟨hz, hzP⟩).2⟩

theorem isPLOn_of_forall_exists_isOpen_inter_eq {f : M → N} {K : Set M}
    (hloc : ∀ x ∈ K, ∃ O : Set M, IsOpen O ∧ x ∈ O ∧ ∃ P : Set M, O ∩ K = O ∩ P ∧
      IsPLWithinAt n m f P x) : IsPLOn n m f K := by
  intro x hx
  obtain ⟨O, hO, hxO, P, hOP, hf⟩ := hloc x hx
  exact (isPLWithinAt_congr_of_isOpen_inter_eq hO hxO hOP).mpr hf

end LocalModel

section Identity

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

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

theorem IsPolyhedralManifoldWithBoundary.isPLOn_id {m : ℕ} {P : Set X}
    (hP : IsPolyhedralManifoldWithBoundary (n := n) m P) : IsPLOn n n (id : X → X) P := by
  obtain ⟨T, -⟩ := hP
  exact T.isPLOn_id

end Identity

section LocallyFinite

variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) X]

theorem IsLocallyFinitePolyhedralManifoldWithBoundary.isPLOn_id {K : Set X}
    (hK : IsLocallyFinitePolyhedralManifoldWithBoundary (n := m + 1) (m + 1) K) :
    IsPLOn (m + 1) (m + 1) (id : X → X) K := by
  refine isPLOn_of_forall_exists_isOpen_inter_eq fun x hx => ?_
  obtain ⟨O, hO, hxO, P, hP, -, hOP⟩ := hK.exists_isOpen_inter_eq hx
  exact ⟨O, hO, hxO, P, hOP, hP.isPLOn_id x (hOP.subset ⟨hxO, hx⟩).2⟩

end LocallyFinite

end DifferentialGeometry.Topology.PiecewiseLinear
