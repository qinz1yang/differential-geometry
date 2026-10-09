/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceComplement
import DifferentialGeometry.Topology.PiecewiseLinear.EuclideanPolyhedralManifold

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPolyhedralManifold.not_isPreconnected_compl
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsPolyhedralManifold (n := 3) 2 S)
    (hne : S.Nonempty) : ¬IsPreconnected Sᶜ := by
  obtain ⟨K, hfinite, hspace, hK⟩ := hS.exists_simplicialComplex
  let _ : Finite K.faces := hfinite.to_subtype
  rw [← hspace] at hne ⊢
  exact hK.not_isPreconnected_compl K (by simp) hne

theorem IsPolyhedralManifold.exists_connectedComponentIn_pair_compl
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsPolyhedralManifold (n := 3) 2 S)
    (hconn : IsConnected S) :
    ∃ a ∈ Sᶜ, ∃ b ∈ Sᶜ,
      let A := connectedComponentIn Sᶜ a
      let B := connectedComponentIn Sᶜ b
      Disjoint A B ∧ A ∪ B = Sᶜ ∧ closure A ∪ closure B = univ ∧
        closure A ∩ closure B = S ∧ frontier A = S ∧ frontier B = S := by
  obtain ⟨K, hfinite, hspace, hK⟩ := hS.exists_simplicialComplex
  let _ : Finite K.faces := hfinite.to_subtype
  rw [← hspace] at hconn ⊢
  exact hK.exists_connectedComponentIn_pair_compl K (by simp) hconn

theorem IsPolyhedralManifold.isTwoSided
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsPolyhedralManifold (n := 3) 2 S)
    (hconn : IsConnected S) : Topology.IsTwoSided S := by
  obtain ⟨K, hfinite, hspace, hK⟩ := hS.exists_simplicialComplex
  let _ : Finite K.faces := hfinite.to_subtype
  rw [← hspace] at hconn ⊢
  exact hK.isTwoSided K (by simp) hconn

end DifferentialGeometry.Topology.PiecewiseLinear
