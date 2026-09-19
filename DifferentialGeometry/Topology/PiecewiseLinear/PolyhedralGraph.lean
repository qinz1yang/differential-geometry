/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePieceTower

/-!
# Locally finite polyhedral graphs and regular neighborhoods
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

open Classical in
def IsLocallyFinitePolyhedralGraph (K : Set X) : Prop :=
  ∃ T : LocallyFinitePieceTower n X K,
    ∀ i s, s ∈ (T.piece i).piece.complex.faces → s.card ≤ 2

theorem PLPiece.isLocallyFinitePolyhedralGraph {K : Set X} (P : PLPiece n X K)
    (hP : ∀ s, s ∈ P.piece.complex.faces → s.card ≤ 2) :
    IsLocallyFinitePolyhedralGraph (n := n) K :=
  ⟨LocallyFinitePieceTower.ofPiece P, fun _ => hP⟩

namespace LocallyFinitePieceTower

open Classical in
def regularNeighborhoodImage {U : Set X} (T : LocallyFinitePieceTower n X U)
    (G : ∀ i, Geometry.SimplicialComplex ℝ
      (EuclideanSpace ℝ (Fin (T.piece i).ambientDim))) (i : ℕ) : Set X :=
  (T.piece i).piece.map ''
    (regularNeighborhoodIn (T.piece i).piece.complex (G i).space).space

end LocallyFinitePieceTower

open Classical in
def IsLocallyFiniteRegularNeighborhoodOf (N K U : Set X) : Prop :=
  ∃ (T : LocallyFinitePieceTower n X U)
    (G : ∀ i, Geometry.SimplicialComplex ℝ
      (EuclideanSpace ℝ (Fin (T.piece i).ambientDim))),
    (∀ i, IsCombinatorialManifoldWithBoundary n (T.piece i).piece.complex) ∧
    (∀ i, (G i).faces ⊆ (T.core i).faces) ∧
    (∀ i s, s ∈ (G i).faces → s.card ≤ 2) ∧
    (∀ i s, s ∈ (G i).faces → s.image (T.embed i) ∈ (G (i + 1)).faces) ∧
    (⋃ i, (T.piece i).piece.map '' (G i).space) = K ∧
    (∀ i, IsCombinatorialManifoldWithBoundary n
      (regularNeighborhoodIn (T.piece i).piece.complex (G i).space)) ∧
    Monotone (T.regularNeighborhoodImage G) ∧
    N = ⋃ i, T.regularNeighborhoodImage G i ∧
    N ∈ nhdsSet K ∧
    N ⊆ U ∧
    IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) n N

theorem IsLocallyFiniteRegularNeighborhoodOf.mem_nhdsSet {N K U : Set X}
    (h : IsLocallyFiniteRegularNeighborhoodOf (n := n) N K U) : N ∈ nhdsSet K := by
  obtain ⟨T, G, -, -, -, -, -, -, -, -, hN, -, -⟩ := h
  exact hN

theorem IsLocallyFiniteRegularNeighborhoodOf.subset {N K U : Set X}
    (h : IsLocallyFiniteRegularNeighborhoodOf (n := n) N K U) : N ⊆ U := by
  obtain ⟨T, G, -, -, -, -, -, -, -, -, -, hNU, -⟩ := h
  exact hNU

theorem IsLocallyFiniteRegularNeighborhoodOf.isLocallyFinitePolyhedralManifoldWithBoundary
    {N K U : Set X} (h : IsLocallyFiniteRegularNeighborhoodOf (n := n) N K U) :
    IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) n N := by
  obtain ⟨T, G, -, -, -, -, -, -, -, -, -, -, hN⟩ := h
  exact hN

end DifferentialGeometry.Topology.PiecewiseLinear
