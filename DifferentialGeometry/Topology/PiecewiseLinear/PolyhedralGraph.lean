/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GeneratedSubcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePieceTower
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundary
import DifferentialGeometry.Topology.SimplicialComplex.ConnectedSpace

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

open Classical in
theorem exists_tetrahedron_oneSkeleton :
    ∃ L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      L.faces.Finite ∧
      (∀ s ∈ L.faces, s.card ≤ 2) ∧
      (∃ e ∈ L.faces, e.card = 2) ∧
      IsConnected L.space ∧
      (∀ v : L.vertices,
        ((SimplicialComplex.edgeGraph L).neighborSet v).ncard ≠ 1) ∧
      ∃ v : L.vertices,
        ((SimplicialComplex.edgeGraph L).neighborSet v).ncard = 3 := by
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  obtain ⟨T, hT, hTcard, -, -, -⟩ :=
    exists_affineIndependent_openSimplex_subset
      (E := EuclideanSpace ℝ (Fin 3)) (n := 2) (by simp) 0 (U := Set.univ) (by simp)
  let A := simplexComplex T hT
  let L := subcomplexGeneratedBy A {s | s.card = 2}
  have hAfin : A.faces.Finite := simplexComplex_faces_finite T hT
  have hLfin : L.faces.Finite :=
    hAfin.subset (subcomplexGeneratedBy_faces_subset A {s | s.card = 2})
  let _ : Finite L.faces := hLfin.to_subtype
  have hdim : ∀ s ∈ L.faces, s.card ≤ 2 := by
    rintro s ⟨t, ht, hst, -⟩
    exact (Finset.card_le_card hst).trans_eq ht.2
  have hvertices : L.vertices = (T : Set (EuclideanSpace ℝ (Fin 3))) := by
    ext v
    constructor
    · intro hv
      have hvA := subcomplexGeneratedBy_faces_subset A {s | s.card = 2} hv
      exact (mem_simplexComplex_faces_iff T hT).mp hvA |>.2 (by simp)
    · intro hv
      obtain ⟨w, hwT, hwv⟩ := Finset.exists_mem_ne (by omega : 1 < T.card) v
      refine ⟨{v, w}, ⟨?_, ?_⟩, ?_, Finset.singleton_nonempty v⟩
      · exact (mem_simplexComplex_faces_iff T hT).mpr
          ⟨by simp, by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact hv
            · exact hwT⟩
      · change ({v, w} : Finset (EuclideanSpace ℝ (Fin 3))).card = 2
        rw [Finset.card_pair hwv.symm]
      · simp
  have hgraph : SimplicialComplex.edgeGraph L = ⊤ := by
    ext u v
    rw [SimplicialComplex.edgeGraph_adj, SimpleGraph.top_adj]
    constructor
    · exact fun h => h.1
    · intro huv
      refine ⟨huv, ⟨{(u : EuclideanSpace ℝ (Fin 3)), (v : EuclideanSpace ℝ (Fin 3))},
        ⟨?_, ?_⟩, fun _ h => h, by simp⟩⟩
      · exact (mem_simplexComplex_faces_iff T hT).mpr
          ⟨by simp, by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact hvertices.subset u.2
            · exact hvertices.subset v.2⟩
      · have huv' : (u : EuclideanSpace ℝ (Fin 3)) ≠ v := fun h => huv (Subtype.ext h)
        exact Finset.card_pair huv'
  have hcardV : Nat.card L.vertices = 4 := by
    calc
      Nat.card L.vertices = Nat.card (T : Set (EuclideanSpace ℝ (Fin 3))) :=
        Nat.card_congr (Equiv.setCongr hvertices)
      _ = T.card := by simp
      _ = 4 := by omega
  have hnonempty : Nonempty L.vertices := by
    rw [hvertices]
    apply Set.nonempty_coe_sort.mpr
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by rw [hTcard]; norm_num)
    exact ⟨v, hv⟩
  let _ : Finite L.vertices := (SimplicialComplex.finite_vertices L).to_subtype
  let _ : Nonempty L.vertices := hnonempty
  have hdegree (v : L.vertices) :
      ((SimplicialComplex.edgeGraph L).neighborSet v).ncard = 3 := by
    rw [hgraph, SimpleGraph.neighborSet_top, Set.ncard_compl, Set.ncard_singleton, hcardV]
  have hedge : ∃ e ∈ L.faces, e.card = 2 := by
    let v : L.vertices := Classical.choice hnonempty
    have hneighborhood : ((SimplicialComplex.edgeGraph L).neighborSet v).Nonempty := by
      exact Set.nonempty_of_ncard_ne_zero (by rw [hdegree v]; norm_num)
    obtain ⟨w, hw⟩ := hneighborhood
    have hvw : (v : EuclideanSpace ℝ (Fin 3)) ≠ w := fun h =>
      ((SimplicialComplex.edgeGraph_adj L v w).mp hw).1 (Subtype.ext h)
    exact ⟨{(v : EuclideanSpace ℝ (Fin 3)), (w : EuclideanSpace ℝ (Fin 3))},
      ((SimplicialComplex.edgeGraph_adj L v w).mp hw).2,
      Finset.card_pair hvw⟩
  refine ⟨L, hLfin, hdim, hedge, isConnected_space_of_edgeGraph_connected L ?_,
    fun v h => by rw [hdegree v] at h; omega, ?_⟩
  · simpa only [hgraph] using (SimpleGraph.connected_top : (⊤ : SimpleGraph L.vertices).Connected)
  · exact ⟨Classical.choice hnonempty, hdegree _⟩

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
