/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.NatEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.GeneratedSubcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodManifold
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRetraction
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePieceTower
import DifferentialGeometry.Topology.PiecewiseLinear.PieceParametrization
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundary
import DifferentialGeometry.Topology.SimplicialComplex.ConnectedSpace

/-!
# Locally finite polyhedral graphs and regular neighborhoods
-/

open Set Topology
open DifferentialGeometry.Topology.Homotopy

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

open Classical in
def derivedNeighborhoodExhaustionAmbient {m : ℕ}
    (A L : ℕ → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  ⋃ i, (@derivedNeighborhood _ _ _ (Classical.decEq _) (A i) (L i)).space

open Classical in
def derivedNeighborhoodExhaustionCore {m : ℕ}
    (A L : ℕ → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))) :
    Set (derivedNeighborhoodExhaustionAmbient A L) :=
  deformationRetractExhaustionCore (fun i => (L i).space)
    (fun i => (@derivedNeighborhood _ _ _ (Classical.decEq _) (A i) (L i)).space)

open Classical in
def IsDerivedNeighborhoodExhaustion (N K : Set X) : Prop :=
  ∃ (m : ℕ)
    (J : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m)))
    (A L : ℕ → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m)))
    (f : derivedNeighborhoodExhaustionAmbient A L → X),
    J.faces = ⋃ i, (A i).faces ∧
    LocallyFinite (fun s : J.faces =>
      (Subtype.val : J.space → EuclideanSpace ℝ (Fin m)) ⁻¹'
        convexHull ℝ ((s : Finset (EuclideanSpace ℝ (Fin m))) :
          Set (EuclideanSpace ℝ (Fin m)))) ∧
    (∀ i, (A i).faces.Finite) ∧
    (∀ i, (L i).faces ⊆ (A i).faces) ∧
    (∀ i s, s ∈ (L i).faces → s.card ≤ 2) ∧
    (∀ i, IsCombinatorialManifoldWithBoundary n (A i)) ∧
    (∀ i, IsCombinatorialManifoldWithBoundary n
      (@derivedNeighborhood _ _ _ (Classical.decEq _) (A i) (L i))) ∧
    Monotone (fun i => (A i).faces) ∧
    Monotone (fun i => (L i).faces) ∧
    (∀ {i j}, i ≤ j → ∀ s ∈ (A i).faces,
      s ∈ (L j).faces → s ∈ (L i).faces) ∧
    (∀ i {x : EuclideanSpace ℝ (Fin m)},
      x ∈ (@derivedNeighborhood _ _ _ (Classical.decEq _) (A i) (L i)).space →
        (@derivedNeighborhood _ _ _ (Classical.decEq _) (A (i + 1)) (L (i + 1))).space ∈
          nhdsWithin x (derivedNeighborhoodExhaustionAmbient A L)) ∧
    IsEmbedding f ∧
    Set.range f = N ∧
    f '' derivedNeighborhoodExhaustionCore A L = K

open Classical in
def IsLocallyFiniteRegularNeighborhoodOf (N K U : Set X) : Prop :=
  IsDerivedNeighborhoodExhaustion (n := n) N K ∧
    N ∈ nhdsSet K ∧
    N ⊆ U ∧
    IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) n N

theorem IsLocallyFiniteRegularNeighborhoodOf.mem_nhdsSet {N K U : Set X}
    (h : IsLocallyFiniteRegularNeighborhoodOf (n := n) N K U) : N ∈ nhdsSet K := by
  exact h.2.1

theorem IsLocallyFiniteRegularNeighborhoodOf.subset {N K U : Set X}
    (h : IsLocallyFiniteRegularNeighborhoodOf (n := n) N K U) : N ⊆ U := by
  exact h.2.2.1

theorem IsLocallyFiniteRegularNeighborhoodOf.isLocallyFinitePolyhedralManifoldWithBoundary
    {N K U : Set X} (h : IsLocallyFiniteRegularNeighborhoodOf (n := n) N K U) :
    IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) n N := by
  exact h.2.2.2

omit [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] in
open Classical in
theorem IsDerivedNeighborhoodExhaustion.nonempty_strongDeformationRetract
    {N K : Set X} (h : IsDerivedNeighborhoodExhaustion (n := n) N K) :
    Nonempty (StrongDeformationRetract {x : N | (x : X) ∈ K}) := by
  obtain ⟨m, J, A, L, f, hJ, hlocal, hfinite, hLA, hcard, hambient, hderived,
    hAmono, hLmono, hrestrict, hnhds, hf, hN, hK⟩ := h
  let _ : ∀ i, Finite (A i).faces := fun i => (hfinite i).to_subtype
  let R := derivedNeighborhoodCompatibleStrongDeformationRetractSystem A L hLA hAmono
    hLmono hrestrict hnhds
  rw [← hN, ← hK]
  exact ⟨R.toStrongDeformationRetract.embeddingImage f hf⟩

open Classical in
theorem IsLocallyFiniteRegularNeighborhoodOf.nonempty_strongDeformationRetract
    {N K U : Set X} (h : IsLocallyFiniteRegularNeighborhoodOf (n := n) N K U) :
    Nonempty (StrongDeformationRetract {x : N | (x : X) ∈ K}) := by
  exact h.1.nonempty_strongDeformationRetract

open Classical in
noncomputable def IsLocallyFiniteRegularNeighborhoodOf.strongDeformationRetract
    {N K U : Set X} (h : IsLocallyFiniteRegularNeighborhoodOf (n := n) N K U) :
    StrongDeformationRetract {x : N | (x : X) ∈ K} :=
  Classical.choice h.nonempty_strongDeformationRetract

open Classical in
theorem PLPiece.isLocallyFiniteRegularNeighborhoodOf_derivedNeighborhood {U : Set X}
    [T2Space X]
    (P : PLPiece n X U)
    (G : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin P.ambientDim)))
    (hG : G.faces ⊆ P.piece.complex.faces)
    (hcard : ∀ s ∈ G.faces, s.card ≤ 2)
    (hambient : IsCombinatorialManifoldWithBoundary n P.piece.complex)
    (hderived : IsCombinatorialManifoldWithBoundary n
      (@derivedNeighborhood _ _ _ (Classical.decEq _) P.piece.complex G))
    (hnhds : P.piece.map ''
      (@derivedNeighborhood _ _ _ (Classical.decEq _) P.piece.complex G).space ∈
      nhdsSet (P.piece.map '' G.space)) :
    IsLocallyFiniteRegularNeighborhoodOf (n := n)
      (P.piece.map ''
        (@derivedNeighborhood _ _ _ (Classical.decEq _) P.piece.complex G).space)
      (P.piece.map '' G.space) U := by
  let D := @derivedNeighborhood _ _ _ (Classical.decEq _) P.piece.complex G
  let A : ℕ → Geometry.SimplicialComplex ℝ
      (EuclideanSpace ℝ (Fin P.ambientDim)) := fun _ => P.piece.complex
  let L : ℕ → Geometry.SimplicialComplex ℝ
      (EuclideanSpace ℝ (Fin P.ambientDim)) := fun _ => G
  let _ : Finite P.piece.complex.faces := P.piece.finite_faces.to_subtype
  have hDspace : D.space ⊆ P.piece.complex.space := by
    change (@derivedNeighborhood _ _ _ (Classical.decEq _)
      P.piece.complex G).space ⊆ P.piece.complex.space
    exact @derivedNeighborhood_space_subset _ _ _ (Classical.decEq _)
      P.piece.complex G
  have hExhaustionSpace : derivedNeighborhoodExhaustionAmbient A L ⊆
      P.piece.complex.space := by
    intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact hDspace (by simpa only [A, L, D] using hxi)
  let f : derivedNeighborhoodExhaustionAmbient A L → X :=
    (fun x : P.piece.complex.space => P.piece.map x) ∘
      Set.inclusion hExhaustionSpace
  have hf : IsEmbedding f :=
    P.piece.isClosedEmbedding.isEmbedding.comp (IsEmbedding.inclusion hExhaustionSpace)
  have hfrange : Set.range f = P.piece.map '' D.space := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp x.2
      exact ⟨x, by simpa only [A, L, D] using hxi, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      let y : derivedNeighborhoodExhaustionAmbient A L :=
        ⟨x, Set.mem_iUnion.mpr ⟨0, by simpa only [A, L, D] using hx⟩⟩
      exact ⟨y, rfl⟩
  have hfcore : f '' derivedNeighborhoodExhaustionCore A L =
      P.piece.map '' G.space := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (x : EuclideanSpace ℝ (Fin P.ambientDim)) ∈ ⋃ i, (L i).space at hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      exact ⟨x, by simpa only [L] using hxi, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      let z : derivedNeighborhoodExhaustionAmbient A L :=
        ⟨x, Set.mem_iUnion.mpr ⟨0, by
          simpa only [A, L, D] using subcomplex_space_subset_derivedNeighborhood hG hx⟩⟩
      refine ⟨z, ?_, rfl⟩
      change (z : EuclideanSpace ℝ (Fin P.ambientDim)) ∈ ⋃ i, (L i).space
      exact Set.mem_iUnion.mpr ⟨0, by simpa only [L] using hx⟩
  refine ⟨⟨P.ambientDim, P.piece.complex, A, L, f, ?_, locallyFinite_of_finite _,
    fun _ => P.piece.finite_faces, fun _ => hG, fun _ => hcard, fun _ => hambient,
    fun _ => hderived, ?_, ?_, ?_, ?_, hf, hfrange, hfcore⟩, hnhds, ?_, ?_⟩
  · exact (iUnion_const (ι := ℕ) P.piece.complex.faces).symm
  · intro i j hij
    exact Subset.rfl
  · intro i j hij
    exact Subset.rfl
  · intro i j hij s hsA hsL
    simpa only [A, L] using hsL
  · intro i x hx
    simpa only [derivedNeighborhoodExhaustionAmbient, A, L, iUnion_const] using
      (self_mem_nhdsWithin : D.space ∈ nhdsWithin x D.space)
  · rintro x ⟨y, hy, rfl⟩
    let _ : DecidableEq (EuclideanSpace ℝ (Fin P.ambientDim)) := Classical.decEq _
    exact P.piece.bijOn.mapsTo (derivedNeighborhood_space_subset P.piece.complex G hy)
  · let _ : DecidableEq (EuclideanSpace ℝ (Fin P.ambientDim)) := Classical.decEq _
    let P' := P.piece.subdivide (secondDerived P.piece.complex)
      (secondDerived_isSubdivision P.piece.complex) (Set.toFinite _)
    let D' := P'.restrict D (derivedNeighborhood_faces_subset P.piece.complex G)
    exact (isPolyhedralManifoldWithBoundary_of_pieceIn D' hderived).isLocallyFinite

private def vertexOnlyComplex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) : Geometry.SimplicialComplex ℝ E where
  faces := {s | ∃ v ∈ V, s = {v}}
  isRelLowerSet_faces := by
    rintro s ⟨v, hv, rfl⟩
    refine ⟨Finset.singleton_nonempty v, fun t hts ht => ?_⟩
    exact ⟨v, hv, ht.subset_singleton_iff.mp hts⟩
  indep := by
    rintro s ⟨v, -, rfl⟩
    exact affineIndependent_of_subsingleton ℝ _
  inter_subset_convexHull := by
    rintro s t ⟨v, -, rfl⟩ ⟨w, -, rfl⟩
    simp only [Finset.coe_singleton, convexHull_singleton]
    by_cases h : v = w
    · subst w
      simp
    · simp [h]

private theorem vertexOnlyComplex_space {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) : (vertexOnlyComplex V).space = V := by
  ext x
  rw [Geometry.SimplicialComplex.mem_space_iff]
  constructor
  · rintro ⟨s, ⟨v, hv, rfl⟩, hx⟩
    rw [Finset.coe_singleton, convexHull_singleton] at hx
    rwa [hx]
  · intro hx
    exact ⟨{x}, ⟨x, hx, rfl⟩, by simp⟩

open Classical in
private theorem vertexOnlyComplex_isCombinatorialManifoldWithBoundary_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Set E) :
    IsCombinatorialManifoldWithBoundary 0 (vertexOnlyComplex V) := by
  intro v hv
  rw [Set.eq_empty_iff_forall_notMem]
  intro t ht
  obtain ⟨hne, hvt, hins⟩ :=
    (@SimplicialComplex.mem_geometricLink_singleton ℝ E _ _ _ _
      (Classical.decEq E) (vertexOnlyComplex V) v t).mp ht
  obtain ⟨w, -, heq⟩ := hins
  obtain ⟨x, hxt⟩ := hne
  have hvw : v = w := by
    have hv : v ∈ ({w} : Finset E) := heq ▸ Finset.mem_insert_self v t
    simpa using hv
  have hxw : x = w := by
    have hx : x ∈ ({w} : Finset E) := heq ▸ Finset.mem_insert_of_mem hxt
    simpa using hx
  exact hvt ((hxw.trans hvw.symm) ▸ hxt)

open Classical in
private theorem isCombinatorialManifoldWithBoundary_zero_of_card_le_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (hcard : ∀ s ∈ K.faces, s.card ≤ 1) :
    IsCombinatorialManifoldWithBoundary 0 K := by
  intro v hv
  rw [Set.eq_empty_iff_forall_notMem]
  intro t ht
  obtain ⟨hne, hvt, hins⟩ :=
    (@SimplicialComplex.mem_geometricLink_singleton ℝ E _ _ _ _
      (Classical.decEq E) K v t).mp ht
  have hle := hcard _ hins
  rw [Finset.card_insert_of_notMem hvt] at hle
  have hpos := Finset.card_pos.mpr hne
  omega

open Classical in
theorem noncompact_derivedNeighborhoodExhaustion_nat :
    IsDerivedNeighborhoodExhaustion (n := 0) (Set.univ : Set ℕ) Set.univ ∧
      ¬IsCompact (Set.univ : Set ℕ) := by
  refine ⟨?_, noncompact_univ ℕ⟩
  obtain ⟨p, hp⟩ := exists_topology_isEmbedding_nat (EuclideanSpace ℝ (Fin 1))
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 1)) := Classical.decEq _
  let J := vertexOnlyComplex (Set.range p)
  let A : ℕ → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 1)) :=
    fun i => vertexOnlyComplex (p '' Set.Iic i)
  let L := A
  have hJspace : J.space = Set.range p := by
    simpa only [J] using vertexOnlyComplex_space (Set.range p)
  have hAspace (i : ℕ) : (A i).space = p '' Set.Iic i := by
    simpa only [A] using vertexOnlyComplex_space (p '' Set.Iic i)
  have hfinite (i : ℕ) : (A i).faces.Finite := by
    have hV : (p '' Set.Iic i).Finite := (Set.toFinite (Set.Iic i)).image p
    refine (hV.image fun v => ({v} : Finset (EuclideanSpace ℝ (Fin 1)))).subset ?_
    intro s hs
    obtain ⟨v, hv, rfl⟩ := hs
    exact ⟨v, hv, rfl⟩
  have hDspace (i : ℕ) :
      (@derivedNeighborhood _ _ _ (Classical.decEq _) (A i) (L i)).space = (A i).space := by
    let _ : Finite (A i).faces := (hfinite i).to_subtype
    apply Subset.antisymm
    · exact derivedNeighborhood_space_subset (A i) (L i)
    · exact subcomplex_space_subset_derivedNeighborhood (by
        change (A i).faces ⊆ (A i).faces
        exact Subset.rfl)
  have hAunion : (⋃ i, (A i).space) = Set.range p := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      rw [hAspace] at hxi
      obtain ⟨k, -, rfl⟩ := hxi
      exact Set.mem_range_self k
    · rintro ⟨k, rfl⟩
      exact Set.mem_iUnion.mpr ⟨k, hAspace k ▸ ⟨k, Set.mem_Iic.mpr le_rfl, rfl⟩⟩
  have hDunion : derivedNeighborhoodExhaustionAmbient A L = Set.range p := by
    change (⋃ i, (@derivedNeighborhood _ _ _ (Classical.decEq _) (A i) (L i)).space) =
      Set.range p
    simp_rw [hDspace]
    exact hAunion
  have hJfaces : J.faces = ⋃ i, (A i).faces := by
    ext s
    constructor
    · rintro ⟨v, ⟨k, rfl⟩, rfl⟩
      exact Set.mem_iUnion.mpr ⟨k, ⟨p k, ⟨k, Set.mem_Iic.mpr le_rfl, rfl⟩, rfl⟩⟩
    · intro hs
      obtain ⟨i, hsi⟩ := Set.mem_iUnion.mp hs
      obtain ⟨v, ⟨k, -, rfl⟩, rfl⟩ := hsi
      exact ⟨p k, Set.mem_range_self k, rfl⟩
  have hlocal : LocallyFinite (fun s : J.faces =>
      (Subtype.val : J.space → EuclideanSpace ℝ (Fin 1)) ⁻¹'
        convexHull ℝ ((s : Finset (EuclideanSpace ℝ (Fin 1))) :
          Set (EuclideanSpace ℝ (Fin 1)))) := by
    let _ : DiscreteTopology J.space := by
      rw [hJspace]
      exact hp.toHomeomorph.symm.isEmbedding.discreteTopology
    intro x
    have hxrange : (x : EuclideanSpace ℝ (Fin 1)) ∈ Set.range p := hJspace ▸ x.2
    have hxface : ({(x : EuclideanSpace ℝ (Fin 1))} : Finset _) ∈ J.faces :=
      ⟨x, hxrange, rfl⟩
    let sx : J.faces := ⟨{(x : EuclideanSpace ℝ (Fin 1))}, hxface⟩
    refine ⟨{x}, (isOpen_discrete {x}).mem_nhds (Set.mem_singleton x), ?_⟩
    refine Set.Finite.subset (Set.finite_singleton sx) ?_
    intro s hs
    obtain ⟨y, hyface, hyx⟩ := hs
    have hyx' : y = x := Set.mem_singleton_iff.mp hyx
    subst y
    change (x : EuclideanSpace ℝ (Fin 1)) ∈
      convexHull ℝ ((s : Finset (EuclideanSpace ℝ (Fin 1))) :
        Set (EuclideanSpace ℝ (Fin 1))) at hyface
    obtain ⟨v, -, hsv⟩ := s.2
    have hxv : (x : EuclideanSpace ℝ (Fin 1)) = v := by
      rw [hsv, Finset.coe_singleton, convexHull_singleton] at hyface
      exact hyface
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    change (s : Finset (EuclideanSpace ℝ (Fin 1))) =
      {(x : EuclideanSpace ℝ (Fin 1))}
    rw [hsv, hxv]
  have hambient (i : ℕ) : IsCombinatorialManifoldWithBoundary 0 (A i) := by
    simpa only [A] using
      vertexOnlyComplex_isCombinatorialManifoldWithBoundary_zero (p '' Set.Iic i)
  have hderived (i : ℕ) : IsCombinatorialManifoldWithBoundary 0
      (@derivedNeighborhood _ _ _ (Classical.decEq _) (A i) (L i)) := by
    let _ : Finite (A i).faces := (hfinite i).to_subtype
    apply isCombinatorialManifoldWithBoundary_zero_of_card_le_one
    intro s hs
    exact (hambient i).secondDerived.card_le_one
      (derivedNeighborhood_faces_subset (A i) (L i) hs)
  have hstrict : StrictMono (fun i => (A i).faces) := by
    intro i j hij
    refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro s hs
      obtain ⟨v, ⟨k, hki, rfl⟩, rfl⟩ := hs
      exact ⟨p k, ⟨k, Set.mem_Iic.mpr ((Set.mem_Iic.mp hki).trans hij.le), rfl⟩, rfl⟩
    · intro heq
      have hj : ({p j} : Finset (EuclideanSpace ℝ (Fin 1))) ∈ (A j).faces :=
        ⟨p j, ⟨j, Set.mem_Iic.mpr le_rfl, rfl⟩, rfl⟩
      have hi : ({p j} : Finset (EuclideanSpace ℝ (Fin 1))) ∈ (A i).faces := by
        change (A i).faces = (A j).faces at heq
        exact heq.symm ▸ hj
      obtain ⟨v, ⟨k, hki, rfl⟩, hface⟩ := hi
      have hpjk : p j = p k := Finset.singleton_injective hface
      have hji : j ≤ i := by
        simpa [hp.injective hpjk] using Set.mem_Iic.mp hki
      exact (Nat.not_le_of_gt hij) hji
  let e : derivedNeighborhoodExhaustionAmbient A L ≃ₜ ℕ :=
    (Homeomorph.setCongr hDunion).trans hp.toHomeomorph.symm
  let f : derivedNeighborhoodExhaustionAmbient A L → ℕ := e
  let _ : DiscreteTopology (derivedNeighborhoodExhaustionAmbient A L) :=
    e.isEmbedding.discreteTopology
  have hnhds (i : ℕ) {x : EuclideanSpace ℝ (Fin 1)}
      (hx : x ∈ (@derivedNeighborhood _ _ _ (Classical.decEq _) (A i) (L i)).space) :
      (@derivedNeighborhood _ _ _ (Classical.decEq _) (A (i + 1)) (L (i + 1))).space ∈
        nhdsWithin x (derivedNeighborhoodExhaustionAmbient A L) := by
    let y : derivedNeighborhoodExhaustionAmbient A L :=
      ⟨x, Set.mem_iUnion.mpr ⟨i, hx⟩⟩
    apply (preimage_coe_mem_nhds_subtype
      (s := derivedNeighborhoodExhaustionAmbient A L)
      (t := (@derivedNeighborhood _ _ _ (Classical.decEq _)
        (A (i + 1)) (L (i + 1))).space) (a := y)).mp
    apply (isOpen_discrete _).mem_nhds
    exact space_mono_of_faces_subset
      (derivedNeighborhood_faces_mono (hstrict.monotone (Nat.le_succ i))
        (hstrict.monotone (Nat.le_succ i))) hx
  have hcore : derivedNeighborhoodExhaustionCore A L = Set.univ := by
    ext x
    constructor
    · intro
      exact Set.mem_univ x
    · intro
      change (x : EuclideanSpace ℝ (Fin 1)) ∈ ⋃ i, (L i).space
      rw [show (⋃ i, (L i).space) = Set.range p by simpa only [L] using hAunion]
      rw [← hDunion]
      exact x.2
  refine ⟨1, J, A, L, f, hJfaces, hlocal, hfinite, fun i => by
      change (A i).faces ⊆ (A i).faces
      exact Subset.rfl,
    fun i s hs => ?_, hambient, hderived, hstrict.monotone, ?_, ?_, hnhds,
    e.isEmbedding, ?_, ?_⟩
  · obtain ⟨v, -, rfl⟩ := hs
    simp
  · simpa only [L] using hstrict.monotone
  · intro i j hij s hs _
    change s ∈ (A i).faces
    exact hs
  · simpa only [f] using e.surjective.range_eq
  · rw [hcore, Set.image_univ]
    simpa only [f] using e.surjective.range_eq

end DifferentialGeometry.Topology.PiecewiseLinear
