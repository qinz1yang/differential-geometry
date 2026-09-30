/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.NatEmbedding
import Mathlib.Topology.Order.AtTopBotIxx
import DifferentialGeometry.Topology.PiecewiseLinear.ArcCellBoundaryExample
import DifferentialGeometry.Topology.PiecewiseLinear.GeneratedSubcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodManifold
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRetraction
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePieceTower
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyPolyhedral
import DifferentialGeometry.Topology.PiecewiseLinear.PieceParametrization
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundary
import DifferentialGeometry.Topology.SimplicialComplex.ConnectedSpace

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

structure LocallyFinitePLPieceIn (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] (Y : Set X) where
  complex : Geometry.SimplicialComplex ℝ E
  locallyFinite : LocallyFinite (fun s : complex.faces =>
    (Subtype.val : complex.space → E) ⁻¹'
      convexHull ℝ ((s : Finset E) : Set E))
  map : E → X
  bijOn : BijOn map complex.space Y
  continuousOn : ContinuousOn map complex.space
  isEmbedding : IsEmbedding (fun x : complex.space => map x)
  isPiecewiseAffineOn_chart : ∀ e ∈ atlas (EuclideanSpace ℝ (Fin n)) X,
    IsPiecewiseAffineOn (e ∘ map) (complex.space ∩ map ⁻¹' e.source)
  isPiecewiseAffineOn_chart_symm : ∀ e ∈ atlas (EuclideanSpace ℝ (Fin n)) X,
    IsPiecewiseAffineOn (Function.invFunOn map complex.space ∘ e.symm)
      (e.target ∩ e.symm ⁻¹' Y)

open Classical in
def PLPieceIn.toLocallyFinite {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [T2Space X] {Y : Set X}
    (T : PLPieceIn E n X Y) : LocallyFinitePLPieceIn E n X Y := by
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  exact
    { complex := T.complex
      locallyFinite := locallyFinite_of_finite _
      map := T.map
      bijOn := T.bijOn
      continuousOn := T.continuousOn
      isEmbedding := T.isClosedEmbedding.isEmbedding
      isPiecewiseAffineOn_chart := T.isPiecewiseAffineOn_chart
      isPiecewiseAffineOn_chart_symm := T.isPiecewiseAffineOn_chart_symm }

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
        Nat.card_congr (Set.equivOfEq hvertices)
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
def IsPLDerivedNeighborhoodExhaustion (N K U : Set X) : Prop :=
  ∃ (m : ℕ)
    (T : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin m)) n X U)
    (A L : ℕ → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))),
    T.complex.faces = ⋃ i, (A i).faces ∧
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
    Set.range (fun x : derivedNeighborhoodExhaustionAmbient A L => T.map x) = N ∧
    (fun x : derivedNeighborhoodExhaustionAmbient A L => T.map x) ''
      derivedNeighborhoodExhaustionCore A L = K

open Classical in
private theorem derivedNeighborhoodExhaustionAmbient_subset_complex
    {m : ℕ} {J : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))}
    {A L : ℕ → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))}
    (hJ : J.faces = ⋃ i, (A i).faces) :
    derivedNeighborhoodExhaustionAmbient A L ⊆ J.space := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  apply space_mono_of_faces_subset (K := J)
  · intro s hs
    rw [hJ]
    exact Set.mem_iUnion.mpr ⟨i, hs⟩
  · exact (@derivedNeighborhood_space_subset _ _ _ (Classical.decEq _) (A i) (L i)) hxi

open Classical in
theorem IsPLDerivedNeighborhoodExhaustion.isDerivedNeighborhoodExhaustion
    {N K U : Set X} (h : IsPLDerivedNeighborhoodExhaustion (n := n) N K U) :
    IsDerivedNeighborhoodExhaustion (n := n) N K := by
  obtain ⟨m, T, A, L, hJ, hfinite, hLA, hcard, hambient, hderived,
    hAmono, hLmono, hrestrict, hnhds, hN, hK⟩ := h
  have hsub : derivedNeighborhoodExhaustionAmbient A L ⊆ T.complex.space :=
    derivedNeighborhoodExhaustionAmbient_subset_complex hJ
  let f : derivedNeighborhoodExhaustionAmbient A L → X :=
    (fun x : T.complex.space => T.map x) ∘ Set.inclusion hsub
  have hf : IsEmbedding f := T.isEmbedding.comp (IsEmbedding.inclusion hsub)
  exact ⟨m, T.complex, A, L, f, hJ, T.locallyFinite, hfinite, hLA, hcard,
    hambient, hderived, hAmono, hLmono, hrestrict, hnhds, hf, hN, hK⟩

open Classical in
theorem IsPLDerivedNeighborhoodExhaustion.subset_ambient
    {N K U : Set X} (h : IsPLDerivedNeighborhoodExhaustion (n := n) N K U) : N ⊆ U := by
  obtain ⟨m, T, A, L, hJ, -, -, -, -, -, -, -, -, -, hN, -⟩ := h
  have hsub : derivedNeighborhoodExhaustionAmbient A L ⊆ T.complex.space :=
    derivedNeighborhoodExhaustionAmbient_subset_complex hJ
  rw [← hN]
  rintro _ ⟨x, rfl⟩
  exact T.bijOn.mapsTo (hsub x.2)

open Classical in
def IsLocallyFiniteRegularNeighborhoodOf (N K U : Set X) : Prop :=
  IsPLDerivedNeighborhoodExhaustion (n := n) N K U ∧
    N ∈ nhdsSet K ∧
    IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) n N

theorem IsLocallyFiniteRegularNeighborhoodOf.mem_nhdsSet {N K U : Set X}
    (h : IsLocallyFiniteRegularNeighborhoodOf (n := n) N K U) : N ∈ nhdsSet K := by
  exact h.2.1

theorem IsLocallyFiniteRegularNeighborhoodOf.subset {N K U : Set X}
    (h : IsLocallyFiniteRegularNeighborhoodOf (n := n) N K U) : N ⊆ U := by
  exact h.1.subset_ambient

theorem IsLocallyFiniteRegularNeighborhoodOf.isLocallyFinitePolyhedralManifoldWithBoundary
    {N K U : Set X} (h : IsLocallyFiniteRegularNeighborhoodOf (n := n) N K U) :
    IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) n N := by
  exact h.2.2

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
  exact h.1.isDerivedNeighborhoodExhaustion.nonempty_strongDeformationRetract

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
  let T := P.piece.toLocallyFinite
  have hfrange : Set.range
      (fun x : derivedNeighborhoodExhaustionAmbient A L => T.map x) =
      P.piece.map '' D.space := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp x.2
      exact ⟨x, by simpa only [A, L, D] using hxi, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      let y : derivedNeighborhoodExhaustionAmbient A L :=
        ⟨x, Set.mem_iUnion.mpr ⟨0, by simpa only [A, L, D] using hx⟩⟩
      exact ⟨y, rfl⟩
  have hfcore : (fun x : derivedNeighborhoodExhaustionAmbient A L => T.map x) ''
      derivedNeighborhoodExhaustionCore A L =
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
  refine ⟨⟨P.ambientDim, T, A, L, ?_,
    fun _ => P.piece.finite_faces, fun _ => hG, fun _ => hcard, fun _ => hambient,
    fun _ => hderived, ?_, ?_, ?_, ?_, hfrange, hfcore⟩, hnhds, ?_⟩
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
  · let _ : DecidableEq (EuclideanSpace ℝ (Fin P.ambientDim)) := Classical.decEq _
    let P' := P.piece.subdivide (secondDerived P.piece.complex)
      (secondDerived_isSubdivision P.piece.complex) (Set.toFinite _)
    let D' := P'.restrict D (derivedNeighborhood_faces_subset P.piece.complex G)
    exact (isPolyhedralManifoldWithBoundary_of_pieceIn D' hderived).isLocallyFinite

private def disjointUnionComplex {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : ι → Geometry.SimplicialComplex ℝ E)
    (hdis : Pairwise fun i j => Disjoint (C i).space (C j).space) (I : Set ι) :
    Geometry.SimplicialComplex ℝ E where
  faces := ⋃ i ∈ I, (C i).faces
  isRelLowerSet_faces := by
    rintro s hs
    obtain ⟨i, hi, hsi⟩ := Set.mem_iUnion₂.mp hs
    obtain ⟨hne, hdown⟩ := (C i).isRelLowerSet_faces hsi
    exact ⟨hne, fun _ hts ht => Set.mem_iUnion₂.mpr ⟨i, hi, hdown hts ht⟩⟩
  indep := by
    rintro s hs
    obtain ⟨i, -, hsi⟩ := Set.mem_iUnion₂.mp hs
    exact (C i).indep hsi
  inter_subset_convexHull := by
    rintro s t hs ht
    obtain ⟨i, -, hsi⟩ := Set.mem_iUnion₂.mp hs
    obtain ⟨j, -, htj⟩ := Set.mem_iUnion₂.mp ht
    by_cases hij : i = j
    · subst j
      exact (C i).inter_subset_convexHull hsi htj
    · intro x hx
      exact (Set.disjoint_left.mp (hdis hij)
        ((C i).convexHull_subset_space hsi hx.1)
        ((C j).convexHull_subset_space htj hx.2)).elim

private theorem mem_disjointUnionComplex_faces_iff {ι E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {C : ι → Geometry.SimplicialComplex ℝ E}
    {hdis : Pairwise fun i j => Disjoint (C i).space (C j).space} {I : Set ι}
    {s : Finset E} :
    s ∈ (disjointUnionComplex C hdis I).faces ↔ ∃ i ∈ I, s ∈ (C i).faces := by
  change s ∈ ⋃ i ∈ I, (C i).faces ↔ _
  constructor
  · intro h
    obtain ⟨i, hi, hs⟩ := Set.mem_iUnion₂.mp h
    exact ⟨i, hi, hs⟩
  · rintro ⟨i, hi, hs⟩
    exact Set.mem_iUnion₂.mpr ⟨i, hi, hs⟩

private theorem disjointUnionComplex_space {ι E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : ι → Geometry.SimplicialComplex ℝ E)
    (hdis : Pairwise fun i j => Disjoint (C i).space (C j).space) (I : Set ι) :
    (disjointUnionComplex C hdis I).space = ⋃ i ∈ I, (C i).space := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := (disjointUnionComplex C hdis I).mem_space_iff.mp hx
    obtain ⟨i, hi, hsi⟩ := (mem_disjointUnionComplex_faces_iff.mp hs)
    exact Set.mem_iUnion₂.mpr ⟨i, hi, (C i).convexHull_subset_space hsi hxs⟩
  · intro hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨s, hsi, hxs⟩ := (C i).mem_space_iff.mp hxi
    exact (disjointUnionComplex C hdis I).convexHull_subset_space
      (mem_disjointUnionComplex_faces_iff.mpr ⟨i, hi, hsi⟩) hxs

private theorem disjointUnionComplex_faces_finite {ι E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {C : ι → Geometry.SimplicialComplex ℝ E}
    {hdis : Pairwise fun i j => Disjoint (C i).space (C j).space} {I : Set ι}
    (hI : I.Finite) (hC : ∀ i, (C i).faces.Finite) :
    (disjointUnionComplex C hdis I).faces.Finite := by
  change (⋃ i ∈ I, (C i).faces).Finite
  exact hI.biUnion fun i _ => hC i

private theorem index_eq_of_mem_faces_of_pairwise_disjoint {ι E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : ι → Geometry.SimplicialComplex ℝ E}
    (hdis : Pairwise fun i j => Disjoint (C i).space (C j).space)
    {i j : ι} {s : Finset E} (hsi : s ∈ (C i).faces) (hsj : s ∈ (C j).faces) : i = j := by
  by_contra hij
  obtain ⟨v, hv⟩ := (C i).nonempty_of_mem_faces hsi
  exact Set.disjoint_left.mp (hdis hij)
    ((C i).subset_space hsi hv) ((C j).subset_space hsj hv)

private theorem index_eq_of_comparable_faces_of_pairwise_disjoint {ι E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : ι → Geometry.SimplicialComplex ℝ E}
    (hdis : Pairwise fun i j => Disjoint (C i).space (C j).space)
    {i j : ι} {s t : Finset E} (hsi : s ∈ (C i).faces) (htj : t ∈ (C j).faces)
    (hcomp : s ⊆ t ∨ t ⊆ s) : i = j := by
  by_contra hij
  rcases hcomp with hst | hts
  · obtain ⟨v, hv⟩ := (C i).nonempty_of_mem_faces hsi
    exact Set.disjoint_left.mp (hdis hij)
      ((C i).subset_space hsi hv) ((C j).subset_space htj (hst hv))
  · obtain ⟨v, hv⟩ := (C j).nonempty_of_mem_faces htj
    exact Set.disjoint_left.mp (hdis hij)
      ((C i).subset_space hsi (hts hv)) ((C j).subset_space htj hv)

private theorem exists_component_of_flag_of_mem_iff {ι E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : ι → Geometry.SimplicialComplex ℝ E}
    (hdis : Pairwise fun i j => Disjoint (C i).space (C j).space) {I : Set ι}
    {K : Geometry.SimplicialComplex ℝ E}
    (hmem : ∀ {s : Finset E}, s ∈ K.faces ↔ ∃ i ∈ I, s ∈ (C i).faces)
    {d : Finset (Finset E)} (hd : IsFlag K d) (hne : d.Nonempty) :
    ∃ i ∈ I, IsFlag (C i) d := by
  obtain ⟨s₀, hs₀⟩ := hne
  obtain ⟨i, hi, hs₀i⟩ := hmem.mp (hd.mem_faces hs₀)
  refine ⟨i, hi, ⟨fun s hs => ?_, fun s hs t ht => hd.subset_or_subset hs ht⟩⟩
  obtain ⟨j, -, hsj⟩ := hmem.mp (hd.mem_faces hs)
  have hji := index_eq_of_comparable_faces_of_pairwise_disjoint hdis hsj hs₀i
    (hd.subset_or_subset hs hs₀)
  simpa only [hji] using hsj

open Classical in
private theorem mem_barycentricSubdivision_disjointUnionComplex_faces_iff
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : ι → Geometry.SimplicialComplex ℝ E}
    {hdis : Pairwise fun i j => Disjoint (C i).space (C j).space} {I : Set ι}
    {s : Finset E} :
    s ∈ (barycentricSubdivision (disjointUnionComplex C hdis I)).faces ↔
      ∃ i ∈ I, s ∈ (barycentricSubdivision (C i)).faces := by
  constructor
  · rintro ⟨d, hd, hne, rfl⟩
    obtain ⟨i, hi, hdi⟩ := exists_component_of_flag_of_mem_iff hdis
      (fun {_} => mem_disjointUnionComplex_faces_iff) hd hne
    exact ⟨i, hi, d, hdi, hne, rfl⟩
  · rintro ⟨i, hi, d, hd, hne, rfl⟩
    refine ⟨d, hd.of_le ?_, hne, rfl⟩
    intro t ht
    exact mem_disjointUnionComplex_faces_iff.mpr ⟨i, hi, ht⟩

open Classical in
private theorem derivedNeighborhood_disjointUnionComplex_faces
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C H : ι → Geometry.SimplicialComplex ℝ E}
    {hdis : Pairwise fun i j => Disjoint (C i).space (C j).space}
    (hHC : ∀ i, (H i).faces ⊆ (C i).faces) (I : Set ι) :
    (derivedNeighborhood (disjointUnionComplex C hdis I)
      (disjointUnionComplex H (fun i j hij =>
        (hdis hij).mono (space_mono_of_faces_subset (hHC i))
          (space_mono_of_faces_subset (hHC j))) I)).faces =
      ⋃ i ∈ I, (derivedNeighborhood (C i) (H i)).faces := by
  let hdisH : Pairwise fun i j => Disjoint (H i).space (H j).space :=
    fun i j hij => (hdis hij).mono (space_mono_of_faces_subset (hHC i))
      (space_mono_of_faces_subset (hHC j))
  let hdisB : Pairwise fun i j =>
      Disjoint (barycentricSubdivision (C i)).space
        (barycentricSubdivision (C j)).space := by
    intro i j hij
    rw [(barycentricSubdivision_isSubdivision (C i)).space_eq,
      (barycentricSubdivision_isSubdivision (C j)).space_eq]
    exact hdis hij
  ext u
  constructor
  · rintro ⟨D, hD, hne, hmeet, rfl⟩
    obtain ⟨i, hi, hDi⟩ := exists_component_of_flag_of_mem_iff hdisB
      (fun {_} => mem_barycentricSubdivision_disjointUnionComplex_faces_iff) hD hne
    apply Set.mem_iUnion₂.mpr
    refine ⟨i, hi, D, hDi, hne, ?_, rfl⟩
    intro e he
    obtain ⟨σ, hσ, hcentroid⟩ := hmeet e he
    obtain ⟨j, -, hσj⟩ := (mem_disjointUnionComplex_faces_iff
      (C := H) (hdis := hdisH)).mp hσ
    have hcentroidCi : σ.centroid ℝ id ∈ (C i).space := by
      rw [← (barycentricSubdivision_isSubdivision (C i)).space_eq]
      exact (barycentricSubdivision (C i)).subset_space (hDi.mem_faces he) hcentroid
    have hcentroidCj : σ.centroid ℝ id ∈ (C j).space := by
      apply space_mono_of_faces_subset (hHC j)
      exact (H j).convexHull_subset_space hσj
        (openSimplex_subset_convexHull σ (centroid_mem_openSimplex_of_mem_faces (H j) σ hσj))
    have hji : j = i := by
      by_contra hneji
      exact Set.disjoint_left.mp (hdis hneji) hcentroidCj hcentroidCi
    exact ⟨σ, hji ▸ hσj, hcentroid⟩
  · intro hu
    obtain ⟨i, hi, hui⟩ := Set.mem_iUnion₂.mp hu
    obtain ⟨D, hD, hne, hmeet, rfl⟩ := hui
    refine ⟨D, hD.of_le ?_, hne, ?_, rfl⟩
    · exact barycentricSubdivision_faces_subset fun t ht =>
        mem_disjointUnionComplex_faces_iff.mpr ⟨i, hi, ht⟩
    · intro e he
      obtain ⟨σ, hσ, hcentroid⟩ := hmeet e he
      exact ⟨σ, mem_disjointUnionComplex_faces_iff.mpr ⟨i, hi, hσ⟩, hcentroid⟩

open Classical in
private theorem derivedNeighborhood_disjointUnionComplex_space
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C H : ι → Geometry.SimplicialComplex ℝ E}
    {hdis : Pairwise fun i j => Disjoint (C i).space (C j).space}
    (hHC : ∀ i, (H i).faces ⊆ (C i).faces) (I : Set ι) :
    (derivedNeighborhood (disjointUnionComplex C hdis I)
      (disjointUnionComplex H (fun i j hij =>
        (hdis hij).mono (space_mono_of_faces_subset (hHC i))
          (space_mono_of_faces_subset (hHC j))) I)).space =
      ⋃ i ∈ I, (derivedNeighborhood (C i) (H i)).space := by
  let D : ι → Geometry.SimplicialComplex ℝ E := fun i => derivedNeighborhood (C i) (H i)
  let hdisD : Pairwise fun i j => Disjoint (D i).space (D j).space :=
    fun i j hij => (hdis hij).mono
      (derivedNeighborhood_space_subset (C i) (H i))
      (derivedNeighborhood_space_subset (C j) (H j))
  have heq : derivedNeighborhood (disjointUnionComplex C hdis I)
      (disjointUnionComplex H (fun i j hij =>
        (hdis hij).mono (space_mono_of_faces_subset (hHC i))
          (space_mono_of_faces_subset (hHC j))) I) =
      disjointUnionComplex D hdisD I := by
    ext s
    rw [derivedNeighborhood_disjointUnionComplex_faces hHC I]
    change s ∈ ⋃ i ∈ I, (D i).faces ↔ s ∈ (disjointUnionComplex D hdisD I).faces
    constructor
    · intro hs
      obtain ⟨i, hi, hsi⟩ := Set.mem_iUnion₂.mp hs
      exact mem_disjointUnionComplex_faces_iff.mpr ⟨i, hi, hsi⟩
    · intro hs
      obtain ⟨i, hi, hsi⟩ := mem_disjointUnionComplex_faces_iff.mp hs
      exact Set.mem_iUnion₂.mpr ⟨i, hi, hsi⟩
  rw [heq, disjointUnionComplex_space]

private theorem locallyFinite_faces_disjointUnionComplex_univ
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : ι → Geometry.SimplicialComplex ℝ E}
    {hdis : Pairwise fun i j => Disjoint (C i).space (C j).space}
    (hloc : LocallyFinite fun i => (C i).space) (hfin : ∀ i, (C i).faces.Finite) :
    LocallyFinite (fun s : (disjointUnionComplex C hdis Set.univ).faces =>
      (Subtype.val : (disjointUnionComplex C hdis Set.univ).space → E) ⁻¹'
        convexHull ℝ ((s : Finset E) : Set E)) := by
  let J := disjointUnionComplex C hdis Set.univ
  have hloc' : LocallyFinite (fun i =>
      (Subtype.val : J.space → E) ⁻¹' (C i).space) :=
    hloc.preimage_continuous continuous_subtype_val
  intro x
  obtain ⟨U, hUx, hactive⟩ := hloc' x
  refine ⟨U, hUx, ?_⟩
  let active : Set ι := {i | (((Subtype.val : J.space → E) ⁻¹' (C i).space) ∩ U).Nonempty}
  have hactive' : active.Finite := hactive
  have hface (i : ι) : {s : J.faces | (s : Finset E) ∈ (C i).faces}.Finite :=
    (hfin i).preimage Subtype.val_injective.injOn
  apply (hactive'.biUnion fun i _ => hface i).subset
  intro s hs
  obtain ⟨y, hyface, hyU⟩ := hs
  obtain ⟨i, -, hsi⟩ := mem_disjointUnionComplex_faces_iff.mp s.2
  have hi : i ∈ active := by
    exact ⟨y, (C i).convexHull_subset_space hsi hyface, hyU⟩
  exact Set.mem_iUnion₂.mpr ⟨i, hi, hsi⟩

open Classical in
noncomputable def euclideanLocallyFinitePLPieceIn {m : ℕ}
    (J : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m)))
    (hloc : LocallyFinite (fun s : J.faces =>
      (Subtype.val : J.space → EuclideanSpace ℝ (Fin m)) ⁻¹'
        convexHull ℝ ((s : Finset (EuclideanSpace ℝ (Fin m))) :
          Set (EuclideanSpace ℝ (Fin m))))) :
    LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin m)) m
      (EuclideanSpace ℝ (Fin m)) J.space := by
  have hpa : IsPiecewiseAffineOn
      (id : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) J.space :=
    (isLocallyPolyhedral_space_of_locallyFinite J hloc).isPiecewiseAffineOn_id
  have hinv : IsPiecewiseAffineOn (Function.invFunOn id J.space) J.space :=
    hpa.congr fun y hy => (bijOn_id J.space).invOn_invFunOn.1 hy
  exact
    { complex := J
      locallyFinite := hloc
      map := id
      bijOn := bijOn_id J.space
      continuousOn := continuous_id.continuousOn
      isEmbedding := Topology.IsEmbedding.subtypeVal
      isPiecewiseAffineOn_chart := fun e he => by
        rw [chartedSpaceSelf_atlas] at he
        subst e
        simpa using hpa
      isPiecewiseAffineOn_chart_symm := fun e he => by
        rw [chartedSpaceSelf_atlas] at he
        subst e
        simpa using hinv }

open Classical in
private theorem geometricLink_disjointUnionComplex {ι E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {C : ι → Geometry.SimplicialComplex ℝ E}
    {hdis : Pairwise fun i j => Disjoint (C i).space (C j).space}
    {I : Set ι} {i : ι} (hi : i ∈ I) {v : E} (hvi : {v} ∈ (C i).faces) :
    SimplicialComplex.geometricLink (disjointUnionComplex C hdis I) {v} =
      SimplicialComplex.geometricLink (C i) {v} := by
  ext t
  simp only [SimplicialComplex.mem_geometricLink_singleton]
  constructor
  · rintro ⟨hne, hvt, ht⟩
    obtain ⟨j, -, htj⟩ := mem_disjointUnionComplex_faces_iff.mp ht
    have hvj : {v} ∈ (C j).faces :=
      (C j).down_closed htj (by simp) (Finset.singleton_nonempty v)
    have hji := index_eq_of_mem_faces_of_pairwise_disjoint hdis hvj hvi
    subst j
    exact ⟨hne, hvt, htj⟩
  · rintro ⟨hne, hvt, ht⟩
    exact ⟨hne, hvt, mem_disjointUnionComplex_faces_iff.mpr ⟨i, hi, ht⟩⟩

open Classical in
private theorem isCombinatorialManifoldWithBoundary_three_disjointUnionComplex
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : ι → Geometry.SimplicialComplex ℝ E}
    {hdis : Pairwise fun i j => Disjoint (C i).space (C j).space} {I : Set ι}
    (hC : ∀ i, IsCombinatorialManifoldWithBoundary 3 (C i)) :
    IsCombinatorialManifoldWithBoundary 3 (disjointUnionComplex C hdis I) := by
  intro v hv
  obtain ⟨i, hi, hvi⟩ := mem_disjointUnionComplex_faces_iff.mp hv
  rw [geometricLink_disjointUnionComplex hi hvi]
  exact hC i v hvi

open Classical in
private theorem isCombinatorialManifold_three_disjointUnionComplex
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : ι → Geometry.SimplicialComplex ℝ E}
    {hdis : Pairwise fun i j => Disjoint (C i).space (C j).space} {I : Set ι}
    (hC : ∀ i, IsCombinatorialManifold 3 (C i)) :
    IsCombinatorialManifold 3 (disjointUnionComplex C hdis I) := by
  intro v hv
  obtain ⟨i, hi, hvi⟩ := mem_disjointUnionComplex_faces_iff.mp hv
  rw [geometricLink_disjointUnionComplex hi hvi]
  exact hC i v hvi

open Classical in
private theorem exists_translated_arc_component_family :
    ∃ (C H : ℤ → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (w : ℤ → EuclideanSpace ℝ (Fin 3)) (S : ℝ)
      (p q : EuclideanSpace ℝ (Fin 3)),
      0 < S ∧
      (∀ z, (C z).faces.Finite) ∧
      (∀ z, (H z).faces.Finite) ∧
      (∀ z, (H z).faces ⊆ (C z).faces) ∧
      (∀ z s, s ∈ (H z).faces → s.card ≤ 2) ∧
      (∀ z, IsCombinatorialManifoldWithBoundary 3 (C z)) ∧
      Pairwise (fun z z' => Disjoint (C z).space (C z').space) ∧
      LocallyFinite (fun z => (C z).space) ∧
      (∀ z, w z ∈ (H z).space) ∧
      (∀ z, (w z) 0 = (w 0) 0 + (z : ℝ) * S) ∧
      p ≠ q ∧ ({p, q} : Finset (EuclideanSpace ℝ (Fin 3))) ∈ (H 0).faces := by
  let E := EuclideanSpace ℝ (Fin 3)
  obtain ⟨B, v, hBfin, hB, hvert, hedge, hinj, -⟩ :=
    exists_simplicialArc_one_with_all_faces_interior (E := E)
      (by simp only [E, finrank_euclideanSpace, Fintype.card_fin])
  let _ : Finite B.faces := hBfin.to_subtype
  let G := arcComplexIn B v 1
  have hGB : G.faces ⊆ B.faces := arcComplexIn_faces_subset B v 1
  have hGfin : G.faces.Finite := hBfin.subset hGB
  let _ : Finite G.faces := hGfin.to_subtype
  have hGcard : ∀ s ∈ G.faces, s.card ≤ 2 := by
    rintro s ⟨-, j, -, rfl⟩
    exact arcChainFace_card_le_two v j
  have hedgeG : ({v 0, v 1} : Finset E) ∈ G.faces := by
    change ({v 0, v 1} : Finset E) ∈ (arcComplexIn B v 1).faces
    have h := arcChainFace_mem_arcComplexIn_faces hvert hedge (j := 1) (by omega)
    convert h using 1
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton, mem_arcChainFace_iff]
  have hv0G : v 0 ∈ G.space :=
    G.subset_space hedgeG (Finset.mem_insert_self (v 0) {v 1})
  have hpq : v 0 ≠ v 1 := by
    intro h
    have := hinj 0 (by omega) 1 (by omega) h
    omega
  obtain ⟨R, hR, hBR⟩ :=
    (isPolyhedron_space B).isCompact.isBounded.subset_closedBall_lt 0 (0 : E)
  let S : ℝ := 2 * R + 1
  have hS : 0 < S := by
    dsimp only [S]
    linarith
  let shift : ℤ → E ≃ᵃ[ℝ] E := fun z =>
    AffineEquiv.constVAdd ℝ E (EuclideanSpace.single (0 : Fin 3) ((z : ℝ) * S))
  let C : ℤ → Geometry.SimplicialComplex ℝ E := fun z => affineImage B (shift z)
  let H : ℤ → Geometry.SimplicialComplex ℝ E := fun z => affineImage G (shift z)
  let w : ℤ → E := fun z => shift z (v 0)
  let p : E := shift 0 (v 0)
  let q : E := shift 0 (v 1)
  have hCfin (z : ℤ) : (C z).faces.Finite := by
    exact affineImage_faces_finite B (shift z)
  have hHfin (z : ℤ) : (H z).faces.Finite := by
    exact affineImage_faces_finite G (shift z)
  have hHC (z : ℤ) : (H z).faces ⊆ (C z).faces := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := (mem_affineImage_faces_iff G (shift z)).mp ht
    exact (mem_affineImage_faces_iff B (shift z)).mpr ⟨s, hGB hs, rfl⟩
  have hHcard (z : ℤ) (s : Finset E) (hs : s ∈ (H z).faces) : s.card ≤ 2 := by
    obtain ⟨t, ht, hst⟩ := (mem_affineImage_faces_iff G (shift z)).mp hs
    have hcard := congrArg Finset.card hst
    rw [hcard]
    exact le_trans
      (@Finset.card_image_le E E t (shift z) (fun a b => Classical.propDecidable (a = b)))
      (hGcard t ht)
  have hCman (z : ℤ) : IsCombinatorialManifoldWithBoundary 3 (C z) := by
    let _ : Finite (C z).faces := (hCfin z).to_subtype
    exact hB.of_isPLHomeomorphOn (isPLHomeomorphOn_affineImage B (shift z))
  have hCcoord (z : ℤ) {x : E} (hx : x ∈ (C z).space) :
      x 0 ∈ Set.Icc ((z : ℝ) * S - R) ((z : ℝ) * S + R) := by
    change x ∈ (affineImage B (shift z)).space at hx
    rw [affineImage_space] at hx
    obtain ⟨y, hyB, rfl⟩ := hx
    have hynorm : ‖y‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hBR hyB
    have hycoord : |y 0| ≤ ‖y‖ := by
      simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le y (0 : Fin 3))
    simp only [shift, AffineEquiv.constVAdd_apply, vadd_eq_add]
    rw [PiLp.add_apply, PiLp.single_eq_same]
    constructor <;> nlinarith [abs_le.mp hycoord |>.1, abs_le.mp hycoord |>.2]
  have hCdis : Pairwise (fun z z' => Disjoint (C z).space (C z').space) := by
    intro z z' hzz'
    apply Set.disjoint_left.mpr
    intro x hxz hxz'
    have hz := hCcoord z hxz
    have hz' := hCcoord z' hxz'
    rcases lt_or_gt_of_ne hzz' with hlt | hgt
    · have hcast : (z : ℝ) + 1 ≤ (z' : ℝ) := by
        exact_mod_cast (Int.add_one_le_iff.mpr hlt)
      have hmul := mul_le_mul_of_nonneg_right hcast hS.le
      dsimp only [S] at hmul
      nlinarith [hz.2, hz'.1]
    · have hcast : (z' : ℝ) + 1 ≤ (z : ℝ) := by
        exact_mod_cast (Int.add_one_le_iff.mpr hgt)
      have hmul := mul_le_mul_of_nonneg_right hcast hS.le
      dsimp only [S] at hmul
      nlinarith [hz.1, hz'.2]
  have hintervals : LocallyFinite
      (fun z : ℤ => Set.Icc ((z : ℝ) * S - R) ((z : ℝ) * S + R)) := by
    have htop : Filter.Tendsto (fun z : ℤ => (z : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_intCast_atTop_atTop
    have hbot : Filter.Tendsto (fun z : ℤ => (z : ℝ)) Filter.atBot Filter.atBot :=
      tendsto_intCast_atBot_iff.mpr Filter.tendsto_id
    apply locallyFinite_Icc_of_tendsto
    · simpa only [sub_eq_add_neg] using
        Filter.tendsto_atTop_add_const_right Filter.atTop (-R) (htop.atTop_mul_const hS)
    · exact Filter.tendsto_atBot_add_const_right Filter.atBot R (hbot.atBot_mul_const hS)
  have hCsucc : LocallyFinite (fun z => (C z).space) := by
    have hpre := hintervals.preimage_continuous
      (EuclideanSpace.proj (0 : Fin 3)).continuous
    exact hpre.subset fun z x hx => hCcoord z hx
  have hw (z : ℤ) : w z ∈ (H z).space := by
    change w z ∈ (affineImage G (shift z)).space
    rw [affineImage_space]
    exact ⟨v 0, hv0G, rfl⟩
  have hwcoord (z : ℤ) : (w z) 0 = (w 0) 0 + (z : ℝ) * S := by
    simp only [w, shift, AffineEquiv.constVAdd_apply, vadd_eq_add]
    rw [PiLp.add_apply, PiLp.single_eq_same, PiLp.add_apply, PiLp.single_eq_same]
    norm_num
    ring
  have hpq' : p ≠ q := by
    exact (shift 0).injective.ne hpq
  have hedgeH : ({p, q} : Finset E) ∈ (H 0).faces := by
    apply (mem_affineImage_faces_iff G (shift 0)).mpr
    refine ⟨{v 0, v 1}, hedgeG, ?_⟩
    apply Finset.ext
    intro x
    simp only [p, q, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨v 0, Or.inl rfl, rfl⟩
      · exact ⟨v 1, Or.inr rfl, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      rcases ha with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
  exact ⟨C, H, w, S, p, q, hS, hCfin, hHfin, hHC, hHcard, hCman,
    hCdis, hCsucc, hw, hwcoord, hpq', hedgeH⟩

open Classical in
theorem exists_noncompact_locallyFinite_simplicialComplex_three_with_edge :
    ∃ J : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      LocallyFinite (fun s : J.faces =>
        (Subtype.val : J.space → EuclideanSpace ℝ (Fin 3)) ⁻¹'
          convexHull ℝ ((s : Finset (EuclideanSpace ℝ (Fin 3))) :
            Set (EuclideanSpace ℝ (Fin 3)))) ∧
      ¬ IsCompact J.space ∧
      ∃ e ∈ J.faces, e.card = 2 := by
  let E := EuclideanSpace ℝ (Fin 3)
  obtain ⟨C, H, w, S, p, q, hS, hCfin, -, hHC, -, -, hCdis,
    hCloc, hw, hwcoord, hpq, hedge⟩ := exists_translated_arc_component_family
  let J : Geometry.SimplicialComplex ℝ E :=
    disjointUnionComplex C hCdis Set.univ
  have hJlocal : LocallyFinite (fun s : J.faces =>
      (Subtype.val : J.space → E) ⁻¹'
        convexHull ℝ ((s : Finset E) : Set E)) := by
    simpa only [J] using
      (locallyFinite_faces_disjointUnionComplex_univ
        (C := C) (hdis := hCdis) hCloc hCfin)
  have hwJ (z : ℤ) : w z ∈ J.space := by
    rw [disjointUnionComplex_space C hCdis Set.univ]
    exact Set.mem_iUnion₂.mpr
      ⟨z, Set.mem_univ z, space_mono_of_faces_subset (hHC z) (hw z)⟩
  have hJnoncompact : ¬ IsCompact J.space := by
    intro hcompact
    obtain ⟨R, hJR⟩ := hcompact.isBounded.subset_closedBall (0 : E)
    obtain ⟨i, hi⟩ := exists_nat_gt ((R - (w 0) 0) / S)
    have hmul : R - (w 0) 0 < (i : ℝ) * S := (div_lt_iff₀ hS).mp hi
    have hlarge : R < (w (i : ℤ)) 0 := by
      rw [hwcoord]
      norm_num
      linarith
    have hball := hJR (hwJ (i : ℤ))
    have hnorm : ‖w (i : ℤ)‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hball
    have habs : |(w (i : ℤ)) 0| ≤ ‖w (i : ℤ)‖ := by
      simpa only [Real.norm_eq_abs] using
        (PiLp.norm_apply_le (w (i : ℤ)) (0 : Fin 3))
    have hcoord : (w (i : ℤ)) 0 ≤ ‖w (i : ℤ)‖ :=
      (le_abs_self _).trans habs
    linarith
  have hedgeJ : ({p, q} : Finset E) ∈ J.faces :=
    mem_disjointUnionComplex_faces_iff.mpr
      ⟨0, Set.mem_univ 0, hHC 0 hedge⟩
  exact ⟨J, hJlocal, hJnoncompact, {p, q}, hedgeJ, Finset.card_pair hpq⟩

open Classical in
theorem exists_noncompact_locallyFinite_combinatorialManifold_three_with_edge :
    ∃ J : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 4)),
      LocallyFinite (fun s : J.faces =>
        (Subtype.val : J.space → EuclideanSpace ℝ (Fin 4)) ⁻¹'
          convexHull ℝ ((s : Finset (EuclideanSpace ℝ (Fin 4))) :
            Set (EuclideanSpace ℝ (Fin 4)))) ∧
      ¬ IsCompact J.space ∧ IsCombinatorialManifold 3 J ∧
      ∃ e ∈ J.faces, e.card = 2 := by
  let E := EuclideanSpace ℝ (Fin 4)
  obtain ⟨T, hT, hTcard, -, -, -⟩ :=
    exists_affineIndependent_openSimplex_subset (E := E) (n := 3)
      (by simp [E]) (0 : E) Filter.univ_mem
  let B := simplexBoundary T hT
  have hBfin : B.faces.Finite := simplexBoundary_faces_finite T hT
  let _ : Finite B.faces := hBfin.to_subtype
  have hBsphere : IsPLSphere 3 B.space := by
    rw [simplexBoundary_space T hT (by omega)]
    exact isPLSphere_biUnion_erase T hT hTcard
  have hBman : IsCombinatorialManifold 3 B := hBsphere.isCombinatorialManifold
  obtain ⟨p, hpT⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  have hTerase : (T.erase p).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hpT, hTcard]
    omega
  obtain ⟨q, hqerase⟩ := hTerase
  have hqp : q ≠ p := (Finset.mem_erase.mp hqerase).1
  have hqT : q ∈ T := (Finset.mem_erase.mp hqerase).2
  have hpq : p ≠ q := hqp.symm
  have hedgeB : ({p, q} : Finset E) ∈ B.faces := by
    apply mem_simplexBoundary_faces_iff.mpr
    refine ⟨?_, Finset.insert_nonempty _ _, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hpT
      · exact hqT
    · intro heq
      have hc := congrArg Finset.card heq
      rw [Finset.card_pair hpq, hTcard] at hc
      omega
  obtain ⟨R, hR, hBR⟩ :=
    (isPolyhedron_space B).isCompact.isBounded.subset_closedBall_lt 0 (0 : E)
  let S : ℝ := 2 * R + 1
  have hS : 0 < S := by
    dsimp only [S]
    linarith
  let shift : ℤ → E ≃ᵃ[ℝ] E := fun z =>
    AffineEquiv.constVAdd ℝ E (EuclideanSpace.single (0 : Fin 4) ((z : ℝ) * S))
  let C : ℤ → Geometry.SimplicialComplex ℝ E := fun z => affineImage B (shift z)
  let w : ℤ → E := fun z => shift z p
  have hCfin (z : ℤ) : (C z).faces.Finite := affineImage_faces_finite B (shift z)
  have hCman (z : ℤ) : IsCombinatorialManifold 3 (C z) := by
    let _ : Finite (C z).faces := (hCfin z).to_subtype
    exact hBman.of_isPLHomeomorphOn (isPLHomeomorphOn_affineImage B (shift z))
  have hCcoord (z : ℤ) {x : E} (hx : x ∈ (C z).space) :
      x 0 ∈ Set.Icc ((z : ℝ) * S - R) ((z : ℝ) * S + R) := by
    change x ∈ (affineImage B (shift z)).space at hx
    rw [affineImage_space] at hx
    obtain ⟨y, hyB, rfl⟩ := hx
    have hynorm : ‖y‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hBR hyB
    have hycoord : |y 0| ≤ ‖y‖ := by
      simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le y (0 : Fin 4))
    simp only [shift, AffineEquiv.constVAdd_apply, vadd_eq_add]
    rw [PiLp.add_apply, PiLp.single_eq_same]
    constructor <;> nlinarith [abs_le.mp hycoord |>.1, abs_le.mp hycoord |>.2]
  have hCdis : Pairwise (fun z z' => Disjoint (C z).space (C z').space) := by
    intro z z' hzz'
    apply Set.disjoint_left.mpr
    intro x hxz hxz'
    have hz := hCcoord z hxz
    have hz' := hCcoord z' hxz'
    rcases lt_or_gt_of_ne hzz' with hlt | hgt
    · have hcast : (z : ℝ) + 1 ≤ (z' : ℝ) := by
        exact_mod_cast (Int.add_one_le_iff.mpr hlt)
      have hmul := mul_le_mul_of_nonneg_right hcast hS.le
      dsimp only [S] at hmul
      nlinarith [hz.2, hz'.1]
    · have hcast : (z' : ℝ) + 1 ≤ (z : ℝ) := by
        exact_mod_cast (Int.add_one_le_iff.mpr hgt)
      have hmul := mul_le_mul_of_nonneg_right hcast hS.le
      dsimp only [S] at hmul
      nlinarith [hz.1, hz'.2]
  have hintervals : LocallyFinite
      (fun z : ℤ => Set.Icc ((z : ℝ) * S - R) ((z : ℝ) * S + R)) := by
    have htop : Filter.Tendsto (fun z : ℤ => (z : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_intCast_atTop_atTop
    have hbot : Filter.Tendsto (fun z : ℤ => (z : ℝ)) Filter.atBot Filter.atBot :=
      tendsto_intCast_atBot_iff.mpr Filter.tendsto_id
    apply locallyFinite_Icc_of_tendsto
    · simpa only [sub_eq_add_neg] using
        Filter.tendsto_atTop_add_const_right Filter.atTop (-R) (htop.atTop_mul_const hS)
    · exact Filter.tendsto_atBot_add_const_right Filter.atBot R (hbot.atBot_mul_const hS)
  have hCloc : LocallyFinite (fun z => (C z).space) := by
    have hpre := hintervals.preimage_continuous
      (EuclideanSpace.proj (0 : Fin 4)).continuous
    exact hpre.subset fun z x hx => hCcoord z hx
  have hw (z : ℤ) : w z ∈ (C z).space := by
    change shift z p ∈ (affineImage B (shift z)).space
    rw [affineImage_space]
    exact ⟨p, B.subset_space hedgeB (Finset.mem_insert_self p {q}), rfl⟩
  have hwcoord (z : ℤ) : (w z) 0 = (w 0) 0 + (z : ℝ) * S := by
    simp only [w, shift, AffineEquiv.constVAdd_apply, vadd_eq_add]
    rw [PiLp.add_apply, PiLp.single_eq_same, PiLp.add_apply, PiLp.single_eq_same]
    norm_num
    ring
  let J : Geometry.SimplicialComplex ℝ E := disjointUnionComplex C hCdis Set.univ
  have hJlocal : LocallyFinite (fun s : J.faces =>
      (Subtype.val : J.space → E) ⁻¹' convexHull ℝ ((s : Finset E) : Set E)) := by
    simpa only [J] using
      (locallyFinite_faces_disjointUnionComplex_univ
        (C := C) (hdis := hCdis) hCloc hCfin)
  have hwJ (z : ℤ) : w z ∈ J.space := by
    rw [disjointUnionComplex_space C hCdis Set.univ]
    exact Set.mem_iUnion₂.mpr ⟨z, Set.mem_univ z, hw z⟩
  have hJnoncompact : ¬ IsCompact J.space := by
    intro hcompact
    obtain ⟨A, hJA⟩ := hcompact.isBounded.subset_closedBall (0 : E)
    obtain ⟨i, hi⟩ := exists_nat_gt ((A - (w 0) 0) / S)
    have hmul : A - (w 0) 0 < (i : ℝ) * S := (div_lt_iff₀ hS).mp hi
    have hlarge : A < (w (i : ℤ)) 0 := by
      rw [hwcoord]
      norm_num
      linarith
    have hball := hJA (hwJ (i : ℤ))
    have hnorm : ‖w (i : ℤ)‖ ≤ A := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hball
    have habs : |(w (i : ℤ)) 0| ≤ ‖w (i : ℤ)‖ := by
      simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le (w (i : ℤ)) (0 : Fin 4))
    have hcoord : (w (i : ℤ)) 0 ≤ ‖w (i : ℤ)‖ := (le_abs_self _).trans habs
    linarith
  let p₀ := shift 0 p
  let q₀ := shift 0 q
  have hpq₀ : p₀ ≠ q₀ := (shift 0).injective.ne hpq
  have hedgeC : ({p₀, q₀} : Finset E) ∈ (C 0).faces := by
    apply (mem_affineImage_faces_iff B (shift 0)).mpr
    refine ⟨{p, q}, hedgeB, ?_⟩
    ext x
    simp [p₀, q₀]
  have hedgeJ : ({p₀, q₀} : Finset E) ∈ J.faces :=
    mem_disjointUnionComplex_faces_iff.mpr ⟨0, Set.mem_univ 0, hedgeC⟩
  exact ⟨J, hJlocal, hJnoncompact,
    isCombinatorialManifold_three_disjointUnionComplex hCman,
    {p₀, q₀}, hedgeJ, Finset.card_pair hpq₀⟩

private def symmetricIntegerInterval (i : ℕ) : Set ℤ :=
  Set.Icc (-(i : ℤ)) (i : ℤ)

private theorem symmetricIntegerInterval_finite (i : ℕ) :
    (symmetricIntegerInterval i).Finite :=
  Set.finite_Icc (-(i : ℤ)) (i : ℤ)

private theorem monotone_symmetricIntegerInterval : Monotone symmetricIntegerInterval := by
  intro i j hij z hz
  change -(i : ℤ) ≤ z ∧ z ≤ (i : ℤ) at hz
  change -(j : ℤ) ≤ z ∧ z ≤ (j : ℤ)
  have hij' : (i : ℤ) ≤ (j : ℤ) := by exact_mod_cast hij
  constructor <;> omega

private theorem exists_mem_symmetricIntegerInterval (z : ℤ) :
    ∃ i, z ∈ symmetricIntegerInterval i := by
  cases z with
  | ofNat i =>
      refine ⟨i, ?_⟩
      change -Int.ofNat i ≤ Int.ofNat i ∧ Int.ofNat i ≤ Int.ofNat i
      rw [Int.ofNat_eq_natCast]
      omega
  | negSucc i =>
      refine ⟨i + 1, ?_⟩
      change -Int.ofNat (i + 1) ≤ Int.negSucc i ∧ Int.negSucc i ≤ Int.ofNat (i + 1)
      rw [Int.negSucc_eq, Int.ofNat_eq_natCast]
      omega

open Classical in
theorem exists_noncompact_isPLDerivedNeighborhoodExhaustion_three_with_edge :
    ∃ N K U : Set (EuclideanSpace ℝ (Fin 3)),
      IsPLDerivedNeighborhoodExhaustion (n := 3) N K U ∧
      ¬ IsCompact N ∧
      (∃ p q, p ≠ q ∧ segment ℝ p q ⊆ K) ∧
      Nonempty (StrongDeformationRetract {x : N | (x : EuclideanSpace ℝ (Fin 3)) ∈ K}) := by
  let E := EuclideanSpace ℝ (Fin 3)
  let _ : DecidableEq E := Classical.decEq E
  obtain ⟨C, H, w, S, p, q, hS, hCfin, hHfin, hHC, hHcard, hCman,
    hCdis, hCloc, hw, hwcoord, hpq, hedge⟩ := exists_translated_arc_component_family
  have hHdis : Pairwise (fun z z' => Disjoint (H z).space (H z').space) :=
    fun z z' hzz' => (hCdis hzz').mono
      (space_mono_of_faces_subset (hHC z)) (space_mono_of_faces_subset (hHC z'))
  let A : ℕ → Geometry.SimplicialComplex ℝ E := fun i =>
    disjointUnionComplex C hCdis (symmetricIntegerInterval i)
  let L : ℕ → Geometry.SimplicialComplex ℝ E := fun i =>
    disjointUnionComplex H hHdis (symmetricIntegerInterval i)
  let J : Geometry.SimplicialComplex ℝ E :=
    disjointUnionComplex C hCdis Set.univ
  let D : ℤ → Geometry.SimplicialComplex ℝ E := fun z => derivedNeighborhood (C z) (H z)
  let N : Set E := derivedNeighborhoodExhaustionAmbient A L
  let K : Set E := ⋃ z, (H z).space
  let U : Set E := J.space
  have hAfinite (i : ℕ) : (A i).faces.Finite := by
    simpa only [A] using
      (disjointUnionComplex_faces_finite (C := C) (hdis := hCdis)
        (symmetricIntegerInterval_finite i) hCfin)
  have hLA (i : ℕ) : (L i).faces ⊆ (A i).faces := by
    intro s hs
    obtain ⟨z, hz, hsz⟩ := mem_disjointUnionComplex_faces_iff.mp hs
    exact mem_disjointUnionComplex_faces_iff.mpr ⟨z, hz, hHC z hsz⟩
  have hcard (i : ℕ) (s : Finset E) (hs : s ∈ (L i).faces) : s.card ≤ 2 := by
    obtain ⟨z, -, hsz⟩ := mem_disjointUnionComplex_faces_iff.mp hs
    exact hHcard z s hsz
  have hambient (i : ℕ) : IsCombinatorialManifoldWithBoundary 3 (A i) := by
    simpa only [A] using
      (isCombinatorialManifoldWithBoundary_three_disjointUnionComplex
        (C := C) (hdis := hCdis) hCman)
  have hderived (i : ℕ) : IsCombinatorialManifoldWithBoundary 3
      (derivedNeighborhood (A i) (L i)) := by
    let _ : Finite (A i).faces := (hAfinite i).to_subtype
    exact (hambient i).derivedNeighborhood (L i)
  have hAmono : Monotone (fun i => (A i).faces) := by
    intro i j hij s hs
    obtain ⟨z, hz, hsz⟩ := mem_disjointUnionComplex_faces_iff.mp hs
    exact mem_disjointUnionComplex_faces_iff.mpr
      ⟨z, monotone_symmetricIntegerInterval hij hz, hsz⟩
  have hLmono : Monotone (fun i => (L i).faces) := by
    intro i j hij s hs
    obtain ⟨z, hz, hsz⟩ := mem_disjointUnionComplex_faces_iff.mp hs
    exact mem_disjointUnionComplex_faces_iff.mpr
      ⟨z, monotone_symmetricIntegerInterval hij hz, hsz⟩
  have hrestrict : ∀ {i j}, i ≤ j → ∀ s ∈ (A i).faces,
      s ∈ (L j).faces → s ∈ (L i).faces := by
    intro i j hij s hsA hsL
    obtain ⟨z, hzi, hszC⟩ := mem_disjointUnionComplex_faces_iff.mp hsA
    obtain ⟨z', -, hsz'H⟩ := mem_disjointUnionComplex_faces_iff.mp hsL
    have hzz' : z = z' :=
      index_eq_of_mem_faces_of_pairwise_disjoint hCdis hszC (hHC z' hsz'H)
    subst z'
    exact mem_disjointUnionComplex_faces_iff.mpr ⟨z, hzi, hsz'H⟩
  have hDstage (i : ℕ) : (derivedNeighborhood (A i) (L i)).space =
      ⋃ z ∈ symmetricIntegerInterval i, (D z).space := by
    simpa only [A, L, D] using
      (derivedNeighborhood_disjointUnionComplex_space (C := C) (H := H)
        (hdis := hCdis) hHC (symmetricIntegerInterval i))
  have hDloc : LocallyFinite (fun z => (D z).space) :=
    hCloc.subset fun z => derivedNeighborhood_space_subset (C z) (H z)
  have hDclosed (z : ℤ) : IsClosed (D z).space := by
    let _ : Finite (C z).faces := (hCfin z).to_subtype
    let _ : Finite (D z).faces := (derivedNeighborhood_faces_finite (C z) (H z)).to_subtype
    exact (isPolyhedron_space (D z)).isClosed
  have hDdis : Pairwise (fun z z' => Disjoint (D z).space (D z').space) :=
    fun z z' hzz' => (hCdis hzz').mono
      (derivedNeighborhood_space_subset (C z) (H z))
      (derivedNeighborhood_space_subset (C z') (H z'))
  have hnhds (i : ℕ) {x : E} (hx : x ∈ (derivedNeighborhood (A i) (L i)).space) :
      (derivedNeighborhood (A (i + 1)) (L (i + 1))).space ∈
        nhdsWithin x (derivedNeighborhoodExhaustionAmbient A L) := by
    rw [hDstage i] at hx
    obtain ⟨z, hzi, hxz⟩ := Set.mem_iUnion₂.mp hx
    let Z := {z : ℤ // z ∉ symmetricIntegerInterval (i + 1)}
    have houtsideLoc : LocallyFinite (fun z : Z => (D z).space) :=
      hDloc.comp_injective Subtype.val_injective
    have houtsideClosed : IsClosed (⋃ z : Z, (D z).space) :=
      houtsideLoc.isClosed_iUnion fun z => hDclosed z
    have hxoutside : x ∈ (⋃ z : Z, (D z).space)ᶜ := by
      rw [Set.mem_compl_iff]
      intro hxout
      obtain ⟨z', hxz'⟩ := Set.mem_iUnion.mp hxout
      have hznext : z ∈ symmetricIntegerInterval (i + 1) :=
        monotone_symmetricIntegerInterval (Nat.le_succ i) hzi
      have hzz' : z ≠ (z' : ℤ) := by
        intro h
        subst z
        exact z'.2 hznext
      exact Set.disjoint_left.mp (hDdis hzz') hxz hxz'
    apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    refine ⟨(⋃ z : Z, (D z).space)ᶜ,
      houtsideClosed.isOpen_compl.mem_nhds hxoutside, ?_⟩
    intro y hy
    obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hy.2
    rw [hDstage j] at hyj
    obtain ⟨z, hzj, hyz⟩ := Set.mem_iUnion₂.mp hyj
    have hznext : z ∈ symmetricIntegerInterval (i + 1) := by
      by_contra hz
      exact hy.1 (Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hyz⟩)
    rw [hDstage (i + 1)]
    exact Set.mem_iUnion₂.mpr ⟨z, hznext, hyz⟩
  have hJfaces : J.faces = ⋃ i, (A i).faces := by
    ext s
    constructor
    · intro hs
      obtain ⟨z, -, hsz⟩ := mem_disjointUnionComplex_faces_iff.mp hs
      obtain ⟨i, hzi⟩ := exists_mem_symmetricIntegerInterval z
      exact Set.mem_iUnion.mpr
        ⟨i, mem_disjointUnionComplex_faces_iff.mpr ⟨z, hzi, hsz⟩⟩
    · intro hs
      obtain ⟨i, hsi⟩ := Set.mem_iUnion.mp hs
      obtain ⟨z, -, hsz⟩ := mem_disjointUnionComplex_faces_iff.mp hsi
      exact mem_disjointUnionComplex_faces_iff.mpr ⟨z, Set.mem_univ z, hsz⟩
  have hJlocal : LocallyFinite (fun s : J.faces =>
      (Subtype.val : J.space → E) ⁻¹' convexHull ℝ ((s : Finset E) : Set E)) := by
    simpa only [J] using
      (locallyFinite_faces_disjointUnionComplex_univ
        (C := C) (hdis := hCdis) hCloc hCfin)
  let T : LocallyFinitePLPieceIn E 3 E U := by
    simpa only [U] using euclideanLocallyFinitePLPieceIn J hJlocal
  have hLstage (i : ℕ) : (L i).space =
      ⋃ z ∈ symmetricIntegerInterval i, (H z).space := by
    simpa only [L] using disjointUnionComplex_space H hHdis (symmetricIntegerInterval i)
  have hLunion : (⋃ i, (L i).space) = K := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      rw [hLstage i] at hxi
      obtain ⟨z, -, hxz⟩ := Set.mem_iUnion₂.mp hxi
      exact Set.mem_iUnion.mpr ⟨z, hxz⟩
    · intro hx
      obtain ⟨z, hxz⟩ := Set.mem_iUnion.mp hx
      obtain ⟨i, hzi⟩ := exists_mem_symmetricIntegerInterval z
      exact Set.mem_iUnion.mpr ⟨i, hLstage i ▸ Set.mem_iUnion₂.mpr ⟨z, hzi, hxz⟩⟩
  have hKsubsetN : K ⊆ N := by
    intro x hx
    obtain ⟨z, hxz⟩ := Set.mem_iUnion.mp hx
    obtain ⟨i, hzi⟩ := exists_mem_symmetricIntegerInterval z
    let _ : Finite (A i).faces := (hAfinite i).to_subtype
    have hxL : x ∈ (L i).space := by
      rw [hLstage i]
      exact Set.mem_iUnion₂.mpr ⟨z, hzi, hxz⟩
    change x ∈ ⋃ j, (derivedNeighborhood (A j) (L j)).space
    exact Set.mem_iUnion.mpr
      ⟨i, subcomplex_space_subset_derivedNeighborhood (hLA i) hxL⟩
  have hNrange : Set.range (fun x : derivedNeighborhoodExhaustionAmbient A L => T.map x) = N := by
    change Set.range (fun x : N => (x : E)) = N
    exact Subtype.range_val
  have hKimage : (fun x : derivedNeighborhoodExhaustionAmbient A L => T.map x) ''
      derivedNeighborhoodExhaustionCore A L = K := by
    change (fun x : N => (x : E)) ''
      {x : N | (x : E) ∈ ⋃ i, (L i).space} = K
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hLunion] at hx
      exact hx
    · intro hy
      let x : N := ⟨y, hKsubsetN hy⟩
      refine ⟨x, ?_, rfl⟩
      change y ∈ ⋃ i, (L i).space
      rw [hLunion]
      exact hy
  have hPL : IsPLDerivedNeighborhoodExhaustion (n := 3) N K U := by
    exact ⟨3, T, A, L, hJfaces, hAfinite, hLA, hcard, hambient, hderived,
      hAmono, hLmono, hrestrict, hnhds, hNrange, hKimage⟩
  have hwK (z : ℤ) : w z ∈ K :=
    Set.mem_iUnion.mpr ⟨z, hw z⟩
  have hNnoncompact : ¬ IsCompact N := by
    intro hcompact
    obtain ⟨R, hNR⟩ := hcompact.isBounded.subset_closedBall (0 : E)
    obtain ⟨i, hi⟩ := exists_nat_gt ((R - (w 0) 0) / S)
    have hmul : R - (w 0) 0 < (i : ℝ) * S := (div_lt_iff₀ hS).mp hi
    have hlarge : R < (w (i : ℤ)) 0 := by
      rw [hwcoord]
      norm_num
      linarith
    have hball := hNR (hKsubsetN (hwK (i : ℤ)))
    have hnorm : ‖w (i : ℤ)‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hball
    have habs : |(w (i : ℤ)) 0| ≤ ‖w (i : ℤ)‖ := by
      simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le (w (i : ℤ)) (0 : Fin 3))
    have hcoord : (w (i : ℤ)) 0 ≤ ‖w (i : ℤ)‖ := (le_abs_self _).trans habs
    linarith
  have hsegment : segment ℝ p q ⊆ K := by
    have hconv := (H 0).convexHull_subset_space hedge
    have hsegH : segment ℝ p q ⊆ (H 0).space := by
      simpa only [Finset.coe_insert, Finset.coe_singleton, convexHull_pair] using hconv
    exact hsegH.trans fun x hx => Set.mem_iUnion.mpr ⟨0, hx⟩
  exact ⟨N, K, U, hPL, hNnoncompact, ⟨p, q, hpq, hsegment⟩,
    hPL.isDerivedNeighborhoodExhaustion.nonempty_strongDeformationRetract⟩

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
