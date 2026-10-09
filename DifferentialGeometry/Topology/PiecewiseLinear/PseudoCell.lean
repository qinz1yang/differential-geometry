/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalConfiguration
import DifferentialGeometry.Topology.PiecewiseLinear.DualCells
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyPolyhedral

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Cells

def IsOpenTopologicalCell (n : ℕ) {X : Type*} [TopologicalSpace X] (U : Set X) : Prop :=
  Nonempty (U ≃ₜ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)

def IsTopologicalSphere (n : ℕ) {X : Type*} [TopologicalSpace X] (J : Set X) : Prop :=
  Nonempty (J ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

structure IsPseudoCell (Ec Eint Ebd : Set (EuclideanSpace ℝ (Fin 3)))
    (P : EuclideanSpace ℝ (Fin 3)) : Prop where
  carrierEq : Ec = Eint ∪ Ebd
  isOpenCell : IsOpenTopologicalCell 2 Eint
  isSphere : IsTopologicalSphere 1 Ebd
  disjointRim : Disjoint Eint Ebd
  closureEq : closure Eint = Eint ∪ Ebd
  centerMem : P ∈ Eint
  regular : IsLocallyPolyhedral (Eint \ {P})

end Cells

section PlanarPolyhedron

noncomputable def euclideanCoord {n : ℕ} (i : Fin n) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ where
  toFun x := x i
  map_add' _ _ := by simp [PiLp.add_apply]
  map_smul' _ _ := by simp [PiLp.smul_apply]

@[simp] theorem euclideanCoord_apply {n : ℕ} (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    euclideanCoord i x = x i := rfl

theorem isHPolytope_of_coordBox {C : Set (EuclideanSpace ℝ (Fin 3))} (hC : IsCompact C)
    (lower upper : Fin 3 → ℝ) (heq : C = {p | ∀ i, p i ∈ Icc (lower i) (upper i)}) :
    IsHPolytope C := by
  refine ⟨hC, Fin 3 ⊕ Fin 3, inferInstance,
    Sum.elim (fun i => euclideanCoord i) (fun i => -euclideanCoord i),
    Sum.elim upper (fun i => -lower i), ?_⟩
  rw [heq]
  ext p
  constructor
  · intro hp i
    rcases i with i | i
    · simpa using (hp i).2
    · simpa using neg_le_neg (hp i).1
  · intro hp i
    have h1 : p i ≤ upper i := by simpa using hp (Sum.inl i)
    have h2 : -p i ≤ -lower i := by simpa using hp (Sum.inr i)
    exact ⟨by linarith, h1⟩

theorem isCompact_rectTwo (a b c d : ℝ) : IsCompact (rectTwo a b c d) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_rectTwo a b c d) (isBounded_rectTwo a b c d)

theorem isPolyhedron_planarRect (a b c d : ℝ) :
    IsPolyhedron (planarPoint '' rectTwo a b c d) := by
  refine IsHPolytope.isPolyhedron (isHPolytope_of_coordBox
    ((isCompact_rectTwo a b c d).image continuous_planarPoint)
    (fun i => if i = 0 then a else if i = 1 then c else 0)
    (fun i => if i = 0 then b else if i = 1 then d else 0) ?_)
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    fin_cases i
    · simpa using hx.1
    · simpa using hx.2
    · simp
  · intro hp
    have h2 : p 2 = 0 := le_antisymm (by simpa using (hp 2).2) (by simpa using (hp 2).1)
    obtain ⟨x, rfl⟩ := (planarPoint_mem_iff p).mpr h2
    exact ⟨x, ⟨by simpa using hp 0, by simpa using hp 1⟩, rfl⟩

end PlanarPolyhedron

section PseudoCellInhabitant

noncomputable def squareTwo : Set (EuclideanSpace ℝ (Fin 2)) := rectTwo (-1) 1 (-1) 1

noncomputable def planarSquare : Set (EuclideanSpace ℝ (Fin 3)) := planarPoint '' squareTwo

noncomputable def planarSquareInterior : Set (EuclideanSpace ℝ (Fin 3)) :=
  planarPoint '' interior squareTwo

noncomputable def planarSquareRim : Set (EuclideanSpace ℝ (Fin 3)) :=
  planarPoint '' frontier squareTwo

theorem convex_squareTwo : Convex ℝ squareTwo := convex_rectTwo (-1) 1 (-1) 1

theorem isClosed_squareTwo : IsClosed squareTwo := isClosed_rectTwo (-1) 1 (-1) 1

theorem isCompact_squareTwo : IsCompact squareTwo := isCompact_rectTwo (-1) 1 (-1) 1

theorem isBounded_squareTwo : Bornology.IsBounded squareTwo := isBounded_rectTwo (-1) 1 (-1) 1

theorem isPolyhedron_planarSquare : IsPolyhedron planarSquare :=
  isPolyhedron_planarRect (-1) 1 (-1) 1

theorem zero_mem_interior_squareTwo : (0 : EuclideanSpace ℝ (Fin 2)) ∈ interior squareTwo := by
  refine openRectTwo_subset_interior_rectTwo (-1) 1 (-1) 1 ⟨?_, ?_⟩
  · change (0 : EuclideanSpace ℝ (Fin 2)) 0 ∈ Ioo (-1 : ℝ) 1
    norm_num [PiLp.zero_apply]
  · change (0 : EuclideanSpace ℝ (Fin 2)) 1 ∈ Ioo (-1 : ℝ) 1
    norm_num [PiLp.zero_apply]

theorem interior_nonempty_squareTwo : (interior squareTwo).Nonempty :=
  ⟨0, zero_mem_interior_squareTwo⟩

theorem disjoint_interior_frontier_squareTwo :
    Disjoint (interior squareTwo) (frontier squareTwo) :=
  disjoint_left.mpr fun _ hx hx' => hx'.2 hx

theorem sdiff_frontier_squareTwo : squareTwo \ frontier squareTwo = interior squareTwo := by
  ext x
  constructor
  · rintro ⟨hx, hxf⟩
    by_contra hxi
    exact hxf ⟨subset_closure hx, hxi⟩
  · intro hx
    exact ⟨interior_subset hx, fun hxf => hxf.2 hx⟩

theorem interior_union_frontier_squareTwo :
    interior squareTwo ∪ frontier squareTwo = squareTwo := by
  have h : interior squareTwo ∪ frontier squareTwo = closure squareTwo :=
    union_sdiff_cancel interior_subset_closure
  rw [h, isClosed_squareTwo.closure_eq]

theorem isClosed_planarSquareRim : IsClosed planarSquareRim :=
  ((isCompact_squareTwo.of_isClosed_subset isClosed_frontier
    isClosed_squareTwo.frontier_subset).image continuous_planarPoint).isClosed

theorem isPseudoCell_planarSquare :
    IsPseudoCell planarSquare planarSquareInterior planarSquareRim (planarPoint 0) := by
  have hne : (interior squareTwo).Nonempty := interior_nonempty_squareTwo
  have hcarrier : planarSquare = planarSquareInterior ∪ planarSquareRim := by
    rw [planarSquare, planarSquareInterior, planarSquareRim, ← image_union,
      interior_union_frontier_squareTwo]
  refine ⟨hcarrier, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact nonempty_homeomorph_planarImage_interior convex_squareTwo isBounded_squareTwo hne
  · exact nonempty_homeomorph_planarImage_frontier convex_squareTwo isBounded_squareTwo hne
  · exact Set.disjoint_image_of_injective planarPoint_injective
      disjoint_interior_frontier_squareTwo
  · have hclint : closure (interior squareTwo) = squareTwo := by
      rw [convex_squareTwo.closure_interior_eq_closure_of_nonempty_interior hne,
        isClosed_squareTwo.closure_eq]
    rw [← hcarrier, planarSquare, planarSquareInterior]
    refine Subset.antisymm (closure_minimal (image_mono interior_subset)
      ((isCompact_squareTwo.image continuous_planarPoint).isClosed)) ?_
    calc planarPoint '' squareTwo = planarPoint '' closure (interior squareTwo) := by
          rw [hclint]
      _ ⊆ closure (planarPoint '' interior squareTwo) :=
          image_closure_subset_closure_image continuous_planarPoint
  · exact ⟨0, zero_mem_interior_squareTwo, rfl⟩
  · have hdiff : planarSquareInterior = planarSquare \ planarSquareRim := by
      rw [planarSquare, planarSquareInterior, planarSquareRim,
        ← image_sdiff planarPoint_injective, sdiff_frontier_squareTwo]
    rw [hdiff]
    exact ((isPolyhedron_planarSquare.isLocallyPolyhedral.sdiff_isClosed
      isClosed_planarSquareRim).sdiff_isClosed isClosed_singleton)

theorem isOpenTopologicalCell_planarSquareInterior :
    IsOpenTopologicalCell 2 planarSquareInterior :=
  isPseudoCell_planarSquare.isOpenCell

theorem isTopologicalSphere_planarSquareRim : IsTopologicalSphere 1 planarSquareRim :=
  isPseudoCell_planarSquare.isSphere

theorem not_isClosed_planarSquareInterior : ¬ IsClosed planarSquareInterior := by
  intro hclosed
  have hcl := isPseudoCell_planarSquare.closureEq
  rw [hclosed.closure_eq] at hcl
  have hsub : planarSquareRim ⊆ planarSquareInterior := by
    conv_rhs => rw [hcl]
    exact subset_union_right
  have hempty : planarSquareRim = ∅ := by
    have hd : Disjoint planarSquareRim planarSquareRim :=
      (isPseudoCell_planarSquare.disjointRim).mono_left hsub
    simpa using disjoint_self.mp hd
  have hfr : frontier squareTwo = ∅ := by
    by_contra hfrne
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hfrne
    have hmem : planarPoint x ∈ planarSquareRim := mem_image_of_mem planarPoint hx
    rw [hempty] at hmem
    exact hmem
  have hclopen : IsClopen squareTwo := isClopen_iff_frontier_eq_empty.mpr hfr
  rcases isClopen_iff.mp hclopen with h | h
  · have hzero : (0 : EuclideanSpace ℝ (Fin 2)) ∈ interior squareTwo :=
      zero_mem_interior_squareTwo
    rw [h, interior_empty] at hzero
    exact hzero
  · have hmem : EuclideanSpace.single (0 : Fin 2) (2 : ℝ) ∈ rectTwo (-1) 1 (-1) 1 := by
      have hu : EuclideanSpace.single (0 : Fin 2) (2 : ℝ) ∈ squareTwo := by
        rw [h]; exact mem_univ _
      exact hu
    have h2 : (EuclideanSpace.single (0 : Fin 2) (2 : ℝ)) 0 ≤ 1 := (mem_rectTwo.mp hmem).1.2
    simp at h2

end PseudoCellInhabitant

section Tubes

theorem classical_insert_singleton_eq_pair {α : Type*} [DecidableEq α] (u v : α) :
    @insert α (Finset α) (@Finset.instInsert α fun a b => Classical.propDecidable (a = b)) u {v}
      = ({u, v} : Finset α) := by
  ext a
  simp

open Classical in
structure IsTube (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (N : Set (EuclideanSpace ℝ (Fin 3)))
    (C : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3)))
    (D Dbd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (N' : Set (EuclideanSpace ℝ (Fin 3))) : Prop where
  facesFinite : K.faces.Finite
  oneDimensional : ∀ s ∈ K.faces, s.card ≤ 2
  hasEdge : ∃ e ∈ K.faces, e.card = 2
  isNeighborhood : N ∈ nhdsSet K.space
  derivedModel : ∃ A : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
    A.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 A ∧ K.faces ⊆ A.faces ∧
      (∀ v ∈ K.vertices, C v = (graphDualCell A K v).space) ∧
      ∀ e ∈ K.faces, e.card = 2 → ∀ he : e ∈ A.faces, D e = (splittingDisk A e he).space
  dualBall : ∀ v ∈ K.vertices, IsPLBall 3 (C v)
  splitCell : ∀ e ∈ K.faces, e.card = 2 →
    ∃ r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D e) ∧ Dbd e = r '' stdSimplexBoundary 2
  unionEq : N = ⋃ v ∈ K.vertices, C v
  splitProper : ∀ e ∈ K.faces, e.card = 2 → D e ∩ frontier N = Dbd e
  splitSeparates : ∀ u ∈ K.vertices, ∀ v ∈ K.vertices, u ≠ v →
    ({u, v} : Finset _) ∈ K.faces →
    DifferentialGeometry.Topology.Separates
      (((↑) : interior (C u ∪ C v) → EuclideanSpace ℝ (Fin 3)) ⁻¹' (D {u, v} \ Dbd {u, v}))
      (((↑) : interior (C u ∪ C v) → EuclideanSpace ℝ (Fin 3)) ⁻¹' {u})
      (((↑) : interior (C u ∪ C v) → EuclideanSpace ℝ (Fin 3)) ⁻¹' {v})
  freeFaceConnected : ∀ v ∈ K.vertices,
    IsConnected ((frontier (C v) ∩ frontier N) \
      (⋃ e ∈ {e : Finset (EuclideanSpace ℝ (Fin 3)) | e ∈ K.faces ∧ e.card = 2 ∧ v ∈ e}, Dbd e))
  isEmbedding : Topology.IsEmbedding (N.domRestrict h)
  imageEq : N' = h '' N

open Classical in
structure IsHandleDecompositionOfTube
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (N : Set (EuclideanSpace ℝ (Fin 3)))
    (C : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3)))
    (D Dbd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (N' : Set (EuclideanSpace ℝ (Fin 3)))
    (Ec Eint Ebd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
    (Cpp : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3))) : Prop where
  tube : IsTube K N C D Dbd h N'
  pseudoCell : ∀ e ∈ K.faces, e.card = 2 →
    IsPseudoCell (Ec e) (Eint e) (Ebd e) (h (e.centroid ℝ id))
  rimEq : ∀ e ∈ K.faces, e.card = 2 → Ebd e = h '' Dbd e
  rimFrontier : ∀ e ∈ K.faces, e.card = 2 → Ec e ∩ frontier N' = Ebd e
  meetsGraph : ∀ e ∈ K.faces, e.card = 2 →
    Ec e ∩ h '' K.space = {h (e.centroid ℝ id)}
  pseudoCellDisjoint : ∀ e ∈ K.faces, e.card = 2 → ∀ f ∈ K.faces, f.card = 2 → e ≠ f →
    Disjoint (Ec e) (Ec f)
  oneVertex : ∀ v ∈ K.vertices, Cpp v ∩ h '' K.vertices = {h v}
  coversTube : N' = ⋃ v ∈ K.vertices, Cpp v
  componentClosure : ∀ v ∈ K.vertices, Cpp v = closure (connectedComponentIn
    (N' \ (⋃ e ∈ {e : Finset (EuclideanSpace ℝ (Fin 3)) | e ∈ K.faces ∧ e.card = 2}, Ec e))
    (h v))
  handleEdge : ∀ u ∈ K.vertices, ∀ v ∈ K.vertices, u ≠ v → ({u, v} : Finset _) ∈ K.faces →
    Cpp u ∩ Cpp v = Ec {u, v}
  handleNonEdge : ∀ u ∈ K.vertices, ∀ v ∈ K.vertices, u ≠ v →
    ({u, v} : Finset _) ∉ K.faces → Cpp u ∩ Cpp v = ∅

variable {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {N N' : Set (EuclideanSpace ℝ (Fin 3))}
  {C : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3))}
  {D Dbd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}

theorem IsTube.dualVertex (ht : IsTube K N C D Dbd h N') {v : EuclideanSpace ℝ (Fin 3)}
    (hv : v ∈ K.vertices) : C v ∩ K.vertices = {v} := by
  obtain ⟨A, -, -, hKA, hC, -⟩ := ht.derivedModel
  rw [hC v hv]
  ext w
  simp only [mem_inter_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hwC, hwV⟩
    exact (mem_graphDualCell_space_iff_of_singleton_mem A K hKA hv hwV).mp hwC
  · rintro rfl
    exact ⟨mem_graphDualCell_space_of_singleton_mem A K hKA hv, hv⟩

theorem IsTube.interEdge (ht : IsTube K N C D Dbd h N') {u v : EuclideanSpace ℝ (Fin 3)}
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset (EuclideanSpace ℝ (Fin 3))) ∈ K.faces) : C u ∩ C v = D {u, v} := by
  obtain ⟨A, -, -, hKA, hC, hD⟩ := ht.derivedModel
  have hcl := classical_insert_singleton_eq_pair u v
  have hecl := hcl.symm ▸ he
  calc C u ∩ C v = (graphDualCell A K u).space ∩ (graphDualCell A K v).space := by
        rw [hC u hu, hC v hv]
    _ = (splittingDisk A _ (hKA hecl)).space :=
        graphDualCell_space_inter A K hKA ht.oneDimensional huv hecl
    _ = D _ := (hD _ hecl (by rw [hcl]; exact Finset.card_pair huv) (hKA hecl)).symm
    _ = D {u, v} := congrArg D hcl

theorem IsTube.interNonEdge (ht : IsTube K N C D Dbd h N') {u v : EuclideanSpace ℝ (Fin 3)}
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset (EuclideanSpace ℝ (Fin 3))) ∉ K.faces) : C u ∩ C v = ∅ := by
  obtain ⟨A, -, -, hKA, hC, -⟩ := ht.derivedModel
  have hcl := classical_insert_singleton_eq_pair u v
  rw [hC u hu, hC v hv]
  exact graphDualCell_space_inter_eq_empty A K hKA ht.oneDimensional hu hv huv
    fun hmem => he (hcl ▸ hmem)

theorem IsTube.splitMidpoint (ht : IsTube K N C D Dbd h N')
    {e : Finset (EuclideanSpace ℝ (Fin 3))} (he : e ∈ K.faces) (hcard : e.card = 2) :
    D e ∩ K.space = {e.centroid ℝ id} := by
  obtain ⟨A, -, -, hKA, -, hD⟩ := ht.derivedModel
  rw [hD e he hcard (hKA he)]
  exact splittingDisk_space_inter A K hKA he fun t htK => by
    rw [hcard]; exact ht.oneDimensional t htK

theorem IsTube.splitDisjoint (ht : IsTube K N C D Dbd h N')
    {e f : Finset (EuclideanSpace ℝ (Fin 3))} (he : e ∈ K.faces) (hecard : e.card = 2)
    (hf : f ∈ K.faces) (hfcard : f.card = 2) (hef : e ≠ f) : Disjoint (D e) (D f) := by
  obtain ⟨A, -, -, hKA, -, hD⟩ := ht.derivedModel
  rw [hD e he hecard (hKA he), hD f hf hfcard (hKA hf)]
  exact disjoint_splittingDisk_space A (hKA he) (hKA hf) hef (by rw [hecard, hfcard])

theorem IsTube.spaceEq (ht : IsTube K N C D Dbd h N')
    (inst : DecidableEq (EuclideanSpace ℝ (Fin 3))) :
    ∃ A : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      K.faces ⊆ A.faces ∧ N = (@derivedNeighborhood _ _ _ inst A K).space := by
  obtain ⟨A, -, -, hKA, hC, -⟩ := ht.derivedModel
  refine ⟨A, hKA, ?_⟩
  have hinst : inst = fun a b => Classical.propDecidable (a = b) := by
    funext a b
    exact Subsingleton.elim _ _
  subst hinst
  rw [ht.unionEq, ← iUnion_graphDualCell_space A K hKA]
  exact iUnion₂_congr hC

end Tubes

section Statements

open Classical in
def Moise321 : Prop :=
  ∀ (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (N : Set (EuclideanSpace ℝ (Fin 3)))
    (C : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3)))
    (D Dbd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (N' : Set (EuclideanSpace ℝ (Fin 3))),
    IsTube K N C D Dbd h N' →
    ∀ u ∈ K.vertices, ∀ v ∈ K.vertices, u ≠ v → ({u, v} : Finset _) ∈ K.faces →
    ∀ W : Set (EuclideanSpace ℝ (Fin 3)), IsClosed W →
      h '' (D {u, v} \ Dbd {u, v}) \ {h (({u, v} : Finset _).centroid ℝ id)} ⊆ interior W →
      W ⊆ h '' C u ∪ h '' C v →
      W ∩ frontier (h '' C u ∪ h '' C v) = h '' Dbd {u, v} →
      W ∩ h '' K.space = {h (({u, v} : Finset _).centroid ℝ id)} →
      ∃ Ec Eint Ebd : Set (EuclideanSpace ℝ (Fin 3)),
        IsPseudoCell Ec Eint Ebd (h (({u, v} : Finset _).centroid ℝ id)) ∧
        Ebd = h '' Dbd {u, v} ∧ Ec ⊆ W ∧
        DifferentialGeometry.Topology.Separates
          (((↑) : interior (h '' C u ∪ h '' C v) → EuclideanSpace ℝ (Fin 3)) ⁻¹' Eint)
          (((↑) : interior (h '' C u ∪ h '' C v) → EuclideanSpace ℝ (Fin 3)) ⁻¹' {h u})
          (((↑) : interior (h '' C u ∪ h '' C v) → EuclideanSpace ℝ (Fin 3)) ⁻¹' {h v}) ∧
        Ec ∩ h '' K.space = {h (({u, v} : Finset _).centroid ℝ id)}

open Classical in
def Moise322 : Prop :=
  ∀ (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (N : Set (EuclideanSpace ℝ (Fin 3)))
    (C : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3)))
    (D Dbd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (N' : Set (EuclideanSpace ℝ (Fin 3))),
    IsTube K N C D Dbd h N' →
    ∀ u ∈ K.vertices, ∀ v ∈ K.vertices, u ≠ v → ({u, v} : Finset _) ∈ K.faces →
    ∀ W : Set (EuclideanSpace ℝ (Fin 3)), IsClosed W →
      h '' (D {u, v} \ Dbd {u, v}) \ {h (({u, v} : Finset _).centroid ℝ id)} ⊆ interior W →
      W ⊆ h '' C u ∪ h '' C v →
      W ∩ frontier (h '' C u ∪ h '' C v) = h '' Dbd {u, v} →
      W ∩ h '' K.space = {h (({u, v} : Finset _).centroid ℝ id)} →
      ∃ (Ec Eint Ebd U₁ U₂ : Set (EuclideanSpace ℝ (Fin 3))),
        IsPseudoCell Ec Eint Ebd (h (({u, v} : Finset _).centroid ℝ id)) ∧
        Ebd = h '' Dbd {u, v} ∧ Ec ⊆ W ∧
        DifferentialGeometry.Topology.Separates
          (((↑) : interior (h '' C u ∪ h '' C v) → EuclideanSpace ℝ (Fin 3)) ⁻¹' Eint)
          (((↑) : interior (h '' C u ∪ h '' C v) → EuclideanSpace ℝ (Fin 3)) ⁻¹' {h u})
          (((↑) : interior (h '' C u ∪ h '' C v) → EuclideanSpace ℝ (Fin 3)) ⁻¹' {h v}) ∧
        Ec ∩ h '' K.space = {h (({u, v} : Finset _).centroid ℝ id)} ∧
        h u ∈ U₁ ∧ h v ∈ U₂ ∧
        IsConnected U₁ ∧ IsConnected U₂ ∧ Disjoint U₁ U₂ ∧
        U₁ ∪ U₂ = (h '' C u ∪ h '' C v) \ Ec ∧
        (∀ V : Set (EuclideanSpace ℝ (Fin 3)), IsPreconnected V →
          V ⊆ (h '' C u ∪ h '' C v) \ Ec → V ⊆ U₁ ∨ V ⊆ U₂) ∧
        Ec ⊆ frontier U₁ ∧ Ec ⊆ frontier U₂ ∧
        h '' (frontier (C u) ∩ frontier N) ⊆ frontier U₁ ∧
        h '' (frontier (C v) ∩ frontier N) ⊆ frontier U₂

def Moise323 : Prop :=
  ∀ (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (N : Set (EuclideanSpace ℝ (Fin 3)))
    (C : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3)))
    (D Dbd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (N' : Set (EuclideanSpace ℝ (Fin 3))),
    IsTube K N C D Dbd h N' →
    ∀ V : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3)),
      (∀ v ∈ K.vertices, V v ∈ nhdsSet (h '' C v)) →
      ∃ (Ec Eint Ebd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
        (Cpp : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3))),
        IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp ∧
        ∀ v ∈ K.vertices, Cpp v ⊆ V v

def Moise324 : Prop :=
  ∀ (Ec Eint Ebd : Set (EuclideanSpace ℝ (Fin 3))) (P : EuclideanSpace ℝ (Fin 3)),
    IsPseudoCell Ec Eint Ebd P →
    ∀ δ : ℝ, 0 < δ →
      ∃ (Δ Δbd : Set (EuclideanSpace ℝ (Fin 3)))
        (r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
        IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧
        Δbd = r '' stdSimplexBoundary 2 ∧
        Δ ⊆ Metric.ball P δ ∧
        Δbd = Δ ∩ Ec ∧
        ∃ DJ DJint : Set (EuclideanSpace ℝ (Fin 3)),
          IsTopologicalCellWithInterior 2 DJ DJint ∧ DJ ⊆ Ec ∧ DJ \ DJint = Δbd ∧ P ∈ DJint

end Statements

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Vocabulary

structure IsCanonicalTower (φ : E3 → E3) (Pt : ℤ → E3)
    (Dp Dpint J A S T S'' T'' : ℤ → Set E3) (Dimg Dbdimg W I : Set E3) (P' : E3) : Prop where
  config : ∀ i : ℤ, IsCanonicalConfiguration (fun j : Fin 4 => Pt (i + ((j : ℕ) : ℤ)))
    (fun j : Fin 3 => Dp (i + ((j : ℕ) : ℤ))) (fun j : Fin 3 => Dpint (i + ((j : ℕ) : ℤ)))
    (fun j : Fin 4 => J (i + ((j : ℕ) : ℤ))) (fun j : Fin 3 => A (i + ((j : ℕ) : ℤ)))
    (fun j : Fin 3 => S (i + ((j : ℕ) : ℤ))) (fun j : Fin 3 => T (i + ((j : ℕ) : ℤ)))
    (⋃ j : Fin 3, S (i + ((j : ℕ) : ℤ))) φ (fun j : Fin 3 => S'' (i + ((j : ℕ) : ℤ)))
    (fun j : Fin 3 => T'' (i + ((j : ℕ) : ℤ)))
  apart : ∀ i k : ℤ, 2 ≤ |i - k| → Disjoint (φ '' S i) (φ '' S k)
  annuliEq : φ '' (⋃ i, A i) = Dimg \ (Dbdimg ∪ {P'})
  subsetW : ∀ i, φ '' S i ⊆ W
  subsetInterior : ∀ i, φ '' S i ⊆ I
  centerMemInterior : P' ∈ I
  closureLower : ∀ m : ℤ,
    closure (⋃ i, ⋃ (_ : i ≤ m), φ '' S i) = (⋃ i, ⋃ (_ : i ≤ m), φ '' S i) ∪ {P'}
  closureUpper : ∀ m : ℤ,
    closure (⋃ i, ⋃ (_ : m ≤ i), φ '' S i) = (⋃ i, ⋃ (_ : m ≤ i), φ '' S i) ∪ Dbdimg
  locallyFinite : ∀ x ∈ I, x ≠ P' → ∃ U ∈ 𝓝 x, {i | (φ '' S i ∩ U).Nonempty}.Finite

def initialSurface (S'' T'' : ℤ → Set E3) (P' : E3) : Set E3 :=
  (⋃ i, T'' (2 * i)) ∪ ((⋃ i, T'' (2 * i + 1)) \ ⋃ i, interior (S'' (2 * i))) ∪ {P'}

structure IsAnnularChain (H B Jlo Jhi S' S'' T'' : ℤ → Set E3) (P' : E3) : Prop where
  half : ∀ i, IsPLAnnulusWithEnds (H i) (Jhi (i - 1)) (Jlo i)
  halfSubset : ∀ i, H i ⊆ T'' (2 * i)
  halfSubsetTorus : ∀ i, H i ⊆ S' (2 * i)
  bridge : ∀ i, IsPLAnnulusWithEnds (B i) (Jlo i) (Jhi i)
  bridgeSubset : ∀ i, B i ⊆ S' (2 * i) ∪ S' (2 * i + 1) ∪ S' (2 * i + 2)
  loSubset : ∀ i, Jlo i ⊆ T'' (2 * i)
  hiSubset : ∀ i, Jhi i ⊆ T'' (2 * i + 2)
  loGenerator : ∀ i, ∀ hsub : Jlo i ⊆ S'' (2 * i), ∀ x : Jlo i,
    Function.Surjective (FundamentalGroup.map
      (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ : C(Jlo i, S'' (2 * i))) x)
  hiGenerator : ∀ i, ∀ hsub : Jhi i ⊆ S'' (2 * i + 2), ∀ x : Jhi i,
    Function.Surjective (FundamentalGroup.map
      (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ : C(Jhi i, S'' (2 * i + 2))) x)
  halfInterBridge : ∀ i, H i ∩ B i = Jlo i
  bridgeInterHalf : ∀ i, B i ∩ H (i + 1) = Jhi i
  halfDisjoint : ∀ i k, i ≠ k → Disjoint (H i) (H k)
  bridgeDisjoint : ∀ i k, i ≠ k → Disjoint (B i) (B k)
  halfBridgeDisjoint : ∀ i k, k ≠ i → k ≠ i - 1 → Disjoint (H i) (B k)
  centerNotMem : ∀ i, P' ∉ H i ∪ B i

def annularChain (H B : ℤ → Set E3) (P' : E3) : Set E3 :=
  (⋃ i, H i ∪ B i) ∪ {P'}

open Classical in
def SplitsDualCellsAlong (K : Geometry.SimplicialComplex ℝ E3) (N : Set E3) (C : E3 → Set E3)
    (Dbd : Finset E3 → Set E3) (h : E3 → E3) (W Ec Eint Ebd : Set E3) (u v : E3) : Prop :=
  IsPseudoCell Ec Eint Ebd (h (({u, v} : Finset E3).centroid ℝ id)) ∧
  Ebd = h '' Dbd {u, v} ∧ Ec ⊆ W ∧
  Separates (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' Eint)
    (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h u})
    (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h v}) ∧
  Ec ∩ h '' K.space = {h (({u, v} : Finset E3).centroid ℝ id)} ∧
  ∃ U₁ U₂ : Set E3, h u ∈ U₁ ∧ h v ∈ U₂ ∧ IsConnected U₁ ∧ IsConnected U₂ ∧ Disjoint U₁ U₂ ∧
    U₁ ∪ U₂ = (h '' C u ∪ h '' C v) \ Ec ∧
    (∀ V : Set E3, IsPreconnected V → V ⊆ (h '' C u ∪ h '' C v) \ Ec → V ⊆ U₁ ∨ V ⊆ U₂) ∧
    Ec ⊆ frontier U₁ ∧ Ec ⊆ frontier U₂ ∧
    h '' (frontier (C u) ∩ frontier N) ⊆ frontier U₁ ∧
    h '' (frontier (C v) ∩ frontier N) ⊆ frontier U₂

def IsEdgeCollarFamily (K : Geometry.SimplicialComplex ℝ E3) (C : E3 → Set E3)
    (D Dbd : Finset E3 → Set E3) (h : E3 → E3) (V : E3 → Set E3) (W : Finset E3 → Set E3) :
    Prop :=
  ∀ e ∈ K.faces, e.card = 2 →
    IsClosed (W e) ∧ h '' (D e \ Dbd e) \ {h (e.centroid ℝ id)} ⊆ interior (W e) ∧
    W e ∩ h '' K.space = {h (e.centroid ℝ id)} ∧
    (∀ u ∈ e, ∀ v ∈ e, u ≠ v → W e ⊆ h '' C u ∪ h '' C v ∧
      W e ∩ frontier (h '' C u ∪ h '' C v) = h '' Dbd e) ∧
    (∀ v ∈ e, IsConnected (h '' C v \ W e) ∧ W e ⊆ V v) ∧
    ∀ f ∈ K.faces, f.card = 2 → e ≠ f → Disjoint (W e) (W f)

def handlePiece (K : Geometry.SimplicialComplex ℝ E3) (N' : Set E3) (Ec : Finset E3 → Set E3)
    (h : E3 → E3) (v : E3) : Set E3 :=
  closure (connectedComponentIn
    (N' \ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e) (h v))

def CrossesPseudoCell (F Ec Eint : Set E3) (P : E3) : Prop :=
  ∃ (n : ℕ) (G : Fin n → Set E3), (∀ i, IsPLSphere 1 (G i)) ∧
    Pairwise (fun i j => Disjoint (G i) (G j)) ∧ F ∩ Ec = ⋃ i, G i ∧
    (⋃ i, G i) ⊆ Eint \ {P} ∧ ∀ x ∈ F ∩ Ec, HasPLCrossingAt F Ec x

end Vocabulary

section TubeFacts

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {v : E3}

theorem IsTube.mem_interior_dualCell (ht : IsTube K N C D Dbd h N') (hv : v ∈ K.vertices) :
    v ∈ interior (C v) := by
  have hfin : K.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn ht.facesFinite
  have hclosed : IsClosed (⋃ w ∈ K.vertices \ {v}, C w) :=
    (hfin.subset sdiff_subset).isClosed_biUnion fun w hw =>
      (ht.dualBall w hw.1).isPolyhedron.isClosed
  have hN : N ∈ 𝓝 v :=
    mem_nhdsSet_iff_forall.mp ht.isNeighborhood v
      (Geometry.SimplicialComplex.vertices_subset_space hv)
  have hU : interior N \ ⋃ w ∈ K.vertices \ {v}, C w ∈ 𝓝 v := by
    refine (isOpen_interior.sdiff hclosed).mem_nhds ⟨mem_interior_iff_mem_nhds.mpr hN, ?_⟩
    intro hmem
    obtain ⟨w, hw, hvw⟩ := mem_iUnion₂.mp hmem
    have hvw' : v ∈ C w ∩ K.vertices := ⟨hvw, hv⟩
    rw [ht.dualVertex hw.1] at hvw'
    exact hw.2 (mem_singleton_iff.mpr (mem_singleton_iff.mp hvw').symm)
  refine mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset hU ?_)
  rintro x ⟨hxN, hxU⟩
  have hxN' : x ∈ N := interior_subset hxN
  rw [ht.unionEq] at hxN'
  obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.mp hxN'
  by_cases hwv : w = v
  · exact hwv ▸ hxw
  · exact absurd (mem_iUnion₂.mpr ⟨w, ⟨hw, fun hw' => hwv (mem_singleton_iff.mp hw')⟩, hxw⟩) hxU

end TubeFacts

open Classical in
theorem Moise322.exists_splitsDualCellsAlong (h322 : Moise322)
    {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
    {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3} {W : Set E3}
    (ht : IsTube K N C D Dbd h N') (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset E3) ∈ K.faces) (hW : IsClosed W)
    (hWint : h '' (D {u, v} \ Dbd {u, v}) \ {h (({u, v} : Finset E3).centroid ℝ id)} ⊆
      interior W)
    (hWsub : W ⊆ h '' C u ∪ h '' C v)
    (hWfr : W ∩ frontier (h '' C u ∪ h '' C v) = h '' Dbd {u, v})
    (hWK : W ∩ h '' K.space = {h (({u, v} : Finset E3).centroid ℝ id)}) :
    ∃ Ec Eint Ebd : Set E3, SplitsDualCellsAlong K N C Dbd h W Ec Eint Ebd u v := by
  obtain ⟨Ec, Eint, Ebd, U₁, U₂, hpc, hbd, hsub, hsep, hK, hU⟩ :=
    h322 K N C D Dbd h N' ht u hu v hv huv he W hW hWint hWsub hWfr hWK
  exact ⟨Ec, Eint, Ebd, hpc, hbd, hsub, hsep, hK, U₁, U₂, hU⟩

end DifferentialGeometry.Topology.PiecewiseLinear
