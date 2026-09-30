import DifferentialGeometry.Topology.PiecewiseLinear.ExhaustionGeneral
import DifferentialGeometry.Topology.PiecewiseLinear.PieceTransport
import DifferentialGeometry.Topology.PiecewiseLinear.RelativePieceNeighborhood

open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [T2Space X] [HasGroupoid X (plGroupoid n)]

open Classical in
theorem PLPiece.exists_union_chart_with_regularNeighborhood {Y : Set X} (T : PLPiece n X Y)
    (B : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin T.ambientDim)))
    (hB : B.faces ⊆ T.piece.complex.faces)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsHPolytope C) (hCe : C ⊆ e.target)
    (hdis : Disjoint (T.piece.map '' (regularNeighborhoodIn T.piece.complex B.space).space)
      (e.symm '' C)) :
    ∃ T' : PLPiece n X (Y ∪ e.symm '' C),
      ∃ B' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin T'.ambientDim)),
        ∃ φ : EuclideanSpace ℝ (Fin T.ambientDim) → EuclideanSpace ℝ (Fin T'.ambientDim),
          ∃ φ' : EuclideanSpace ℝ (Fin T'.ambientDim) → EuclideanSpace ℝ (Fin T.ambientDim),
            B'.faces ⊆ T'.piece.complex.faces ∧ IsGlueIso B B' φ φ' ∧
              (∀ x ∈ B.space, T'.piece.map (simplicialMap B φ x) = T.piece.map x) ∧
                T'.piece.map '' (regularNeighborhoodIn T'.piece.complex B'.space).space ⊆
                  T.piece.map '' (regularNeighborhoodIn T.piece.complex B.space).space := by
  have hdis' : Disjoint (regularNeighborhoodIn T.piece.complex B.space).space
      (T.piece.complex.space ∩ T.piece.map ⁻¹' (e.symm '' C)) := by
    rw [Set.disjoint_left]
    exact fun x hx hy => Set.disjoint_left.mp hdis ⟨x, hx, rfl⟩ hy.2
  obtain ⟨Q, A, φ, φ', hA, hiso, hmap, hreg⟩ :=
    T.piece.exists_glue_chart_with_regularNeighborhood e he hC hCe B hB hdis'
  obtain ⟨T', B', ψ, ψ', hB', hiso', hmap', hreg'⟩ := Q.exists_pLPiece_with_regularNeighborhood A hA
  refine ⟨T', B', ψ ∘ φ, φ' ∘ ψ', hB', hiso.trans hiso', ?_, hreg'.subset.trans hreg⟩
  intro x hx
  rw [← hiso.simplicialMap_comp ψ hx]
  exact (hmap' _ (hiso.mapsTo_left hx)).trans (hmap x hx)

open Classical in
theorem PLPiece.exists_union_charts_with_regularNeighborhood {Y : Set X} (T : PLPiece n X Y)
    (B : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin T.ambientDim)))
    (hB : B.faces ⊆ T.piece.complex.faces) {ι : Type*} (V : ι → Set X)
    (hV : ∀ i, ∃ e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)),
      e ∈ atlas (EuclideanSpace ℝ (Fin n)) X ∧
        ∃ C : Set (EuclideanSpace ℝ (Fin n)), IsHPolytope C ∧ C ⊆ e.target ∧ V i = e.symm '' C)
    (t : Finset ι)
    (hdis : ∀ i ∈ t, Disjoint (T.piece.map '' (regularNeighborhoodIn T.piece.complex B.space).space)
      (V i)) :
    ∃ T' : PLPiece n X (Y ∪ ⋃ i ∈ t, V i),
      ∃ B' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin T'.ambientDim)),
        ∃ φ : EuclideanSpace ℝ (Fin T.ambientDim) → EuclideanSpace ℝ (Fin T'.ambientDim),
          ∃ φ' : EuclideanSpace ℝ (Fin T'.ambientDim) → EuclideanSpace ℝ (Fin T.ambientDim),
            B'.faces ⊆ T'.piece.complex.faces ∧ IsGlueIso B B' φ φ' ∧
              (∀ x ∈ B.space, T'.piece.map (simplicialMap B φ x) = T.piece.map x) ∧
                T'.piece.map '' (regularNeighborhoodIn T'.piece.complex B'.space).space ⊆
                  T.piece.map '' (regularNeighborhoodIn T.piece.complex B.space).space := by
  revert hdis
  induction t using Finset.induction_on with
  | empty =>
    intro _
    have hset : Y ∪ ⋃ i ∈ (∅ : Finset ι), V i = Y := by simp
    rw [hset]
    refine ⟨T, B, id, id, hB, ⟨fun s hs => by simpa using hs,
      fun s hs => by simpa using hs, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩, ?_, Subset.refl _⟩
    intro x hx
    exact congrArg T.piece.map (simplicialMap_eq_of_forall_affineOn B id
      (fun _ _ => ⟨AffineMap.id ℝ _, fun _ _ => rfl⟩) hx)
  | @insert a t _ ih =>
    intro hdis
    obtain ⟨T₁, B₁, φ, φ', hB₁, hiso, hmap, hreg⟩ :=
      ih (fun i hi => hdis i (Finset.mem_insert_of_mem hi))
    obtain ⟨e, he, C, hC, hCe, hVa⟩ := hV a
    have hdis₁ : Disjoint (T₁.piece.map '' (regularNeighborhoodIn T₁.piece.complex B₁.space).space)
        (e.symm '' C) := hVa ▸ (hdis a (Finset.mem_insert_self a t)).mono_left hreg
    have hset : (Y ∪ ⋃ i ∈ t, V i) ∪ e.symm '' C = Y ∪ ⋃ i ∈ insert a t, V i := by
      rw [Finset.set_biUnion_insert, ← hVa]
      ext x
      simp only [mem_union]
      tauto
    rw [← hset]
    obtain ⟨T₂, B₂, ψ, ψ', hB₂, hiso', hmap', hreg'⟩ :=
      T₁.exists_union_chart_with_regularNeighborhood B₁ hB₁ e he hC hCe hdis₁
    refine ⟨T₂, B₂, ψ ∘ φ, φ' ∘ ψ', hB₂, hiso.trans hiso', ?_, hreg'.trans hreg⟩
    intro x hx
    rw [← hiso.simplicialMap_comp ψ hx]
    exact (hmap' _ (hiso.mapsTo_left hx)).trans (hmap x hx)

open Classical in
theorem PLPiece.exists_neighborhood_preserving_subcomplex {Y : Set X} (T : PLPiece n X Y)
    (B : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin T.ambientDim)))
    (hB : B.faces ⊆ T.piece.complex.faces)
    (hBY : T.piece.map '' (regularNeighborhoodIn T.piece.complex B.space).space ⊆ interior Y)
    {C U : Set X} (hC : IsCompact C) (hU : IsOpen U) (hYU : Y ⊆ U) (hCU : C ⊆ U) :
    ∃ Q : Set X, ∃ T' : PLPiece n X Q,
      ∃ B' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin T'.ambientDim)),
        ∃ φ : EuclideanSpace ℝ (Fin T.ambientDim) → EuclideanSpace ℝ (Fin T'.ambientDim),
          ∃ φ' : EuclideanSpace ℝ (Fin T'.ambientDim) → EuclideanSpace ℝ (Fin T.ambientDim),
            Y ∪ C ⊆ interior Q ∧ Q ⊆ U ∧ B'.faces ⊆ T'.piece.complex.faces ∧
              IsGlueIso B B' φ φ' ∧
                (∀ x ∈ B.space, T'.piece.map (simplicialMap B φ x) = T.piece.map x) ∧
                  T'.piece.map '' (regularNeighborhoodIn T'.piece.complex B'.space).space ⊆
                    T.piece.map '' (regularNeighborhoodIn T.piece.complex B.space).space := by
  let D := T.piece.map '' (regularNeighborhoodIn T.piece.complex B.space).space
  have hDc : IsCompact D :=
    (T.piece.restrict (regularNeighborhoodIn T.piece.complex B.space) (fun _ hs => hs.1)).isCompact
  let S := (Y ∪ C) \ interior Y
  have hS : IsCompact S := (T.piece.isCompact.union hC).diff isOpen_interior
  have hSU : S ⊆ U \ D := by
    intro x hx
    exact ⟨hx.1.elim (fun h => hYU h) (fun h => hCU h), fun h => hx.2 (hBY h)⟩
  have hlocal : ∀ x : S, ∃ P : Set (EuclideanSpace ℝ (Fin n)), IsHPolytope P ∧
      P ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) (x : X)).target ∧
        (chartAt (EuclideanSpace ℝ (Fin n)) (x : X)).symm '' P ∈ 𝓝 (x : X) ∧
          (chartAt (EuclideanSpace ℝ (Fin n)) (x : X)).symm '' P ⊆ U \ D := fun x =>
    exists_isHPolytope_image_symm_mem_nhds_subset (hU.sdiff hDc.isClosed) (hSU x.property)
  choose P hP hPe hPx hPU using hlocal
  let V : S → Set X := fun x => (chartAt (EuclideanSpace ℝ (Fin n)) (x : X)).symm '' P x
  have hcover : S ⊆ ⋃ x : S, interior (V x) := fun x hx =>
    mem_iUnion.mpr ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (hPx ⟨x, hx⟩)⟩
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun x : S => interior (V x))
    (fun _ => isOpen_interior) hcover
  have hV : ∀ i : S, ∃ e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)),
      e ∈ atlas (EuclideanSpace ℝ (Fin n)) X ∧
        ∃ P : Set (EuclideanSpace ℝ (Fin n)), IsHPolytope P ∧ P ⊆ e.target ∧ V i = e.symm '' P :=
    fun i => ⟨chartAt _ (i : X), chart_mem_atlas _ _, P i, hP i, hPe i, rfl⟩
  have hdis : ∀ i ∈ t, Disjoint D (V i) := by
    intro i _
    rw [Set.disjoint_left]
    exact fun x hx hy => (hPU i hy).2 hx
  obtain ⟨T', B', φ, φ', hB', hiso, hmap, hreg⟩ :=
    T.exists_union_charts_with_regularNeighborhood B hB V hV t hdis
  refine ⟨Y ∪ ⋃ i ∈ t, V i, T', B', φ, φ', ?_, ?_, hB', hiso, hmap, hreg⟩
  · intro x hx
    by_cases hxY : x ∈ interior Y
    · exact interior_mono subset_union_left hxY
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht ⟨hx, hxY⟩)
      exact interior_mono (fun y hy => Or.inr (mem_iUnion₂.mpr ⟨i, hi, hy⟩)) hxi
  · refine union_subset hYU (iUnion₂_subset fun i _ => ?_)
    exact (hPU i).trans sdiff_subset

open Classical in
theorem PLPiece.exists_manifold_neighborhood_with_core {m : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) X]
    [T2Space X] [HasGroupoid X (plGroupoid (m + 1))] {Y : Set X} (T : PLPiece (m + 1) X Y)
    (B : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin T.ambientDim)))
    (hB : B.faces ⊆ T.piece.complex.faces)
    (hBY : T.piece.map '' (regularNeighborhoodIn T.piece.complex B.space).space ⊆ interior Y)
    {C U : Set X} (hC : IsCompact C) (hU : IsOpen U) (hYU : Y ⊆ U) (hCU : C ⊆ U) :
    ∃ P : Set X, ∃ T' : PLPiece (m + 1) X P,
      ∃ L A : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin T'.ambientDim)),
        ∃ φ : EuclideanSpace ℝ (Fin T.ambientDim) → EuclideanSpace ℝ (Fin T'.ambientDim),
          ∃ φ' : EuclideanSpace ℝ (Fin T'.ambientDim) → EuclideanSpace ℝ (Fin T.ambientDim),
            IsCombinatorialManifoldWithBoundary (m + 1) T'.piece.complex ∧ P ⊆ U ∧
              L.faces ⊆ T'.piece.complex.faces ∧ Y ∪ C ⊆ T'.piece.map '' L.space ∧
                Y ∪ C ⊆ interior P ∧
                  T'.piece.map '' (regularNeighborhoodIn T'.piece.complex L.space).space ⊆
                    interior P ∧ A.faces ⊆ L.faces ∧ IsGlueIso B A φ φ' ∧
                      ∀ x ∈ B.space, T'.piece.map (simplicialMap B φ x) = T.piece.map x := by
  obtain ⟨Q, TQ, A, φ, φ', hYQ, hQU, hA, hiso, hmap, hreg⟩ :=
    T.exists_neighborhood_preserving_subcomplex B hB hBY hC hU hYU hCU
  have hAQ : TQ.piece.map '' (regularNeighborhoodIn TQ.piece.complex A.space).space ⊆
      interior Q := hreg.trans (hBY.trans (interior_subset.trans (fun _ hy => hYQ (Or.inl hy))))
  obtain ⟨P, TP, L, hman, hL, hAL, hcover, hYP, hPQ, hTP, hdeep⟩ :=
    TQ.piece.exists_manifold_neighborhood_preserving_subcomplex A hA hAQ
      (T.piece.isCompact.union hC) hYQ
  refine ⟨P, ⟨TQ.ambientDim, TP⟩, L, A, φ, φ', hman,
    hPQ.trans (interior_subset.trans hQU), hL, hcover, hYP, hdeep, hAL, hiso, ?_⟩
  intro x hx
  change TP.map (simplicialMap B φ x) = T.piece.map x
  rw [hTP]
  exact hmap x hx

end DifferentialGeometry.Topology.PiecewiseLinear
