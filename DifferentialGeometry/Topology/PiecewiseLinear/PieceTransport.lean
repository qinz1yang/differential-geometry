import DifferentialGeometry.Topology.PiecewiseLinear.SubdivisionTransport

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem isGlueIso_of_faces_eq_linearEquiv [DecidableEq E] [DecidableEq F]
    (K : Geometry.SimplicialComplex ℝ E) (K' : Geometry.SimplicialComplex ℝ F) (L : E ≃ₗ[ℝ] F)
    (hfaces : K'.faces = simplicialImageFaces K L) : IsGlueIso K K' L L.symm := by
  refine ⟨fun s hs => hfaces.symm.subset ⟨s, hs, rfl⟩, ?_,
    fun _ _ v _ => L.symm_apply_apply v, fun _ _ v _ => L.apply_symm_apply v⟩
  intro t ht
  obtain ⟨s, hs, rfl⟩ := hfaces.subset ht
  rw [Finset.image_image]
  have heq : s.image (L.symm ∘ L) = s.image id :=
    Finset.image_congr fun v _ => L.symm_apply_apply v
  rwa [heq, Finset.image_id]

theorem PLPieceIn.exists_transport_with_regularNeighborhood
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [DecidableEq E] [DecidableEq F]
    {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    {Y : Set X} (T : PLPieceIn E n X Y) (L : E ≃ₗ[ℝ] F)
    (B : Geometry.SimplicialComplex ℝ E) (hB : B.faces ⊆ T.complex.faces) :
    ∃ T' : PLPieceIn F n X Y, ∃ B' : Geometry.SimplicialComplex ℝ F,
      B'.faces ⊆ T'.complex.faces ∧ IsGlueIso B B' L L.symm ∧
        (∀ x ∈ B.space, T'.map (L x) = T.map x) ∧
          T'.map '' (regularNeighborhoodIn T'.complex B'.space).space =
            T.map '' (regularNeighborhoodIn T.complex B.space).space := by
  obtain ⟨T', hfaces, hmap⟩ := T.exists_transport L
  have hiso := isGlueIso_of_faces_eq_linearEquiv T.complex T'.complex L hfaces
  obtain ⟨B', hB', hisoB⟩ := hiso.exists_subcomplex B hB
  have hsub := space_mono_of_faces_subset hB
  have hsimp : EqOn (simplicialMap T.complex L) L T.complex.space :=
    simplicialMap_eq_of_forall_affineOn T.complex L fun _ _ =>
      ⟨(L : E →ₗ[ℝ] F).toAffineMap, fun _ _ => rfl⟩
  have hsimpB : EqOn (simplicialMap B L) L B.space :=
    simplicialMap_eq_of_forall_affineOn B L fun _ _ =>
      ⟨(L : E →ₗ[ℝ] F).toAffineMap, fun _ _ => rfl⟩
  have himageB : simplicialMap T.complex L '' B.space = B'.space :=
    ((hsimp.mono hsub).image_eq.trans hsimpB.image_eq.symm).trans hisoB.image_left
  have hreg : L '' (regularNeighborhoodIn T.complex B.space).space =
      (regularNeighborhoodIn T'.complex B'.space).space := by
    have hh := hiso.image_regularNeighborhoodIn hsub
    rw [himageB] at hh
    exact (hsimp.mono (space_regularNeighborhoodIn_subset _ _)).image_eq.symm.trans hh
  refine ⟨T', B', hB', hisoB, fun x hx => hmap x (hsub hx), ?_⟩
  rw [← hreg, image_image]
  exact (show EqOn (T'.map ∘ L) T.map (regularNeighborhoodIn T.complex B.space).space from
    fun x hx => hmap x (space_regularNeighborhoodIn_subset _ _ hx)).image_eq

open Classical in
theorem PLPieceIn.exists_pLPiece_with_regularNeighborhood [FiniteDimensional ℝ E] [DecidableEq E]
    {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    {Y : Set X} (T : PLPieceIn E n X Y) (B : Geometry.SimplicialComplex ℝ E)
    (hB : B.faces ⊆ T.complex.faces) :
    ∃ T' : PLPiece n X Y,
      ∃ B' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin T'.ambientDim)),
        ∃ φ : E → EuclideanSpace ℝ (Fin T'.ambientDim),
          ∃ φ' : EuclideanSpace ℝ (Fin T'.ambientDim) → E,
            B'.faces ⊆ T'.piece.complex.faces ∧ IsGlueIso B B' φ φ' ∧
              (∀ x ∈ B.space, T'.piece.map (simplicialMap B φ x) = T.map x) ∧
                T'.piece.map '' (regularNeighborhoodIn T'.piece.complex B'.space).space =
                  T.map '' (regularNeighborhoodIn T.complex B.space).space := by
  let L : E ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (Module.finBasis ℝ E).equivFun.trans (WithLp.linearEquiv 2 ℝ _).symm
  obtain ⟨T', B', hB', hiso, hmap, hreg⟩ := T.exists_transport_with_regularNeighborhood L B hB
  refine ⟨⟨Module.finrank ℝ E, T'⟩, B', L, L.symm, hB', hiso, ?_, hreg⟩
  intro x hx
  have heq := simplicialMap_eq_of_forall_affineOn B L
    (fun _ _ => ⟨(L : E →ₗ[ℝ] _).toAffineMap, fun _ _ => rfl⟩) hx
  exact (congrArg T'.map heq).trans (hmap x hx)

end DifferentialGeometry.Topology.PiecewiseLinear
